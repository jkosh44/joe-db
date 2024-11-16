//! This module consists of the structs used to represent data on disk and in memory.

use std::error::Error;
use std::fmt::{Display, Formatter};

#[cfg(test)]
use crate::data::tests::{DebugPage, DebugRecord};
use crate::util::{bytes_from_u32, u32_from_bytes, U32_SIZE};

/// A [`Page`] represents a disk block in memory. It contains one or more [`Record`]s. The metadata
/// starts at the front of the block and grows towards the back. The actual data starts at the back
/// of the block and grows forward. A block is considered full when the two sections meet.
///
/// - The first 32-bits of a page indicate the number of records.
/// - The next n * 32 bits are used to indicate the offset of each record.
/// - The rest of the block stores the actual data.
///
/// When a record is deleted, its key length is set to 0.
///
/// Block format:
/// ---------------------------------------------------------------------------------------------
/// |     Metadata     |          Offset Section          | Empty |        Data Section         |
/// ---------------------------------------------------------------------------------------------
/// | num records (2B) | offset #1 (2B) | ... | offset #N | empty | record #n | ... | record #1 |
/// ---------------------------------------------------------------------------------------------
///
/// Record format:
/// ---------------------------------------------------------------------
/// |                             Record #i                             |
/// ---------------------------------------------------------------------
/// | key len (2B) | key (key len) | value len (2B) | value (value len) |
/// ---------------------------------------------------------------------
#[derive(Debug)]
struct Page {
    offsets: Vec<u32>,
    block: Vec<u8>,
}

impl Page {
    fn from_size(block_size: usize) -> Self {
        assert!(
            block_size <= u32::MAX as usize,
            "block size ({block_size}) offsets must fit into u32"
        );
        Self {
            offsets: Vec::new(),
            block: (0..block_size).map(|_| 0).collect(),
        }
    }

    fn num_records(&self) -> usize {
        self.offsets.len()
    }

    fn capacity(&self) -> usize {
        self.block.len()
    }

    fn space_used(&self) -> usize {
        let num_records_size = U32_SIZE;
        let offsets_size = self.num_records() * U32_SIZE;
        let data_size = match self.offsets.last() {
            Some(offset) => self.block.len() - (*offset as usize),
            None => 0,
        };
        num_records_size + offsets_size + data_size
    }

    fn free_space(&self) -> usize {
        self.capacity() - self.space_used()
    }

    fn get_record(&self, idx: usize) -> Option<Record> {
        // key length
        let start = *self.offsets.get(idx)? as usize;
        let end = start + U32_SIZE;
        let key_len = u32_from_bytes(&self.block[start..end]) as usize;

        // Record has been deleted.
        if key_len == 0 {
            return Some(Record::empty());
        }

        // key
        let start = end;
        let end = start + key_len;
        let key = &self.block[start..end];

        // value length
        let start = end;
        let end = start + U32_SIZE;
        let val_len = u32_from_bytes(&self.block[start..end]) as usize;

        // value
        let start = end;
        let end = start + val_len;
        let value = &self.block[start..end];

        Some(Record { key, value })
    }

    fn get_records_by_key<'a>(&'a self, key: &'a [u8]) -> impl Iterator<Item = Record<'a>> {
        self.into_iter().filter(move |r| r.key == key)
    }

    fn insert_record<'a>(&mut self, record: Record<'a>) -> Result<(), InsertError<'a>> {
        // There must be enough room for the record and offset.
        // We subtract a u32 size from capacity to account for the num_records field.
        if record.len() + U32_SIZE > self.capacity() - U32_SIZE {
            return Err(InsertError::RecordTooLarge);
        }
        if record.len() + U32_SIZE > self.free_space() {
            return Err(InsertError::BlockFull(record));
        }

        let last_record_start =
            self.offsets.last().copied().unwrap_or_else(|| {
                u32::try_from(self.block.len()).expect("block len fits into u32")
            });
        let offset =
            last_record_start - u32::try_from(record.len()).expect("record len fits into u32");
        self.offsets.push(offset);

        // key length
        let start = offset as usize;
        let end = start + U32_SIZE;
        let key_len = u32::try_from(record.key.len()).expect("record key len fits into u32");
        self.block[start..end].copy_from_slice(&bytes_from_u32(key_len));

        // key
        let start = end;
        let end = start + key_len as usize;
        self.block[start..end].copy_from_slice(&record.key);

        // value length
        let start = end;
        let end = start + U32_SIZE;
        let val_len = u32::try_from(record.value.len()).expect("record key len fits into u32");
        self.block[start..end].copy_from_slice(&bytes_from_u32(val_len));

        // value
        let start = end;
        let end = start + val_len as usize;
        self.block[start..end].copy_from_slice(&record.value);

        Ok(())
    }

    fn delete_record(&mut self, idx: usize) {
        let Some(offset) = self.offsets.get(idx) else {
            return;
        };
        let start = *offset as usize;
        let end = start + U32_SIZE;
        self.block[start..end].copy_from_slice(&bytes_from_u32(0));
    }

    fn delete_records_by_key(&mut self, key: &[u8]) {
        for idx in 0..self.num_records() {
            if let Some(record) = self.get_record(idx) {
                if record.key == key {
                    self.delete_record(idx);
                }
            }
        }
    }

    #[allow(unused)]
    #[cfg(test)]
    fn debug(&self) -> DebugPage {
        self.into()
    }
}

impl<'a> IntoIterator for &'a Page {
    type Item = Record<'a>;
    type IntoIter = BlockIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        BlockIterator::new(self)
    }
}

/// An iterator over a block.
#[derive(Debug)]
struct BlockIterator<'a> {
    page: &'a Page,
    idx: usize,
}

impl<'a> BlockIterator<'a> {
    fn new(page: &'a Page) -> Self {
        Self { page, idx: 0 }
    }
}

impl<'a> Iterator for BlockIterator<'a> {
    type Item = Record<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut record = Record::empty();
        while record.is_tombstone() {
            record = self.page.get_record(self.idx)?;
            self.idx += 1;
        }
        Some(record)
    }
}

/// A [`Record`] represents a reference to a single key-value pair.
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
struct Record<'a> {
    key: &'a [u8],
    value: &'a [u8],
}

impl<'a> Record<'a> {
    fn empty() -> Self {
        Self {
            key: &[],
            value: &[],
        }
    }

    fn len(&self) -> usize {
        U32_SIZE + self.key.len() + U32_SIZE + self.value.len()
    }

    fn is_tombstone(&self) -> bool {
        self.key.is_empty()
    }

    #[cfg(test)]
    fn debug(&self) -> DebugRecord {
        self.into()
    }
}

/// An error from a failed insert.
#[derive(Debug, PartialEq, Eq)]
enum InsertError<'a> {
    BlockFull(Record<'a>),
    RecordTooLarge,
}

impl Display for InsertError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::BlockFull(_) => write!(f, "block full"),
            InsertError::RecordTooLarge => write!(f, "record too large"),
        }
    }
}

impl Error for InsertError<'_> {}

#[cfg(test)]
mod tests {
    use std::str::from_utf8;

    use crate::data::{InsertError, Page, Record};
    use crate::util::U32_SIZE;

    #[test]
    fn test_page() {
        const N: usize = 5;
        let block_size = 1024;
        let mut page = Page::from_size(block_size);
        let mut free_space = block_size - U32_SIZE;
        let mut all_records = Vec::new();

        fn insert<'a>(
            page: &mut Page,
            r: &Record<'a>,
            free_space: &mut usize,
            all_records: &mut Vec<DebugRecord>,
        ) {
            page.insert_record(r.clone()).unwrap();
            *free_space -= r.len() + U32_SIZE;
            all_records.push(r.into());
        }

        assert_eq!(page.num_records(), 0);
        assert_eq!(page.capacity(), block_size);
        assert_eq!(page.free_space(), free_space);
        assert_eq!(page.get_record(0).map(|r| r.debug()), None);
        assert_eq!(
            records_into_debug(page.get_records_by_key(b"foo")),
            Vec::new()
        );
        assert_eq!(records_into_debug(page.into_iter()), all_records);

        // Insert some records.
        for i in 0..N {
            let key = format!("k{i}").into_bytes();
            let key = key.as_slice();
            let value = format!("v{i}").into_bytes();
            let value = value.as_slice();
            let r = Record { key, value };

            insert(&mut page, &r, &mut free_space, &mut all_records);

            assert_eq!(page.num_records(), i + 1);
            assert_eq!(page.capacity(), block_size);
            assert_eq!(page.free_space(), free_space);
            assert_eq!(
                page.get_record(i).map(|r| r.debug()),
                Some(r.clone().debug())
            );
            assert_eq!(
                records_into_debug(page.get_records_by_key(key)),
                records_into_debug([r])
            );
            assert_eq!(records_into_debug(page.into_iter()), all_records);
        }

        // Insert duplicate records.
        for i in 0..N {
            let key = format!("k{i}").into_bytes();
            let key = key.as_slice();
            let value = format!("v{i}").into_bytes();
            let value = value.as_slice();
            let value1 = format!("vv{i}").into_bytes();
            let value1 = value1.as_slice();
            let value2 = format!("vvv{i}").into_bytes();
            let value2 = value2.as_slice();
            let r = Record { key, value };
            let r1 = Record { key, value: value1 };
            let r2 = Record { key, value: value2 };

            insert(&mut page, &r1, &mut free_space, &mut all_records);
            insert(&mut page, &r2, &mut free_space, &mut all_records);

            assert_eq!(page.num_records(), N + (i + 1) * 2);
            assert_eq!(page.capacity(), block_size);
            assert_eq!(page.free_space(), free_space);
            assert_eq!(
                page.get_record(N + (i * 2)).map(|r| r.debug()),
                Some(r1.debug())
            );
            assert_eq!(
                page.get_record(N + (i * 2) + 1).map(|r| r.debug()),
                Some(r2.debug())
            );
            assert_eq!(
                records_into_debug(page.get_records_by_key(key)),
                records_into_debug([r, r1, r2])
            );
            assert_eq!(records_into_debug(page.into_iter()), all_records);
        }

        // Delete records.
        for i in 0..N {
            let key = format!("k{i}").into_bytes();
            let key = key.as_slice();
            let value = format!("v{i}").into_bytes();
            let value = value.as_slice();
            let value1 = format!("vv{i}").into_bytes();
            let value1 = value1.as_slice();
            let value2 = format!("vvv{i}").into_bytes();
            let value2 = value2.as_slice();
            let r = Record { key, value };
            let r1 = Record { key, value: value1 };
            let r2 = Record { key, value: value2 };

            page.delete_record(i);
            all_records.retain(|record| record != &r.debug());

            assert_eq!(page.num_records(), 3 * N);
            assert_eq!(page.capacity(), block_size);
            assert_eq!(page.free_space(), free_space);
            assert_eq!(
                page.get_record(i).map(|r| r.debug()),
                Some(Record::empty().debug())
            );
            assert_eq!(
                records_into_debug(page.get_records_by_key(key)),
                records_into_debug([r1, r2])
            );
            assert_eq!(records_into_debug(page.into_iter()), all_records);
        }

        // Delete records by key.
        for i in 0..N {
            let key = format!("k{i}").into_bytes();
            let key = key.as_slice();
            let value1 = format!("vv{i}").into_bytes();
            let value1 = value1.as_slice();
            let value2 = format!("vvv{i}").into_bytes();
            let value2 = value2.as_slice();
            let r1 = Record { key, value: value1 };
            let r2 = Record { key, value: value2 };

            page.delete_records_by_key(key);
            all_records.retain(|record| record != &r1.debug() && record != &r2.debug());

            assert_eq!(page.num_records(), 3 * N);
            assert_eq!(page.capacity(), block_size);
            assert_eq!(page.free_space(), free_space);
            assert_eq!(
                page.get_record(N + (i * 2)).map(|r| r.debug()),
                Some(Record::empty().debug())
            );
            assert_eq!(
                page.get_record(N + (i * 2) + 1).map(|r| r.debug()),
                Some(Record::empty().debug())
            );
            assert_eq!(records_into_debug(page.get_records_by_key(key)), Vec::new());
            assert_eq!(records_into_debug(page.into_iter()), all_records);
        }
    }

    #[test]
    fn test_large_key() {
        let block_size = 1024;
        let mut page = Page::from_size(block_size);
        let record_size = block_size - U32_SIZE - U32_SIZE;
        let key_value_size = record_size - U32_SIZE - U32_SIZE;
        let (key_size, value_size) = (key_value_size / 2, key_value_size / 2 + 2);
        let key: Vec<_> = (0..key_size).map(|_| 1).collect();
        let key = key.as_slice();
        let value: Vec<_> = (0..value_size).map(|_| 1).collect();
        let value = value.as_slice();
        let record = Record { key, value };

        assert_eq!(
            page.insert_record(record).unwrap_err(),
            InsertError::RecordTooLarge
        );
    }

    #[test]
    fn test_full_block() {
        let block_size = 32;
        let mut page = Page::from_size(block_size);
        let key = "k".to_string().into_bytes();
        let key = key.as_slice();
        let value = "v".to_string().into_bytes();
        let value = value.as_slice();
        let record = Record { key, value };
        page.insert_record(record.clone()).unwrap();
        page.insert_record(record.clone()).unwrap();

        assert_eq!(
            page.insert_record(record.clone()).unwrap_err(),
            InsertError::BlockFull(record),
        );
    }

    #[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
    pub(super) struct DebugRecord {
        key: String,
        value: String,
    }

    impl<'a> From<&Record<'a>> for DebugRecord {
        fn from(record: &Record) -> Self {
            let key = from_utf8(record.key).unwrap().to_string();
            let value = from_utf8(record.value).unwrap().to_string();
            DebugRecord { key, value }
        }
    }

    impl<'a> From<Record<'a>> for DebugRecord {
        fn from(record: Record) -> Self {
            (&record).into()
        }
    }

    fn records_into_debug<'a>(records: impl IntoIterator<Item = Record<'a>>) -> Vec<DebugRecord> {
        records.into_iter().map(From::from).collect()
    }

    #[allow(unused)]
    #[derive(Debug)]
    pub(super) struct DebugPage {
        num_records: u32,
        offsets: Vec<u32>,
        free_space: usize,
        records: Vec<DebugRecord>,
    }

    impl From<&Page> for DebugPage {
        fn from(page: &Page) -> Self {
            let mut records: Vec<_> = page.into_iter().map(|r| r.into()).collect();
            records.reverse();
            Self {
                num_records: u32::try_from(page.num_records()).expect("block len fits into u32"),
                offsets: page.offsets.clone(),
                free_space: page.free_space(),
                records,
            }
        }
    }
}
