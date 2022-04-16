use crate::vfs::{INode, Metadata, Result};
use alloc::{string::String, sync::Arc};

pub struct File {
    inode: Arc<dyn INode>,
    offset: usize,
    readable: bool,
    writable: bool,
}

impl File {
    pub fn new(inode: Arc<dyn INode>, readable: bool, writable: bool) -> Self {
        File {
            inode,
            offset: 0,
            readable,
            writable,
        }
    }

    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        assert!(self.readable);
        let len = self.inode.read_at(self.offset, buf)?;
        self.offset += len;
        Ok(len)
    }

    pub fn write(&mut self, buf: &[u8]) -> Result<usize> {
        assert!(self.writable);
        let len = self.inode.write_at(self.offset, buf)?;
        self.offset += len;
        Ok(len)
    }

    pub fn info(&self) -> Result<Metadata> {
        self.inode.metadata()
    }

    pub fn get_entry(&mut self) -> Result<String> {
        assert!(self.readable);
        let (next_offset, name) = self.inode.get_entry(self.offset)?;
        self.offset = next_offset;
        return Ok(name);
    }
}
