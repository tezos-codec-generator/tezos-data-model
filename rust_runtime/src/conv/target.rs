pub trait Target {
    fn anticipate(&mut self, extra: usize);

    fn push_one(&mut self, b: u8) -> usize;

    fn push_all(&mut self, buf: &[u8]) -> usize;

    fn resolve(&mut self);

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize;

    fn create() -> Self;
}

pub type ByteCounter = std::io::Sink;

impl Target for ByteCounter {
    #[inline]
    fn anticipate(self: &mut Self, _: usize) {
        return;
    }

    #[inline]
    fn push_one(self: &mut Self, _: u8) -> usize {
        1
    }

    #[inline]
    fn push_all(self: &mut Self, buf: &[u8]) -> usize {
        buf.len()
    }

    #[inline]
    fn resolve(self: &mut Self) {
        return;
    }

    #[inline]
    fn push_many<const N: usize>(&mut self, _: [u8; N]) -> usize {
        N
    }

    fn create() -> Self {
        std::io::sink()
    }
}

impl Target for Vec<u8> {
    #[inline]
    fn push_one(&mut self, b: u8) -> usize {
        self.push(b);
        1
    }

    #[inline]
    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.extend_from_slice(buf);
        buf.len()
    }

    #[inline]
    fn anticipate(&mut self, extra: usize) {
        self.reserve_exact(extra)
    }

    #[inline]
    fn resolve(self: &mut Self) {
        return;
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.extend(&arr);
        N
    }

    fn create() -> Self {
        Self::new()
    }
}
/*
impl<T: std::io::Write> Target for T {
    fn push_one(&mut self, b: u8) -> usize {
        self.write(&[b])
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.write(&arr)
    }

    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.write(buf)
    }
}
*/
