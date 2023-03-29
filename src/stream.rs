pub trait PeekableStream<'a, T> {
    fn is_at_end(&'a self) -> bool;
    fn lookaround(&'a self, offset: i32) -> Option<&'a T>;
    fn shift(&'a mut self, offset: i32) -> ();
}


#[derive(Debug)]
pub struct Stream<T>
    where T: Clone
{
    iter: Vec<T>,
    ctr: usize,
}

impl<'a, T> Stream<T>
    where T: Clone
{
    pub fn new(elements: &[T]) -> Self {
        Self {
            iter: elements.iter().cloned().collect(),
            ctr: 0,
        }
    }

    pub fn size(&'a self) -> usize {
        self.iter.len()
    }

    pub fn advance(&'a mut self) -> () {
        self.ctr = self.compute_bounded_offset(1) as usize;
    }

    pub fn peek(&'a self) -> Option<&'a T> {
        self.lookaround(0)
    }

    //pub fn consume(&'a mut self) -> Option<&'a T> {
    //    let tmp = self.peek();
    //    self.advance();
    //    tmp
    //}

    /// Computes current stream pointer position offset by integer `offset`
    /// amount, returning the new position in the range `[-1, size()]`.
    ///
    /// Note: this function makes the assumption that `i128` contains the range
    /// `[-usize, usize]`.
    fn compute_bounded_offset(&self, offset: i32) -> i128 {
        let curr: i128 = self.ctr as i128 + offset as i128; //so no over/underflow
        if offset < 0 {
            std::cmp::max(-1, curr)
        } else {
            std::cmp::min(self.iter.len(), curr as usize) as i128
        }
    }
}

impl<'a, T> PeekableStream<'a, T> for Stream<T>
    where T: Clone
{
    fn is_at_end(&'a self) -> bool {
        self.ctr >= self.iter.len()
    }

    fn lookaround(&'a self, offset: i32) -> Option<&'a T> {
        let i = self.compute_bounded_offset(offset);
        if i < 0 || self.size() <= i as usize {
            None
        } else {
            Some(&(self.iter[i as usize]))
        }
    }

    fn shift(&'a mut self, offset: i32) -> () {
        let i = self.compute_bounded_offset(offset);
        self.ctr = i as usize;
    }
}
