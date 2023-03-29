pub trait PeekableStream<'a, T> {
    /// Returns true if the stream has reached the end.
    fn is_at_end(&'a self) -> bool;

    /// Returns the number of elements in the stream.
    fn size(&'a self) -> usize;

    /// Returns a reference to the element `offset` positions away from the
    /// element currently being pointed to by the stream pointer. If the
    /// computed offset is outside the bounds of the stream, `None` is returned.
    fn lookaround(&'a self, offset: i32) -> Option<&'a T>;

    /// Shifts the stream pointer by `offset` positions. The computed offset
    /// will be within the range `[0, size()]`. If the computed offset is less
    /// than 0, the stream pointer will point to the first element. If the
    /// computed offset is greater than `size() - 1`, the stream pointer will
    /// point to the end and `is_at_end()` returns true.
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
    /// Creates a `Stream` object that owns all elements of `&[T]` via cloning.
    pub fn new(elements: &[T]) -> Self {
        Self {
            iter: elements.iter().cloned().collect(),
            ctr: 0,
        }
    }

    /// A convenience method that advances the stream pointer by 1. If the
    /// stream is at the end, no action is taken. This is equivalent to calling
    /// `shift(1)`.
    pub fn advance(&'a mut self) -> () {
        self.shift(1);
    }

    /// Returns a reference to the element currently being pointed to by the
    /// stream pointer.
    pub fn peek(&'a self) -> Option<&'a T> {
        self.lookaround(0)
    }

    /// Returns a clone of the element currently being pointed to by the stream
    /// pointer, then advances the pointer by 1. If a clone is not desired,
    /// it is recommended to call `peek()` followed by `advance()` manually.
    pub fn consume(&'a mut self) -> Option<T> {
        let tmp = match self.peek() {
            Some(v) => Some(v.clone()),
            None => None,
        };
        self.advance();
        tmp
    }

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

    fn size(&'a self) -> usize {
        self.iter.len()
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
