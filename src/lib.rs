use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeekableBuffer<T>
    where T: Clone
{
    iter: Vec<T>,
    ctr: Rc<RefCell<usize>>,
}

impl<T> IntoIterator for PeekableBuffer<T>
    where T: Clone
{
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter()
    }
}

impl<T> PeekableBuffer<T>
    where T: Clone
{
    /// Creates a `Stream` object that owns all elements of `&[T]` via cloning.
    pub fn new<E>(elements: E) -> Self
        where E: AsRef<[T]>
    {
        Self {
            iter: elements.as_ref().iter().cloned().collect(),
            ctr: Rc::new(RefCell::new(0)),
        }
    }

    /// Returns true if the stream has reached the end.
    pub fn is_at_end(&self) -> bool {
        let borrowed_ctr = self.ctr.borrow();
        *borrowed_ctr >= self.iter.len()
    }

    /// Returns the number of elements in the stream.
    pub fn len(&self) -> usize {
        self.iter.len()
    }

    /// Returns a reference to the element `offset` positions away from the
    /// element currently being pointed to by the stream pointer. If the
    /// computed offset is outside the bounds of the stream, `None` is returned.
    pub fn lookaround(&self, offset: i64) -> Option<&T> {
        let i = self.compute_bounded_offset(offset);
        if i < 0 || self.len() <= i as usize {
            None
        } else {
            Some(&(self.iter[i as usize]))
        }
    }

    /// Returns a reference to the element just after the element currently
    /// being pointed to by the stream pointer. This is equivalent to calling
    /// `lookaround(1)`.
    pub fn peek(&self) -> Option<&T> {
        self.lookaround(1)
    }

    /// Returns a reference to the element currently being pointed to by the
    /// stream pointer. This is equivalent to calling `lookaround(0)`.
    pub fn current(&self) -> Option<&T> {
        self.lookaround(0)
    }

    /// Shifts the stream pointer by `offset` positions. The computed offset
    /// will be within the range `[0, len()]`. If the computed offset is less
    /// than 0, the stream pointer will point to the first element. If the
    /// computed offset is greater than `len() - 1`, the stream pointer will
    /// point to the end and `is_at_end()` returns true.
    pub fn shift(&mut self, offset: i64) -> () {
        let i = self.compute_bounded_offset(offset);
        *self.ctr.borrow_mut() = if i == -1 {
            0
        } else {
            i as usize
        }
    }

    /// A convenience method that advances the stream pointer by 1. If the
    /// stream is at the end, no action is taken. This is equivalent to calling
    /// `shift(1)`.
    pub fn advance(&mut self) -> () {
        self.shift(1);
    }

    /// Sets the zero-indexed position of the stream pointer. If the
    /// given `pos` is outside of the range of the stream length, the
    /// stream pointer will be set to `len()`.
    pub fn set_pos(&mut self, pos: usize) -> usize {
        let i = std::cmp::min(pos, self.iter.len());
        *self.ctr.borrow_mut() = i;
        i
    }

    /// Returns the current zero-indexed position of the stream pointer. The
    /// returned value is in the range `[0, len()]`.
    pub fn pos(&self) -> usize {
        *self.ctr.borrow_mut()
    }

    /// Returns a reference to the element currently being pointed to by the
    /// stream pointer, then advances the pointer by 1.
    pub fn consume(&mut self) -> Option<&T> {
        let tmp = self.current();
        let mut mctr = self.ctr.borrow_mut();
        *mctr += 1;
        if *mctr >= self.len() {
            *mctr = self.len(); //just in case
        }
        tmp
    }

    /// Returns an iterator containing elements that satisfy the given
    /// predicate, starting from the element currently pointed to by the stream
    /// pointer, up to either the end of the stream, or when the predicate
    /// returns fall, whichever comes first.
    pub fn take_while<P>(&mut self, predicate: P) -> impl Iterator<Item = &T>
        where P: Fn(&T) -> bool
    {
        let mut v = Vec::new();
        let mut mctr = self.ctr.borrow_mut();
        while *mctr < self.iter.len() && predicate(&self.iter[*mctr]) {
            v.push(&self.iter[*mctr]);
            *mctr += 1;
        }
        v.into_iter()
    }

    /// Returns an iterator containing all elements in the range
    /// `[pos(), pos() + n)`. The stream pointer will point to either the
    /// end of the stream, or the element at `pos() + n`, whichever is
    /// first. If `pos() + n` is outside the bounds of the stream, then
    /// the rest of the stream is consumed and `is_at_end()` returns true.
    pub fn take(&mut self, n: usize) -> impl Iterator<Item = &T> {
        let mut v = Vec::new();
        let mut mctr = self.ctr.borrow_mut();
        for _ in 0..n {
            if *mctr >= self.iter.len() {
                break;
            }
            v.push(&self.iter[*mctr]);
            *mctr += 1;
        }
        v.into_iter()
    }

    /// Returns true if the current element matches the given predicate, false
    /// otherwise. The function will return false if the stream is at the end
    /// regardless of the predicate.
    pub fn accept<P>(&self, predicate: P) -> bool
        where P: Fn(&T) -> bool
    {
        if self.is_at_end() {
            false
        } else {
            predicate(self.current().unwrap())
        }
    }

    /// Returns a new `PeekableBuffer` containing all elements from the range
    /// `[from_inc, len() - 1]`, cloning the required elements into their
    /// own iterable.
    pub fn slice_from(&self, from_inc: usize) -> PeekableBuffer<T> {
        self.slice_between(from_inc, self.len())
    }

    /// Returns a new `PeekableBuffer` containing all elements from the range
    /// `[from_inc, to_exc - 1]`, cloning the required elements into their
    /// own iterable.
    pub fn slice_between(&self, from_inc: usize, to_exc: usize) -> PeekableBuffer<T> {
        let f = self.compute_bounded_offset(from_inc as i64);
        let t = self.compute_bounded_offset(to_exc as i64);
        PeekableBuffer::new(&self.iter[f as usize..t as usize])
    }

    /// Computes current stream pointer position offset by integer `offset`
    /// amount, returning the new position in the range `[-1, len()]`.
    ///
    /// Note: this function makes the assumption that `i128` contains the range
    /// `[-usize, usize]`.
    fn compute_bounded_offset(&self, offset: i64) -> i128 {
        let curr: i128 = *self.ctr.borrow_mut() as i128 + offset as i128; //so no over/underflow
        if offset < 0 {
            std::cmp::max(-1, curr)
        } else {
            std::cmp::min(self.iter.len(), curr as usize) as i128
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_at_end() {
        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);
        for _ in elems {
            stream.advance();
        }
        assert!(stream.is_at_end());
    }

    #[test]
    fn test_len() {
        let elems = vec![1, 2, 3, 4];
        let stream = PeekableBuffer::new(&elems);
        assert_eq!(stream.len(), elems.len());
    }

    #[test]
    fn test_lookaround_peek_current() {
        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);

        assert_eq!(stream.len(), 3);

        // pointer at position 0
        assert!(!stream.is_at_end());
        assert_eq!(stream.pos(), 0);
        assert_eq!(stream.current(), Some(&1));
        assert_eq!(stream.peek(), Some(&2));
        assert_eq!(stream.lookaround(-1), None);
        assert_eq!(stream.lookaround(0), Some(&1));
        assert_eq!(stream.lookaround(1), Some(&2));
        assert_eq!(stream.lookaround(2), Some(&3));
        assert_eq!(stream.lookaround(3), None);
        assert_eq!(stream.lookaround(4), None);

        assert!(!stream.is_at_end());
        assert_eq!(stream.current(), Some(&1));

        // pointer at position 1
        stream.advance();
        assert_eq!(stream.pos(), 1);
        assert_eq!(stream.peek(), Some(&3));
        stream.shift(-1);
        assert_eq!(stream.pos(), 0);
        assert_eq!(stream.peek(), Some(&2));
        stream.shift(1);
        assert_eq!(stream.pos(), 1);
        assert_eq!(stream.peek(), Some(&3));
        assert!(!stream.is_at_end());
        assert_eq!(stream.current(), Some(&2));
        assert_eq!(stream.peek(), Some(&3));
        assert_eq!(stream.lookaround(-2), None);
        assert_eq!(stream.lookaround(-1), Some(&1));
        assert_eq!(stream.lookaround(0), Some(&2));
        assert_eq!(stream.lookaround(1), Some(&3));
        assert_eq!(stream.lookaround(2), None);
        assert_eq!(stream.lookaround(3), None);

        assert!(!stream.is_at_end());
        assert_eq!(stream.current(), Some(&2));
    }

    #[test]
    fn test_shift_advance() {
        fn limit(stream: &mut PeekableBuffer<i64>) {
            let offset_from_end = *stream.ctr.borrow_mut() as i64 - stream.len() as i64;

            // shift right
            stream.shift(i64::MAX);
            assert_eq!(stream.pos(), 3);
            assert!(stream.is_at_end());
            assert_eq!(stream.current(), None);
            stream.shift(-2);
            assert_eq!(stream.current(), Some(&2));

            // shift left
            assert!(!stream.is_at_end());
            stream.shift(i64::MIN);
            assert_eq!(stream.pos(), 0);
            assert!(!stream.is_at_end());
            assert_eq!(stream.current(), Some(&1));
            stream.shift(1);
            assert_eq!(stream.current(), Some(&2));

            // reset to original position
            stream.shift(i64::MAX);
            stream.shift(offset_from_end as i64);
        }

        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);
        for i in 1..=4 {
            assert_eq!(stream.pos(), (i - 1) as usize);
            limit(&mut stream);
            stream.advance();
        }
    }

    #[test]
    fn test_set_pos() {
        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);
        assert_eq!(stream.current(), Some(&1));
        stream.set_pos(2);
        assert_eq!(stream.current(), Some(&3));
        stream.set_pos(1);
        assert_eq!(stream.current(), Some(&2));
        stream.set_pos(0);
        assert_eq!(stream.current(), Some(&1));
        stream.set_pos(3);
        assert_eq!(stream.current(), None);
        stream.set_pos(100);
        assert_eq!(stream.current(), None);
        assert!(stream.is_at_end());
    }

    #[test]
    fn test_pos_consume() {
        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);

        assert_eq!(stream.len(), 3);

        assert_eq!(stream.pos(), 0);
        assert_eq!(stream.consume(), Some(&1));
        assert_eq!(stream.pos(), 1);
        assert_eq!(stream.consume(), Some(&2));
        assert_eq!(stream.pos(), 2);
        assert_eq!(stream.consume(), Some(&3));
        assert_eq!(stream.pos(), 3);
        assert_eq!(stream.consume(), None);
        assert_eq!(stream.pos(), 3);
        assert_eq!(stream.consume(), None);
        assert_eq!(stream.pos(), 3);
    }

    #[test]
    fn test_take_while_consumes_part_of_stream() {
        let elems = vec![1, 2, 3, 3, 4, 5];
        let mut stream = PeekableBuffer::new(&elems);

        assert_eq!(stream.len(), 6);

        let taken: Vec<&i64> = stream.take_while(|&i| i < 4).collect();
        assert_eq!(taken, vec![&1, &2, &3, &3]);

        assert_eq!(stream.pos(), 4);
        assert!(!stream.is_at_end());
        assert_eq!(stream.current(), Some(&4));
        assert_eq!(stream.peek(), Some(&5));
    }

    #[test]
    fn test_take_while_predicate_consumes_entire_stream() {
        let elems = vec![1, 2, 3, 4, 5];
        let mut stream = PeekableBuffer::new(&elems);

        assert_eq!(stream.len(), 5);

        let taken: Vec<&i64> = stream.take_while(|&i| i < 10).collect();
        assert_eq!(taken, vec![&1, &2, &3, &4, &5]);

        assert_eq!(stream.pos(), 5);
        assert!(stream.is_at_end());
        assert_eq!(stream.current(), None);
        assert_eq!(stream.peek(), None);
        assert_eq!(stream.lookaround(-1), Some(&5));
    }

    #[test]
    fn test_take_while_predicate_consumes_no_elements() {
        let elems = vec![1, 2, 3, 4, 5];
        let mut stream = PeekableBuffer::new(&elems);

        assert_eq!(stream.len(), 5);

        // at position 1
        stream.advance();

        let taken: Vec<&i64> = stream.take_while(|&i| i == 1).collect();
        assert!(taken.is_empty());

        assert_eq!(stream.pos(), 1);
        assert!(!stream.is_at_end());
        assert_eq!(stream.current(), Some(&2));
        assert_eq!(stream.peek(), Some(&3));
    }

    #[test]
    fn test_take() {
        let elems = vec![1, 2, 3, 4, 5];
        let mut stream = PeekableBuffer::new(&elems);
        assert_eq!(stream.len(), 5);

        {
            let taken: Vec<&i64> = stream.take(0).collect();
            assert!(taken.is_empty());
            assert_eq!(taken, Vec::<&i64>::new());
            assert!(stream.pos() == 0);
            assert!(!stream.is_at_end());
        }
        {
            let taken: Vec<&i64> = stream.take(2).collect();
            assert!(!taken.is_empty());
            assert_eq!(taken, vec![&1, &2]);
            assert!(stream.pos() == 2);
            assert!(!stream.is_at_end());
        }
        {
            let taken: Vec<&i64> = stream.take(2).collect();
            assert!(!taken.is_empty());
            assert_eq!(taken, vec![&3, &4]);
            assert!(stream.pos() == 4);
            assert!(!stream.is_at_end());
        }
        {
            let taken: Vec<&i64> = stream.take(2).collect();
            assert!(!taken.is_empty());
            assert_eq!(taken, vec![&5]);
            assert!(stream.pos() == 5);
            assert!(stream.is_at_end());
        }
        {
            let taken: Vec<&i64> = stream.take(10).collect();
            assert!(taken.is_empty());
            assert_eq!(taken, Vec::<&i64>::new());
            assert!(stream.pos() == 5);
            assert!(stream.is_at_end());
        }
    }

    #[test]
    fn test_accept() {
        let elems = vec![1, 2, 3];
        let mut stream = PeekableBuffer::new(&elems);
        assert!(stream.accept(|&x| x < 2));
        stream.advance();
        assert!(stream.accept(|&x| x == 2));
        stream.advance();
        assert!(stream.accept(|&x| x >= 3));
        assert!(stream.accept(|&x| x != 3) == false);
        stream.advance();
        assert!(stream.accept(|&_| true) == false);
    }

    #[test]
    pub fn slice_from() {
        let elems = vec![1, 2, 3, 4, 5];
        let stream = PeekableBuffer::new(&elems);
        assert_eq!(stream.slice_from(0), PeekableBuffer::new(&vec![1, 2, 3, 4, 5]));
        assert_eq!(stream.slice_from(1), PeekableBuffer::new(&vec![2, 3, 4, 5]));
        assert_eq!(stream.slice_from(4), PeekableBuffer::new(&vec![5]));
        assert_eq!(stream.slice_from(5), PeekableBuffer::new(&vec![]));
    }

    #[test]
    pub fn slice_between() {
        let elems = vec![1, 2, 3, 4, 5];
        let stream = PeekableBuffer::new(&elems);

        //to len()
        assert_eq!(stream.slice_between(0, 5), PeekableBuffer::new(&vec![1, 2, 3, 4, 5]));
        assert_eq!(stream.slice_between(1, 5), PeekableBuffer::new(&vec![2, 3, 4, 5]));
        assert_eq!(stream.slice_between(4, 5), PeekableBuffer::new(&vec![5]));
        assert_eq!(stream.slice_between(5, 5), PeekableBuffer::new(&vec![]));

        //to >len()
        assert_eq!(stream.slice_between(0, 10), PeekableBuffer::new(&vec![1, 2, 3, 4, 5]));
        assert_eq!(stream.slice_between(1, 10), PeekableBuffer::new(&vec![2, 3, 4, 5]));
        assert_eq!(stream.slice_between(4, 10), PeekableBuffer::new(&vec![5]));
        assert_eq!(stream.slice_between(5, 10), PeekableBuffer::new(&vec![]));

        //in between
        assert_eq!(stream.slice_between(0, 1), PeekableBuffer::new(&vec![1]));
        assert_eq!(stream.slice_between(1, 3), PeekableBuffer::new(&vec![2, 3]));
        assert_eq!(stream.slice_between(2, 4), PeekableBuffer::new(&vec![3, 4]));
        assert_eq!(stream.slice_between(3, 5), PeekableBuffer::new(&vec![4, 5]));
    }
}
