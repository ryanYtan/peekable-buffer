use std::{cell::RefCell, rc::Rc};

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
    ctr: Rc<RefCell<usize>>,
}

impl<'a, T> Stream<T>
    where T: Clone
{
    /// Creates a `Stream` object that owns all elements of `&[T]` via cloning.
    pub fn new(elements: &[T]) -> Self {
        Self {
            iter: elements.iter().cloned().collect(),
            ctr: Rc::new(RefCell::new(0)),
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

    /// Returns a reference to the element currently being pointed to by the
    /// stream pointer, then advances the pointer by 1.
    pub fn consume(&'a mut self) -> Option<&'a T> {
        let tmp = self.peek();
        *self.ctr.borrow_mut() += 1;
        if *self.ctr.borrow_mut() >= self.size() {
            *self.ctr.borrow_mut() = self.size(); //just in case
        }
        tmp
    }

    /// Computes current stream pointer position offset by integer `offset`
    /// amount, returning the new position in the range `[-1, size()]`.
    ///
    /// Note: this function makes the assumption that `i128` contains the range
    /// `[-usize, usize]`.
    fn compute_bounded_offset(&self, offset: i32) -> i128 {
        let curr: i128 = *self.ctr.borrow_mut() as i128 + offset as i128; //so no over/underflow
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
        *self.ctr.borrow_mut() >= self.iter.len()
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
        *self.ctr.borrow_mut() = if i == -1 {
            0
        } else {
            i as usize
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lookaround_peek() {
        let elems = vec![1, 2, 3];
        let mut stream = Stream::new(&elems);

        assert_eq!(stream.size(), 3);

        // pointer at position 0
        assert!(!stream.is_at_end());
        assert_eq!(stream.peek(), Some(&1));
        assert_eq!(stream.lookaround(-1), None);
        assert_eq!(stream.lookaround(0), Some(&1));
        assert_eq!(stream.lookaround(1), Some(&2));
        assert_eq!(stream.lookaround(2), Some(&3));
        assert_eq!(stream.lookaround(3), None);
        assert_eq!(stream.lookaround(4), None);

        assert!(!stream.is_at_end());
        assert_eq!(stream.peek(), Some(&1));

        // pointer at position 1
        stream.advance();
        stream.shift(-1);
        stream.shift(1);
        assert!(!stream.is_at_end());
        assert_eq!(stream.peek(), Some(&2));
        assert_eq!(stream.lookaround(-2), None);
        assert_eq!(stream.lookaround(-1), Some(&1));
        assert_eq!(stream.lookaround(0), Some(&2));
        assert_eq!(stream.lookaround(1), Some(&3));
        assert_eq!(stream.lookaround(2), None);
        assert_eq!(stream.lookaround(3), None);

        assert!(!stream.is_at_end());
        assert_eq!(stream.peek(), Some(&2));
    }

    #[test]
    fn test_shifting() {
        fn limit(stream: &mut Stream<i32>) {
            let offset_from_end = *stream.ctr.borrow_mut() as i32 - stream.size() as i32;

            // shift right
            stream.shift(i32::MAX);
            assert!(stream.is_at_end());
            assert_eq!(stream.peek(), None);
            stream.shift(-2);
            assert_eq!(stream.peek(), Some(&2));

            // shift left
            assert!(!stream.is_at_end());
            stream.shift(i32::MIN);
            assert!(!stream.is_at_end());
            assert_eq!(stream.peek(), Some(&1));
            stream.shift(1);
            assert_eq!(stream.peek(), Some(&2));

            // reset to original position
            stream.shift(i32::MAX);
            stream.shift(offset_from_end as i32);
        }

        let elems = vec![1, 2, 3];
        let mut stream = Stream::new(&elems);

        assert_eq!(stream.size(), 3);

        for _i in 1..=4 {
            limit(&mut stream);
            stream.advance();
        }
    }

    #[test]
    fn test_consume() {
        let elems = vec![1, 2, 3];
        let mut stream = Stream::new(&elems);

        assert_eq!(stream.size(), 3);

        assert_eq!(stream.consume(), Some(&1));
        assert_eq!(stream.consume(), Some(&2));
        assert_eq!(stream.consume(), Some(&3));
        assert_eq!(stream.consume(), None);
        assert_eq!(stream.consume(), None);
    }
}
