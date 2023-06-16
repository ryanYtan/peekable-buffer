# Overview
This crate defines a buffer with a cursor, plus some useful operations on the
buffer.

## Caveats
1. The parameterized type of `PeekableBuffer` must implement `Clone`
2. If your `PeekableBuffer` contains close to `usize.MAX` elements, the indexing operations will probably fail

## Quick Start
In `Cargo.toml`
```
[dependencies]
peekable_buffer = "0.1.0"
```

Create a `PeekableBuffer<T>` using
```rust
let v = vec![1, 2, 3, 4, 5];
let mut stream = PeekableBuffer::new(&v);

assert!(!stream.is_at_end());
assert_eq!(stream.pos(), 0);
assert_eq!(stream.current(), Some(&1));

stream.advance();
assert_eq!(stream.pos(), 1);
assert_eq!(stream.current(), Some(&2));

assert_eq!(stream.lookaround(-1), Some(&1));
assert_eq!(stream.lookaround(-10), None);

stream.shift(3);
assert_eq!(stream.current(), Some(&5));

assert_eq!(stream.consume(), Some(&5));
assert!(stream.is_at_end());
assert_eq!(stream.current(), None);
```

## Available Operations
These are taken directly from the source.
```rust
/// Creates a `Stream` object that owns all elements of `&[T]` via cloning.
pub fn new<E>(elements: E) -> Self
    where E: AsRef<[T]>;

/// Returns true if the stream has reached the end.
pub fn is_at_end(&self) -> bool;

/// Returns the number of elements in the stream.
pub fn len(&self) -> usize;

/// Returns a reference to the element `offset` positions away from the
/// element currently being pointed to by the stream pointer. If the
/// computed offset is outside the bounds of the stream, `None` is returned.
pub fn lookaround(&self, offset: i64) -> Option<&T>;

/// Returns a reference to the element just after the element currently
/// being pointed to by the stream pointer. This is equivalent to calling
/// `lookaround(1)`.
pub fn peek(&self) -> Option<&T>;

/// Returns a reference to the element currently being pointed to by the
/// stream pointer. This is equivalent to calling `lookaround(0)`.
pub fn current(&self) -> Option<&T>;

/// Shifts the stream pointer by `offset` positions. The computed offset
/// will be within the range `[0, len()]`. If the computed offset is less
/// than 0, the stream pointer will point to the first element. If the
/// computed offset is greater than `len() - 1`, the stream pointer will
/// point to the end and `is_at_end()` returns true.
pub fn shift(&mut self, offset: i64) -> ();

/// A convenience method that advances the stream pointer by 1. If the
/// stream is at the end, no action is taken. This is equivalent to calling
/// `shift(1)`.
pub fn advance(&mut self) -> ();

/// Sets the zero-indexed position of the stream pointer. If the
/// given `pos` is outside of the range of the stream length, the
/// stream pointer will be set to `len()`.
pub fn set_pos(&mut self, pos: usize) -> usize;

/// Returns the current zero-indexed position of the stream pointer. The
/// returned value is in the range `[0, len()]`.
pub fn pos(&self) -> usize;

/// Returns a reference to the element currently being pointed to by the
/// stream pointer, then advances the pointer by 1.
pub fn consume(&mut self) -> Option<&T>;

/// Returns an iterator containing elements that satisfy the given
/// predicate, starting from the element currently pointed to by the stream
/// pointer, up to either the end of the stream, or when the predicate
/// returns fall, whichever comes first.
pub fn take_while<P>(&mut self, predicate: P) -> impl Iterator<Item = &T>
    where P: Fn(&T) -> bool;

/// Returns an iterator containing all elements in the range
/// `[pos(), pos() + n)`. The stream pointer will point to either the
/// end of the stream, or the element at `pos() + n`, whichever is
/// first. If `pos() + n` is outside the bounds of the stream, then
/// the rest of the stream is consumed and `is_at_end()` returns true.
pub fn take(&mut self, n: usize) -> impl Iterator<Item = &T>;

/// Returns true if the current element matches the given predicate, false
/// otherwise. The function will return false if the stream is at the end
/// regardless of the predicate.
pub fn accept<P>(&self, predicate: P) -> bool
    where P: Fn(&T) -> bool;

/// Returns a new `PeekableBuffer` containing all elements from the range
/// `[from_inc, len() - 1]`, cloning the required elements into their
/// own iterable. If `from_inc` is outside the range of the stream, an
/// empty `PeekableBuffer` is returned.
pub fn slice_from(&self, from_inc: usize) -> PeekableBuffer<T>;

/// Returns a new `PeekableBuffer` containing all elements from the range
/// `[from_inc, to_exc - 1]`, cloning the required elements into their
/// own iterable. If `from_inc > to_exc`, this function will panic.
/// Otherwise, if `from_inc` are greater than `len()`, an
/// empty `PeekableBuffer` is returned. If `from_inc == to_exc`, an
/// empty `PeekableBuffer` is returned as well.
pub fn slice_between(&self, from_inc: usize, to_exc: usize) -> PeekableBuffer<T>;
```

## Error Handling
Most of the APIs have defined behavior for the more common "strange input"
cases, so there's no error handling to be found in this library. All of the
libraries that return a reference to an element in the buffer is returned as
an `Option<&T>`.

The exception is the function `slice_between` that panicks in the case where
`from_inc > to_exc`. Do LBYL before passing the parameters to this particular
function.
