pub(crate) trait Stack {
    /// Type of the values that are pushed onto the stack.
    type Item: Copy;

    /// Return the topmost value of the Stack, or `None` if it is empty
    fn peek(&self) -> Option<Self::Item>;

    /// Return the topmost value of the Stack, or `default` if it is empty
    fn peek_or(&self, default: Self::Item) -> Self::Item {
        self.peek().unwrap_or(default)
    }

    /// Return a mutable reference to the topmost value of the stack without otherwise
    /// mutating the stack itself.
    fn peek_mut(&mut self) -> Option<&mut Self::Item>;

    /// Like `peek`, but the topmost value of the stack is removed if it exists.
    fn pop(&mut self) -> Option<Self::Item>;

    /// Like `peek_or`, but the value returned is removed from the stack if it was not empty.
    fn pop_or(&mut self, default: Self::Item) -> Self::Item {
        self.pop().unwrap_or(default)
    }

    /// Push `item` onto the top of the stack.
    fn push(&mut self, item: Self::Item);

    /// Given a closure that returns `None` in the case of a valid value to push,
    /// and `Some(err)` if an error occured, pre-validate and push `item` onto the
    /// Stack.
    ///
    /// If `Err(_)` is returned, the mutably borrowed receiver should be unmodified.
    fn push_validated<Error, F: Fn(Option<Self::Item>, Self::Item) -> Option<Error>>(
        &mut self,
        item: Self::Item,
        validate: F,
    ) -> Result<(), Error> {
        match validate(self.peek(), item) {
            None => Ok(self.push(item)),
            Some(err) => Err(err),
        }
    }
}

impl<T: Copy> Stack for Vec<T> {
    type Item = T;

    fn peek(&self) -> Option<Self::Item> {
        self.last().copied()
    }

    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(self)
    }

    fn push(&mut self, item: Self::Item) {
        Vec::push(self, item)
    }

    fn peek_mut(&mut self) -> Option<&mut Self::Item> {
        self.last_mut()
    }
}
