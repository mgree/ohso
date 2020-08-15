mod doc;

type D<A> = doc::Doc<A>;

/// The type of pretty-printable documents.
pub struct Doc<A: Clone>(D<A>);

macro_rules! conversion {
    ($id:ident, $T:ty) => {
        /// Macro-generated `Doc` conversion taking $T to a `Doc`.
        pub fn $id(v: $T) -> Self {
            Doc::text(format!("{}", v))
        }
    };
}

macro_rules! derived {
    ($id:ident, $s:expr) => {
        /// Macro-generated `Doc` containing just `$s`.
        pub fn $id() -> Self {
            Doc::text(String::from($s))
        }
    };
}

macro_rules! wrapped {
    ($id:ident, $l:expr, $r:expr) => {
        /// Macro-generated method that wraps a `Doc` in `$l` and `$r`.
        pub fn $id(self) -> Self {
            Doc::char($l).append(self).append(Doc::char($r))
        }

        paste::paste! {
        /// A conditional form of `$id`; it only applies when `b` is `true`;
        /// otherwise it's the identity function.
        pub fn [< maybe_ $id >](self, b: bool) -> Self {
                if b {
                    self.$id()
                } else {
                    self
                }
            }
        }
    };
}

impl<A: Clone> Doc<A> {
    /// A `Doc` of height and width 1, containing the character provided.
    pub fn char(c: char) -> Self {
        Doc(D::char(c))
    }

    /// A `Doc` of height 1 containing the given string. Its width is determined
    /// by the number of (UTF-8) characters in `s`.
    pub fn text(s: String) -> Self {
        let len = s.chars().count();
        Doc(D::sized_text(s, len))
    }

    /// A `Doc` of text with zero width. Useful for non-printing text, like
    /// markup. (??? MMG: Is it zero height, though?)
    pub fn zero_width_text(s: String) -> Self {
        Doc(D::sized_text(s, 0))
    }

    /// A `Doc` of text with the given width.
    pub fn sized_text(s: String, len: usize) -> Self {
        Doc(D::sized_text(s, len))
    }

    /// The empty `Doc`.
    pub fn empty() -> Self {
        Doc(D::Empty)
    }

    /// Creates a choice between two possible layouts of the same document.
    ///
    /// It is an (unchecked, internal) invariant that the two layouts flatten
    /// into the same text; the only difference should be in spacing and
    /// horizontal/vertical layout.
    pub fn union(self, d2: Self) -> Self {
        Doc(self.0.union(d2.0))
    }

    /// Returns its first argument if it is non-empty, otherwise its second.
    ///
    /// Dispatches to `or_else`.
    pub fn first(d1: Self, d2: Self) -> Self {
        d1.or_else(d2)
    }

    /// Returns `self` if it is non-empty, otherwise its second.
    pub fn or_else(self, d2: Self) -> Self {
        if self.0.is_non_empty_set() {
            self
        } else {
            d2
        }
    }

    /// Nest/indent a document by a given number of positions. Indentation may
    /// be negative in sub-parts of the document, but document layout will
    /// misbehave if there are top-level negative indents.
    pub fn nest(self, i: isize) -> Self {
        Doc(self.0.nest(i))
    }

    /// Put a document directly next to another, with no space.
    ///
    /// `d1.append(d2)` is the same as `d1.beside(false, d2)`
    ///
    /// This is the `(<>)` operation in Haskell.
    pub fn append(self, d2: Self) -> Self {
        Doc(self.0.beside(false, d2.0))
    }

    /// Put a document directly next to another with a space between (if both
    /// are non-empty).
    ///
    /// `d1.append_(d2)` is the same as `d1.beside(true, d2)`
    ///
    /// This is the `(<+>)` operation in Haskell.
    pub fn append_(self, d2: Self) -> Self {
        Doc(self.0.beside(true, d2.0))
    }

    /// Put this document above `d2`, with no possibility of overlap.
    ///
    /// `d1.over(d2)` is the same as `d1.above(false, d2)`
    ///
    /// This is the `($+$)` operation in Haskell.
    pub fn over(self, d2: Self) -> Self {
        Doc(self.0.above(false, d2.0))
    }

    /// Put this document above `d2`, with overlapping.
    ///
    /// `d1.overlap(d2)` is the same as `d1.above(true, d2)`
    ///
    /// This is the `($$)` operation in Haskell.
    pub fn overlap(self, d2: Self) -> Self {
        Doc(self.0.above(true, d2.0))
    }

    pub fn sep<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Doc(D::sep_x(true, docs.into_iter().map(|d| d.0)))
    }

    pub fn cat<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Doc(D::sep_x(false, docs.into_iter().map(|d| d.0)))
    }

    /// Hangs `d2` off `d1`, indented by `i`.
    ///
    /// `d1.hang(i, d2)` is the same as `Doc::sep(vec![self, d2.nest(i)])`
    pub fn hang(self, i: isize, d2: Self) -> Self {
        Doc(D::sep_x(true, vec![self.0, d2.0.nest(i)]))
    }

    /// `sep.punctuate(docs)` joins `docs` together, separated by `sep`. No
    /// trailing separator.
    pub fn punctuate<I>(self, docs: I) -> Vec<Self>
    where
        I: IntoIterator<Item = Self>,
    {
        self.0
            .punctuate(docs.into_iter().map(|d| d.0))
            .into_iter()
            .map(|d| Doc(d))
            .collect()
    }

    /// Like `cat` but with paragraph fill.
    pub fn fcat<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Doc(D::fill(docs.into_iter().map(|d| d.0), false))
    }

    /// Like `sep` but with paragraph fill.
    pub fn fsep<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Doc(D::fill(docs.into_iter().map(|d| d.0), true))
    }

    /// Attaches an annotation to a document.
    pub fn annotate(self, a: A) -> Self {
        Doc(D::annotate(self.0, a))
    }

    //////////////////////////////////////////////////////////////////////
    // Conversions

    conversion!(isize, isize);
    conversion!(i8, i8);
    conversion!(i16, i16);
    conversion!(i32, i32);
    conversion!(i64, i64);
    conversion!(i128, i128);

    conversion!(usize, usize);
    conversion!(u8, u8);
    conversion!(u16, u16);
    conversion!(u32, u32);
    conversion!(u64, u64);
    conversion!(u128, u128);

    conversion!(f32, f32);
    conversion!(f64, f64);

    //////////////////////////////////////////////////////////////////////
    // Derived documents

    derived!(semi, ";");
    derived!(dot, ".");
    derived!(comma, ",");
    derived!(colon, ":");
    derived!(space, " ");
    derived!(equals, "=");
    derived!(lparen, "(");
    derived!(rparen, ")");
    derived!(lbrack, "[");
    derived!(rbrack, "]");
    derived!(lbrace, "{");
    derived!(rbrace, "}");
    derived!(langle, "<");
    derived!(rangle, ">");

    //////////////////////////////////////////////////////////////////////
    // Wrapping

    wrapped!(single_quotes, '\'', '\'');
    wrapped!(double_quotes, '"', '"');
    wrapped!(parens, '(', ')');
    wrapped!(brackets, '[', ']');
    wrapped!(braces, '{', '}');
    wrapped!(angles, '<', '>');

    //////////////////////////////////////////////////////////////////////
    // Abstract nonsense

    /// Maps a function `f` over the annotations in the document.
    pub fn map<B: Clone, F>(self, f: &F) -> Doc<B>
    where
        F: Fn(A) -> B,
    {
        Doc(D::map(self.0, f))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
