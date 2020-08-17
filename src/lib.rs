mod doc;
mod render;
pub use doc::Annot;
pub use doc::Text;
pub use render::*;
use std::convert::TryFrom;

type D<A> = doc::Doc<A>;

/// The type of pretty-printable documents.
pub struct Doc<A: Clone>(D<A>);

pub trait Pretty<A: Clone> {
    fn to_doc(self) -> Doc<A>;
}

macro_rules! conversion {
    ($id:ident, $T:ty) => {
        impl<A: Clone> Doc<A> {
            /// Macro-generated `Doc` conversion taking $T to a `Doc`.
            pub fn $id(v: $T) -> Self {
                Doc::text(format!("{}", v))
            }
        }

        impl<A: Clone> Pretty<A> for $T {
            /// Macro-generated, automatic conversion from `$T` to `Doc`. Calls
            /// `Doc::$id`.
            fn to_doc(self) -> Doc<A> {
                Doc::$id(self)
            }
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
    pub fn text<S: ToString>(s: S) -> Self {
        let s = s.to_string();
        let len = s.chars().count();
        Doc(D::sized_text(
            s,
            isize::try_from(len).expect("text too long"),
        ))
    }

    /// A `Doc` of text with zero width. Useful for non-printing text, like
    /// markup. (??? MMG: Is it zero height, though?)
    pub fn zero_width_text(s: String) -> Self {
        Doc(D::sized_text(s, 0))
    }

    /// A `Doc` of text with the given width.
    pub fn sized_text(s: String, len: usize) -> Self {
        Doc(D::sized_text(
            s,
            isize::try_from(len).expect("text too long"),
        ))
    }

    /// The empty `Doc`.
    pub fn empty() -> Self {
        Doc(D::Empty)
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
    pub fn append<T: Pretty<A>>(self, d2: T) -> Self {
        Doc(self.0.beside(false, d2.to_doc().0))
    }

    /// Put a document directly next to another with a space between (if both
    /// are non-empty).
    ///
    /// `d1.append_(d2)` is the same as `d1.beside(true, d2)`
    ///
    /// This is the `(<+>)` operation in Haskell.
    pub fn append_<T: Pretty<A>>(self, d2: T) -> Self {
        Doc(self.0.beside(true, d2.to_doc().0))
    }

    /// Put this document above `d2`, requiring vertical space---no overlap.
    ///
    /// This is the `($+$)` operation in Haskell.
    pub fn over<T: Pretty<A>>(self, d2: T) -> Self {
        Doc(self.0.above(true, d2.to_doc().0))
    }

    /// Put this document above `d2`, possibly with vertical space or possibly
    /// with overlapping.
    ///
    /// This is the `($$)` operation in Haskell.
    pub fn overlap<T: Pretty<A>>(self, d2: T) -> Self {
        Doc(self.0.above(false, d2.to_doc().0))
    }

    /// Space-separates the documents in `I`. Will automatically choose between
    /// horizontal and vertical spacing.
    ///
    /// A list form of `append_`.
    pub fn sep<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::sep_x(true, docs.into_iter().map(|d| d.to_doc().0)))
    }

    /// Concatenates the documents in `I`. Will automatically choose between
    /// horizontal and vertical spacing.
    ///
    /// A list form of `append`.
    pub fn cat<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::sep_x(false, docs.into_iter().map(|d| d.to_doc().0)))
    }

    /// Like `sep`, but only horizontal spacing.
    pub fn hsep<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::hsep(docs.into_iter().map(|d| d.to_doc().0)))
    }

    /// Like `cat`, but only horizontal spacing.
    pub fn hcat<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::hcat(docs.into_iter().map(|d| d.to_doc().0)))
    }

    /// Like `cat`, but only vertical spacing (allowing overlap).
    pub fn vcat<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::vcat(docs.into_iter().map(|d| d.to_doc().0)))
    }

    /// Like `cat` but with paragraph fill.
    pub fn fcat<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Doc(D::fill(docs.into_iter().map(|d| d.to_doc().0), false))
    }

    /// Like `sep` but with paragraph fill.
    pub fn fsep<I, T>(docs: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        Doc(D::fill(docs.into_iter().map(|d| d.to_doc().0), true))
    }

    /// Hangs `d2` off `d1`, indented by `i`.
    ///
    /// `d1.hang(i, d2)` is the same as `Doc::sep(vec![self, d2.nest(i)])`
    pub fn hang<T: Pretty<A>>(self, i: isize, d2: T) -> Self {
        Doc(D::sep_x(true, vec![self.0, d2.to_doc().0.nest(i)]))
    }

    /// `sep.punctuate(docs)` joins `docs` together, separated by `sep`. No
    /// trailing separator.
    pub fn punctuate<I, T>(self, docs: I) -> Vec<Self>
    where
        I: IntoIterator<Item = T>,
        T: Pretty<A>,
    {
        self.0
            .punctuate(docs.into_iter().map(|d| d.to_doc().0))
            .into_iter()
            .map(|d| Doc(d))
            .collect()
    }

    /// Attaches an annotation to a document.
    pub fn annotate(self, a: A) -> Self {
        Doc(D::annotate(self.0, a))
    }

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

impl<A: Clone> Pretty<A> for char {
    fn to_doc(self) -> Doc<A> {
        Doc::char(self)
    }
}

impl<A: Clone> Pretty<A> for String {
    fn to_doc(self) -> Doc<A> {
        Doc::text(self)
    }
}

impl<A: Clone> Pretty<A> for &str {
    fn to_doc(self) -> Doc<A> {
        Doc::text(self.to_string())
    }
}

impl<A: Clone> Pretty<A> for Doc<A> {
    fn to_doc(self) -> Doc<A> {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type PlainDoc = Doc<()>;

    #[test]
    fn plain_text() {
        assert_eq!(PlainDoc::text("hello").to_string(), "hello".to_string());
        assert_eq!(PlainDoc::text("hi").to_string(), "hi".to_string());

        assert_eq!(PlainDoc::char('q').to_string(), "q".to_string());
        assert_eq!(PlainDoc::usize(32).to_string(), "32".to_string());

        assert_eq!(PlainDoc::comma().to_string(), ",".to_string());
    }

    #[test]
    fn plain_concatenation() {
        assert_eq!(
            PlainDoc::text("hell")
                .append(PlainDoc::text("o"))
                .to_string(),
            "hello".to_string()
        );

        assert_eq!(
            Pretty::<()>::to_doc("hell").append("o").to_string(),
            "hello".to_string()
        );

        assert_eq!(
            PlainDoc::text("hell").append("o").to_string(),
            "hello".to_string()
        );

        assert_eq!(
            PlainDoc::text("hello")
                .append_(PlainDoc::text("world"))
                .to_string(),
            "hello world".to_string()
        );

        assert_eq!(
            PlainDoc::text("hello").append_("world").to_string(),
            "hello world".to_string()
        );
    }

    #[test]
    fn wrapping() {
        assert_eq!(
            PlainDoc::text("hello")
                .append_(PlainDoc::text("world"))
                .parens()
                .to_string(),
            "(hello world)".to_string()
        );

        assert_eq!(
            PlainDoc::text("hello")
                .append_("world")
                .parens()
                .to_string(),
            "(hello world)".to_string()
        );
    }

    #[test]
    fn overlap() {
        assert_eq!(
            PlainDoc::text("hi")
                .overlap(PlainDoc::text("there").nest(5))
                .to_string(),
            "hi   there"
        );

        assert_eq!(
            PlainDoc::text("hi")
                .overlap("there".to_doc().nest(5))
                .to_string(),
            "hi   there"
        );

        assert_eq!(
            PlainDoc::text("hi")
                .over(PlainDoc::text("there").nest(5))
                .to_string(),
            "hi\n     there"
        );
    }

    #[test]
    fn punctuate_sep_hsep_hcat() {
        assert_eq!(
            Doc::sep(PlainDoc::comma().punctuate(vec![
                PlainDoc::text("et cetera"),
                PlainDoc::text("etc"),
                PlainDoc::text("&c"),
            ]))
            .to_string(),
            "et cetera, etc, &c".to_string()
        );

        assert_eq!(
            Doc::hsep(PlainDoc::comma().punctuate(vec!["et cetera", "etc", "&c"])).to_string(),
            "et cetera, etc, &c".to_string()
        );

        assert_eq!(
            Doc::hcat(PlainDoc::comma().punctuate(vec!["et cetera", "etc", "&c"])).to_string(),
            "et cetera,etc,&c".to_string()
        );

        assert_eq!(
            Doc::cat(PlainDoc::comma().punctuate(vec!["et cetera", "etc", "&c"])).to_string(),
            "et cetera,etc,&c".to_string()
        );
    }

    #[test]
    fn vcat() {
        assert_eq!(
            PlainDoc::vcat(vec!["one", "2", "iii"]).to_string(),
            "one\n2\niii".to_string()
        )
    }

    #[test]
    fn huge_text() {
        // anything bigger overflows 8MB stack
        let t = vec!["hi"; 1020];

        let doc = PlainDoc::vcat(t.clone());
        assert_eq!(doc.to_string(), t.join("\n").to_string())
    }

    #[test]
    fn huge_text_left() {
        // anything bigger overflows 8MB stack
        let t = vec!["hi"; 1815];

        let doc = PlainDoc::vcat(t.clone());
        assert_eq!(
            doc.render(&Style {
                mode: Mode::Left,
                ..Style::default()
            })
            .0,
            t.join("\n").to_string()
        )
    }

    #[test]
    fn huge_text_oneline() {
        // anything bigger overflows 8MB stack
        let t = vec!["hi"; 4837];

        let doc = PlainDoc::vcat(t.clone());
        assert_eq!(
            doc.render(&Style {
                mode: Mode::OneLine,
                ..Style::default()
            })
            .0,
            t.join(" ").to_string()
        )
    }

    #[test]
    fn enormous_text() {
        let t = vec!["hi"; 2000];

        let doc = PlainDoc::vcat(t.clone());
        eprintln!("built doc");
        assert_eq!(doc.to_string(), t.join("\n").to_string())
    }
}
