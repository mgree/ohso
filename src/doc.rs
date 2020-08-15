use std::convert::TryFrom;

/// Documents. `A` is the type of annotations.
///
/// Here are the invariants:
///
/// 1) The argument of `NilAbove` is never `Empty`. Therefore a `NilAbove` occupies at
/// least two lines.
///
/// 2) The argument of `TextBeside` is never `Nest`.
///
/// 3) The layouts of the two arguments of `Union` both flatten to the same string.
///
/// 4) The arguments of `Union` are either `TextBeside`, or `NilAbove`.
///
/// 5) A `NoDoc` may only appear on the first line of the left argument of an
///    union. Therefore, the right argument of an union can never be equivalent to
///    the empty set (`NoDoc`).
///
/// 6) An empty document is always represented by `Empty`. It can't be hidden
///    inside a `Nest`, or a `Union` of two `Empty`s.
///
/// 7) The first line of every layout in the left argument of `Union` is longer
///    than the first line of any layout in the right argument. (1) ensures that
///    the left argument has a first line. In view of (3), this invariant means
///    that the right argument must have at least two lines.
///
/// Notice the difference between
///    * NoDoc (no documents)
///    * Empty (one empty document; no height and no width)
///    * text "" (a document containing the empty string; one line high, but has no
///               width)
///
/// A `Doc` is "reduced" when there isn't a top-level `Above` or `Beside`.
///
/// Following https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#Doc.
#[derive(Clone, Debug)]
pub(crate) enum Doc<A>
where
    A: Clone,
{
    Empty,
    NilAbove(Box<Doc<A>>),
    TextBeside(Annot<A>, Box<Doc<A>>),
    Nest(isize, Box<Doc<A>>), // !!! can be negative, but it indicates an error in client code
    Union(Box<Doc<A>>, Box<Doc<A>>),
    NoDoc,
    /// `Beside(d1, b, d2)` is d1 next to d2, with b indicating whether there should be space between.
    Beside(Box<Doc<A>>, bool, Box<Doc<A>>),
    /// `Above(d1, b, d2)` is d1 above d2, with b indicating whether overlap is allowed.
    Above(Box<Doc<A>>, bool, Box<Doc<A>>),
}

/// Annotations.
///
/// Following https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#AnnotDetails.
#[derive(Clone, Debug)]
pub enum Annot<A>
where
    A: Clone,
{
    Start,
    No(Text, usize),
    End(A),
}

/// A fragment of text that will be output at some point in a `Doc`.
///
/// Following https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#TextDetails.
#[derive(Clone, Debug)]
pub enum Text {
    Char(char),
    Str(String),
    // OPT MMG small string?
}

impl<A: Clone> Doc<A> {
    pub fn map<B: Clone, F>(self, f: &F) -> Doc<B>
    where
        F: Fn(A) -> B,
    {
        match self {
            Doc::Empty => Doc::Empty,
            Doc::NilAbove(d) => Doc::NilAbove(Box::new(d.map(f))),
            Doc::TextBeside(ann, d) => Doc::TextBeside(ann.map(f), Box::new(d.map(f))),
            Doc::Nest(i, d) => Doc::Nest(i, Box::new(d.map(f))),
            Doc::Union(d1, d2) => Doc::Union(Box::new(d1.map(f)), Box::new(d2.map(f))),
            Doc::NoDoc => Doc::NoDoc,
            Doc::Beside(d1, b, d2) => Doc::Beside(Box::new(d1.map(f)), b, Box::new(d2.map(f))),
            Doc::Above(d1, b, d2) => Doc::Above(Box::new(d1.map(f)), b, Box::new(d2.map(f))),
        }
    }

    /// Attaches an annotation to a document.
    pub fn annotate(self, a: A) -> Self {
        Doc::TextBeside(
            Annot::Start,
            Box::new(
                self.reduce()
                    .mk_beside(false, Doc::TextBeside(Annot::End(a), Box::new(Doc::Empty))),
            ),
        )
    }

    pub fn char(c: char) -> Self {
        Doc::TextBeside(Annot::No(Text::Char(c), 1), Box::new(Doc::Empty))
    }

    pub fn sized_text(s: String, len: usize) -> Self {
        Doc::TextBeside(Annot::No(Text::Str(s), len), Box::new(Doc::Empty))
    }

    /// Determinse whether a `Doc` is empty.
    pub fn is_empty(&self) -> bool {
        match self {
            Doc::Empty => true,
            _ => false,
        }
    }

    /// Corresponds to mkUnion
    pub fn union(self, d2: Self) -> Self {
        match (self, d2) {
            (Doc::Empty, d) => d, // ??? MMG why no RHS check?
            (d1, d2) => Doc::Union(Box::new(d1), Box::new(d2)),
        }
    }

    /// Nest/indent a document by a given number of positions. Indentation may
    /// be negative.
    ///
    /// Following
    /// https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#nest.
    pub fn nest(self, i: isize) -> Self {
        let d = self.reduce();
        d.mk_nest(i)
    }

    fn mk_nest(self, i: isize) -> Self {
        if i == 0 {
            return self;
        }

        match self {
            Doc::Nest(k, d) => Doc::Nest(i + k, d),
            Doc::NoDoc => Doc::NoDoc,
            Doc::Empty => Doc::Empty,
            d => Doc::Nest(i, Box::new(d)),
        }
    }

    /// Put one document beside another.
    ///
    /// Following
    /// https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#beside_.
    pub fn beside(self, space: bool, d2: Self) -> Self {
        match (self, d2) {
            (Doc::Empty, d) | (d, Doc::Empty) => d,
            (d1, d2) => Doc::Beside(Box::new(d1), space, Box::new(d2)),
        }
    }

    /// Following https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#beside
    fn mk_beside(self, space: bool, d2: Self) -> Self {
        match self {
            Doc::NoDoc => Doc::NoDoc,
            Doc::Union(d11, d12) => Doc::Union(
                Box::new(d11.mk_beside(space, d2.clone())),
                Box::new(d12.mk_beside(space, d2)),
            ),
            Doc::Empty => d2,
            Doc::Nest(i, d1) => Doc::Nest(i, Box::new(d1.mk_beside(space, d2))),
            Doc::Beside(d11, b, d12) if b == space => {
                d11.mk_beside(space, d12.mk_beside(space, d2))
            }
            d1 @ Doc::Beside(..) => d1.reduce().mk_beside(space, d2),
            d1 @ Doc::Above(..) => d1.reduce().mk_beside(space, d2),
            Doc::NilAbove(d1) => Doc::NilAbove(Box::new(d1.mk_beside(space, d2))),
            Doc::TextBeside(ann, d1) => Doc::TextBeside(
                ann,
                Box::new(if d1.is_empty() {
                    Doc::nil_beside(space, d2)
                } else {
                    d1.mk_beside(space, d2)
                }),
            ),
        }
    }

    fn nil_beside(space: bool, d2: Self) -> Self {
        match d2 {
            Doc::Empty => Doc::Empty,
            Doc::Nest(_, d2) => Doc::nil_beside(space, *d2),
            d2 => {
                if space {
                    Doc::TextBeside(Annot::space(), Box::new(d2))
                } else {
                    d2
                }
            }
        }
    }

    /// Put one `Doc` above another.
    pub fn above(self, overlap: bool, d2: Self) -> Self {
        match (self, d2) {
            (Doc::Empty, d) | (d, Doc::Empty) => d,
            (Doc::Above(d1, b, d2), d3) => d1.above(b, d2.above(overlap, d3)),
            (d1 @ Doc::Beside(..), d2) => d1.reduce().above_nest(overlap, 0, d2.reduce()),
            (d1, d2) => d1.above_nest(overlap, 0, d2),
        }
    }

    fn above_nest(self, overlap: bool, i: isize, d2: Self) -> Self {
        match self {
            Doc::NoDoc => Doc::NoDoc,
            Doc::Union(d11, d12) => Doc::Union(
                Box::new(d11.above_nest(overlap, i, d2.clone())),
                Box::new(d12.above_nest(overlap, i, d2)),
            ),
            Doc::Empty => d2.mk_nest(i),
            Doc::Nest(i1, d1) => {
                assert!(!d1.is_empty()); // invariant says `d1` can't be empty, so no need for `mk_nest`
                Doc::Nest(i1, Box::new(d1.above_nest(overlap, i - i1, d2)))
            }
            Doc::NilAbove(d) => Doc::NilAbove(Box::new(d.above_nest(overlap, i, d2))),
            Doc::TextBeside(ann, d1) => {
                let i = i - isize::try_from(ann.size()).expect("text too long");
                Doc::TextBeside(
                    ann,
                    Box::new(if d1.is_empty() {
                        Doc::nil_above_nest(overlap, i, d2)
                    } else {
                        d1.above_nest(overlap, i, d2)
                    }),
                )
            }
            Doc::Above(..) => panic!("above_nest on Above"),
            Doc::Beside(..) => panic!("above_nest on Beside"),
        }
    }

    fn nil_above_nest(overlap: bool, i: isize, d2: Self) -> Self {
        match d2 {
            Doc::Empty => Doc::Empty,
            Doc::Nest(k, d2) => Doc::nil_above_nest(overlap, i + k, *d2),
            d2 if !overlap && i > 0 => Doc::TextBeside(
                Annot::indent(usize::try_from(i).expect("positive")),
                Box::new(d2),
            ),
            d2 => Doc::NilAbove(Box::new(d2.mk_nest(i))),
        }
    }

    pub fn sep_x<I>(spaces: bool, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut iter = docs.into_iter();

        let d1 = match iter.next() {
            None => return Doc::Empty,
            Some(d) => d,
        };

        d1.sep1(spaces, 0, iter)
    }

    fn sep1<I>(self, spaces: bool, i: isize, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        match self {
            Doc::NoDoc => Doc::NoDoc,
            Doc::Union(d1, d2) => {
                let docs = docs.into_iter().collect::<Vec<_>>();
                Doc::Union(
                    Box::new(d1.sep1(spaces, i, docs.clone())),
                    Box::new(d2.above_nest(false, i, Doc::vcat(docs))),
                )
            }
            Doc::Empty => Doc::sep_x(spaces, docs).mk_nest(i),
            Doc::Nest(n, d1) => Doc::Nest(n, Box::new(d1.sep1(spaces, i - n, docs))),
            Doc::NilAbove(d1) => {
                Doc::NilAbove(Box::new(d1.above_nest(false, i, Doc::vcat(docs).reduce())))
            }
            Doc::TextBeside(ann, d1) => {
                let k = isize::try_from(ann.size()).expect("text too long");

                Doc::TextBeside(ann, Box::new(d1.sep_nb(spaces, i - k, docs)))
            }
            Doc::Above(..) => panic!("sep1 on Above"),
            Doc::Beside(..) => panic!("sep1 on Beside"),
        }
    }

    fn sep_nb<I>(self, spaces: bool, i: isize, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        match self {
            Doc::Nest(_, d1) => d1.sep_nb(spaces, i, docs), // supposedly never triggered?
            Doc::Empty => {
                let docs = docs.into_iter().collect::<Vec<_>>();

                let rest = if spaces {
                    Doc::hsep(docs.clone())
                } else {
                    Doc::hcat(docs.clone())
                };

                Doc::nil_beside(spaces, rest)
                    .oneliner()
                    .union(Doc::nil_above_nest(false, i, Doc::vcat(docs).reduce()))
            }
            d1 => d1.sep1(spaces, i, docs),
        }
    }

    /// Like `append_`, but for a list of documents. No trailing spaces.
    pub fn hsep<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut docs = docs.into_iter();
        let mut d1 = match docs.next() {
            None => return Doc::Empty,
            Some(d) => d,
        };

        for d2 in docs {
            d1 = Doc::Beside(Box::new(d1), true, Box::new(d2));
        }

        d1.reduce_horiz()
    }

    /// Like `append`, but for a list of documents.
    pub fn hcat<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut docs = docs.into_iter();
        let mut d1 = match docs.next() {
            None => return Doc::Empty,
            Some(d) => d,
        };

        for d2 in docs {
            d1 = Doc::Beside(Box::new(d1), false, Box::new(d2));
        }

        d1.reduce_horiz()
    }

    fn reduce_horiz(self) -> Self {
        match self {
            Doc::Beside(d1, b, d2) => {
                if d1.is_empty() {
                    *d2
                } else {
                    let d1 = d1.reduce_horiz();
                    let d2 = d2.reduce_horiz();

                    if d2.is_empty() {
                        d1
                    } else {
                        Doc::Beside(Box::new(d1), b, Box::new(d2))
                    }
                }
            }
            d => d,
        }
    }

    /// Like `over`, but for a list.
    pub fn vcat<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut docs = docs.into_iter();
        let mut d1 = match docs.next() {
            None => return Doc::Empty,
            Some(d) => d,
        };

        for d2 in docs {
            d1 = Doc::Above(Box::new(d1), false, Box::new(d2));
        }

        d1.reduce_vert()
    }

    fn reduce_vert(self) -> Self {
        match self {
            Doc::Above(d1, b, d2) => {
                if d1.is_empty() {
                    *d2
                } else {
                    let d1 = d1.reduce_vert();
                    let d2 = d2.reduce_vert();

                    if d2.is_empty() {
                        d1
                    } else {
                        Doc::Above(Box::new(d1), b, Box::new(d2))
                    }
                }
            }
            d => d,
        }
    }

    pub fn fill<I>(docs: I, spaces: bool) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut docs = docs.into_iter();

        let d1 = match docs.next() {
            None => return Doc::Empty,
            Some(d) => d,
        };

        d1.reduce().fill1(spaces, 0, docs)
    }

    fn fill1<I>(self, spaces: bool, i: isize, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        match self {
            Doc::NoDoc => Doc::NoDoc,
            Doc::Union(d1, d2) => {
                let docs = docs.into_iter().collect::<Vec<_>>();

                Doc::Union(
                    Box::new(d1.fill1(spaces, i, docs.clone())),
                    Box::new(d2.above_nest(false, i, Doc::fill(docs, spaces))),
                )
            }
            Doc::Empty => Doc::fill(docs, spaces).mk_nest(i),
            Doc::Nest(n, d1) => Doc::Nest(n, Box::new(d1.fill1(spaces, i - n, docs))),
            Doc::NilAbove(d1) => {
                Doc::NilAbove(Box::new(d1.above_nest(false, i, Doc::fill(docs, spaces))))
            }
            Doc::TextBeside(ann, d1) => {
                let size = isize::try_from(ann.size()).expect("text too long");
                Doc::TextBeside(ann, Box::new(d1.fill_nb(spaces, i - size, docs)))
            }
            Doc::Above(..) => panic!("fill1 on Above"),
            Doc::Beside(..) => panic!("fill1 on Beside"),
        }
    }

    fn fill_nb<I>(self, spaces: bool, i: isize, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        match self {
            Doc::Nest(_, d1) => d1.fill_nb(spaces, i, docs), // supposedly never triggered
            Doc::Empty => {
                let mut docs = docs.into_iter();
                match docs.next() {
                    None => Doc::Empty,
                    Some(Doc::Empty) => Doc::Empty.fill_nb(spaces, i, docs),
                    Some(d2) => d2.fill_nbe(spaces, i, docs),
                }
            }
            d1 => d1.fill1(spaces, i, docs),
        }
    }

    fn fill_nbe<I>(self, spaces: bool, i: isize, docs: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let docs = docs.into_iter().collect::<Vec<_>>();

        Doc::Union(
            Box::new(Doc::nil_beside(
                spaces,
                self.clone().reduce().oneliner().elide_nest().fill1(
                    spaces,
                    if spaces { i - 1 } else { i },
                    docs.clone(),
                ),
            )),
            Box::new(Doc::nil_above_nest(
                false,
                i,
                Doc::fill(std::iter::once(self).chain(docs), spaces),
            )),
        )
    }

    /// `sep.punctuate(docs)` joins `docs` together, separated by `sep`. No
    /// trailing separator.
    pub fn punctuate<I>(self, docs: I) -> Vec<Self>
    where
        I: IntoIterator<Item = Self>,
    {
        let mut v = Vec::new();
        let mut iter = docs.into_iter().peekable();

        loop {
            match iter.next() {
                None => return v,
                Some(d) => {
                    if iter.peek().is_some() {
                        v.push(d.beside(false, self.clone()));
                    } else {
                        v.push(d);
                        return v;
                    }
                }
            }
        }
    }

    fn oneliner(self) -> Self {
        match self {
            Doc::NoDoc => Doc::NoDoc,
            Doc::Empty => Doc::Empty,
            Doc::NilAbove(..) => Doc::NoDoc,
            Doc::TextBeside(s, d) => Doc::TextBeside(s, Box::new(d.oneliner())),
            Doc::Nest(i, d) => Doc::Nest(i, Box::new(d.oneliner())),
            Doc::Union(d, _) => d.oneliner(),
            Doc::Above(..) => panic!("oneliner on Above"),
            Doc::Beside(..) => panic!("oneliner on Beside"),
        }
    }

    pub fn is_non_empty_set(&self) -> bool {
        match self {
            Doc::NoDoc => false,
            Doc::Union(..) | Doc::Empty | Doc::NilAbove(..) => true,
            Doc::TextBeside(_ann, d) => d.is_non_empty_set(),
            Doc::Nest(_i, d) => d.is_non_empty_set(),
            Doc::Above(..) => panic!("is_non_empty_set on Above"),
            Doc::Beside(..) => panic!("is_non_empty_set on Beside"),
        }
    }

    fn elide_nest(self) -> Self {
        match self {
            Doc::Nest(_, d) => *d,
            d => d,
        }
    }

    fn reduce(self) -> Self {
        match self {
            Doc::Beside(d1, b, d2) => d1.mk_beside(b, *d2),
            Doc::Above(d1, b, d2) => d1.above(b, *d2),
            d => d,
        }
    }
}

impl<A: Clone> Annot<A> {
    /// The size of an annotation. Looks only at the text parts (`Annot::No`).
    pub fn size(&self) -> usize {
        match self {
            Annot::No(_txt, l) => *l,
            Annot::Start | Annot::End(_) => 0,
        }
    }

    /// Maps over annotations.
    pub fn map<B: Clone, F>(self, f: F) -> Annot<B>
    where
        F: FnOnce(A) -> B,
    {
        match self {
            Annot::Start => Annot::Start,
            Annot::No(txt, l) => Annot::No(txt, l),
            Annot::End(a) => Annot::End(f(a)),
        }
    }

    pub fn space() -> Self {
        Annot::No(Text::Char(' '), 1)
    }

    pub fn indent(i: usize) -> Self {
        Annot::No(
            Text::Str(std::iter::repeat(' ').take(i).collect::<String>()),
            i,
        )
    }
}