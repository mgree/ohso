use std::convert::{TryFrom, TryInto};

use crate::doc::{Annot, Text};

type D<A> = crate::doc::Doc<A>;

type Doc<A> = crate::Doc<A>;

////////////////////////////////////////////////////////////////////////////////
// Configuration

#[derive(Clone, Copy)]
pub enum Mode {
    /// The default rendering mode; `line_length` and `ribbons_per_line` are
    /// respected.
    Page,
    ///  With 'zig-zag' cuts. (MMG: no idea what this means... no outdenting?)
    ZigZag,
    /// No indentation, but newlines (e.g., `Doc::over()`) are respected.
    Left,
    /// Everything on one line. Newlines---even explicit ones---are turned into
    /// spaces.
    OneLine,
}

#[derive(Clone, Copy)]
pub struct Style {
    /// The rendering `Mode`.
    mode: Mode,
    /// Maximum line length, in characters/graphemes.
    line_length: usize,
    /// Number of ribbons per line, where a 'ribbon' is the text on a line
    /// _after_ indentation (which is always spaces).
    ///
    /// A `line_length` of 80 with `ribbnons_per_line` of `2.0` would really
    /// only allow up to 40 characters of a ribbon on a line, while allowing
    /// indentation up to 40 spaces.
    ribbons_per_line: f32,
}

impl Default for Mode {
    fn default() -> Self {
        Mode::Page
    }
}

impl Default for Style {
    fn default() -> Self {
        Style {
            mode: Mode::default(),
            line_length: 100,
            ribbons_per_line: 1.5,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Spans

/// An annotation in a rendered document, capturing where the annotation begins,
/// how far it goes, and the annotation itself.
#[derive(Clone)]
pub struct Span<A: Clone> {
    start: usize,
    length: usize,
    annotation: A,
}

////////////////////////////////////////////////////////////////////////////////
// Rendering

impl<A: Clone> Doc<A> {
    pub fn render<W>(self, out: &mut W) -> Vec<Span<A>>
    where
        W: std::io::Write,
    {
        todo!()
    }

    pub fn full_render<F, B>(self, style: &Style, txt: &F, end: B) -> B
    where
        F: Fn(Text, B) -> B,
    {
        self.full_render_ann(
            style,
            &|ann, b| match ann {
                Annot::Text(s, _) => txt(s, b),
                _ => b,
            },
            end,
        )
    }

    pub fn full_render_ann<F, B>(self, style: &Style, txt: &F, end: B) -> B
    where
        F: Fn(Annot<A>, B) -> B,
    {
        match style.mode {
            Mode::OneLine => self
                .0
                .reduce()
                .easy_display(Annot::space(), &|_d1, d2| d2, txt, end),
            Mode::Left => self
                .0
                .reduce()
                .easy_display(Annot::newline(), &D::first, txt, end),
            Mode::Page | Mode::ZigZag => {
                let line_length = match style.mode {
                    Mode::ZigZag => usize::MAX,
                    _ => style.line_length,
                };
                let ribbon_length: usize =
                    (style.line_length as f32 / style.ribbons_per_line as f32).round() as usize;

                self.0.reduce().best(line_length, ribbon_length).display(
                    style,
                    ribbon_length,
                    txt,
                    end,
                )
            }
        }
    }
}

impl<A: Clone> D<A> {
    pub fn easy_display<C, F, B>(self, nl_space: Annot<A>, choose: &C, txt: &F, end: B) -> B
    where
        C: Fn(Self, Self) -> Self,
        F: Fn(Annot<A>, B) -> B,
    {
        match self {
            D::Union(d1, d2) => choose(*d1, *d2).easy_display(nl_space, choose, txt, end),
            D::Nest(_, d) => d.easy_display(nl_space, choose, txt, end),
            D::Empty => end,
            D::NilAbove(d) => txt(nl_space.clone(), d.easy_display(nl_space, choose, txt, end)),
            D::TextBeside(ann, d) => txt(ann, d.easy_display(nl_space, choose, txt, end)),
            D::Above(..) => panic!("easy_display on Above"),
            D::Beside(..) => panic!("easy_display on Beside"),
            D::NoDoc => panic!("easy_display on NoDoc"),
        }
    }

    pub fn display<F, B>(self, style: &Style, ribbon_length: usize, txt: &F, end: B) -> B
    where
        F: Fn(Annot<A>, B) -> B,
    {
        let gap_width = style.line_length - ribbon_length;
        let shift = gap_width / 2;

        self.lay(style, gap_width, shift, 0, txt, end)
    }

    fn lay<F, B>(
        self,
        style: &Style,
        gap_width: usize,
        shift: usize,
        k: usize,
        txt: &F,
        end: B,
    ) -> B
    where
        F: Fn(Annot<A>, B) -> B,
    {
        match self {
            D::Nest(k1, d) => d.lay(
                style,
                gap_width,
                shift,
                k + usize::try_from(k1).expect("positive"),
                txt,
                end,
            ),
            D::Empty => end,
            D::NilAbove(d) => txt(
                Annot::newline(),
                d.lay(style, gap_width, shift, k, txt, end),
            ),
            D::TextBeside(ann, d) => match style.mode {
                Mode::ZigZag => {
                    if k >= gap_width {
                        txt(
                            Annot::newline(),
                            txt(
                                Annot::Text(
                                    Text::Str(std::iter::repeat('/').take(shift).collect()),
                                    shift,
                                ),
                                txt(
                                    Annot::newline(),
                                    d.lay1(style, gap_width, shift, k - shift, ann, txt, end),
                                ),
                            ),
                        )
                    } else {
                        txt(
                            Annot::newline(),
                            txt(
                                Annot::Text(
                                    Text::Str(std::iter::repeat('\\').take(shift).collect()),
                                    shift,
                                ),
                                txt(
                                    Annot::newline(),
                                    d.lay1(style, gap_width, shift, k + shift, ann, txt, end),
                                ),
                            ),
                        )
                    }
                }
                _ => d.lay1(style, gap_width, shift, k, ann, txt, end),
            },
            D::Above(..) => panic!("display on Above"),
            D::Beside(..) => panic!("display on Beside"),
            D::NoDoc => panic!("display on NoDoc"),
            D::Union(..) => panic!("display on Union"),
        }
    }

    fn lay1<F, B>(
        self,
        style: &Style,
        gap_width: usize,
        shift: usize,
        k: usize,
        ann: Annot<A>,
        txt: &F,
        end: B,
    ) -> B
    where
        F: Fn(Annot<A>, B) -> B,
    {
        let size = ann.size();
        txt(
            Annot::indent(k),
            txt(ann, self.lay2(style, gap_width, shift, k + size, txt, end)),
        )
    }

    fn lay2<F, B>(
        self,
        style: &Style,
        gap_width: usize,
        shift: usize,
        k: usize,
        txt: &F,
        end: B,
    ) -> B
    where
        F: Fn(Annot<A>, B) -> B,
    {
        match self {
            D::NilAbove(d) => txt(
                Annot::newline(),
                d.lay(style, gap_width, shift, k, txt, end),
            ),
            D::TextBeside(ann, d) => {
                let size = ann.size();
                txt(ann, d.lay2(style, gap_width, shift, k + size, txt, end))
            }
            D::Nest(_, d) => d.lay2(style, gap_width, shift, k, txt, end),
            D::Empty => end,
            D::Above(..) => panic!("lay2 on Above"),
            D::Beside(..) => panic!("lay2 on Beside"),
            D::NoDoc => panic!("lay2 on NoDoc"),
            D::Union(..) => panic!("lay2 on Union"),
        }
    }

    pub fn best(self, line_length: usize, ribbon_length: usize) -> Self {
        match self {
            D::Empty => D::Empty,
            D::NoDoc => D::NoDoc,
            D::NilAbove(d) => D::NilAbove(Box::new(d.best(line_length, ribbon_length))),
            D::TextBeside(ann, d) => {
                let size = ann.size();
                D::TextBeside(ann, Box::new(d.best1(line_length, ribbon_length, size)))
            }
            D::Nest(i, d) => D::Nest(
                i,
                Box::new(d.best(
                    line_length - usize::try_from(i).expect("positive indent"),
                    ribbon_length,
                )),
            ),
            D::Union(d1, d2) => D::nicest(
                d1.best(line_length, ribbon_length),
                d2.best(line_length, ribbon_length),
                line_length,
                ribbon_length,
                0, /* no indent */
            ),
            D::Above(..) => panic!("best on Above"),
            D::Beside(..) => panic!("best on Beside"),
        }
    }

    fn best1(self, line_length: usize, ribbon_length: usize, sl: usize) -> Self {
        match self {
            D::Empty => D::Empty,
            D::NoDoc => D::NoDoc,
            D::NilAbove(d) => D::NilAbove(Box::new(d.best(line_length - sl, ribbon_length))),
            D::TextBeside(ann, d) => {
                let size = ann.size();
                D::TextBeside(
                    ann,
                    Box::new(d.best1(line_length, ribbon_length, sl + size)),
                )
            }
            D::Nest(_, d) => d.best1(line_length, ribbon_length, sl),
            D::Union(d1, d2) => D::nicest(
                d1.best1(line_length, ribbon_length, sl),
                d2.best1(line_length, ribbon_length, sl),
                line_length,
                ribbon_length,
                sl,
            ),
            D::Above(..) => panic!("best1 on Above"),
            D::Beside(..) => panic!("best1 on Beside"),
        }
    }

    fn nicest(d1: Self, d2: Self, line_length: usize, ribbon_length: usize, sl: usize) -> Self {
        if d1.fits(
            (std::cmp::min(line_length, ribbon_length) - sl)
                .try_into()
                .expect("text too long"),
        ) {
            d1
        } else {
            d2
        }
    }

    fn fits(&self, len: isize) -> bool {
        match self {
            D::NoDoc => false,
            D::Empty | D::NilAbove(_) => true,
            D::TextBeside(ann, d) => {
                d.fits(len - isize::try_from(ann.size()).expect("text too long"))
            }
            D::Nest(..) => panic!("fits on Nest"),
            D::Union(..) => panic!("fits on Union"),
            D::Above(..) => panic!("fits on Above"),
            D::Beside(..) => panic!("fits on Beside"),
        }
    }
}
