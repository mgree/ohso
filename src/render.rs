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

#[derive(Clone)]
struct OpenSpan<A: Clone> {
    end: usize,
    annotation: A,
}

impl<A: Clone> OpenSpan<A> {
    fn start(self, start: usize) -> Span<A> {
        Span {
            start,
            length: start - self.end,
            annotation: self.annotation,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Rendering

impl<A: Clone> std::fmt::Display for Doc<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s, _) = self.render(&Style::default());

        write!(f, "{}", s)
    }
}

impl<A: Clone> Doc<A> {
    pub fn render(&self, style: &Style) -> (String, Vec<Span<A>>) {
        // this is offset _from the end_
        let mut offset: usize = 0;
        let mut stack: Vec<OpenSpan<A>> = Vec::new();
        let mut spans: Vec<Span<A>> = Vec::new();
        // stored in reverse order
        // OPT MMG use a rope or something
        let mut output: Vec<(Text, usize)> = Vec::new();

        self.full_render_ann(style, &mut |ann| match ann {
            Annot::Start => {
                let span = stack.pop().expect("span stack underflow in render");
                spans.push(span.start(offset));
            }
            Annot::End(annotation) => stack.push(OpenSpan {
                end: offset,
                annotation: annotation.clone(),
            }),
            Annot::Text(txt, len) => {
                offset += len;
                output.push((txt.clone(), *len));
            }
        });

        // fix up start of span
        for span in &mut spans {
            span.start = offset - span.start;
        }

        // construct the output string
        // OPT MMG use std::io::Write?
        output.reverse();
        let len = output.iter().map(|(_, len)| len).sum();
        let mut rendered = String::new();
        rendered.reserve(len);

        for txt in output.into_iter() {
            match txt {
                (Text::Char(c), _) => rendered.push(c),
                (Text::Str(s), _) => rendered.push_str(&s),
            }
        }

        (rendered, spans)
    }

    pub fn render_annotated<F>(&self, style: &Style, ann_start: &mut F, ann_end: &mut F) -> String
    where
        F: FnMut(&A) -> &str,
    {
        // this is offset _from the end_
        let mut offset: usize = 0;
        let mut stack: Vec<A> = Vec::new();
        let mut output: Vec<(Text, usize)> = Vec::new();

        self.full_render_ann(style, &mut |ann| match ann {
            Annot::Start => {
                let annotation = stack
                    .pop()
                    .expect("span stack underflow in render_annotated");
                let s = ann_start(&annotation);
                output.push((s.into(), s.len()));
            }
            Annot::End(annotation) => {
                let s = ann_end(&annotation);
                output.push((s.into(), s.len()));
                stack.push(annotation.clone());
            }
            Annot::Text(txt, len) => {
                offset += len;
                output.push((txt.clone(), *len));
            }
        });

        // construct the output string
        // OPT MMG use std::io::Write?
        output.reverse();
        let len = output.iter().map(|(_, len)| len).sum();
        let mut rendered = String::new();
        rendered.reserve(len);

        for txt in output.into_iter() {
            match txt {
                (Text::Char(c), _) => rendered.push(c),
                (Text::Str(s), _) => rendered.push_str(&s),
            }
        }

        rendered
    }

    /// A fold over the `Doc` structure, using `style` to make decisions. The
    /// `txt` function adds text segments and `end` is the base case for empty
    /// documents.
    ///
    /// Implemented by the more general `full_render_ann`, which looks at all
    /// annotations. This version looks only at `Annot::Text`.
    pub fn full_render<F>(&self, style: &Style, txt: &mut F)
    where
        F: FnMut(&Text) -> (),
    {
        self.full_render_ann(style, &mut |ann| match ann {
            Annot::Text(s, _) => txt(s),
            Annot::Start | Annot::End(..) => (),
        })
    }

    /// A fold over the `Doc` structure, using `style` to make decisions. The
    /// `txt` function handles anotations and `end` is the base case for empty
    /// documents.
    ///
    /// Traversal is in reverse: later parts of the string are processed first,
    /// with `Annot::Start` coming _after_ `Annot::End`.
    pub fn full_render_ann<F>(&self, style: &Style, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        // OPT MMG ugh, this clone :(
        let doc = self.0.clone().reduce();
        match style.mode {
            Mode::OneLine => doc.easy_display(Annot::space(), Policy::Second, txt),
            Mode::Left => doc.easy_display(Annot::newline(), Policy::First, txt),
            Mode::Page | Mode::ZigZag => {
                let line_length = match style.mode {
                    Mode::ZigZag => usize::MAX,
                    _ => style.line_length,
                };
                let ribbon_length: usize =
                    (style.line_length as f32 / style.ribbons_per_line as f32).round() as usize;

                doc.best(line_length, ribbon_length)
                    .display(style, ribbon_length, txt)
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Policy {
    First,
    Second,
}

impl<A: Clone> D<A> {
    fn easy_display<F>(&self, nl_space: Annot<A>, policy: Policy, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        match self {
            D::Union(d1, d2) => {
                let choice = match policy {
                    Policy::First => D::first(d1, d2),
                    Policy::Second => d2,
                };

                choice.easy_display(nl_space, policy, txt)
            }
            D::Nest(_, d) => d.easy_display(nl_space, policy, txt),
            D::Empty => (),
            D::NilAbove(d) => {
                d.easy_display(nl_space.clone(), policy, txt);
                txt(&nl_space);
            }
            D::TextBeside(ann, d) => {
                d.easy_display(nl_space, policy, txt);
                txt(ann);
            }
            D::Above(..) => panic!("easy_display on Above"),
            D::Beside(..) => panic!("easy_display on Beside"),
            D::NoDoc => panic!("easy_display on NoDoc"),
        }
    }

    pub fn display<F>(&self, style: &Style, ribbon_length: usize, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        let gap_width = style.line_length - ribbon_length;
        let shift = gap_width / 2;

        self.lay(style, gap_width, shift, 0, txt)
    }

    fn lay<F>(&self, style: &Style, gap_width: usize, shift: usize, k: usize, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        match self {
            D::Nest(k1, d) => d.lay(
                style,
                gap_width,
                shift,
                k + usize::try_from(*k1).expect("positive"),
                txt,
            ),
            D::Empty => (),
            D::NilAbove(d) => {
                d.lay(style, gap_width, shift, k, txt);
                txt(&Annot::newline());
            }
            D::TextBeside(ann, d) => match style.mode {
                Mode::ZigZag => {
                    if k >= gap_width {
                        d.lay1(style, gap_width, shift, k - shift, ann, txt);
                        txt(&Annot::newline());
                        txt(&Annot::Text(
                            Text::Str(std::iter::repeat('/').take(shift).collect()),
                            shift,
                        ));

                        txt(&Annot::newline())
                    } else {
                        d.lay1(style, gap_width, shift, k + shift, ann, txt);
                        txt(&Annot::newline());
                        txt(&Annot::Text(
                            Text::Str(std::iter::repeat('\\').take(shift).collect()),
                            shift,
                        ));
                        txt(&Annot::newline());
                    }
                }
                _ => d.lay1(style, gap_width, shift, k, ann, txt),
            },
            D::Above(..) => panic!("display on Above"),
            D::Beside(..) => panic!("display on Beside"),
            D::NoDoc => panic!("display on NoDoc"),
            D::Union(..) => panic!("display on Union"),
        }
    }

    fn lay1<F>(
        &self,
        style: &Style,
        gap_width: usize,
        shift: usize,
        k: usize,
        ann: &Annot<A>,
        txt: &mut F,
    ) where
        F: FnMut(&Annot<A>) -> (),
    {
        self.lay2(style, gap_width, shift, k + ann.size(), txt);
        txt(ann);
        txt(&Annot::indent(k));
    }

    fn lay2<F>(&self, style: &Style, gap_width: usize, shift: usize, k: usize, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        match self {
            D::NilAbove(d) => {
                d.lay(style, gap_width, shift, k, txt);
                txt(&Annot::newline());
            }
            D::TextBeside(ann, d) => {
                d.lay2(style, gap_width, shift, k + ann.size(), txt);
                txt(ann);
            }
            D::Nest(_, d) => d.lay2(style, gap_width, shift, k, txt),
            D::Empty => (),
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
            D::Nest(i, d) => {
                let indent = line_length as isize - i;
                assert!(indent >= 0, "positive indent");                
                D::Nest(i, Box::new(d.best(indent as usize, ribbon_length)))
            }
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
