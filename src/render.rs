use std::convert::TryFrom;

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
    pub mode: Mode,
    /// Maximum line length, in characters/graphemes.
    pub line_length: isize,
    /// Number of ribbons per line, where a 'ribbon' is the text on a line
    /// _after_ indentation (which is always spaces).
    ///
    /// A `line_length` of 80 with `ribbnons_per_line` of `2.0` would really
    /// only allow up to 40 characters of a ribbon on a line, while allowing
    /// indentation up to 40 spaces.
    pub ribbons_per_line: f32,
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
    start: isize,
    length: isize,
    annotation: A,
}

#[derive(Clone)]
struct OpenSpan<A: Clone> {
    end: isize,
    annotation: A,
}

impl<A: Clone> OpenSpan<A> {
    fn start(self, start: isize) -> Span<A> {
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
        let mut offset: isize = 0;
        let mut stack: Vec<OpenSpan<A>> = Vec::new();
        let mut spans: Vec<Span<A>> = Vec::new();
        // stored in reverse order
        // OPT MMG use a rope or something
        let mut output: Vec<(Text, usize)> = Vec::new();

        eprintln!("rendering");
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
                output.push((
                    txt.clone(),
                    usize::try_from(*len).expect("positive text length"),
                ));
            }
        });
        eprintln!("rendered");

        // fix up start of span
        for span in &mut spans {
            span.start = offset - span.start;
        }

        // construct the output string
        // OPT MMG use std::io::Write?
        output.reverse();
        let len = output.iter().map(|(_, len)| *len).sum();
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
        let mut offset: isize = 0;
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
                output.push((
                    txt.clone(),
                    usize::try_from(*len).expect("positive string length"),
                ));
            }
        });

        // construct the output string
        // OPT MMG don't actually reverse, just iterate top down
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
                    Mode::ZigZag => isize::MAX,
                    _ => style.line_length,
                };
                let ribbon_length: isize =
                    (style.line_length as f32 / style.ribbons_per_line as f32).round() as isize;

                eprintln!("calculating layout");
                let doc = doc.best(line_length, ribbon_length);

                eprintln!("calculated layout, displaying");
                doc.display(style, ribbon_length, txt);
                eprintln!("displayed");
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
        let mut stack: Vec<&Annot<A>> = vec![];
        let mut doc = self;

        loop {
            match doc {
                D::Empty => {
                    for ann in stack.iter() {
                        txt(ann);
                    }
                    return;
                }
                D::Union(d1, d2) => {
                    doc = match policy {
                        Policy::First => D::first(d1, d2),
                        Policy::Second => d2,
                    };
                }
                D::Nest(_, d) => doc = d,
                D::NilAbove(d) => {
                    doc = d;
                    stack.push(&nl_space);
                }
                D::TextBeside(ann, d) => {
                    doc = d;
                    stack.push(ann);
                }
                D::Above(..) => panic!("easy_display on Above"),
                D::Beside(..) => panic!("easy_display on Beside"),
                D::NoDoc => panic!("easy_display on NoDoc"),
            }
        }
    }

    pub fn display<F>(&self, style: &Style, ribbon_length: isize, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        let gap_width = style.line_length - ribbon_length;
        let shift = gap_width / 2;

        self.lay(style, gap_width, shift, 0, txt)
    }

    fn lay<F>(&self, style: &Style, gap_width: isize, shift: isize, k: isize, txt: &mut F)
    where
        F: FnMut(&Annot<A>) -> (),
    {
        match self {
            D::Nest(k1, d) => d.lay(style, gap_width, shift, k + *k1, txt),
            D::Empty => (),
            D::NilAbove(d) => {
                d.lay(style, gap_width, shift, k, txt);
                txt(&Annot::newline());
            }
            D::TextBeside(ann, d) => match style.mode {
                Mode::ZigZag => {
                    let ushift = usize::try_from(shift).expect("positive shift");

                    if k >= gap_width {
                        d.lay1(style, gap_width, shift, k - shift, ann, txt);
                        txt(&Annot::newline());
                        txt(&Annot::Text(
                            Text::Str(std::iter::repeat('/').take(ushift).collect()),
                            shift,
                        ));

                        txt(&Annot::newline())
                    } else {
                        d.lay1(style, gap_width, shift, k + shift, ann, txt);
                        txt(&Annot::newline());
                        txt(&Annot::Text(
                            Text::Str(std::iter::repeat('\\').take(ushift).collect()),
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
        gap_width: isize,
        shift: isize,
        k: isize,
        ann: &Annot<A>,
        txt: &mut F,
    ) where
        F: FnMut(&Annot<A>) -> (),
    {
        self.lay2(style, gap_width, shift, k + ann.size(), txt);
        txt(ann);
        txt(&Annot::indent(k));
    }

    fn lay2<F>(&self, style: &Style, gap_width: isize, shift: isize, k: isize, txt: &mut F)
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
}

// continuations for `best`
enum BestCont<A: Clone> {
    NilAbove { line_length: isize },
    TextBeside(Annot<A>),
    Nest { line_length: isize, i: isize },
    Union(D<A>),
    // generated by the `best1` loop but can end up in the outer stack from `NilAbove`
    InnerTextBeside { ann: Annot<A>, sl: isize },
}

impl<A: Clone> D<A> {
    pub fn best(self, line_length: isize, ribbon_length: isize) -> Self {
        use BestCont::*;
        let mut stack: Vec<BestCont<A>> = vec![];

        let mut line_length = line_length;
        let mut doc = self;
        'best: loop {
            match doc {
                D::Empty | D::NoDoc => 'build: loop {
                    match stack.pop() {
                        None => break 'best,
                        Some(NilAbove { line_length: ll }) => {
                            doc = D::NilAbove(Box::new(doc));
                            line_length = ll;
                        }
                        Some(TextBeside(ann)) | Some(InnerTextBeside { ann, .. }) => {
                            doc = D::TextBeside(ann, Box::new(doc))
                        }
                        Some(Nest { line_length: ll, i }) => {
                            doc = D::Nest(i, Box::new(doc));
                            line_length = ll;
                        }
                        Some(Union(d2)) => {
                            if doc.fits(std::cmp::min(line_length, ribbon_length)) {
                                continue;
                            } else {
                                doc = d2;
                                break 'build;
                            }
                        }
                    }
                },
                D::NilAbove(d) => {
                    doc = *d;
                    stack.push(NilAbove { line_length });
                }
                D::TextBeside(ann, d) => {
                    let mut sl = ann.size();
                    stack.push(TextBeside(ann));

                    let mut inner_stack: Vec<BestCont<A>> = vec![];
                    let mut inner_doc = *d;
                    'best1: loop {
                        match inner_doc {
                            D::Empty | D::NoDoc => 'best1_build: loop {
                                match inner_stack.pop() {
                                    None => {
                                        doc = inner_doc;
                                        break 'best1;
                                    }
                                    Some(InnerTextBeside { ann, sl: old_sl }) => {
                                        sl = old_sl;
                                        inner_doc = D::TextBeside(ann, Box::new(inner_doc));
                                    }
                                    Some(Union(d2)) => {
                                        if inner_doc
                                            .fits(std::cmp::min(line_length, ribbon_length) - sl)
                                        {
                                            continue;
                                        } else {
                                            inner_doc = d2;
                                            break 'best1_build;
                                        }
                                    }
                                    Some(NilAbove { .. })
                                    | Some(TextBeside(..))
                                    | Some(Nest { .. }) => panic!("best1 loop: outer cont"),
                                }
                            },
                            D::NilAbove(d) => {
                                stack.extend(inner_stack);
                                stack.push(BestCont::NilAbove {
                                    line_length: line_length - sl,
                                });
                                doc = *d;
                                break 'best1;
                            }
                            D::TextBeside(ann, d) => {
                                sl = sl + ann.size();
                                inner_stack.push(InnerTextBeside { ann, sl });
                                inner_doc = *d;
                            }
                            D::Nest(_, d) => {
                                inner_doc = *d;
                            }
                            D::Union(d1, d2) => {
                                inner_doc = *d1;
                                inner_stack.push(Union(*d2));
                            }
                            D::Above(..) => panic!("best1 on Above"),
                            D::Beside(..) => panic!("best1 on Beside"),
                        }
                    }
                }
                D::Nest(i, d) => {
                    doc = *d;
                    stack.push(Nest { line_length, i });
                    line_length = line_length - i;
                }
                D::Union(d1, d2) => {
                    doc = *d1;
                    stack.push(Union(*d2));
                }
                D::Above(..) => panic!("best on Above"),
                D::Beside(..) => panic!("best on Beside"),
            }
        }

        doc
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
