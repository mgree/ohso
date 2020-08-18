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

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Mode::Page => write!(f, "Page"),
            Mode::ZigZag => write!(f, "ZigZag"),
            Mode::Left => write!(f, "Left"),
            Mode::OneLine => write!(f, "OneLine"),
        }
    }
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
        let doc = &self.0.as_reduced();
        assert!(doc.is_reduced());

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

                let doc = doc.best(line_length, ribbon_length);

                doc.display(style, ribbon_length, txt);
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
        let mut stack: Vec<&Annot<A>> = Vec::new();
        let mut doc = self;

        loop {
            match doc {
                D::Empty => loop {
                    match stack.pop() {
                        None => return,
                        Some(ann) => txt(ann),
                    }
                },
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

        self.lay_loop(style, gap_width, shift, 0, txt)
    }

    #[allow(dead_code)]
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

// continuations for `best`'s state machine
#[derive(Clone, Copy, Debug)]
enum BestMode {
    Get,
    Get1 { sl: isize },
}

impl BestMode {
    fn sl(&self) -> isize {
        match self {
            BestMode::Get => 0,
            BestMode::Get1 { sl } => *sl,
        }
    }
}

enum BestCont<'a, A: Clone> {
    NilAbove { old_line_length: isize },
    Nest { old_line_length: isize, i: isize },
    Union { d2: &'a D<A>, old_mode: BestMode },
    TextBeside { ann: Annot<A> },
}

impl<A: Clone> D<A> {
    pub fn best<'a>(&'a self, line_length: isize, ribbon_length: isize) -> Self {
        use BestCont::*;
        use BestMode::*;

        let mut stack: Vec<BestCont<'a, A>> = Vec::new();
        let mut line_length = line_length;
        let mut doc = self;
        let mut mode = Get;

        'best: loop {
            match (mode, doc) {
                (_, D::Empty) | (_, D::NoDoc) => {
                    let mut out = doc.clone();

                    loop {
                        match stack.pop() {
                            None => return out,
                            Some(NilAbove { old_line_length }) => {
                                out = D::NilAbove(Box::new(out));
                                line_length = old_line_length;
                            }
                            Some(Nest { old_line_length, i }) => {
                                out = D::Nest(i, Box::new(out));
                                line_length = old_line_length;
                            }
                            Some(Union { d2, old_mode }) => {
                                // if the first alternative sucks, throw away `out` and try again with the other alternative
                                if !out
                                    .fits(std::cmp::min(line_length, ribbon_length) - old_mode.sl())
                                {
                                    mode = old_mode;
                                    doc = d2;
                                    continue 'best;
                                }
                            }
                            Some(TextBeside { ann }) => {
                                out = D::TextBeside(ann, Box::new(out));
                            }
                        }
                    }
                }
                (Get, D::NilAbove(d)) => {
                    stack.push(NilAbove {
                        old_line_length: line_length,
                    });
                    doc = d.as_ref();
                }
                (Get, D::Nest(i, d)) => {
                    stack.push(Nest {
                        old_line_length: line_length,
                        i: *i,
                    });
                    doc = d.as_ref();
                    line_length = line_length - i;
                }
                (Get, D::Union(d1, d2)) => {
                    stack.push(Union {
                        d2: d2.as_ref(),
                        old_mode: mode,
                    });
                    doc = d1.as_ref();
                }
                (Get, D::TextBeside(ann, d)) => {
                    stack.push(TextBeside { ann: ann.clone() });
                    doc = d.as_ref();
                    mode = Get1 { sl: ann.size() };
                }
                (Get1 { sl }, D::NilAbove(d)) => {
                    stack.push(NilAbove {
                        old_line_length: line_length,
                    });
                    doc = d.as_ref();
                    mode = Get;
                    line_length = line_length - sl;
                }
                (Get1 { sl }, D::TextBeside(ann, d)) => {
                    stack.push(TextBeside { ann: ann.clone() });
                    mode = Get1 {
                        sl: sl + ann.size(),
                    };
                    doc = d.as_ref();
                }
                (Get1 { .. }, D::Nest(_, d)) => {
                    doc = d.as_ref();
                }
                (Get1 { .. }, D::Union(d1, d2)) => {
                    stack.push(Union {
                        d2: d2.as_ref(),
                        old_mode: mode,
                    });
                    doc = d1.as_ref();
                }
                (mode, D::Above(..)) => panic!("best ({:?}) on Above", mode),
                (mode, D::Beside(..)) => panic!("best ({:?}) on Beside", mode),
            }
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

enum LayCont<'a, A: Clone> {
    NilAbove,
    BesideZigZag { forward: bool },
    Ann { ann: &'a Annot<A>, indent: isize }, // from a call to lay1
    InnerTextBeside { ann: &'a Annot<A> },
}

impl<A: Clone> D<A> {
    fn lay_loop<'a, F>(
        &'a self,
        style: &Style,
        gap_width: isize,
        shift: isize,
        k: isize,
        txt: &mut F,
    ) where
        F: FnMut(&Annot<A>) -> (),
    {
        use LayCont::*;
        let mut stack: Vec<LayCont<'a, A>> = Vec::new();
        let mut doc = self;
        let mut k = k;

        loop {
            match doc {
                D::Empty => loop {
                    match stack.pop() {
                        None => return,
                        Some(InnerTextBeside { ann }) => {
                            txt(ann);
                        }
                        Some(NilAbove) => {
                            txt(&Annot::newline());
                        }
                        Some(BesideZigZag { forward }) => {
                            let nl = Annot::newline();
                            txt(&nl);

                            let ushift = usize::try_from(shift).expect("positive shift");
                            txt(&Annot::Text(
                                Text::Str(
                                    std::iter::repeat(if forward { '/' } else { '\\' })
                                        .take(ushift)
                                        .collect(),
                                ),
                                shift,
                            ));

                            txt(&nl);
                        }
                        Some(Ann { ann, indent }) => {
                            txt(ann);
                            eprintln!("indenting {}", indent);
                            txt(&Annot::indent(indent));
                        }
                    }
                },
                D::Nest(k1, d) => {
                    k = k + *k1;
                    doc = d;
                }
                D::NilAbove(d) => {
                    stack.push(NilAbove);
                    doc = d;
                }
                D::TextBeside(ann, d) => {
                    let old_k = k;
                    k = match style.mode {
                        Mode::ZigZag => {
                            let forward = k >= gap_width;
                            stack.push(BesideZigZag { forward });

                            if forward {
                                k - shift
                            } else {
                                k + shift
                            }
                        }
                        _ => k,
                    };

                    stack.push(Ann { ann, indent: k });
                    k = k + ann.size();

                    let mut inner_stack: Vec<LayCont<'a, A>> = Vec::new();
                    let mut inner_doc = d.as_ref();
                    'lay2: loop {
                        match inner_doc {
                            D::Empty => loop {
                                match inner_stack.pop() {
                                    None => {
                                        doc = inner_doc;
                                        break 'lay2;
                                    }
                                    Some(InnerTextBeside { ann }) => {
                                        txt(ann);
                                        k = old_k;
                                    }
                                    Some(NilAbove)
                                    | Some(BesideZigZag { .. })
                                    | Some(Ann { .. }) => panic!("lay2 loop: outer cont"),
                                }
                            },
                            D::NilAbove(d) => {
                                stack.extend(inner_stack);
                                stack.push(NilAbove);
                                doc = d.as_ref();
                                break 'lay2;
                            }
                            D::TextBeside(ann, d) => {
                                k = k + ann.size();
                                inner_stack.push(InnerTextBeside { ann });
                                inner_doc = d.as_ref();
                            }
                            D::Nest(_, d) => {
                                inner_doc = d.as_ref();
                            }
                            D::Above(..) => panic!("lay2 on Above"),
                            D::Beside(..) => panic!("lay2 on Beside"),
                            D::NoDoc => panic!("lay2 on NoDoc"),
                            D::Union(..) => panic!("lay2 on Union"),
                        }
                    }
                }
                D::Above(..) => panic!("display on Above"),
                D::Beside(..) => panic!("display on Beside"),
                D::NoDoc => panic!("display on NoDoc"),
                D::Union(..) => panic!("display on Union"),
            }
        }
    }
}
