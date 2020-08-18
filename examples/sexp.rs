use ohso::{Doc, Pretty, Style};

enum SExp {
    Atom(String),
    Apply(Vec<SExp>),
}

impl SExp {
    pub fn atom<S: ToString>(s: S) -> Self {
        SExp::Atom(s.to_string())
    }

    pub fn apply<I: IntoIterator<Item = SExp>>(i: I) -> Self {
        SExp::Apply(i.into_iter().collect())
    }
}

impl Pretty<()> for &SExp {
    fn to_doc(self) -> Doc<()> {
        match self {
            SExp::Atom(a) => a.clone().to_doc(),
            SExp::Apply(xs) => Doc::sep(xs.into_iter().map(|x| x.to_doc().nest(1))).parens(),
        }
    }
}

pub fn main() {
    // (1 2 3)
    let e123 = SExp::apply(vec![SExp::atom(1), SExp::atom(2), SExp::atom(3)]);

    // ((1) (2 3) (4 5 6))
    let e1to6 = SExp::apply(vec![
        SExp::apply(std::iter::once(SExp::atom(1))),
        SExp::apply(vec![SExp::atom(2), SExp::atom(3)]),
        SExp::apply(vec![SExp::atom(4), SExp::atom(5), SExp::atom(6)]),
    ]);

    let v: Vec<Vec<usize>> = vec![
        vec![0, 1, 2, 3],
        vec![4, 5, 6, 7, 8, 9, 10],
        vec![11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
    ];
    let big_e = SExp::apply(
        v.iter()
            .map(|v| SExp::apply(v.iter().map(|a| SExp::atom(a)))),
    );

    for mode in vec![
        ohso::Mode::OneLine,
        ohso::Mode::Left,
        ohso::Mode::ZigZag,
        ohso::Mode::Page,
    ]
    .into_iter()
    {
        println!("MODE: {}", mode);
        show_for_mode(&e123, mode);
        show_for_mode(&e1to6, mode);
        show_for_mode(&big_e, mode);
    }
}

fn show_for_mode(e: &SExp, mode: ohso::Mode) {
    let style = Style {
        line_length: 10,
        mode: mode,
        ..Style::default()
    };
    println!("{}", e.to_doc().render(&style).0);
}
