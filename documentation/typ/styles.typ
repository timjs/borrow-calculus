

#let setup(
  body-font: "Libertinus Serif",
  sans-font: "Libertinus Sans",
  math-font: ("Libertinus Math", "New Computer Modern Math"),
  font-size: 11pt,
  font-leading: 0.65em,
  indent-depth: 1.5em,
  margin-width: 1in,
) = {
  //// Setups ////
  let line-height = font-size + font-leading
  let gutter-width = 0.25*margin-width
  let outer-width = margin-width - gutter-width
  let side-width = 2*margin-width
  let side-start() = -margin-width + page.width - outer-width - side-width
  let heading-offset = 4

  //// Helpers ////
  let sq(n) = calc.pow(calc.sqrt(calc.sqrt(2)), n) * font-size
  let pc(x) = x/6 * 1in
  let w(x) = v(x, weak: true)

  //// Functions ///
  let wideblock(it) = block(width: 100% + gutter-width + side-width, it)
  let sideblock(heading: none, dy: -0.5, it) = context(
    place(left, dx: side-start(), dy: dy*line-height,
      block(width: side-width)[
        #if heading != none {text(size: sq(0.5), style: "italic")[#heading\ ]}
        #text(size: sq(-1), it)
      ])
    )
  let sidenote(dy: -0.5, it) = sideblock(dy: dy, it)
  let aside(dy: -0.5, it) = sideblock(dy: dy, heading: "Aside", it)
  let todo(dy: -0.5, it) = sideblock(dy: dy, heading: "Todo", it)

  let template(
    title: none,
    authors: none,
    date: datetime.today(),
    abstract: none,
    it,
  ) = {

    //// Document ////
    set document(title: title, author: authors.map((a) => a.name))

    //// Page ////
    set page(
      paper: "a4",
      margin: (
        left: margin-width,
        right: 3*margin-width,
        top: margin-width,
        bottom: 1.5*margin-width,
      ),
      numbering: "1",
      number-align: right + bottom,
    )

    //// Body ////
    set text(
      font: body-font,
      size: font-size,
    )
    set par(
      leading: font-leading,
      spacing: font-leading, //FIXME: is this correct?
      first-line-indent: indent-depth,
      justify: true,
    )
    show link: underline

    //// Headings ////
    // set heading(numbering: none)
    show heading: (it) => {
      let h = sq(heading-offset - it.level)
      v(h/2)
      text(h, weight: "regular", style: "italic", it)
      v(h/4)
    }
    show heading.where(level: 1): (it) => {
      pagebreak()
      it
    }

    //// Lists ////

    //// Equations ////
    show math.equation: set text(font: math-font)
    set math.lr(size: 1em) // Magic! :-D

    //// Floats ////
    set table(stroke: none)

    //// Main ////

    page(align(left + horizon, {
      text(sq(4), style: "italic", title)
      w(sq(2))
      text(sq(2), style: "italic", authors.at(0).name)
      if date != none {
        w(sq(2))
        text(sq(2), date.display("[day] [month repr:long] [year]"))
      }
      if abstract != none {
        w(sq(2))
        block(width: 80%,
          par(leading: rrt * font-leading, justify: true, linebreaks: "optimized", abstract)
        )
      }
    }))

    it
  }

  (wideblock: wideblock, sideblock: sideblock, sidenote: sidenote, aside: aside, todo: todo, template: template)
}
