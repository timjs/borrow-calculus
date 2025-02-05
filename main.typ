#import "template.typ": setup

#let (wideblock, sideblock, sidenote, aside, todo, template) = setup()

#show: template.with(
  title: [Borrow calculus],
  authors: ((name: "Tim Steenvoorden"),),
)
  // .with(setup: (
  //   body-font: "Lucida Bright OT",
  //   sans-font: "Lucida Sans OT",
  //   math-font: "Lucida Bright Math OT",
  //   font-size: 10pt,
  //   font-leading: 0.85em, //FIXME: change?
  // ))

#include "calculus.typ"