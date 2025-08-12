
#let identity(it) = it

#let chunks(a, n) = {
  let r = ()
  for i in range(int(a.len()/n)) {
    r.push(a.slice(i*n, count: n))
  }
  r
 }

#let w(s) = v(s, weak: true)
#let t = 2
#let rt = calc.sqrt(t)
#let rrt = calc.sqrt(rt)

#let framed(it) = box(stroke: 1pt, inset: 4pt, it)
#let grayed = text.with(fill: gray)

#let grammar(name, symbol, ..rules) = table(
  columns: 4,
  align: (right, center, left, left),
  $symbol$, $::=$, [], name + ":",
  ..(chunks(rules.pos(), 2))
    // .chunks(2)
    .map( ((rule, desc)) => ([], $|$, $rule$, "– " + desc) )
    .flatten()
)
#let constants(name, symbol, ..rules) = table(
  columns: 2,
  align: (right, left),
  ..rules
)
#let rule(name, ..premises, conclusion, condition: []) = {
  let premises = premises.pos().join($wide$)
  $ #text(smallcaps(name)) space frac(premises, conclusion) space #condition $
}


#let quantities = $cal(Q)$
#let lift(it) = $ceil(it)$
#let lower(it) = $floor(it)$
#let freeze(it) = $abs(it)$

#let input(it) = text(blue, it)
#let output(it) = text(red, it)
// #let input(it) = it
// #let output(it) = it

#let meta(it) = $grayed(it)$
#let synthesize(contextIn, expression, quantity , type, contextOut) = $
  input(contextIn) space meta(tack.r) space input(expression) space meta(:)^input(quantity) space output(type) space meta(~>) space output(contextOut)
$
#let lookup(env, elem, type) = $input(env) space meta(forces) space input(elem) space meta(:) space output(type)$

#let keyword(it) = $sans(bold(#it))$
// #let many(item, amount) = {
//   let end = if amount == "" {$thin$} else {$thick$}
//   $overline(thin item thin)^amount$
// }
#let many(item, amount) = $overline(thin item thick)^amount$
#let more(item) = $many(item, *)$
#let most(item) = $many(item, +)$
#let maybe(item) = $many(item, ?)$

// #let many(item, "n") = $item_1, ..., item_amount$
#let each(it) = $forall_(it)$
#let each(it) = $"for each" it$
// #let with = math.dot
#let with = $comma space$
#let merge = $inter.double$

#let borrow(args, body) = $""^args {space body space}$
// #let lam(pars, body) = $|pars| space body$
#let lam(pars, body) = $pars -> body$
#let cls(vars, pars, body) = $attach(tl: vars, {space pars -> body space})$
#let fun(name, pars, body, cont) = $keyword("fun") space name(pars) space body; space cont$
#let apply(func, args) = $func(args)$
#let tuple(..items) = {
  let items = items.pos().join([,])
  $(items)$
}
#let variant(ctor, args) = $ctor(args)$
#let list(items) = $[items]$
#let val(quant, names, body, cont) = $keyword("val")^quant space names = body; space cont$
#let split(quant, names, body, cont) = $keyword("split")^quant space names = body; space cont$
#let match(quant, body, arms) = $keyword("match")^quant space body space arms$
//arms.pos().chunks(2).map(((pat, exp)) => pat |-> exp)$
// #let fold(quant, list, accum, var1, var2, body) = $keyword("fold")^quant space list keyword("from") accum keyword("with") var1, var2 |-> body$
#let fold(quant, list, accum, var1, var2, body) = $keyword("fold")^quant space list, accum, {var1, var2 |-> body}$
#let wilt = $keyword("wilt")$
#let bind(name, body, cont) = $keyword("with") space name space <- body; space cont$

#let Arrow(..from, to) = {
  let from = from.pos().join($, space$)
  $(from) arrow to$
  // let from = from.pos().join($times$)
  // $(from -> to)$
}
#let type(name, ..inner) = {
  let inner = inner.pos().join($, space$)
  // $name angle.l inner angle.r$
  $name(inner)$
}
#let List(inner) = type("List", inner)
#let variants(..items) = {
  let items = items.pos().join($,$)
  $angle.l items angle.r$
}
#let type(name, items) = $keyword("type") space name = angle.l items angle.r$

#let arg(name, quant, type) = $name attach(tr: quant, ":") type$
#let qt(quant, it) = $attach(tl: quant, it)$

#let code(it) = {
  set align(left)
  it
}

#let function(signature, ..rules) = table(
  columns: 3,
  align: (left, center, left),
  table.cell(colspan: 3, signature),
  ..(chunks(rules.pos(), 2))
  // ..rules
  //   .pos()
  //   .chunks(2)
    .map( ((pattern, definition)) => (pattern, $=$, definition) )
    .flatten()
)

#let shorthands(relation, ..rules) = align(center, table(
  columns: 4,
  align: (right, center, left, left),
  ..(chunks(rules.pos(), 3))
    // .chunks(3)
    .map( ((short, long, description)) => (short, relation, long, "– " + description) )
    .flatten()
))
