
#let identity(it) = it

#let todo(it) = text(fill: color.red, it)
#let framed(it) = box(stroke: 1pt, inset: 4pt, it)
#let grayed(it) = {
  set text(fill: color.gray)
  it
}

#let grammar(name, symbol, ..rules) = align(center, table(
  columns: 4,
  align: (right, center, left, left),
  symbol, $::=$, [], name + ":",
  ..rules
    .pos()
    .chunks(2)
    .map( ((rule, desc)) => ([], $|$, rule, "– " + desc) )
    .flatten()
))
#let constants(name, symbol, ..rules) = align(center, table(
  columns: 2,
  align: (right, left),
  ..rules
))
#let rule(name, ..premises, conclusion, condition: []) = {
  let premises = premises.pos().join($wide$)
  $ #text(smallcaps(name)) space frac(premises, conclusion) space #condition $
}


#let quantities = $cal(Q)$
#let owned(it) = $ceil(it)$
#let borrowed(it) = $floor(it)$

// #let input(it) = colour(blue, it)
// #let output(it) = colour(red, it)
#let input(it) = it
#let output(it) = it

#let meta(it) = $grayed(it)$
#let synthesize(contextIn, expression, quantity , type, contextOut) = $
  input(contextIn) space meta(tack.r) space input(expression) space meta(:)^input(quantity) space output(type) space meta(~>) space output(contextOut)
$
#let lookup(env, elem, type) = $input(env) forces input(elem) : output(type)$

#let keyword(it) = $sans(bold(#it))$
// #let many(item, amount) = {
//   let end = if amount == "" {$thin$} else {$thick$}
//   $overline(thin item thin)^amount$
// }
#let more(item) = $overline(thin item thin)$
#let many(item, amount) = $more(item)^amount$
// #let many(item, "n") = $item_1, ..., item_amount$
#let each(it) = $forall_(it)$
#let each(it) = $"for each" it$
// #let with = math.dot
#let with = $comma space$

#let borrow(args, body) = $""^args {body}$
#let box = $keyword("box")$
#let fun(pars, body) = $|pars| space body$
#let cls(pars, vars, body) = $|pars|vars| space body$
#let apply(func, args) = $func\(args\)$
#let tuple(..items) = {
  let items = items.pos().join([,])
  $\(items\)$
}
#let variant(ctor, args) = $ctor\(args\)$
#let list(items) = $\[items\]$
#let bind(quant, names, expr, body) = $keyword("let")^quant space names = expr; space body$
#let match(quant, scrut, arms) = $keyword("match")^quant space scrut space \{arms\}$
//arms.pos().chunks(2).map(((pat, exp)) => pat |-> exp)$
// #let fold(quant, list, accum, var1, var2, body) = $keyword("fold")^quant space list keyword("from") accum keyword("with") var1, var2 |-> body$
#let fold(quant, list, accum, var1, var2, body) = $keyword("fold")^quant space list, accum, {var1, var2 |-> body}$

#let arrow(..from, to) = {
  let from = from.pos().join($, space$)
  $\(from\) -> to$
  // let from = from.pos().join($times$)
  // $\(from -> to\)$
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


#let function(signature, ..rules) = table(
  columns: 3,
  align: (left, center, left),
  table.cell(colspan: 3, signature),
  ..rules
    .pos()
    .chunks(2)
    .map( ((pattern, definition)) => (pattern, $=$, definition) )
    .flatten()
)

#let shorthands(relation, ..rules) = align(center, table(
  columns: 4,
  align: (right, center, left, left),
  ..rules
    .pos()
    .chunks(3)
    .map( ((short, long, description)) => (short, relation, long, "– " + description) )
    .flatten()
))
