#let setup = (
  font-family: "Lucida", //"Libertinus",
  coloured: true,
)

#let setup = if setup.font-family == "Lucida" {
  setup + (
    body-font: "Lucida Bright OT",
    sans-font: "Lucida Sans OT",
    math-font: "Lucida Bright Math OT",
    font-size: 10pt,
    font-leading: 0.85em, //FIXME: change?
  )
} else {
  setup + (
    body-font: "Libertinus Serif",
    sans-font: "Libertinus Sans",
    math-font: "Libertinus Math",
    font-size: 11pt,
    font-leading: 0.65em,
  )
}

#show math.equation: set text(font: setup.math-font)
#set text(font: setup.body-font, size: setup.font-size)
#set par(leading: setup.font-leading)
#set table(stroke: none)

#let identity(it) = it

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

#let colour(colour, it) = if setup.coloured { text(fill: colour, it) } else { it }
#let input(it) = colour(blue, it)
#let output(it) = colour(red, it)

#let quantities = $cal(Q)$
#let owned(it) = $ceil(it)$
#let borrowed(it) = $floor(it)$

#let synthesize(contextIn, expression, quantity , type, contextOut) = $
  input(contextIn) tack.r input(expression) :^input(quantity) output(type) ~> output(contextOut)
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

#let borrow(args, body) = $""^args {body}$
#let funtion(fvars, pvars, body) = $keyword("fn")^fvars\(pvars\) space body$
#let apply(func, args) = $func\(args\)$
#let tuple(..items) = {
  let items = items.pos().join([,])
  $\(items\)$
}
#let variant(ctor, num, args) = $ctor^num \(args\)$
#let list(items) = $\[items\]$
#let bind(quant, names, expr, body) = $keyword("let")^quant space \(names\) = expr; space body$
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
#let List(type) = $"List"(type)$

#let variants(..items) = {
  let items = items.pos().join([,])
  $angle.l items angle.r$
}

#let arg(name, quant, type) = $name attach(tr: quant, ":") type$
#let qt(quant, it) = $attach(tl: quant, it)$

= Borrowing calculus

== Metavariables

#stack(
  dir: ltr,
  spacing: 1fr,
table(
  columns: 2,
  align: (right, left),
  $a$, [],
  $b$, [basic values],
  $c$, [constants],
  $d$, [declarations],
  $e$, [expressions],
  $f$, [],
  $g$, [],
  $h$, [],
  $i$, [],
  $j$, [],
  $k$, [],
  $l$, [],
  $m$, [modules],
  $n$, [],
  $o$, [],
  $p$, [patterns],
  $q$, [quantities],
  $r$, [],
  $s$, [],
  $t$, [],
  $u$, [],
  $v$, [values],
  $w$, [],
  $x$, [variables],
  $y$, [],
  $z$, [],
),
table(
  columns: 2,
  align: (right, left),
  $alpha$,   [],
  $beta$,    [],
  $gamma$,   [],
  $delta$,   [],
  $epsilon$, [()],
  $zeta$,    [],
  $eta$,     [],
  $theta$,   [],
  $iota$,    [],
  $kappa$,   [],
  $lambda$,  [],
  $mu$,      [],
  $nu$,      [],
  $xi$,      [],
  $omicron$, [],
  $pi$,      [],
  $rho$,     [rows],
  $sigma$,   [schemas],
  $tau$,     [types],
  $upsilon$, [],
  $phi$,     [],
  $chi$,     [],
  $psi$,     [],
  $omega$,   [],
)
)

\ We write:
  - $many(x, n)$ for an _ordered_ set of $x$es of length $n$, so $x_1, ..., x_n$.
  - $more(x)$ for an _unordered_ set of $x$es.

#pagebreak()
== Syntax

#grammar("Expressions", $e$,
  $x, y, z$, "variable",
  $borrow(many(x, ""), e)$, "borrow",
  $funtion(many(z, ""), many(arg(x, q, tau), n), e_0)$, "abstraction",
  $apply(e_0, many(e, n))$, "application",
  $tuple(many(e, n))$, "tuple",
  $bind(q_0, many(x, n), e_0, e)$, "split",
  $variant(C, n, many(e, n))$, "variant",
  $match(q_0, e_0, many(C^n \(many(x, n)\) |-> e, m))$, "match",
)

#grammar("Values", $v$,
  $funtion(many(z, ""), many(arg(x, q, tau), n), e_0)$, "abstraction",
  $tuple(many(v, n))$, "tuple",
  $variant(C, n, many(v, n))$, "variant",
)

#grammar("Basic values", $b$,
  $tuple(many(b, n))$, "tuple",
  $variant(C, n, many(b, n))$, "variant",
)


#grammar("Types", $tau$,
  $arrow(many(tau^q, n), tau_0)$, "abstraction",
  $tuple(many(tau, n))$, "tuple",
  $variants(many(C^n (many(tau, n)), m))$, "variant",
  $List(tau)$, "list",
)

#grammar("Quantities", $q$,
  $epsilon$, "borrowed",
  $1$, "linear",
  $omega$, "unrestricted",
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

#shorthands($in$,
  $mu$, ${epsilon, omega}$, "multiple",
  $nu$, ${1, omega}$, "owned",
  $pi$, ${epsilon, 1}$, "parameter",
)

#pagebreak()
== Typing

The algorithmic typing rules of $lambda^"borrow"$ are given in @fig-rules.
The typing relation $synthesize(Gamma, e, q, tau, Gamma')$ can be read as
#quote[using expression $e$ with quantity $q$ can make use of all the bindings in context $Gamma$, which yields type $tau$ and a modifed context $Gamma'$.]

#figure(caption: [Typing rules])[$
  framed(synthesize(Gamma^+, e^+, q^+, tau^-, Gamma^-))
  \

  \
  bold("Variables")
  \

  rule("Var"_1,
    space,
    synthesize(Gamma\, arg(x, 1, tau), x, 1, tau, Gamma),
  ) quad
  rule("Var"_mu,
    space,
    synthesize(Gamma\, arg(x, mu, tau), x, mu, tau, Gamma\, arg(x, mu, tau)),
    condition: mu in {epsilon, omega}
  )\

  // rule("Weak",
  //   synthesize(Gamma, x, omega, tau, Gamma),
  //   synthesize(Gamma, x, 1, tau, Gamma),
  // ) quad
  rule("Var"_"weak",
    space,
    synthesize(Gamma\, arg(x, omega, tau) , x, 1, tau, Gamma\, arg(x, omega, tau)),
  ) quad
  rule("Borrow",
    synthesize(Gamma_0\, more(arg(x, epsilon, tau) ), e, q, tau, Gamma_1\, more(arg(x, epsilon, tau))),
    synthesize(Gamma_0\, more(arg(x, nu, tau)), borrow(more(x), e), q, tau, Gamma_1\, more(arg(x, nu, tau))),
    condition: nu in {1, omega}
  )\

  \
  bold("Introduction")
  \

  rule("Abs",
    synthesize(Gamma_0^nu\, many(arg(x, q, tau), n), e_0, owned(q), tau_0, Gamma_1),
    synthesize(Gamma_0^epsilon union Gamma_0^nu, funtion("", many(arg(x, q, tau), n), e_0), q,
      arrow(many(tau^q, n), tau_0), Gamma_0^epsilon union Gamma_1 without many(x, n)),
    condition: exists z in "fv"(e_0) without many(x, n). space arg(z, 1, tau_z) in Gamma_0  => q = 1,
  )\
  grayed(
    rule("Abs",
      synthesize(Gamma_0^nu\, arg(x_1, q_1, tau_1), e_0, owned(q), tau_0, Gamma_1),
      synthesize(Gamma_0^epsilon union Gamma_0^nu, funtion("", arg(x_1, q_1, tau_1), e_0), q,
        arrow(tau_1^(q_1), tau_0), Gamma_0^epsilon union Gamma_1 without x),
      condition: exists z in "fv"(e_0) without x_1. space arg(z, 1, tau_z) in Gamma_0  => q = 1,
    )\
  )

  rule("Pair",
    each(i in 1..n),
    synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
    synthesize(Gamma_1, tuple(many(e, n)), q, tuple(many(tau, n)), Gamma_(n+1)),
  )\
  grayed(
    rule("Pair",
      synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
      synthesize(Gamma_2, e_2, owned(q), tau_2, Gamma_3),
      synthesize(Gamma_1, tuple(e_1, e_2), q, tuple(tau_1, tau_2), Gamma_3),
    )\
  )

  rule("Con",
    lookup(Delta, C^n, arrow(many(tau, n), tau_0)),
    each(i in 1..n),
    synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
    synthesize(Gamma_1, variant(C, n, many(e, n)), q, tau_0, Gamma_(n+1)),
  )\
  grayed(
    rule("Inj",
      lookup(Delta, C, arrow(tau_1, tau_0)),
      synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
      synthesize(Gamma_1, variant(C, "", e_1), q, tau_0, Gamma_2),
    )\
  )

  \
  bold("Elimination")
  \

  rule("App",
    synthesize(Gamma_0, e_0, q, arrow(many(tau^q, n), tau_0), Gamma_1),
    each(i in 1..n),
    synthesize(Gamma_i, e_i, q_i, tau_i, Gamma_(i+1)),
    synthesize(Gamma_0, apply(e_0, many(e, n)), q, tau_0, Gamma_(n+1)),
  )\
  grayed(
    rule("App",
      synthesize(Gamma_0, e_0, q, arrow(tau_1^(q_1), tau_0), Gamma_1),
      synthesize(Gamma_1, e_1, q_1, tau_1, Gamma_2),
      synthesize(Gamma_0, apply(e_0, e_1), q, tau_0, Gamma_2),
    )\
  )

  rule("Let",
    synthesize(Gamma_0, e_0, q_0, tuple(many(tau, n)), Gamma_1),
    synthesize(Gamma_1\, many(arg(x, q_0, tau), n), e, q, tau, Gamma_2),
    synthesize(Gamma_0, bind(q_0, many(x, n), e_0, e), q, tau, Gamma_2 without many(x, n)),
  )\
  grayed(
    rule("Let",
      synthesize(Gamma_0, e_0, q_0, tuple(tau_1, tau_2), Gamma_1),
      synthesize(Gamma_1\, arg(x_1, q_1, tau_1)\, arg(x_2, q_2, tau_2), e, q, tau, Gamma_2),
      synthesize(Gamma_0, bind(q_0, x_1\, x_2, e_0, e), q, tau, Gamma_2 without x_1\, x_2),
    )\
  )

  rule("Match",
    synthesize(Gamma_0, e_0, q_0, tau_0, Gamma_1),
    each(i in 1..m),
    lookup(Delta, C_i^(n_i), arrow(many(tau, n_i), tau_0)),
    synthesize(Gamma_1\, many(arg(x, q_0, tau), n_i), e_i, q, tau, Gamma_2 union many(arg(x, q_0, tau), n_i)),
    synthesize(Gamma_0, match(q_0, e_0, many(variant(C, n, many(x, n)) |-> e, m)), q, tau, Gamma_2),
  )\

  grayed(
    rule("Match",
      synthesize(Gamma_0, e_0, q_0, tau_0, Gamma_1),
      each(i in 1..2),
      lookup(Delta, C_i, arrow(tau_i, tau_0)),
      synthesize(Gamma_1\, arg(x_i, q_0, tau_i), e_i, q, tau, Gamma_2 union arg(x_i, q_0, tau_i)),
      synthesize(Gamma_0, match(q_0, e_0, many(variant(C, "", x) |-> e, 2)), q, tau, Gamma_2),
    )\
  )

  // rule("Fold",
  //   synthesize(Gamma_1, e_1, q_1, list(tau_1), Gamma_2),
  //   synthesize(Gamma_2, e_2, 1, tau_2, Gamma_3),
  //   synthesize(Gamma_3\, arg(x_1, q, tau_1)\, arg(x_2, 1, tau_2), e_3, 1, tau, Gamma_4),
  //   synthesize(Gamma_1, fold(q_1, e_1, e_2, x_1, x_2, e_3), "", tau, Gamma_4),
  // )\
$]<fig-rules>

#pagebreak()
=== Helpers

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

#function($owned(.) : "Quantity" -> "Quantity"$,
  $owned(epsilon)$, $1$,
  $owned(q)$, $q$,
)

#function($borrowed(.) : "Quantity" -> "Quantity"$,
  $borrowed(\_)$, $epsilon$,
)

=== Constants

#let constants(..rules) = table(
  columns: 3,
  align: (right, center, left),
  ..rules
    .pos()
    .chunks(2)
    .map( ((name, type)) => (name, $:$, type) )
    .flatten()
)
#shorthands(":",
  $"fold"_q$, $forall_q. arrow(qt(q, List(tau_1)), qt(1, tau_2), qt(epsilon, arrow(qt(q, tau_1), qt(1, tau_2), tau_2)), tau_2)$, "fold list",
  $"Nil"^0_tau$, $List(tau)$, "nil list",
  $"Cons"^2$, $arrow(tau, List(tau), List(tau))$, "cons list",
)
#shorthands(":=",
  $"Bool"$, $variants("False"^0: (), "True"^0: ())$, "boolean type",
  $"Option"(tau)$, $variants("None"^0: (), "Some"^1: tau)$, "option type",
  $"Result"(tau_1, tau_2)$, $variants("Wrong"^1: tau_1, "Right"^1: tau_2)$, "either type",
)

#pagebreak()
== Tests

#lorem(250)

$|space.med|space.hair|space.thin|space.sixth|space.quarter|space.third|space.en|space.quad|$

$\
|space| \
|space.quad| 1\
|space.en space.en| 2\
|space.third space.third space.third| 3\
|space.quarter space.quarter space.quarter space.quarter| 4\
|space.sixth space.sixth space.sixth space.sixth space.sixth space.sixth| 6\
$

$\
|thin|med|thick|quad|wide| \
|wide| "wide = 2 quad"\
|quad| "quad"\
|thick thick thick| "3 thick"\
|med med med med| "4 med"\
|thin thin thin thin thin thin| "6 thin"\
|quad| "quad"\
$

$
  Gamma_0 union Gamma_1 without Gamma_2 \
  Gamma_0 union.double Gamma_1 backslash Gamma_2 \
  Gamma_0 union.double Gamma_1 slash.double Gamma_2 \
  Gamma_0 union.plus Gamma_1 union.minus Gamma_2 \
  Gamma_0 plus Gamma_1 minus Gamma_2 \
  Gamma_0 plus.circle Gamma_1 minus.circle Gamma_2 \
  Gamma_0 plus.circle Gamma_1 backslash.circle Gamma_2 \
  Gamma_0 compose Gamma_1 div Gamma_2 \
$
