#let setup = (
  body-font: "Linux Libertine",
  sans-font: "Linux Biolinum",
  math-font: "Libertinus Math",
  coloured: true,
)
#show math.equation: set text(font: setup.math-font)

#let identity(x) = x

#let frame(x) = box(stroke: 1pt, inset: 4pt, x)

#let grammar(name, symbol, ..rules) = {
  $ #table(
    columns: 4,
    align: (right, center, left, left),
    stroke: none,
    symbol, $: : =$, [], name + [:],
    ..rules
      .pos()
      .chunks(2)
      .map(((rule, desc)) => (sym.space, $|$, rule, "– " + desc))
      .flatten()
  ) $
}
#let rule(name, ..premises, conclusion, condition: []) = {
  let premises = premises.pos().join(space.quad)
  $ #text(smallcaps(name)) space frac(premises, conclusion) space #condition $
}

#let colour(c, x) = if setup.coloured { text(fill: c, x) } else { x }
#let input(x) = colour(blue, x)
#let output(x) = colour(red, x)

#let synthesize(contextIn, expression, quantity , type, contextOut) = $
  input(contextIn) tack.r input(expression) :^input(quantity) output(type) ~> output(contextOut)
$
#let lookup(env, elem, type) = $input(env) forces input(elem) : output(type)$

#let keyword(it) = $sans(bold(#it))$
// #let many(item) = $accent(item, harpoon)$
#let many(item, amount: "") = $overline(item)^amount$
// #let many(item, amount: "n") = $item_1, ..., item_amount$

#let borrow(args, body) = $""^args {body}$
#let funtion(pars, body) = $keyword("fn")\(pars\) space body$
#let apply(func, args) = $func\(args\)$
#let tuple(items) = $\(items\)$
#let variant(ctor, num, args) = $ctor^num \(args\)$
#let list(items) = $\[items\]$
#let bind(quant, names, expr, body) = $keyword("let")_quant space \(names\) = expr; space body$
#let match(quant, scrut, arms) = $keyword("match")_quant space scrut space \{arms\}$
//arms.pos().chunks(2).map(((pat, exp)) => pat |-> exp)$
// #let fold(quant, list, accum, var1, var2, body) = $keyword("fold")_quant space list keyword("from") accum keyword("with") var1, var2 |-> body$
#let fold(quant, list, accum, var1, var2, body) = $keyword("fold")_quant space list, accum, {var1, var2 |-> body}$

#let arrow(from, to) = $\(from\) -> to$
#let variants(items) = $angle.l items angle.r$

#let arg(name, quant, type) = $name :^quant type$

= Borrowing calculus

== Syntax

#grammar("Expressions", $e$,
  $x$, "variable",
  $borrow(many(x), e)$, "borrow",
  $funtion(many(arg(x, q, tau)), e_0)$, "function",
  $tuple(many(e))$, "tuple",
  $variant(C, n, many(e, amount: n))$, "variant",
  $list(many(e))$, "list",
  $apply(e_0, many(e))$, "application",
  $bind(q_0, many(x), e_0, e)$, "binding",
  $match(q_0, e_0, many(C^n \(many(x, amount: n)\) |-> e))$, "match",
  $fold(q_1, e_1, e_2, x_1, x_2, e_3)$, "fold"
)

#grammar("Values", $v$,
  $funtion(many(arg(x, q, tau)), e_0)$, "function",
  $tuple(many(v))$, "tuple",
  $variant(C, n, many(v, amount: n))$, "variant",
  $list(many(v))$, "list",
)


#grammar("Types", $tau$,
  $arrow(many(tau^q), tau_0)$, "function",
  $tuple(many(tau))$, "tuple",
  $variants(many(C^n (many(tau))))$, "variant",
  $list(many(tau))$, "list",
)

#pagebreak()
== Typing

$
frame(synthesize(Gamma^+, e^+, q^+, tau^-, Gamma^-))
\

\
bold("Variables")
\

rule("Var"_1,
  space,
  synthesize(Gamma\, arg(x, 1, tau), x, 1, tau, Gamma),
) space.quad
rule("Var"_mu,
  space,
  synthesize(Gamma\, arg(x, mu, tau), x, mu, tau, Gamma\, arg(x, mu, tau)),
  condition: mu in {epsilon, omega}
)\

rule("Weak",
  synthesize(Gamma, x, omega, tau, Gamma),
  synthesize(Gamma, x, 1, tau, Gamma),
) space.quad
rule("Borrow",
  synthesize(Gamma\, many(arg(x, epsilon, tau)), e, q, tau, Gamma'\, many(arg(x, epsilon, tau))),
  synthesize(Gamma\, many(arg(x, nu, tau)), borrow(many(x), e), q, tau, Gamma'\, many(arg(x, nu, tau))),
  condition: nu in {1, omega}
)\
// space.quad (italic("or") space.quad
// rule("Var"_"weak",
//   space,
//   synthesize(Gamma\, arg(x, omega, tau) , x, 1, tau, Gamma\, arg(x, omega, tau)),
// ) )

\
bold("Introduction")
\

rule("Fun",
  synthesize(Gamma_0\, many(arg(x, q, tau), amount: n), e_0, 1, tau_0, Gamma_1),
  synthesize(Gamma_0, funtion(many(arg(x, q, tau), amount: n), e_0), -, arrow(many(tau^q, amount: n), tau_0), Gamma_1 div many(x, amount: n)),
)\

rule("Tuple",
  forall_(i in 1..n),
  synthesize(Gamma_i, e_i, 1, tau_i, Gamma_(i+1)),
  synthesize(Gamma_1, tuple(many(e, amount: n)), -, tuple(many(tau, amount: n)), Gamma_(n+1)),
) space.quad
// rule("Tuple",
//   many(synthesize(Gamma', e, 1, tau, Gamma'')),
//   synthesize(Gamma, tuple(many(e)), -, tuple(many(tau)), Gamma''),
// )\

rule("List",
  forall_(i in 1..n),
  synthesize(Gamma_i, e_i, 1, tau, Gamma_(i+1)),
  synthesize(Gamma_1, list(many(e, amount: n)), -, list(tau), Gamma_(n+1))
)\

rule("Con",
  lookup(Sigma, C^n, arrow(many(tau, amount: n), tau)),
  , forall_(i in 1..n),
  synthesize(Gamma_i, e_i, 1, tau_i, Gamma_(i+1)),
  synthesize(Gamma_1, variant(C, n, many(e, amount: n)), -, tau, Gamma_(n+1)),
)\

\
bold("Elimination")
\

// rule("Abs1",
//   synthesize(Gamma\, x_1 :^(q_1) tau_1, e_0, 1, tau_0, Gamma'),
//   synthesize(Gamma, funtion(x_1 :^(q_1) tau_1, e_0), \-, (tau_1^q) -> tau_0, Gamma' div x_1),
// )\
// rule("App1",
//   synthesize(Gamma, e_0, q, (tau_1^(q_1)) -> tau_0, Gamma'),
//   synthesize(Gamma', e_1, q_1, t_1, Gamma''),
//   synthesize(Gamma, e_0(e_1), q, tau_0, Gamma''),
// )\

// rule("App",
//   synthesize(Gamma, e_0, q, arrow(many(tau^q), tau_0), Gamma'),
//   many(synthesize(Gamma', e, q, tau, Gamma'')),
//   synthesize(Gamma, e_0(many(e)), q, tau_0, Gamma''),
// )\
rule("App",
  synthesize(Gamma, e_0, epsilon, arrow(many(tau^q, amount: n), tau), Gamma_1),
  , forall_(i in 1..n),
  synthesize(Gamma_i, e_i, q_i, tau_i, Gamma_(i+1)),
  // many(synthesize(Gamma', e, q, tau, Gamma'')),
  synthesize(Gamma, apply(e_0, many(e, amount: n)), -, tau, Gamma_(n+1)),
)\
// rule("App",
//   synthesize(Gamma, e_0, q, arrow(tau_1^(q_1)\, ...\,tau_k^(q_k), tau_0), Gamma_1),
//   synthesize(Gamma_1, e_1, q_1, tau_1, Gamma_2),
//   ...,
//   synthesize(Gamma_k, e_k, q_k, tau_k, Gamma_(n+1)),
//   // synthesize(Gamma_i, e_i, q_i, tau_i, Gamma_(i+1)),
//   // many(synthesize(Gamma', e, q, tau, Gamma'')),
//   synthesize(Gamma, e_0(e_1, ..., e_k), q, tau_0, Gamma_(n+1)),
// )\


rule("Let",
  synthesize(Gamma_0, e_0, q_0, tuple(many(tau, amount: n)), Gamma_1),
  synthesize(Gamma_1\, many(arg(x, q_0, tau), amount: n), e, 1, tau, Gamma_2),
  synthesize(Gamma_0, bind(q_0, many(x, amount: n), e_0, e), -, tau, Gamma_2),
)\

rule("Match",
  synthesize(Gamma, e_0, q_0, tau_0, Gamma_1),
  , forall_(i in 1..m),
  lookup(Sigma, C_i^(n_i), arrow(many(tau, amount: n_i), tau_0)),
  synthesize(Gamma_i\, many(arg(x, q_0, tau), amount: n_i), e_i, 1, tau, Gamma_(i+1)),
  synthesize(Gamma, match(q_0, e_0, many(variant(C, n, many(x, amount:n)), amount: m)), -, tau, Gamma_(n+1)),
)\

rule("Fold",
  synthesize(Gamma_1, e_1, q_1, list(tau_1), Gamma_2),
  synthesize(Gamma_2, e_2, 1, tau_2, Gamma_3),
  synthesize(Gamma_3\, arg(x_1, q, tau_1)\, arg(x_2, 1, tau_2), e_3, 1, tau, Gamma_4),
  synthesize(Gamma_1, fold(q_1, e_1, e_2, x_1, x_2, e_3), -, tau, Gamma_4),
)\
$
