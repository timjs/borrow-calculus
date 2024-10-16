#import "commands.typ": *
#import "rules.typ": rules

#let setup = (
  // font-family: "Libertinus",
  // font-family: "Libertine",
  font-family: "Lucida",
  coloured: false,
  line-indent: 1.5em,
)

#let setup = if setup.font-family == "Lucida" {
  setup + (
    body-font: "Lucida Bright OT",
    sans-font: "Lucida Sans OT",
    math-font: "Lucida Bright Math OT",
    font-size: 10pt,
    font-leading: 0.85em, //FIXME: change?
  )
} else if setup.font-family == "Libertinus" {
  setup + (
    body-font: "Libertinus Serif",
    sans-font: "Libertinus Sans",
    math-font: ("Libertinus Math", "New Computer Modern Math"),
    font-size: 11pt,
    font-leading: 0.65em,
  )
} else {
  setup + (
    body-font: "Linux Libertine",
    sans-font: "Linux Biolinum",
    math-font: "Linux Libertine Math",
    font-size: 11pt,
    font-leading: 0.65em,
  )
}

#show math.equation: set text(font: setup.math-font)
#set text(font: setup.body-font, size: setup.font-size)
#set par(
  leading: setup.font-leading,
  first-line-indent: setup.line-indent,
)
#show par: set block(spacing: setup.font-leading)
#set table(stroke: none)

// #let colour(colour, it) = if setup.coloured { text(fill: colour, it) } else { it }

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
  $c$, [primitive values],
  $d$, [declarations],
  $e$, [expressions],
  $f$, [builtin functions],
  $g$, [],
  $h$, [],
  $i$, [(indexing)],
  $j$, [(indexing)],
  $k$, [],
  $l$, [locations],
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
  $alpha$,   [type variables],
  $beta$,    [basic types],
  $gamma$,   [],
  $delta$,   [],
  $epsilon$, [borrow quantity],
  $zeta$,    [],
  $eta$,     [effect row],
  $theta$,   [heap variables],
  $iota$,    [],
  $kappa$,   [kinds],
  $lambda$,  [effect label],
  $mu$,      [multiple quantity],
  $nu$,      [owned quantity],
  $xi$,      [],
  $omicron$, [],
  $pi$,      [primitive types],
  $rho$,     [row variable],
  $sigma$,   [type schemas],
  $tau$,     [types],
  $upsilon$, [],
  $phi$,     [],
  $chi$,     [],
  $psi$,     [],
  $omega$,   [unrestricted quantity],
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
  $box^? fun(many(arg(x, q, tau), n), e_0)$, "abstraction",
  $apply(e_0, many(e, n))$, "application",
  $tuple(many(e, n))$, "tuple",
  $bind(q_0, tuple(many(x, n)), e_0, e)$, "split",
  $variant(C, many(e, n))$, "variant",
  $match(q_0, e_0, many(variant(C, many(x, n)) |-> e, m))$, "match",
)

#grammar("Values", $v$,
  $cls(many(arg(x, q, tau), n), many(z, ""), e_0)$, "abstraction",
  $tuple(many(v, n))$, "tuple",
  $variant(C, many(v, n))$, "variant",
)

#grammar("Basic values", $b$,
  $tuple(many(b, n))$, "tuple",
  $variant(C, many(b, n))$, "variant",
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

#grammar("Declarations", $d$,
  $type(X, many(C^n (many(tau, n)), m))$, "types",
)

#grammar("Modules", $m$,
  $more(d); e$, "main"
)

#shorthands($in$,
  $mu$, ${epsilon, omega}$, "multiple",
  $nu$, ${1, omega}$, "owned",
  $pi$, ${epsilon, 1}$, "parameter",
)

#pagebreak()
== Typing

The algorithmic typing rules of $lambda^"borrow"$ are given below.
The typing relation
$
  framed(synthesize(Gamma^+, e^+, q^+, tau^-, Gamma^-))
$
can be read as
#quote[using expression $e$ with quantity $q$ can make use of all the bindings in context $Gamma$, which yields type $tau$ and a modified context $Gamma'$.]

=== Variable lookup

Variable lookup comes in two flavours.
Linear bindings with quantity $1$ are looked up and removed from the context as shown in rule $"Var"_1$.
Borrowed and unrestricted bindings with quantities $epsilon$ and $omega$ respectively,
are looked up, but stay in the resulting context.
Rules $"Var"_mu$ defines this for $mu in {epsilon, omega}$ simultaneously.
$
  rules.var.one quad rules.var.mu
$

We need a _weakening_ rule which states that unrestricted bindings can be used linearly ($"Var"_"Weak"$).
Equivalently, we could define weakening as a general rule on bindings instead of a rule for variable lookup.
However, this way our rule set would be nondeterministic.
$
  rules.var.weak quad grayed(rules.weak)
$

We allow every owned binding, that is bindings with quantity $1$ or $omega$, to be borrowed.
Borrows are only valid in a lexical region.
After this region ends, we restore the original quantity on the binding.
$
  rules.borrow.nu
$
Here, we need to take care borrowed bindings do not escape from this region.
Therefore, we _lift_ quantity $q$ of the expression surroundings to be _owned_.
That is, borrowed expression surroundings are lifted to unrestricted contexts,
the two owning quantities stay the same.
The definitions of lifting and lowering is as follows.
$
  function(owned(dot) : "Quantity" -> "Quantity",
    owned(epsilon), omega,
    owned(q), q,
  ) \
  function(borrowed(dot) : "Quantity" -> "Quantity",
    borrowed(\_), epsilon,
  )
$

Alternatively, to allow for free borrowing of unrestricted bindings,
we could alter $"Var"_"weak"$ to also include $epsilon$ in its expression surroundings.
We can change $"Borrow"_nu$ accordingly for explicit borrows of linear variables only.
$
  grayed(rules.var.pi\ rules.borrow.one)
$

=== Functions

For function abstraction, we have three cases, one for each quantity.
Depending on the quantity of the expression surroundings,
anonymous function blocks have access to different sets of bindings.
/ $epsilon$:
  As we are in a borrowed expression surroundings, function blocks cannot be returned nor stored: they are _second-class_.
  Therefore, these blocks have access to all borrowed bindings as well as all unrestricted bindings.
  As they can be called multiple times (the code is borrowed and can be used multiple times),
  we cannot allow usage of linear bindings.
/ $omega$:
  For unrestricted expression surroundings the situation in different.
  As these function blocks are owned, they _can_ be stored or returned.
  Therefore, we need to make sure second-class bindings are not stored in its closure.
  Borrowed bindings should not escape, only unrestricted bindings are allowed.
/ $1$:
  Similarly, linear blocks are first-class and can be saved or returned,
  so we cannot close over borrowed bindings.
  However, as we know that the resulting closure can only be used _once_,
  in this case we can also allow access to linear bindings.
$
  rules.abs.epsilon.curried\
  rules.abs.one.curried\
  rules.abs.omega.curried\
$

To select bindings with the proper quantity from the context, we use _context filtering_ which is defined as follows.
$
  function(Gamma^q : "Context" times "Quantity" -> "Context",
    nothing^q, nothing,
    (Gamma with arg(x, q, tau))^q, Gamma^q with arg(x, q, tau),
    (Gamma with arg(x, q', tau))^q, Gamma^q,
  )
$

When functions are applied in an expression surroundings of quantity $q$,
the function itself needs to be available $q$ times.
Quantities of the arguments are determined by the function's type signature.
$
  rules.app.curried
$

=== Datatypes

When creating datatypes, we need to store data so each subexpression in constructors needs to be owned.
Although we allow creating datatypes in borrowed expression surroundings,
we lift the context quantity to make sure stored data is owned.
$
  rules.pair.curried\
  rules.con.curried\
$
Note the similarities and differences between rules $"Con"$ and $"App"$:
- Both "lookup" the type of the function or constructor,
  which directs the type of the arguments and the returntype of the application or construction.
- In application, the quantities of the arguments are directed by the function type,
  while in construction, these quantities are directed by the expression surroundings.

When destructuring datatypes, we have two quantities to take into account:
- The quantity in which the whole destructuring expression is going to be evaluated
  We call this the _expression context quantity_.
- The quantity of the resulting parts of the datatype, that are made available in continuation of the program.
  This is also the quantity that the scrutiny needs to be available for.
  To accommodate for this,
  we annotate destructuring constructs in our language with an addition quantity $q_0$.

For the splitting of tuples, we ask an expression $e_0$ to be available for quantity $q_0$.
The resulting bindings $x_1$ and $x_2$ are then made available for the same quantity $q_0$ in the remaining part of the program.
Note we need to remove these bindings from the resulting context $Gamma_2$ if they still exist.
$
  rules.bind.curried
$

For destructuring we can make a similar argument regarding the match-quantity $q_0$.
Additionally, because now we have multiple branches that can be taken, we need to _merge_ the resulting contexts of each branch and remove the freshly introduced bindings if still existing.
$
  rules.match.curried
$

As after branching, contexts can only differ in removed linear bindings,
merging two contexts is simply set intersection.
#todo[Check this! Aren't we passing let-bound variables to the next argument?]

=== Built-ins

#shorthands(":",
  $"fold"_q$, $arrow(qt(q, List(tau_1)), qt(1, tau_2), qt(epsilon, arrow(qt(q, tau_1), qt(1, tau_2), tau_2)), tau_2)$, "fold list",
)

#shorthands(":",
  $"Nil"_tau$, $List(tau)$, "nil list",
  $"Cons"$, $arrow(tau, List(tau), List(tau))$, "cons list",
)

#shorthands(":=",
  $"Bool"$, $variants("False"(), "True"())$, "boolean type",
  $"Option"(tau)$, $variants("None"(), "Some"(tau))$, "option type",
  $"Result"(tau_1, tau_2)$, $variants("Wrong"(tau_1), "Right"(tau_2))$, "either type",
)


#pagebreak()
== Arrity calculus

#figure(caption: [Typing rules])[$
  bold("Introduction")
  \

  rule("Abs",
    synthesize(Gamma_0^nu with many(arg(x, q, tau), n), e_0, owned(q), tau_0, Gamma_1),
    synthesize(Gamma_0^epsilon with Gamma_0^nu, fun(many(arg(x, q, tau), n), e_0), q,
      arrow(many(tau^q, n), tau_0), Gamma_0^epsilon with Gamma_1 without many(x, n)),
    condition: exists z in "fv"(e_0) without many(x, n). space arg(z, 1, tau_z) in Gamma_0  => q = 1,
  )\

  rule("Pair",
    each(i in 1..n),
    synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
    synthesize(Gamma_1, tuple(many(e, n)), q, tuple(many(tau, n)), Gamma_(n+1)),
  )\

  rule("Con",
    lookup(Delta, C, arrow(many(tau, n), tau_0)),
    each(i in 1..n),
    synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
    synthesize(Gamma_1, variant(C, many(e, n)), q, tau_0, Gamma_(n+1)),
  )\

  \
  bold("Elimination")
  \

  rule("App",
    synthesize(Gamma_0, e_0, borrowed(q), arrow(many(tau^q, n), tau_0), Gamma_1),
    each(i in 1..n),
    synthesize(Gamma_i, e_i, q_i, tau_i, Gamma_(i+1)),
    synthesize(Gamma_0, apply(e_0, many(e, n)), q, tau_0, Gamma_(n+1)),
  )\

  rule("Let",
    synthesize(Gamma_0, e_0, q_0, tuple(many(tau, n)), Gamma_1),
    synthesize(Gamma_1 with many(arg(x, q_0, tau), n), e, q, tau, Gamma_2),
    synthesize(Gamma_0, bind(q_0, many(x, n), e_0, e), q, tau, Gamma_2 without many(x, n)),
  )\

  rule("Match",
    synthesize(Gamma_0, e_0, q_0, tau_0, Gamma'_0),
    each(i in 1..m),
    lookup(Delta, C_i^(n_i), arrow(many(tau, n_i), tau_0)),
    synthesize(Gamma'_0 with many(arg(x, q_0, tau), n_i), e_i, q, tau, Gamma'_i),
    synthesize(Gamma_0, match(q_0, e_0, many(variant(C, many(x, n)) |-> e, m)), q, tau, sect.double_(i in 1..m) Gamma'_i without x_i),
  )\
$]<fig-rules-arrity>

#pagebreak()
== Tests

#lorem(100)

#lorem(150)

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
  union.big.dot sect.big #place(dx: -1.125em, $=$) underline(sect.big) \
  Gamma_0 union Gamma_1 without Gamma_2 \
  Gamma_0 union.double Gamma_1 backslash Gamma_2 \
  Gamma_0 union.double Gamma_1 slash.double Gamma_2 \
  Gamma_0 union.plus Gamma_1 union.minus Gamma_2 \
  Gamma_0 plus Gamma_1 minus Gamma_2 \
  Gamma_0 plus.circle Gamma_1 minus.circle Gamma_2 \
  Gamma_0 plus.circle Gamma_1 backslash.circle Gamma_2 \
  Gamma_0 compose Gamma_1 div Gamma_2 \
  plus.arrow, plus.arrow.circle, plus.circle, plus.dot, plus.small, +, plus.square, plus.triangle \
  minus.tilde, tilde.eq, tilde.basic, tilde, tilde.rev, tilde.op, tilde.equiv \
$
