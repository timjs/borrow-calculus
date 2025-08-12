#import "typ/commands.typ": *
#import "typ/rules.typ": rules

#let identity = (dy: 0pt, it) => it
#let aside = identity
#let todo = identity
#let sidenote = identity
#let wideblock = identity


= Notation

== Metavariables

#stack(
  dir: ltr,
  spacing: 1fr,
  [],
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
  ),
  []
)

We write:\
  - $many(x, n)$ for an _ordered_ set of $x$es of length $n$, so $x_1, ..., x_n$.
  - $more(x)$ for an _unordered, possibly empty_ set of $x$es.
  - $most(x)$ for an _unordered, non-empty_ set of $x$es.
  - $maybe(x)$ for an _optional_ $x$.

= Syntax

// == Expressions

$
  grammar("Modules", m,
    more(d)\; e, "main"
  ) \
  grammar("Declarations", d,
    type(X, many(C^n (many(tau, n)), m)), "types",
  ) \
  grammar("Expressions", e,
    x, "variable",
    borrow(more(x), e), "borrow",
    lam(many(arg(x, q, tau), n), e_0), "abstraction",
    apply(e_0, many(e, n)), "application",
    tuple(many(e, n)), "tuple",
    val(q_0, tuple(many(x, n)), e_0, e), "split",
    variant(C, many(e, n)), "variant",
    match(q_0, e_0, many(variant(C, many(x, n)) -> e, m)), "match",
  ) \
  grammar("Values", v,
    cls(more(z), many(arg(x, q, tau), n), e_0), "abstraction",
    tuple(many(v, n)), "tuple",
    variant(C, many(v, n)), "variant",
  ) \
  grammar("Basic values", b,
    tuple(many(b, n)), "tuple",
    variant(C, many(b, n)), "variant",
  ) \
$
#aside[Note we have $b subset v subset e$]

// == Types

$
  grammar("Types", tau,
    phi, "arrow",
    tuple(many(tau, n)), "product",
    variants(many(variant(C, many(tau, n)), m)), "sum",
    List(tau), "list",
  ) \
  grammar("Function types", phi,
    Arrow(many(qt(q, tau), n), tau_0), "->",
  ) \
  grammar("Quantities", q,
    epsilon, "borrowed",
    1, "linear",
    omega, "unrestricted",
  ) \
$

== Shorthands

$
  shorthands(in,
    mu, {epsilon, omega}, "multiple",
    nu, {1, omega}, "owned",
    pi, {epsilon, 1}, "parameter",
  )
$

== Sugar

#wideblock[$
  shorthands(:=,
    fun(x_0, many(arg(x, q, tau), n), e_0, e), val(omega, x_0, lam(many(arg(x, q, tau), n), e_0), e), "function declaration",
    bind(x_0, apply(e_0, many(e, n)), e), apply(e_0, many(e, n)\, lam(arg(x_0, q, tau), e)), "with binding"
  )
$]

#todo(dy: 1)[About with-binding:
  - Should it be in an $epsilon$ context?
  - What is $q$?
  - How to get $tau$?
]

= Typing

The algorithmic typing rules of $lambda^"borrow"$ are given in between below text.
The typing relation
$
  framed(synthesize(Gamma^+, e^+, q^+, tau^-, Gamma^-))
$
can be read as
#quote[using expression $e$ with quantity $q$ can make use of all the bindings in context $Gamma$, which yields type $tau$ and a modified context $Gamma'$.]

== Variable lookup

Variable lookup comes in two flavours.
Linear bindings with quantity $1$ are looked up and removed from the context as shown in rule $"Var"_1$.
Borrowed and unrestricted bindings with quantities $epsilon$ and $omega$ respectively,
are looked up, but stay in the resulting context.
Rules $"Var"_mu$ define this for $mu in {epsilon, omega}$ simultaneously.
$
  rules.var.one \
  rules.var.mu \
$

We need a _weakening_ rule which states that unrestricted bindings can be used linearly.
Rules $"Var"_pi$ also state that unrestricted bindings can be borrowed freely.
#aside[
  Equivalently, we could define weakening as a general rule on bindings instead of a rule for variable lookup.
  However, this way our rule set would be nondeterministic.
  $
  grayed(rules.weak)
  $
]
$
  rules.var.pi
$

To allow linear bindings, that is bindings with quantity $1$, to be borrowed,
we need to do additional bookkeeping.
Borrows are only valid in a lexical region.
After this region ends, we restore the original quantity on the binding.
$
  rules.borrow.one
$
#todo[Add explanation why linear functions cannot be borrowed.]
Here, we need to take care borrowed bindings do not escape from this region.
Therefore, we _lift_ quantity $q$ of the expression surroundings to be an owned quantity.
That is, borrowed expression surroundings are lifted to unrestricted contexts,
the two owning quantities stay the same.
The definition of lifting is as follows.
$
  function(lift(dot) : "Quantity" -> "Quantity",
    lift(epsilon), omega,
    lift(q), q,
  )
$

// #aside[
  Alternatively, we could enforce explicit borrowing of unrestricted bindings, in the same way we do that for linear ones.
  We can change $"Borrow"_1$ to also include $omega$ bindings.
  Then, we need to alter $"Var"_pi$ to remove $epsilon$ as a free borrow.
  $
    grayed(rules.var.weak\ rules.borrow.nu)
  $
  This restricts the places where we can use explicit borrowing.
// ]
#todo[
  Is this good or bad? Could help in borrow inference: only there were linear variables are used...
]

== Functions

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
  rules.abs.epsilon.uncurried\
  rules.abs.one.uncurried\
  rules.abs.omega.uncurried\
$

For the bodies of the abstractions, there are two things to keep in mind.
First, we should not be allowed to return bindings that are borrowed, so the quantity context of the body should be owning and cannot be $epsilon$.
Second, the body _should not know_ how many times its result will be used.
Take for example the identity function
$
fun("identity", arg(x, 1, tau), x, "") quad
$
which by definition [X] itself is unrestricted
$
val(omega, "identity", lam(arg(x, 1, tau), x), "").
$
This does not mean the body of the abstraction should be checked in an $omega$ context.
We have binding $x$ linearly in the context, we can return it, as it is owned.
However, how the result will be used is a responsibility of the caller.
This means, it suffices to check the body of an abstraction in a linear context!

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
  rules.wilt.uncurried \
$
#todo[
  Is lowering really needed here?
  Calls can be just borrowed, that's probably enough.
  However, do we restrict or allow something when calls cannot be $omega$?
]

$
  function(lower(dot) : "Quantity" -> "Quantity",
    lower(omega), epsilon,
    lower(q), q,
  )
$

Problems arise when linear arguments are passed to functions.
Linear arguments are owned and could be returned by a function.
We need to make sure the returned value can also only be used once.
#block[
  The identity function simply returns its only parameter.
  The quantity of this parameter cannot be $epsilon$,
  as borrowed parameters cannot be returned from functions,
  so it should be owned.
  We could pick $omega$, but then we'd restrict ourselves because it cannot be used on linear arguments.
  Therefore, the sensible choice is to pick $1$.
  $
    fun("identity", arg(x, 1, tau), x, "")
  $

#[
  $val(1, a, 42,\
    val(omega, b, apply("identity", a),\
    tuple(b, b)
    ))$
]


  Variable $a$ is used by passing it to $"identity"$, the returned value $b$ however, is made available with quantity $omega$.
  Therefore, we are allowed to create a pair of two $b$'s and we've indirectly duplicated $a$...
]
There are two solutions:

1. Functions with linear parameters can only be called in a linear quantity context.
2. Functions with linear parameters, when called in an unrestricted quantity context, need their arguments to be unrestricted as well.

The first option would be a severe restriction, as many functions with linear parameters should be usable on unrestricted arguments, and the results would need to be used linearly.
The second option seems more logical.

$
  rules.app.pi.uncurried \
  rules.app.omega.uncurried \
$

$
  function(freeze(dot) : "Quantity" -> "Quantity",
    freeze(1), omega,
    freeze(q), q,
  )
$


== Datatypes

When creating datatypes, we need to store data so each subexpression in constructors needs to be owned.
Although we allow creating datatypes in borrowed expression surroundings,
we lift the surrounding quantity to make sure stored data is owned.
$
  rules.construct.uncurried \
$
Note the similarities and differences between rules $"Con"$ and $"App"$:
- Both "lookup" the type of the function or constructor,
  which directs the type of the arguments and the returntype of the application or construction.
- In application, the quantities of the arguments are directed by the function type,
  while in construction, these quantities are directed by the expression surroundings.

When destructuring datatypes, we have two quantities to take into account:
- The quantity in which the whole destructuring expression is going to be evaluated.
  We call this the _expression surrounding quantity_.
- The quantity of the resulting parts of the datatype, that are made available in continuation of the program.
  This is also the quantity that the scrutiny needs to be available for.
  To accommodate for this,
  we annotate destructuring constructs in our language with an addition quantity $q_0$.
$
  rules.match.uncurried
$

Because now we have multiple branches that can be taken, we need to _merge_ the resulting contexts of each branch and remove the freshly introduced bindings if still existing.
As after branching, contexts can only differ in removed linear bindings,
merging two contexts is simply set intersection.
#todo[Check this! Aren't we passing let-bound variables to the next argument?]

== Tuples

Tuples are _unboxed_, which means they don't allocate space on the heap and therefore do not store their components in the way datatypes do.
Therefore they their components can be borrowed.
$
  rules.pair.uncurried \
$
Due to this design decision, we can define value binding in terms of tuple creation and destruction.
#sidenote[
  Otherwise we would not be able to _reborrow_ a variable, that is, bind a borrowed variable to a new name.
  ```kotlin
  fun reborrow(ε x : a)
      val ε y = x
      ...
  ```
]
$
  shorthands(:=,
    val(q, x, e, c), val(q, (x), (e), c), "value binding",
  )
$

For the splitting of tuples, we ask an expression $e_0$ to be available for quantity $q_0$.
The resulting bindings $x_1$ and $x_2$ are then made available for the same quantity $q_0$ in the remaining part of the program.
Note we need to remove these bindings from the resulting context $Gamma_2$ if they still exist.
This is similar to the way we handle matching on datatypes.
$
  rules.split.uncurried
$

== Built-ins

Note that pre-defined functions, as well as any top-level functions, can be used unrestricted.
So their body is checked in a surrounding of quantity $omega$.
$
  shorthands(":",
    "fold"_q, ->(qt(q, List(tau_1)), qt(1, tau_2), qt(epsilon, ->(qt(q, tau_1), qt(1, tau_2), tau_2)), tau_2), "fold list",
  ) \
  shorthands(":",
    "Nil"_tau, List(tau), "nil list",
    "Cons", ->(tau, List(tau), List(tau)), "cons list",
  ) \
  shorthands(":=",
    "Bool", variants("False"(), "True"()), "boolean type",
    "Option"(tau), variants("None"(), "Some"(tau)), "option type",
    "Result"(tau_1, tau_2), variants("Wrong"(tau_1), "Right"(tau_2)), "either type",
  ) \
$

= Overview

#let varrules = $
  rules.var.one \
  rules.var.mu \
  rules.var.pi \
  \
  rules.borrow.one \
$
#let allrules(kind) = $
  rules.abs.epsilon.at(kind) \
  rules.abs.one.at(kind) \
  rules.abs.omega.at(kind) \
  \
  rules.app.pi.at(kind) \
  rules.app.omega.at(kind) \
  \
  // rules.bind.at(kind) \
  \
  rules.pair.at(kind) \
  rules.split.at(kind) \
  \
  rules.construct.at(kind) \
  rules.match.at(kind) \
$

== Variables

#wideblock[$
  varrules \
$]

== Uncurried

#wideblock[$
  allrules("uncurried")
$]

#pagebreak()
== Curried

#wideblock[$
  allrules("curried")
$]
