#import "commands.typ": rule, synthesize, with, more, owned, borrow, tuple, each, many, merge
#import "commands.typ": fun, arg, qt, arrow, lookup, variant, apply, bind, match, lam

#let rules = (

  var: (
    one: $
      rule("Var"_1,
        space,
        synthesize(Gamma with arg(x, 1, tau), x, 1, tau, Gamma),
      )
    $,
    mu: $
      rule("Var"_mu,
        space,
        synthesize(Gamma with arg(x, mu, tau), x, mu, tau, Gamma with arg(x, mu, tau)),
        condition: mu in {epsilon, omega}
      )
    $,
    pi: $
      rule("Var"_pi,
        space,
        synthesize(Gamma with arg(x, omega, tau) , x, pi, tau, Gamma with arg(x, omega, tau)),
        condition: pi in {1, epsilon}
        )
      $,
     weak: $
      rule("Var"_"weak",
        space,
        synthesize(Gamma with arg(x, omega, tau) , x, 1, tau, Gamma with arg(x, omega, tau)),
      )
    $,
  ),

  weak: $
    rule("Weak",
      synthesize(Gamma, x, omega, tau, Gamma),
      synthesize(Gamma, x, 1, tau, Gamma),
    )
  $,

  borrow: (
    nu: $
      rule("Borrow"_nu,
        synthesize(Gamma_0 with more(arg(x, epsilon, tau) ), e, owned(q), tau, Gamma_1 with more(arg(x, epsilon, tau))),
        synthesize(Gamma_0 with more(arg(x, nu, tau)), borrow(more(x), e), q, tau, Gamma_1 with more(arg(x, nu, tau))),
        condition: nu in {1, omega}
      )
    $,
    one: $
      rule("Borrow"_1,
        synthesize(Gamma_0 with more(arg(x, epsilon, tau) ), e, owned(q), tau, Gamma_1 with more(arg(x, epsilon, tau))),
        synthesize(Gamma_0 with more(arg(x, 1, tau)), borrow(more(x), e), q, tau, Gamma_1 with more(arg(x, 1, tau))),
      )
    $,
  ),

  // rule("Abs",
  //   synthesize(Gamma_0^nu with many(arg(x, q, tau), n), e_0, owned(q), tau_0, Gamma_1),
  //   synthesize(Gamma_0^epsilon with Gamma_0^nu, lam(many(arg(x, q, tau), n), e_0), q, //     arrow(many(tau^q, n), tau_0), Gamma_0^epsilon with Gamma_1 without many(x, n)),
  // )\

  abs: (
    epsilon: (
      curried: $
        rule("Abs"_epsilon,
          synthesize(Gamma_0^epsilon with Gamma_0^omega with arg(x_1, q_1, tau_1), e_0, omega, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(arg(x_1, q_1, tau_1), e_0), epsilon, arrow(qt(q_1, tau_1), tau_0), Gamma_0^1 with Gamma_1 without x),
        )
      $,
      uncurried: $
        rule("Abs"_epsilon,
          synthesize(Gamma_0^epsilon with Gamma_0^omega with many(arg(x, q, tau), n), e_0, omega, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(many(arg(x, q, tau), n), e_0), epsilon, arrow(many(qt(q, tau), n), tau_0), Gamma_0^1 with Gamma_1 without x),
        )
      $,
    ),
    one: (
      curried: $
        rule("Abs"_1,
          synthesize(Gamma_0^1 with Gamma_0^omega with arg(x_1, q_1, tau_1), e_0, 1, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(arg(x_1, q_1, tau_1), e_0), 1, arrow(qt(q_1, tau_1), tau_0), Gamma_0^epsilon with Gamma_1 without x),
        )
      $,
      uncurried: $
        rule("Abs"_1,
          synthesize(Gamma_0^1 with Gamma_0^omega with many(arg(x, q, tau), n), e_0, 1, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(many(arg(x, q, tau), n), e_0), 1, arrow(many(qt(q, tau), n), tau_0), Gamma_0^epsilon with Gamma_1 without x),
        )
      $,
    ),
    omega: (
      curried: $
        rule("Abs"_omega,
          synthesize(Gamma_0^omega with arg(x_1, q_1, tau_1), e_0, omega, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(arg(x_1, q_1, tau_1), e_0), omega, arrow(qt(q_1, tau_1), tau_0), Gamma_0^epsilon with Gamma_0^1 with Gamma_1 without x),
        )
      $,
      uncurried: $
        rule("Abs"_omega,
          synthesize(Gamma_0^omega with many(arg(x, q, tau), n), e_0, omega, tau_0, Gamma_1),
          synthesize(Gamma_0, lam(many(arg(x, q, tau), n), e_0), omega, arrow(many(qt(q, tau), n), tau_0), Gamma_0^epsilon with Gamma_0^1 with Gamma_1 without x),
        )
      $,
    ),
  ),

  app: (
    curried: $
      rule("App",
        synthesize(Gamma_0, e_0, q, arrow(qt(q_1, tau_1), tau_0), Gamma_1),
        synthesize(Gamma_1, e_1, q_1, tau_1, Gamma_2),
        synthesize(Gamma_0, apply(e_0, e_1), q, tau_0, Gamma_2),
      )
    $,
    uncurried: $
      rule("App",
        synthesize(Gamma_0, e_0, q, arrow(many(qt(q, tau), n), tau_0), Gamma_1),
        each(i in 1..n),
        synthesize(Gamma_i, e_i, q_i, tau_i, Gamma_(i+1)),
        synthesize(Gamma_0, apply(e_0, many(e, n)), q, tau_0, Gamma_(n+1)),
      )
    $,
  ),

  pair: (
    curried: $
      rule("Pair",
        synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
        synthesize(Gamma_2, e_2, owned(q), tau_2, Gamma_3),
        synthesize(Gamma_1, tuple(e_1, e_2), q, tuple(tau_1, tau_2), Gamma_3),
      )\
    $,
    uncurried: $
      rule("Pair",
        each(i in 1..n),
        synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
        synthesize(Gamma_1, tuple(many(e, n)), q, tuple(many(tau, n)), Gamma_(n+1)),
      )
    $,
  ),
  bind: (
    curried: $
      rule("Let",
        synthesize(Gamma_0, e_0, q_0, tuple(tau_1, tau_2), Gamma_1),
        synthesize(Gamma_1 with arg(x_1, q_0, tau_1) with arg(x_2, q_0, tau_2), e, q, tau, Gamma_2),
        synthesize(Gamma_0, bind(q_0, tuple(x_1, x_2), e_0, e), q, tau, Gamma_2 without x_1 without x_2),
      )
    $,
    uncurried: $
      rule("Let",
        synthesize(Gamma_0, e_0, q_0, tuple(many(tau, n)), Gamma_1),
        synthesize(Gamma_1 with many(arg(x, q_0, tau), n), e, q, tau, Gamma_2),
        synthesize(Gamma_0, bind(q_0, tuple(many(x, n)), e_0, e), q, tau, Gamma_2 without many(x, n)),
      )
    $,
  ),

  con: (
    curried: $
      rule("Con",
        lookup(Delta, C, arrow(tau_1, tau_0)),
        synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
        synthesize(Gamma_1, variant(C, e_1), q, tau_0, Gamma_2),
      )
    $,
    uncurried: $
      rule("Con",
        lookup(Delta, C, arrow(many(tau, n), tau_0)),
        each(i in 1..n),
        synthesize(Gamma_i, e_i, owned(q), tau_i, Gamma_(i+1)),
        synthesize(Gamma_1, variant(C, many(e, n)), q, tau_0, Gamma_(n+1)),
      )
    $,
 ),
  match: (
    curried: $
      rule("Match",
        synthesize(Gamma_0, e_0, q_0, tau_0, Gamma'_0),
        each(i in 1..2),
        lookup(Delta, C_i, arrow(tau_i, tau_0)),
        synthesize(Gamma'_0 with arg(x_i, q_0, tau_i), e_i, q, tau, Gamma_i),
        synthesize(Gamma_0, match(q_0, e_0, many(variant(C, x) |-> e, 2)), q, tau, Gamma_1 without x_1 merge Gamma_2 without x_2),
      )
    $,
    uncurried: $
      rule("Match",
        synthesize(Gamma_0, e_0, q_0, tau_0, Gamma'_0),
        each(i in 1..m),
        lookup(Delta, C_i, arrow(many(tau, n_i), tau_0)),
        synthesize(Gamma'_0 with many(arg(x, q_0, tau), n_i), e_i, q, tau, Gamma_i),
        synthesize(Gamma_0, match(q_0, e_0, many(variant(C, many(x, n)) |-> e, m)), q, tau, sect.double_(i in 1..m) Gamma_i),
      )
    $,
  ),

)



  // rule("Inl",
  //   synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
  //   synthesize(Gamma_1, variant("Inl", e_1), q, variants(tau_1, tau_2), Gamma_2),
  // ) quad
  // rule("Inr",
  //   synthesize(Gamma_1, e_1, owned(q), tau_1, Gamma_2),
  //   synthesize(Gamma_1, variant("Inr", e_1), q, variants(tau_2, tau_1), Gamma_2),
  // )\
  // rule("Des",
  //   synthesize(Gamma_0, e_0, q_0, variants(many(tau_i, 2)), Gamma'_0),
  //   each(i in 1..2),
  //   synthesize(Gamma'_0 with arg(x_i, q_0, tau_i), e_i, q, tau, Gamma_i),
  //   synthesize(Gamma_0, match(q_0, e_0, many(variant(C, x) |-> e, 2)), q, tau, Gamma_1 without x_1 merge Gamma_2 without x_2),
  // )
