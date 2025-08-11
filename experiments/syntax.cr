synthesize : (Context, Expression, Quantity) | Throw(Error) -> {Type, Context}
synthesize(g0, e, q) =
  match e
    Var(x1) ->
      match q
        Zero -> bug "variable asked with quantity zero"
        One ->
          match g0.lookup(x1)
            Some({One, t}) -> {t, g0.set(Zero, x1)}
            Some({Omega, t}) -> {t, g0}
            Some({q, _}) -> throw VarMismatch(One, q, x1)
            None -> throw VarDoesntExist(x1)
        Epsilon ->
          match g0.lookup(x1)
            Some({Epsilon, t}) -> {t, g0}
            Some({Omega, t}) -> {t, g0}
            Some({q, _}) -> throw VarMismatch(Epsilon, q, x1)
            None -> throw VarDoesntExist(x1)
        Omega ->
          match g0.lookup(x1)
            Some({Omega, t}) -> {t, g0}
            Some({q, _}) -> throw VarMismatch(Omega, q, x1)
            None -> throw VarDoesntExist(x1)

    Borrow(x1, e0) ->
      with {q1, g_} <- g0.borrow(x1).or_else do throw VarDoesntExist(x1)
      {t, g__} = g_.synthesize(e0, own(q))
      {t, g__.set(q1, x1)}

    Abstract(ps, e) ->
      vs = e.freeVars()
      c = vs.map(g0.lookup!(_)).any(at1 >> isLinear)
      when
        c && q != One -> throw AbstractionError(vs)
        otherwise ->
          {g0e, g0n} = g0.split
          g0n_ = g0n.insert(x1, {q1, t1})
          {t0, g1} = g0n_.synthesize(e0, own(q))
          {Arrow(t1, q1, t0), g0e.merge(g1 \\ x1)}

    Apply(e0, es) ->
      match g0.synthesize(e0, borrow(q))
        {Arrow(t1, q1, t0), g1} ->
          {t1_, g2} = g1.synthesize(e1, q1)
          when
            t1 == t1_ -> {t0, g2}
            otherwise -> throw ArgMismatch(t1, t1_)
        {t_, _} -> throw FunNeeded(t_)

    Nat(_) -> {Type/Nat, g0}

    Operate(_, e1, e2) -> synthesize/primitive(Type/Nat, g0, e1, e2, q)

    Compare(_, e1, e2) -> synthesize/primitive(Type/Bool, g0, e1, e2, q)

    Pair(es) ->
      {t1, g1} = g0.synthesize(e1, own(q))
      {t2, g2} = g1.synthesize(e2, own(q))
      {Product(t1, t2), g2}

    Split(q0, xs, e0, e) ->
      match g0.synthesize(e0, q0)
        {Product(ts), g1} ->
          g1_ = g1.extend(q0, xs, ts)
          g1_.synthesize(e, q)
        {t_, _} -> throw SplitMismatch(t_)

    Construct(c1, t2, e) ->
      {t1, g1} = g0.synthesize(e, own(q))
      {Type/Sum(c1, t1, t2), g1}

    Match(q0, e0, {x1, e1}, {x2, e2}) ->
      match g0.synthesize(e0, q0)
        {Sum(t1, t2), g_} ->
          {t1_, g1_} = g_.x1.insert({q0, t1}).synthesize(e1, q)
          {t2_, g2_} = g_.x2.insert({q0, t2}).synthesize(e2, q)
          when
            t1_ == t2_ -> {t1_, g1_.merge(g2_)}
            otherwise -> throw BranchMismatch(t1_, t2_)
        {t_, _} -> throw MatchMismatch(t_)

    Nil(t0) -> {List(t0), g0}

    Cons(e1, e2) ->
      {t1, g_} = g0.synthesize(e1, q)
      match g_.synthesize(e2, q)
        {List(t1_), g__} ->
          when
            t1 == t1_ -> {List(t1), g__}
            otherwise -> throw ConsMismatch(t1, t1_)
        {t1_, _} -> throw ListNeeded(e2, t1_)

    Fold(q1, e1, e2, {x1, x2, e3}) ->
      match g0.synthesize(e1, q1)
        {List(t1), g_} ->
          {t2, g__} = g_.synthesize(e2, One)
          {t2_, g___} = g__.insert(x1, {q1, t1}).insert(x2, {One, t2}).synthesize(e3, One)
          when
            t2 == t2_ -> {t2, g___}
            otherwise -> throw FoldMismatch(t2, t2_)
        {t1, _} -> throw ListNeeded(e1, t1)

    Evaluated(_) -> bug "There shouldn't be an evaluated value in this expression"
