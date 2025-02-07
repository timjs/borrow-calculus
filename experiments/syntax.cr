fn synthesize/go(g0: Context, e: Expression, q: Quantity) |Throw(Error)|-> #(Type, Context)
  case e
    Var(x1) ->
      case q
        Zero -> bug("variable asked with quantity zero")
        One ->
          case g0.lookup(x1)
            Some(#(One, t)) -> #(t, g0.set(Zero, x1))
            Some(#(Omega, t)) -> #(t, g0)
            Some(#(q, _)) -> throw(VarMismatch(One, q, x1))
            None -> throw(VarDoesntExist(x1))
        Epsilon ->
          case g0.lookup(x1)
            Some(#(Epsilon, t)) -> #(t, g0)
            Some(#(Omega, t)) -> #(t, g0)
            Some(#(q, _)) -> throw(VarMismatch(Epsilon, q, x1))
            None -> throw(VarDoesntExist(x1))
        Omega ->
          case g0.lookup(x1)
            Some(#(Omega, t)) -> #(t, g0)
            Some(#(q, _)) -> throw(VarMismatch(Omega, q, x1))
            None -> throw(VarDoesntExist(x1))

    Borrow(x1, e0) ->
      case g0.borrow(x1)
        Some(#(q1, g_)) ->
          let #(t, g__) = synthesize/go(g_, e0, own(q))
          #(t, g__.set(q1, x1))
        None -> throw(VarDoesntExist(x1))

    Abstract(ps, e) ->
      let vs = e.freeVars()
      let c = vs.map(|v| g0.lookup!(v)).any(at1 >> isLinear)
      case c && q != One
        True -> throw(AbstractionError(vs))
        False ->
          let #(g0e, g0n) = g0.split
          let g0n_ = g0n.insert(x1, #(q1, t1))
          let #(t0, g1) = synthesize/go(g0n_, e0, own(q))
          #(Arrow(t1, q1, t0), g0e.merge(g1 \\ x1))

    Apply(e0, es) ->
      case synthesize/go(g0, e0, borrow(q))
        #(Arrow(t1, q1, t0), g1) ->
          let #(t1_, g2) = synthesize/go(g1, e1, q1)
          case t1 == t1_
            True -> #(t0, g2)
            False -> throw(ArgMismatch(t1, t1_))
        #(t_, _) -> throw(FunNeeded(t_))

    Nat(_) -> #(Type/Nat, g0)

    Operate(_, e1, e2) -> synthesize/primitive(Type/Nat, g0, e1, e2, q)

    Compare(_, e1, e2) -> synthesize/primitive(Type/Bool, g0, e1, e2, q)

    Pair(es) ->
      let #(t1, g1) = synthesize/go(g0, e1, own(q))
      let #(t2, g2) = synthesize/go(g1, e2, own(q))
      #(Product(t1, t2), g2)

    Split(q0, xs, e0, e) ->
      case synthesize/go(g0, e0, q0)
        #(Product(ts), g1) ->
          let g1_ = g1.extend(q0, xs, ts)
          synthesize/go(g1_, e, q)
        #(t_, _) -> throw(SplitMismatch(t_))

    Construct(c1, t2, e) ->
      let #(t1, g1) = synthesize/go(g0, e, own(q))
      #(Type/Sum(c1, t1, t2), g1)

    Match(q0, e0, #(x1, e1), #(x2, e2)) ->
      case synthesize/go(g0, e0, q0)
        #(Sum(t1, t2), g_) ->
          let #(t1_, g1_) = synthesize/go(g_.insert(x1, #(q0, t1)), e1, q)
          let #(t2_, g2_) = synthesize/go(g_.insert(x2, #(q0, t2)), e2, q)
          case t1_ == t2_
            True -> #(t1_, g1_.merge(g2_))
            False -> throw(BranchMismatch(t1_, t2_))
        #(t_, _) -> throw(MatchMismatch(t_))

    Nil(t0) -> #(List(t0), g0)

    Cons(e1, e2) ->
      let #(t1, g_) = synthesize/go(g0, e1, q)
      case synthesize/go(g_, e2, q)
        #(List(t1_), g__) ->
          case t1 == t1_
            True -> #(List(t1), g__)
            False -> throw(ConsMismatch(t1, t1_))
        #(t1_, _) -> throw(ListNeeded(e2, t1_))

    Fold(q1, e1, e2, (x1, x2, e3)) ->
      case synthesize/go(g0, e1, q1)
        #(List(t1), g_) ->
          let #(t2, g__) = synthesize/go(g_, e2, One)
          let #(t2_, g___) = synthesize/go(g__.insert(x1, #(q1, t1)).insert(x2, #(One, t2)), e3, One)
          case t2 == t2_
            True -> #(t2, g___)
            False -> throw(FoldMismatch(t2, t2_))
        #(t1, _) -> throw(ListNeeded(e1, t1))

    Evaluated(_) -> bug("There shouldn't be an evaluated value in this expression")
