let equal = fun x, y ->
  case compare(x, y) of
    Equal{} -> True{};
    _       -> False{}
  end
end;

let and = fun x, y ->
  case x of
    False{} -> False{};
    _       -> y
  end
end;

let append = fun xs, @self, ys ->
  case xs of
    [x, ...xs] -> [x, ...self(xs, ys)];
    []         -> ys
  end
end;

let fold = fun f, z, @self, list ->
  case list of
    [x, ...xs] -> f(x, self(xs));
    []         -> z
  end
end;

let map = fun f, list ->
  fold(fun x, xs -> [f(x), ...xs] end, [], list)
end;


let car = fun list ->
  case list of
    Cons {x, xs} -> x
  end
end;

let swap1 = fun either ->
  case either of
    Left  {a} -> Right {a};
    Right {a} -> Left  {a}
  end
end;

let swap2 = fun pair ->
  case pair of
    Pair {a, b} -> Pair {b, a}
  end
end;

let decide = fun ok ->
  case ok of
    Ok{} -> 0;
    Ok{a} -> 1;
    Ok{a, b} -> 2
  end
end;

let one-vs-one = compare(1, 1);
let one-vs-two = compare(1, 2);
let one-vs-one = compare("1", "1");
let one-vs-two = compare("1", "2");
let pair-vs-pair = compare(Pair {1, 2}, Pair {1, 2});
let pair-vs-pair = compare(Pair {2, 2}, Pair {1, 2});
let pair-vs-pair = compare(Pair {1, 3}, Pair {1, 2});
let pair-vs-pair = compare(Pair {1, 2}, Pair {1, 5});
let ok-vs-err = compare(Ok {1, 2}, Err {"foo"});

let empty = Tip {};

let insert = fun k, v, @self, tree ->
  case tree of
    Tip {} -> Branch {k, v, Tip {}, Tip {}};
    Branch {k1, v1, l, r} ->
      case compare(k, k1) of
        Equal   {} -> Branch {k1, v, l, r};
        Less    {} -> Branch {k1, v1, self(l), r};
        Greater {} -> Branch {k1, v1, l, self(r)};
      end
  end
end;

let lookup = fun k, @self, tree ->
  case tree of
    Tip {} -> Nothing {};
    Branch {k1, v, l, r} ->
      case compare(k, k1) of
        Equal   {} -> Just {v};
        Less    {} -> self(l);
        Greater {} -> self(r);
      end;
  end
end;

let range = fun @self, x ->
  case x of
    0 -> Nil {};
    n -> Cons {x, self(minus(x, 1))}
  end
end;

let or = fun a, b ->
  case !a of
    True{} -> True{};
    False{} -> !b;
  end
end;

let if = fun b, y, n ->
  case b of
    True{} -> !y;
    False{} -> !n;
  end
end;

let tree = insert(2, "2", insert(1, "1", insert(3, "3", empty)));
let one   = lookup(1, tree);
let two   = lookup(2, tree);
let three = lookup(3, tree);
let four  = lookup(4, tree);

let test = fun a, @b, c, @d, e, @f, g -> 1 end;

Done {}
