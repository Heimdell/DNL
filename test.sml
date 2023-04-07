let append = fix self ->
  fun xs, ys ->
    case xs of
      [x, ...xs] -> [x, ...self(xs, ys)];
      []         -> ys
    end
  end
end;

let fold = fun f, z, list ->
  let inner = fix self ->
    fun list ->
      case list of
        [x, ...xs] -> f(x, self(xs));
        []         -> z
      end
    end
  end;
  inner(list)
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

let insert = fun k, v, tree ->
  let inner = fix self ->
    fun tree ->
      case tree of
        Tip {} -> Branch {k, v, Tip {}, Tip {}};
        Branch {k1, v1, l, r} ->
          case compare(k, k1) of
            Equal   {} -> Branch {k1, v, l, r};
            Less    {} -> Branch {k1, v, self(l), r};
            Greater {} -> Branch {k1, v1, l, self(r)};
          end
      end
    end
  end;

  inner(tree)
end;

let tree = insert(2, "2", insert(1, "1", insert(3, "3", empty)));

Done {}
