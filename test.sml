let append = fix self ->
  fun xs, ys ->
    case xs {
      [x, ...xs] -> [x, ...self(xs, ys)];
      []         -> ys
    }
  end
end;

let fold = fun f, z, list ->
  let inner = fix self -> fun list ->
    case list {
      [x, ...xs] -> f(x, self(xs));
      []         -> z
    }
  end end;
  inner(list)
end;

let map = fun f, list ->
  fold(fun x, xs -> [f(x), ...xs] end, [], list)
end;


let car = fun list ->
  case list {
    Cons(x, xs) -> x
  }
end;

let swap1 = fun either ->
  case either {
    Left(a) -> Right(a);
    Right(a) -> Left(a)
  }
end;

let swap2 = fun pair ->
  case pair {
    Pair(a, b) -> Pair(b, a)
  }
end;

map(fun x -> add(4, x) end, [1,2,3])
