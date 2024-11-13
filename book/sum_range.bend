#type List(t):
  #Cons { head: t, tail: List(t) }
  #Nil

def sum(xs, r):
  match xs:
    case List/Cons:
      return sum(xs.tail, xs.head + r)
    case List/Nil:
      return r

def range(n, xs):
  switch n:
    case 0:
      return xs
    case _:
      return range(n-1, List/Cons { head: n-1, tail: xs })

def main() -> u64:
  return sum(range(5_000_000, List/Nil), 0)
