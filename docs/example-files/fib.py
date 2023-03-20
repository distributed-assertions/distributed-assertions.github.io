def unary(n):
  ret = 'z'
  for _ in range(n): ret = f'(s { ret })'
  return ret

def doit(n, outfile):
  with open(outfile, 'w') as f:
    for i in range(1, n):
      un = unary(i)
      print(f'name "sq{ i }" (times { un } { un } X).', file=f)
    for i in range(1, n):
      un = unary(i)
      print(f'name "fib{ i }" (fib { un } X).', file = f)
