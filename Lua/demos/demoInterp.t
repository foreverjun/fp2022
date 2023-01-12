  $ ./demoInterp.exe <<-EOF
  > function f(x)
  >   if x >= 1 then return f(x - 1) * x end
  >   return 1
  > end
  > print("Factorial")
  > for i = 1, 10 do
  >   print(f(i))
  > end
  > EOF
  Factorial
  1.
  2.
  6.
  24.
  120.
  720.
  5040.
  40320.
  362880.
  3628800.
  $ ./demoInterp.exe <<-EOF
  > f = function(x)
  >   if x < 2 then
  >     return 1
  >   else
  >     return f(x - 2) + f(x - 1)
  >   end
  > end
  > 
  > print()
  > print("Fibonacci")
  > for i = 1, 10 do
  >   print(f(i))
  > end
  > EOF
  Fibonacci
  1.
  2.
  3.
  5.
  8.
  13.
  21.
  34.
  55.
  89.
  $ ./demoInterp.exe <<-EOF
  > print("Arithmetics and precedence")
  > print(1 + 2 * 3)
  > print(1 * 2 + 3)
  > print(3 + 4 * 9 - 2 ^ 4 * 3)
  > print(3 - 1 - 1)
  > EOF
  Arithmetics and precedence
  7.
  5.
  -9.
  1.
