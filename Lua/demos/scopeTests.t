  $ ./demoInterp.exe <<-EOF
  > a = 4
  > 
  > function b()
  >   a = 3
  >   local a = 5
  >   print("local:")
  >   print(a)
  > end
  > 
  > print()
  > print("Global/local")
  > print("global:")
  > print(a)
  > b()
  > print("global after change:")
  > print(a)
  > EOF
  Global/local
  global:
  4.
  local:
  5.
  global after change:
  3.
  $ ./demoInterp.exe <<-EOF
  > a = 1
  > 
  > print("Lots of blocks")
  > do
  >   local a = 41
  >   do
  >     local a = 441
  >     do
  >       local a = 4441
  >       print(a)
  >     end
  >     print(a)
  >   end
  >   print(a)
  > end
  > print(a)
  Lots of blocks
  4441.
  441.
  41.
  1.
  $ ./demoInterp.exe <<-EOF
  > a = 1
  > i = 0
  > b = 9
  > print("Scopes and loops")
  > for i = 1, 200 do
  >   if i > 197 then
  >     print(i)
  >   end
  > end
  > print(i)
  > while a < 49 do
  >   a = a + 1
  >   local b = 99999
  > end
  > print(a)
  > print(b)
  > repeat 
  > i = i + 10
  > until i < 100
  > print(i) 
  Scopes and loops
  198.
  199.
  200.
  0.
  49.
  9.
  100.
  $ ./demoInterp.exe <<-EOF
  > a = 1
  > b = 2
  > print("Function local")
  > function f(x)
  >   local a = x
  >   local b = x
  >   return a
  > end
  > print(f(b))
  > print(a)
  Function local
  2.
  1.
  $ ./demoInterp.exe <<-EOF
  > a = 1
  > b = 2
  > print("Function in function local")
  > function f(x)
  >   local a = x
  >   local b = x
  >   function f_inner(x)
  >     local a = x + 1
  >     print(a)
  >   end
  >   f_inner(a)
  >   return a
  > end
  > print(f(b))
  > print(a)
  Function in function local
  3.
  2.
  1.
