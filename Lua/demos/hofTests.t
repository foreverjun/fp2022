  $ ./demoInterp.exe <<-EOF
  > function map(lst, f)
  >   local i = 1
  >   while lst[i] do
  >     lst[i] = f(lst[i])
  >     i = i + 1
  >   end
  >   return lst
  > end
  > 
  > l = {2, 4, 6, 8, 10, 12, 14, 17}
  > f_ = function(x) return x ^ 2 end
  > l1 = map(l, f_)
  > 
  > print("Map function")
  > for i = 1, 8 do
  >   print(l1[i])
  > end
  > EOF
  Map function
  4.
  16.
  36.
  64.
  100.
  144.
  196.
  289.
  $ ./demoInterp.exe <<-EOF
  > function filter(lst, f)
  >   local i = 1
  >   local res = {}
  >   local r_i = 1
  >   while lst[i] do
  >     if f(lst[i]) then
  >       res[r_i] = lst[i]
  >       r_i = r_i + 1
  >     end
  >     i = i + 1
  >   end
  >   return res
  > end
  > 
  > l = {9, 4, 13, 8, 1, 12, 14, 17}
  > f_ = function(x) return (x > 8) end
  > l1 = filter(l, f_)
  > 
  > print("Filter")
  > for i = 1, 8 do
  >   print(l1[i])
  > end
  > EOF
  Filter
  9.
  13.
  12.
  14.
  17.
  nil
  nil
  nil
  $ ./demoInterp.exe <<-EOF
  > function printdouble(x)
  >   print(x * 2)
  > end
  > 
  > function square(x, k) 
  >   k(x * x)
  > end
  > 
  > print("square print double")
  > square(20, printdouble)
  > EOF
  square print double
  800.
