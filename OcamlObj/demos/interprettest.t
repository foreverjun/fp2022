(** Copyright 2021-2022, Kalashnikov Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

  $ ./interprettest.exe <<-EOF
  >  let rec fix f x = f (fix f) x
  >  ;;
  >  let factorial x n = if n <= 1 then n else x (n - 1) * n
  >  ;;
  >  let f = fix factorial 5 ;;
  val fix = <fun>
  val factorial = <fun>
  val f = 120
  =-------------------------------------------=
  $ ./interprettest.exe <<-EOF
  >  let o = object (self)
  >    method fix f x = f (self#fix f) x
  >    method factorial f n = if n <= 1 then n else f (n - 1) * n
  >  end;;
  >  let fac n = o#fix o#factorial n;;
  >  let f = fac 5;;

  $ ./interprettest.exe <<-EOF
  >   let pair first1 second1 = object
  >      val first = first1
  >      val second = second1
  >      method get_first = first
  >      method get_second = second
  >   end ;;
  >   let mypair = pair 1 2 ;;
  >   let first = mypair#get_first ;;
  >   let second = mypair#get_second ;;
  >   let sum = mypair#get_first + mypair#get_second ;;
  val pair = <fun>
  val mypair = <object>
  val first = 1
  val second = 2
  val sum = 3
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let inner_objects = object
  >      val i = 10
  >      method g = object
  >      method h = i + 10
  >      end
  >   method f = object
  >      val k = 30
  >      method g = object
  >         val l = 40
  >         method h = k + l
  >         end
  >      end
  >   end
  >   ;;
  >   let a = inner_objects#f#g#h
  val inner_objects = <object>
  val a = 70
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >  let sq y = y * y ;;
  >  let z = sq 5 ;;
  val sq = <fun>
  val z = 25
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let rec fib n =
  >   if n = 0 then 0
  >   else if n = 1 then 1
  >   else fib (n-1) + fib (n-2);;
  >   let x = fib 20 ;;
  val fib = <fun>
  val x = 6765
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  > let simple_match my_int = match  my_int with
  > | 1 -> 1 + 1
  > | 2 -> 2 * 2
  > | 3 -> (3 + 3) * 3
  > | 4 -> (8 - 4) * 4 + 4
  > | 5 -> ((5 * 5) + 5) / 5
  > | other -> other * other * other
  > ;;
  > let test1 = simple_match 1 ;;
  > let test2 = simple_match 2 ;;
  > let test3 = simple_match 3 ;;
  > let test4 = simple_match 4 ;;
  > let test5 = simple_match 5 ;;
  > let test6 = simple_match 8 ;;
  val simple_match = <fun>
  val test1 = 2
  val test2 = 4
  val test3 = 18
  val test4 = 20
  val test5 = 6
  val test6 = 512
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  > let deviding = 5 / 0
  Div_0
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  > let a =
  >    let b =
  >      let c =
  >        let d x = x * 3
  >      in d
  >    in c
  >   in fun x -> b (x + 2) ;;
  > let t = a 5 ;;
  val a = <fun>
  val t = 21
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let new_triplet one two three = object
  >      method get_one = one
  >      method get_two = two
  >      method get_three = three
  >      method get_sum = get_one + get_two + get_three
  >   end ;;
  >   let triplet = new_triplet 1 2 3 ;;
  >   let sum = triplet#get_sum ;;
  (Not_bound "get_one")
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let new_triplet one two three = object (test_this)
  >      method get_one = one
  >      method get_two = two
  >      method get_three = three
  >      method get_sum = test_this#get_one + test_this#get_two + test_this#get_three
  >   end ;;
  >   let triplet = new_triplet 1 2 3 ;;
  >   let sum = triplet#get_sum ;;
  val new_triplet = <fun>
  val triplet = <object>
  val sum = 6
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let new_triplet one two three = object (self)
  >      method get_one = one
  >      method get_two = two
  >      method get_three = three
  >      method get_sum = self#get_one + self#get_two + self#get_three
  >   end ;;
  >   let triplet = new_triplet 1 2 3 ;;
  >   let sum = triplet#get_sum ;;
  val new_triplet = <fun>
  val triplet = <object>
  val sum = 6
  =-------------------------------------------=

  $ ./interprettest.exe <<-EOF
  >   let make f = object (self)
  >      method fac = fun x -> f (self#fac) (0+x)
  >   end ;;
  >   let o  = make (fun self n -> n);;
  >   let rez = o#fac 3 ;;
