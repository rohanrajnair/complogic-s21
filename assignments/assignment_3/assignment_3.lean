import .....inClassNotes.type_library.list
import .....inClassNotes.type_library.box
import .....inClassNotes.type_library.option

/-
HIGHER-ORDER FUNCTION WARMUP
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:
- double 0 = 0
- double (n' + 1) = double n' + 2
-/


-- ANSWER HERE
def double : ℕ → ℕ
| 0 := 0
| (n' + 1) := double n' + 2

#reduce double 10
#reduce double 125

/-
2. Write a function, map_list_nat, that 
takes as its arguments (1) a list, l, of 
natural numbers, and (2) a function, f, 
from nat to nat, and that returns a new 
list of natural numbers constructed by 
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.
-/

-- ANSWER HERE

/-
inductive list (α : Type u) : Type u
| nil {} : list
| cons (h : α) (t : list) : lis
-/

def map_list_nat : list ℕ → (ℕ → ℕ) → list ℕ
| list.nil f := list.nil
| (h::t) f := list.cons (f h) (map_list_nat t f)


/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/
def l1 : list ℕ := 1::2::3::(list.nil)
def l2 : list ℕ := list.nil 
def l3 : list ℕ := list.cons (2) (list.nil)

#eval map_list_nat l1 double -- [2, 4, 6]
#eval map_list_nat l2 double -- []
#eval map_list_nat l3 double -- [4]

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see 
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so 
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/

#eval repr 5

/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

-- ANSWER HERE
def map_list_nat_string : list ℕ → list string
| list.nil := list.nil
| (h::t) := list.cons (repr h) (map_list_nat_string t)

#eval map_list_nat_string l1 -- ["1", "2", "3"]
#eval map_list_nat_string l2 -- []
#eval map_list_nat_string l3 -- ["2"]

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it 
should return [1,2,3,4,5].
-/

-- ANSWER HERE
def filterZeros : list ℕ → list ℕ
| list.nil := list.nil
| (0::t) := filterZeros t
| (h::t) := list.cons (h) (filterZeros t)

def l4 : list ℕ := 1::2::0::3::4::0::0::5::(list.nil)
def l5 : list ℕ := 0::list.nil 
def l6 : list ℕ := list.nil 

#eval filterZeros l4 -- [1,2,3,4,5]
#eval filterZeros l5 -- []
#eval filterZeros l6 -- []

/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

-- ANSWER HERE

def isEqn : ℕ → ℕ → bool 
| 0 0 := tt 
| 0 _ := ff
| _ 0 := ff
| (m+1) (n+1) := isEqn m n

#eval isEqn 25 25 -- tt
#eval isEqn 20 24 -- ff 
#eval isEqn 0 14 -- ff 
#eval isEqn 10 2 -- ff
#eval isEqn 12 12 -- tt 

/-
7.
Write a function filterNs that takes
a function, pred, from nat to bool 
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

-- ANSWER HERE

def isEqn10 (n : ℕ) : bool := 
isEqn n 10 

def filterNs : list ℕ → (ℕ → bool) → list ℕ 
| list.nil _ := list.nil
| (h::t) f := if f h then filterNs t f else list.cons (h) (filterNs t f)

def l7 : list ℕ := 10::20::10::30::40::(list.nil)

#eval filterNs l2 isEqn10 -- [] 
#eval filterNs l7 isEqn10 -- [20, 30, 40]

/-
8. Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and 
recursion. Test your function using 
nat.succ, your double function, and
(nat.add 4) as function arguments. 
-/

-- ANSWER HERE

-- def iterate : Π(f : ℕ → ℕ) (n : ℕ), (ℕ → ℕ) 
-- | f 0 := f
-- | f (n+1) := iterate f (f n)


-- def add3 : ℕ → ℕ := iterate nat.succ 1

-- #reduce add3 3

/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

-- ANSWER HERE

def list_add : (list ℕ) → ℕ
| list.nil := 0
| (h::t) := h + list_add t

#eval list_add l1 -- 6
#eval list_add l2 -- 0
#eval list_add l3 -- 2
#eval list_add l4 -- 15


/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

-- ANSWER HERE

def mul_list : list ℕ := 4::3::2::1::4::list.nil

def list_mul : (list ℕ) → ℕ
| list.nil := 0
| (h::list.nil) := h
| (h::t) := h * list_mul t

#eval list_mul mul_list -- 96
#eval list_mul l1 -- 6
#eval list_mul l2 -- 0
#eval list_mul l3 -- 2

/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

-- ANSWER HERE

def list_has_zero : (list ℕ) → bool
| list.nil := ff
| (h::t) := if (isEqn h 0) then tt else list_has_zero t

def l0 : list ℕ := 1::3::23::0::4::(list.nil)

#eval list_has_zero l0 -- tt
#eval list_has_zero l1 -- ff
#eval list_has_zero l2 -- ff

/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function 
using at least nat.succ and double as
argument values.
-/

-- ANSWER HERE

def compose_nat_nat : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ := 
λ f,
  λ g,
    λ n,
      g (f n)

#eval compose_nat_nat nat.succ double 4 -- 10 
#eval compose_nat_nat double nat.succ 4 -- 9 

/-
13. Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  
-/

-- ANSWER HERE
namespace hidden 

universe u

def map_box : Π{α β : Type u}, (α → β) → box α → box β :=
  λ a, 
    λ b,
      λ f,
        λ a, 
          box.mk (f a.val)

def aBox : box ℕ := box.mk(3)

#reduce map_box double aBox -- {val := 6}
#reduce map_box nat.succ aBox -- {val := 4} 

end hidden 
/-
14. 
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by 
f.
-/

-- ANSWER HERE

universe u 

def map_option : Π {α β : Type u}, (α → β) → option α → option β := 
λ α, 
  λ β, 
    λ f,
      λ a,
        match a with
        | option.none := option.none 
        | option.some v := option.some (f v)
        end

def o1 : option ℕ := option.some 3
def o2 : option (list ℕ) := option.some l1   

#eval l1 
#reduce map_option nat.succ option.none
#reduce map_option list_add o2    


/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and 
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically 
a constant. You'll need to declare a
universe variable for the list problem.
-/

-- ANSWER HERE

def default_nat : ℕ := 0

def default_bool : bool := ff 

def default_list : Π (α : Type u), list α := list.nil  
