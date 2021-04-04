import .field_rename
import ...inClassNotes.typeclasses.functor
import ...inClassNotes.typeclasses.algebra
import data.real.basic
import data.int.basic
import data.rat.basic 

open alg

universe u


/-
1. We've imported our definitions from our
class on basic algebraic structures, such as
monoid and group. Go learn what an algebraic
*ring* is, define a typeclass that expresses
its definition, and define an instance that
expresses the claim that the integers (ℤ or
*int* in Lean) is a ring. You may "stub out"
the required proofs with *sorry*. 
-/

-- A ring is a set R which is closed under + and * and satisfies following props:
-- 1. R is an abelian group under + 
-- 2. * is associative 
-- 3. Distributive Law applies
-- Using Wikipedia definition: (https://en.wikipedia.org/wiki/Ring_(mathematics))


set_option old_structure_cmd true 


@[class]
structure has_ring (α : Type u) extends alg.add_comm_group α, mul_monoid α :=
(dist_left : ∀ (a b c : α), mul_groupoid.mul a (add_groupoid.add b c) = add_groupoid.add (mul_groupoid.mul a b) (mul_groupoid.mul a c))
(dist_right : ∀ (a b c : α), mul_groupoid.mul (add_groupoid.add b c) a = add_groupoid.add (mul_groupoid.mul b a) (mul_groupoid.mul c a))


instance has_zero_int : alg.has_zero ℤ := ⟨ 0 ⟩
instance has_one_int : alg.has_one ℤ := ⟨ 1 ⟩
instance mul_groupoid_int : alg.mul_groupoid ℤ := ⟨ int.mul ⟩ 
instance add_groupoid_int : alg.add_groupoid ℤ := ⟨ int.add ⟩ 
instance mul_semigroup_int : alg.mul_semigroup ℤ := ⟨ sorry ⟩
instance add_semigroup_int : alg.add_semigroup ℤ := ⟨ sorry ⟩
instance mul_monoid_int : alg.mul_monoid ℤ := ⟨ sorry, sorry ⟩
instance add_monoid_int : alg.add_monoid ℤ := ⟨ sorry, sorry ⟩ 
instance add_group_int : alg.add_group ℤ := ⟨ sorry, sorry ⟩ 
instance mul_group_int : alg.mul_group ℤ := ⟨ sorry, sorry ⟩ 
instance add_comm_group_int : alg.add_comm_group ℤ   := ⟨ sorry ⟩
instance mul_comm_group_int : alg.mul_comm_group ℤ := ⟨ sorry ⟩

instance has_ring_int : has_ring ℤ := ⟨ sorry, sorry, sorry, sorry, sorry ⟩

instance has_zero_rat : alg.has_zero ℚ := ⟨ 0 ⟩
instance has_one_rat : alg.has_one ℚ := ⟨ 1 ⟩
instance mul_groupoid_rat : alg.mul_groupoid ℚ := ⟨ rat.mul ⟩ 
instance add_groupoid_rat : alg.add_groupoid ℚ := ⟨ rat.add ⟩ 
instance mul_semigroup_rat : alg.mul_semigroup ℚ := ⟨ sorry ⟩
instance add_semigroup_tat : alg.add_semigroup ℚ := ⟨ sorry ⟩
instance mul_monoid_rat : alg.mul_monoid ℚ := ⟨ sorry, sorry ⟩
instance add_monoid_rat : alg.add_monoid ℚ := ⟨ sorry, sorry ⟩ 
instance add_group_rat : alg.add_group ℚ := ⟨ sorry, sorry ⟩ 
instance mul_group_rat : alg.mul_group ℚ := ⟨ sorry, sorry ⟩ 
instance add_comm_group_rat : alg.add_comm_group ℚ   := ⟨ sorry ⟩
instance mul_comm_group_rat : alg.mul_comm_group ℚ := ⟨ sorry ⟩

instance has_zero_real : alg.has_zero ℝ := ⟨ 0 ⟩
instance has_one_real : alg.has_one ℝ := ⟨ 1 ⟩
instance mul_groupoid_real : alg.mul_groupoid ℝ := ⟨ sorry ⟩ 
instance add_groupoid_real : alg.add_groupoid ℝ := ⟨ sorry ⟩ 
instance mul_semigroup_real : alg.mul_semigroup ℝ := ⟨ sorry ⟩
instance add_semigroup_real : alg.add_semigroup ℝ := ⟨ sorry ⟩
instance mul_monoid_real : alg.mul_monoid ℝ := ⟨ sorry, sorry ⟩
instance add_monoid_real : alg.add_monoid ℝ := ⟨ sorry, sorry ⟩ 
instance add_group_real : alg.add_group ℝ := ⟨ sorry, sorry ⟩ 
instance mul_group_real : alg.mul_group ℝ := ⟨ sorry, sorry ⟩ 
instance add_comm_group_real : alg.add_comm_group ℝ   := ⟨ sorry ⟩
instance mul_comm_group_real : alg.mul_comm_group ℝ := ⟨ sorry ⟩


/-
2. Go learn what an algebraic *field* is, then
define a typeclass to formalize its definition,
and finally define two instances that express
the claims that the rational numbers (ℚ) and 
the real numbers (ℝ) are both fields. Again you
may (and should) stub out the proof fields in
your instances using sorry.
-/

-- A field is a set F which is closed under + and * such that
-- 1. F is abelian group under + 
-- 2. F - {0} (set F without additive identity 0) is abelian under *
-- Distributive Law applies  
-- Using Reed College's definition (http://people.reed.edu/~mayer/math112.html/html1/node16.html)

@[class]
structure has_field (α : Type u) extends has_ring α, mul_monoid α := 
(mul_comm : ∀ (a b : α), (a ≠ alg.has_zero.zero) → mul_groupoid.mul a b = mul_groupoid.mul b a )

instance has_field_rat : has_field ℚ := ⟨ sorry, sorry, sorry, sorry, sorry, sorry ⟩
instance has_field_real : has_field ℝ := ⟨ sorry, sorry, sorry, sorry, sorry, sorry ⟩   

/-
3. Graduate students required. Undergrads extra
credit. Go figure out what an algebraic module is
and write a typeclass to specify it formally. 
Create an instance to implement the typeclass for
the integers (ℤ not ℕ). Stub out the proofs. In
lieu of a formal proof, present a *brief informal*
(in English) argument to convince your instructor
that the integers really do form a module under
the usual arithmetic operators.
-/
-- module is a generalization of vector spaces 
-- scalars from ring instead of field (vector space) 
-- abelian group M of "elements" (not vectors) 
-- r*m is a scaled element
-- distributive properties, associative property, identity
-- Using definition from Socratica: https://www.youtube.com/watch?v=IvukAijXgLE&ab_channel=Socratica

set_option old_structure_cmd true 

-- LEFT MODULE
-- module is a vector space where the scalars are a ring

@[class]
structure has_module (α β : Type u) extends has_ring α, alg.add_group β :=
(add_comm : ∀ (a b : α), add_groupoid.add a b = add_groupoid.add b a ) -- rebuilding abelian group w/ different constructor name
(mod_scale : α → β → β) -- r*m = scaling 
(mod_dist_left : ∀ (r : α) (m1 m2 : β), mod_scale r (add_groupoid.add m1 m2) = add_groupoid.add (mod_scale r m1) (mod_scale r m2))
(mod_dist_right : ∀ (r1 r2 : α) (m : β), mod_scale (add_groupoid.add r1 r2) m = add_groupoid.add (mod_scale r1 m) (mod_scale r2 m))
(mod_assoc : ∀ (r1 r2 : α) (m : β), mod_scale (mul_groupoid.mul r1 r2) m = mod_scale r1 (mod_scale r2 m))
(mod_id : ∀ (m : β), mod_scale alg.has_one.one m = m) 

instance has_module_int : has_module ℤ ℤ := ⟨ sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry ⟩

/-
Informal Proof that the integers form a module: 

We know that the integers form a ring since:
1) Integers are Abelian under addition (commutative property holds for integers)
2) Distributive property applies 

Since the integers form a ring, we can safely choose the scalars of our module to be the set of Integers. 

Since we already established that the integers are abelian under addition, the "elements" of our module
can also come from the integers. The set of integers is both abelian and forms a ring, so the integers must 
form a module. Scaling is nothing more than simple multiplication which we have defined in the multiplicativegroupoid formed by
the integer, and distributive property, associativity, and identity all come from the fact that the integers form an abelian group.
-/




/-
4. The set of (our representations of) natural
numbers is defined inductively. Here's how they
are defined, copied straight from Lean's library.

inductive nat
| zero : nat
| succ (n : nat) : nat

Complete the following function definitions 
for natural number addition, multiplication,
and exponentiation. Write your own functions
here without using Lean's implementations 
(i.e., don't use nat.mul, *, etc). You may
not use + except as a shorthand for using 
the nat.succ constructor to add one. If you
need to do addition of something other than
one, use your own add function. Similarly, if
you need to multiply, using your mul function.
-/

-- multiplication = repeated addition, exponentiation = repeated multiplication 

def add : nat → nat → nat
| 0 m         := m
| (n' + 1) m  := add n' (nat.succ m)

#eval add 4 3       -- 7
#eval add 0 5       -- 5
#eval add 5 0       -- 5 
#eval add 20 30     -- 50 

def mul : nat → nat → nat
| 0 m         := 0
| (n' + 1) m  := add m (mul n' m)

#eval mul 4 20    -- 80
#eval mul 33 3    -- 99
#eval mul 1 9     -- 9
#eval mul 0 5     -- 0        

-- first arg raised to second
def exp : nat → nat → nat 
| n 0 := 1
| n (m'+1) := mul n (exp n m')

#eval exp 2 10    -- expect 1024
#eval exp 5 2     -- 25 

/-
5. Many computations can be expressed 
as compositions of map and fold (also 
sometimes called reduce). For example,
you can compute the length of a list
by mapping each element to the number,
1, and by the folding the list under
natural number addition. A slightly 
more interesting function counts the
number of elements in a list that 
satisfy some predicate (specified by
a boolean-returning function). 

A. Write a function, mul_map_reduce, that 
takes (1) a function, f : α → β, where β
must be a monoid; and (2) a list, l, of
objects of type α; and that then uses f
to map l to a list of objects of a type, 
β, and that then does a fold on the list 
to reduce it to a final value of type β. 

Be sure to use a typeclass instance in 
specifying the type of your function to 
ensure that the only types that can serve
as values of β have monoid structures.
Use both our mul_monoid_foldr and fmap
functions to implement your solution.
-/


def mul_map_reduce {α β : Type} [mul_monoid β] : (α → β) → (list α) → β :=
λ (f : α → β),
  λ (l : list α),
    mul_monoid_foldr (fmap f l) -- mul identity and multiplication function are guaranteed by monoid


/-
B. Complete the given application of 
mul_map_reduce with a lambda expression 
to compute the product of the non-zero 
values in the list 
[1,0,2,0,3,0,4].
-/

#eval mul_map_reduce  (λ (n : nat), if n = 0 then 1 else n) [1,0,2,0,3,0,4]
-- expect 24

/-
6. Here you practice with type families.

A. Define a family of types, each of which
is index by two natural numbers, such that 
each type is inhabited if and only if the 
two natural numbers are equal. You may call
your type family nat_eql. Use implicit args
when it makes the use of your type family
easier. 
-/

inductive nat_eql: nat → nat → Type
| zeros_equal : nat_eql 0 0
| n_succ_m_succ_equal : Π {n m : nat}, nat_eql n m → nat_eql n.succ m.succ  -- require a previous nat_eql for this cons

/-
B. Now either complete the following programs
or argue informally (and briefly) why that
won't be possible.
-/

open nat_eql

def eq_0_0 : nat_eql 0 0 := zeros_equal 
def eq_0_1 : nat_eql 3 4 := _ -- uninhabited type, no way to build this with our constructors
def eq_1_1 : nat_eql 1 1 := n_succ_m_succ_equal zeros_equal -- can apply successor constructor to zeros_equal constructor
--def eq_2_2 : nat_eql 2 2 := n_succ_m_succ_equal (n_succ_m_succ_equal zeros_equal) -- repeatedly applying successor constructor
--def eq_3_3 : nat_eql 3 3 := n_succ_m_succ_equal eq_2_2 

--#reduce eq_2_2 

/-
C. The apply tactic in Lean's tactic language
let's you build the term you need by applying
an already defined function. Moreover, you can
leave holes (underscores) for the arguments and
those holes then become subgoals. In this way,
using tactics allows you to build a solution 
using interactive, top-down, type-guided, aka
structured, programming! Show that eq_2_2 is
inhabited using Lean's tactic language. We get
you started. Hint: remember the "exact" tactic. 
Hint: Think *top down*. Write a single, simple
expression that provides a complete solution
*except* for the holes that remain to be filled.
Then recursively "fill the holes". Continue 
until you're done. Voila! 
-/

def eq_2_2 : nat_eql 2 2 :=
begin
apply (n_succ_m_succ_equal eq_1_1), -- applying successor constructor once
end

/-
In Lean, "repeat" is a tactic that takes
another tactic as an argument (enclosed in
curly braces), applies it repeatedly until
it fails, and leaves you in the resulting 
tactic state. Use the repeat tactic to 
show that "nat_eql 500 500" is inhabited.
If you get a deterministic timeout, pick
smaller numbers, such as 100 and 100. It's
ok with us.
-/

def eq_500_500 : nat_eql 500 500 :=
begin
  apply n_succ_m_succ_equal _, 
repeat {apply n_succ_m_succ_equal _}, -- applying successor constructor 499 times
  apply zeros_equal -- handling 'base case' 
end

#reduce eq_500_500


/-
7. Typeclasses and instances are used in Lean
to implement *coercions*, also known as type
casts. 

As in Java, C++, and many other languages,
coercions are automatically applied conversions
of values of one type, α, to values of another 
type, β, so that that values of type α can be
used where values of type β are needed.

For example, in many languages you may use an 
integer wherever a Boolean value is expected. 
The conversion is typically from zero to false
and from any non-zero value to true. 

Here's the has_coe (has coercion) typeclass as
defined in Lean's libraries. As you can see, a
coercion is really just a function, coe, from 
one type to another, associated with the pair 
of those two types.

class has_coe (a : Sort u) (b : Sort v) :=
(coe : a → b)

A. We provide a simple function, needs_bool, 
that takes a bool value and just returns it. 
Your job is to allow this function to be 
applied to any nat value by defining a new
coercion from nat to bool. 

First define a function, say nat_to_bool, that
converts any nat, n, to a bool, by the rule that
zero goes to false and any other nat goes to tt. 
Then define an instance of the has_coe typeclass
to enable coercions from nat to bool. You should
call it nat_to_bool_coe. When you're done the
test cases below should work.
-/

def nat_to_bool : nat → bool := 
λ n,
  match n with
  | 0 := ff 
  | n'+1 := tt 
end 

instance nat_to_bool_coe : has_coe nat bool := ⟨nat_to_bool⟩ 

def needs_bool : bool → bool := λ b, b

-- Test cases
#eval needs_bool (1:nat)  -- expect tt
#eval needs_bool (0:nat)  -- expect ff


/-
Not only are coercions, when available, applied
automatically, but, with certain limitations, 
Lean can also chain them automatically. Define 
a second coercion called string_to_nat_coe, 
from string to nat, that will coerce any string
to its length as a nat (using the string.length
function). When you're done, you should be able
to apply the needs_bool function to any string, 
where the empty string returns ff and non-empty, 
tt. 
-/

instance string_to_nat_coe : has_coe string nat := ⟨string.length⟩ 

-- Test cases
#eval needs_bool "Hello"  -- expect tt
#eval needs_bool ""  -- expect ff

/-
Do you see how the coercions are being chained,
aka, composed, automatically?
-/

--  Good job!

example : 1 = 1 := 
begin
  exact (eq.refl 1),
end

example : 1 = 1 := 
begin
  apply eq.refl _,
end

