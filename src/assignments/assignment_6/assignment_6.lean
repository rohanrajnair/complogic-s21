import ...inClassNotes.typeclasses.functor
--import ...inClassNotes.typeclasses.algebra

namespace alg

universe u

/-
Typeclasses extends hierarchy modeling algebraic hierarchy
-/

@[class]
structure has_zero (α : Type u) :=
(zero : α)


@[class]
structure has_one (α : Type u) :=
(one : α)


/-
A groupoid is a set with a binary operator. The only consraint 
is that the set must be closed under the given binary operator.
Note: there are other definitions of groupoid in mathematics. A
groupoid is also sometimes called a magma. Here, the set is given
by the type, α, and the operator by the field, *mul*.
-/
@[class]  
structure mul_groupoid (α : Type u) :=   
(mul : α → α → α)                    

@[class]  
structure add_groupoid (α : Type u) :=  -- aka mul_groupoid or magma
(add : α → α → α)                       -- mul must be total (closed)

/-
A semigroup is a groupoid in which the operator is *associative*
-/
@[class]
structure mul_semigroup (α : Type u) extends mul_groupoid α :=
(mul_assoc : ∀ (a b c : α), mul a (mul b c) = mul (mul a b) c)

@[class]
structure add_semigroup (α : Type u) extends add_groupoid α :=
(assoc : ∀ (a b c_1 : α), add a (add b c_1) = add (add a b) c_1)

/-
A monoid is a semigroup with an identity element
-/
@[class]
structure mul_monoid (α : Type u) extends mul_semigroup α, has_one α :=
(mul_ident_left : ∀ (a : α), mul one a = a)
(mul_ident_right: ∀ (a: α), mul a one = a)

@[class]
structure add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(ident_left : ∀ (a : α), add zero a = a)
(ident_right: ∀ (a: α), add a zero = a)

/-
A group is a mul_monoid in which every element has an inverse
-/
@[class]
structure mul_group (α : Type u) extends mul_monoid α :=
(mul_left_inv : ∀ (a : α), ∃ (i : α), mul i a = one )
(mul_right_inv : ∀ (a : α), ∃ (i : α), mul a i = one )

@[class]
structure add_group (α : Type u) extends add_monoid α :=
(left_ident : ∀ (a : α), ∃ (i : α), add i a = zero )
(right_ident : ∀ (a : α), ∃ (i : α), add a i = zero )

/-
A group is commutative, or abelian, if its operator is commutative.
-/
@[class]
structure mul_comm_group (α : Type u) extends mul_group α :=
(mul_comm : ∀ (a b : α), mul a b = mul b a )

@[class]
structure add_comm_group (α : Type u) extends add_group α :=
(comm : ∀ (a b : α), add a b = add b a )

/-
You can keep going to define a whole hierarchy of algebraic
abstractions, and indeed all of these constructs and many more
are already defined in Leans math library.

-- Ring
-- Field
-- Module
-- Vector space
-- etc.
-/


/-
Typeclass instances for nat. Note that we are "stubbing out"
proofs that our objects actually follow the rules. We will 
come back to fill in proofs once we know how to do that. It
will be soon.
-/
instance has_one_nat : has_one nat := ⟨ 1 ⟩ 
instance mul_groupoid_nat : mul_groupoid nat := ⟨ nat.mul ⟩ 
instance mul_semigroup_nat : mul_semigroup nat := ⟨ _ ⟩ 
instance mul_monoid_nat : mul_monoid nat := ⟨ _ , _ ⟩ 

instance has_zero_nat : has_zero nat := ⟨ 0 ⟩ 
instance add_groupoid_nat : add_groupoid nat := ⟨ nat.add ⟩ 
instance add_semigroup_nat : add_semigroup nat := ⟨ _ ⟩ 
instance add_monoid_nat : add_monoid nat := ⟨ _ , _ ⟩ 

-- instance mul_group_nat : mul_group nat := ⟨ _, _ ⟩ 

/-
ℕ isn't a group under either add or mul! No inverses. 
ℤ is an additive group but not a multiplicative group.
ℚ is an additive group; ℚ-{0} is a multiplicative group.
ℚ is thus a field. ℝ is a field in the same way. So is ℂ.
-/ 



/-
So what good can all of this be? Here's one application.
We've noted that arguments to foldr can be inconsistent. The
wrong identity element can be passed for the given operator.
-/


def foldr {α : Type} : (α → α → α) → α → list α → α 
| f id [] := id    
| f id (h::t) := f h (foldr f id t)

#eval foldr nat.mul 0 [1,2,3,4,5]   -- oops!


/-
A better foldr takes a "certified" monoid as an argument.
A monoid bundles an operator with its identity element, so
they can't get out of synch. By "certified,"" we mean that 
an object comes with a rock solid proof of correctness. In
this case, we'd really want to fill a proof that a putative
monoid instance has an identity element that is proven to
be a left and a right identity for the given operator. We
don't know quite yet how to give these proofs, but that's
the idea.  

Here are implementations of foldr taking multiplicative and
additive monoids as arguments. Note that the code is written
to depend only on the definitions of the relevant typeclasses.
You can thus use this fold to reduce lists of values of any 
type as long as that type provides an implementation of the 
monoid typeclass.  

NB: typeclass instances should almost always be anonymous. 
For exaple, write [mul_monoid α] instead of [m : mul_monoid α]. 
Lean does NOT support dot notation for typeclass instances.
Look carefully below: Lean infers an instance of mul_monoid.
That instance in turn extends has_one and mul_semigroup. The
latter extends mul_groupoid (formerly, and in Lean, has_mul).
To get at the mul function of the monoid that we need here,
we refer to it through the typeclass, up the inheritance
hierarchy, that defines it directly: here, mul_groupoid.
-/
def mul_monoid_foldr 
  {α : Type u} 
  [mul_monoid α] 
  :
  list α → α 
| [] := has_one.one
| (h::t) := mul_groupoid.mul h (mul_monoid_foldr t)  

-- Additive version of the same foldr function.
def add_monoid_foldr 
  {α : Type u} 
  [add_monoid α] 
  :
  list α → α 
| [] := has_zero.zero
| (h::t) := add_groupoid.add h (add_monoid_foldr t)  

#eval mul_monoid_foldr [1,2,3,4,5]
#eval add_monoid_foldr [1,2,3,4,5]   -- missing instance above



/-
Copy this file to where you want to work on 
it and then adjust the imports accordingly.
Work through the file following directions
as indicated. Turn in your completed file on
Collab.
-/

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

--open alg

--set_option old_structure_cmd true 


@[class]
structure ring (α : Type u) extends add_comm_group α, mul_monoid α :=
(dist : ∀ (a b c : α), mul a (add b c) = add (mul a b) (mul a c))

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
structure field (α : Type u) extends ring α := 
(mul_comm : ∀ (a b : α) (a ≠ zero), mul a b = mul b a )




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
-- module is a generlization of vector spaces 
-- scalars from ring instead of field (vector space) 
-- abelian group M of elements 
-- distributive properties, associative property, identity


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


-- Your answer here

def mul_map_reduce {α β : Type} [mul_monoid β] : (α → β) → (list α) → β :=
λ (f : α → β),
  λ (l : list α),
    mul_monoid_foldr (fmap f l) 


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
| n_succ_m_succ_equal : Π {n m : nat}, nat_eql n m → nat_eql n.succ m.succ  

/-
B. Now either complete the following programs
or argue informally (and briefly) why that
won't be possible.
-/

open nat_eql

def eq_0_0 : nat_eql 0 0 := zeros_equal 
def eq_0_1 : nat_eql 3 4 := _ 
def eq_1_1 : nat_eql 1 1 := n_succ_m_succ_equal zeros_equal
--def eq_2_2 : nat_eql 2 2 := n_succ_m_succ_equal (n_succ_m_succ_equal zeros_equal)
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
apply (n_succ_m_succ_equal eq_1_1), 
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
repeat {apply n_succ_m_succ_equal _},
  apply zeros_equal 
end


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
end alg 