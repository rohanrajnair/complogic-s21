import data.real.basic
import .lin2k

namespace lin2k 

universe u 

-- Let's work with rational number field
abbreviation K := ℚ  

-- Here are nice abbreviations for types
abbreviation scalr := K
abbreviation vectr := K × K

/-
1A. [10 points]

Declare v1, v2, and v3 to be of type
vectr with values (4,6), (-6,2), and
(3, -7), respectively.
-/

-- HERE

def v1 : vectr := ⟨ 4, 6⟩
def v2 : vectr := ⟨ -6, 2 ⟩
def v3 : vectr := ⟨ 3, -7 ⟩   

/-
1B. [10 points]

Now define v4, *using the vector 
space operators, + and •, to be 
the following "linear combination"
of vectors: twice v1 plus negative 
v2 plus v3. The negative of a vector
is just -1 (in the field K) times
the vector. Write -1 as (-1:K), as 
otherwise Lean will treat it as the 
integer -1. (Note that subtraction
of vectors, v2 - v1 is defined as
v2 + (-1:K) • v1.)
-/

-- HERE 

def v4 : vectr := 2 • v1 + (-1:scalr) • v2 + v3 




/-
Compute the correct answer by hand
here, showing your work, and check
that eval is producing the correct
answer. 

-- HERE

v1 = (4, 6)
v2 = (-6, 2)
v3 = (3, -7)

v4 = 2 • v1 + (-1) • v2 + v3 

2 • v1 = (2(4), 2(6)) = (8, 12)
(-1) • v2 = (6, -2)

v4 = (8, 12) + (6, -2) + (3, -7) 
   = (17, 3)

-/

#eval v4 -- (17, 3)



/-
1C. [10 points]

On a piece of paper, draw a picture
of the preceding computation. Make a
Cartesian plane with x and y axes. 
Draw each vector, v1, v2, v3, as an
arrow from the origin to the point
designated by the coordinates of the
vector.

Scalar multiplication stretches or
shrinks a vector by a given factor.
Show each of the scaled vectors in 
your picture: 2 • v1 and (-1:K) • v2. 

Finally vector addition in graphical
terms works by putting the tail (non
arrow) end of one vector at the head
of the other then drawing the vector
from the tail of the first to the head
of the second. Draw the vectors that
illustrate the sum, v1 + (-1:K) • v2,
and then the sum of that with v3. You
should come out with the same answer
as before. Take a picture of your
drawing and upload it with your test.
-/

-- HERE

/-
2. [15 points]

Many sets can be viewed as fields. For 
example, the integers mod p, where p is
any prime, has the structure of a field
under the usual operations of addition
and multiplication mod p.

In case you forget about the integers 
mod n, it can be understood as the set
of natural numbers from 0 to n-1, where
addition and multiplication wrap around.

For example, the integers mod 5 is the
set {0, 1, 2, 3, 4}. Now 2 + 2 = 4 but
2 + 3 = 5 = 0. It's "clock arithmetic," 
as they say. Similarly 2 * 2 = 4 but 
2 * 3 = 6 = 5 + 1 = 0 + 1 = 1. 

To show informally that the integers 
mod 5 is a field you have to show that
every element of the set has an additive
inverse and that every element of the 
set but 0 has a multiplicative inverse.

Draw two tables below with the values
of the integers mod 5 in each of the 
left column. In the second column of
the first table, write in the additive
inverses of each element. In the second
table, write the multiplicative inverses.
-/

-- HERE

/-

x + b ≡ 0 (mod 5) 

Table 1: 

x ∈ ℤ5    b 
0         0                
1         4
2         3
3         2
4         1

x ⬝ (1/x) ≡ 1 (mod 5)

Table 2: 

x ∈ ℤ5   1/x        
1         1
2         3
3         2
4         4

-/


/-
4. [15 points]
Is the integers mod 4 a field? If so,
prove it informally by writing tables
giving the inverses. If not, show that
not every value in the integers mod 4
(except 0) has a multiplicative inverse,
identify a value that doesn't have an
inverse, and briefly explain why.
-/

-- HERE

/- 
x + b ≡ 0 (mod 4) 

Table 1: 

x ∈ ℤ4    b 
0         0               
1         3  
2         2
3         1

x ⬝ (1/x) ≡ 1 (mod 4)

Table 2: 

x ∈ ℤ4   1/x
1         1 
2         ??
3         3 


The integers mod 4 (ℤ4) is not a field because 
2 does not have a multiplicative inverse mod 4. We can show this more formally 
via a proof by contradiction by assuming 2 times some x is congruent to 1 mod 4: 

2x ≡ 1 (mod 4)

This means that 4 must divide 2x - 1 
(In other words, 2x - 1 is a multiple of 4):

4 | 2x - 1

So, 2x - 1 must also be a multiple of 2: 

2 | 2x - 1

This is not possible; 2 cannot divide 2x - 1 because 2 is even. 

-/

/-
5. [20 points]
Write a function, sum_vectrs, that 
takes a list of our vectr objects as 
an argument and that reduces it to a 
single vector sum. To implement your
function use a version of foldr as we
developed it: one that takes an additive
monoid implicit instance as an argument, 
ensuring consistency of the operator we
are using to reduce the list (add) and 
the corresponding identity element. 
Copy and if needed modify the foldr
definition here. It should use Lean's 
monoid class, as we've done throughout
this exercise. You do not need to and
should not try to use our algebra.lean 
file. Test your function by creating a
list of vectrs, [v1, v2, v3, v4], from
above, compute the expected sum, and
show that your function returns the 
expected/correct result.
-/

-- HERE

def sum_vectrs {α : Type u} [add_monoid α] : list α → α 
| [] := has_zero.zero 
| (h::t) := h + sum_vectrs t

def vec_list : list vectr := [v1, v2, v3, v4]

#eval v1 + v2 + v3 + v4           -- (18, 4)
#eval sum_vectrs [v1, v2, v3, v4] -- (18, 4)

/-
6. Required for graduate students,
optional extra credit for undergrads.

The set of integers mod p can be viewed
as a field with the usual addition and
multiplication operations mod p. These 
finite fields (with only a finite number 
of elements) play a crucial role in many 
areas of number theory (in mathematics), 
and in cryptography in computer science.


A. [20 points]

Instantiate the field typeclass for
the integers mod 5 (a prime). You 
may and should stub out the proofs 
all along the way using "sorry", but
before you do that, convince yourself
that you are *justified* in doing so.

Use a "fake" representation of the
integers mod 5 for this exercise: as
an enumerated type with five values. 
Call them zero, one, two, three, and
four. Then define two functions, 
z5add and z5mul, to add and multiply
values of this type. You can figure
out the addition and multiplication
tables and just write the functions
by cases to return the right result
in each case. Start with Lean's field
typeclass, see what you need to 
instantiate it, and work backwards, 
recursively applying the same method 
until your reach clases that you can
implement directly. Put your code for
this problem below this comment.

Replace the following "assumptions" 
with your actual definitions (commenting
out the axioms as you replace them). You
can right away right click on "field" and
"go to definition" to see what you need
to do. Solving this problem will require
some digging through Lean library code.
-/

inductive Z5 : Type
| zero 
| one
| two 
| three 
| four 


open Z5 

def z5add : Z5 → Z5 → Z5
| zero x := x 
| x zero := x 
| one one := two 
| one two := three
| one three := four 
| one four := zero 
| two one := three 
| two two := four 
| two three := zero  
| two four := one  
| three one := four 
| three two := zero 
| three three := one 
| three four := two 
| four one := zero 
| four two := one 
| four three := two 
| four four := three


def z5mul : Z5 → Z5 → Z5
| zero x := zero  
| x zero := zero  
| one x := x  
| x one := x 
| two two := four 
| two three := one  
| two four := three  
| three two := one 
| three three := four 
| three four := two 
| four two := three 
| four three := two  
| four four := one 


def z5neg : Z5 → Z5 
| zero := zero 
| one :=  four 
| two := three 
| three := two 
| four := one

def z5inv : Z5 → Z5 
| zero := zero 
| one :=  one 
| two := three 
| three := two 
| four := four  

def z5sub : Z5 → Z5 → Z5 
| zero x := z5neg x  
| x zero := x 
| one one := zero 
| one two := four
| one three := three
| one four := two  
| two one := one  
| two two := zero  
| two three := four  
| two four := three  
| three one := two  
| three two := one  
| three three := zero  
| three four := four  
| four one := three  
| four two := two  
| four three := one  
| four four := zero  

-- axioms 
--   -- (Z5 : Type) 
--   -- (z5add : Z5 → Z5 → Z5)
--   (z5mul : Z5 → Z5 → Z5)


-- instance has_zero_Z5 : has_zero Z5 := ⟨ zero ⟩
-- instance has_one_Z5 : has_one Z5 := ⟨ one ⟩ 

-- instance has_add_Z5 : has_add Z5 := ⟨ z5add ⟩
-- instance has_mul_Z5 : has_mul Z5 := ⟨ z5mul ⟩  

-- instance semigroup_Z5 : semigroup Z5 := ⟨ z5mul, sorry ⟩
-- instance add_semigroup_Z5 : add_semigroup Z5 := ⟨ z5add, sorry ⟩

-- instance monoid_Z5 : monoid Z5 := ⟨ z5mul, sorry, one, sorry, sorry ⟩
-- instance add_monoid_Z5 : add_monoid Z5 := ⟨ z5add, sorry, zero, sorry, sorry ⟩



-- instance distrib_Z5 : distrib Z5 := ⟨ z5mul, z5add, sorry, sorry ⟩

-- instance sub_neg_monoid_Z5 : sub_neg_monoid Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry ⟩ 
-- instance add_group_Z5 : add_group Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry, sorry ⟩


-- instance add_comm_semigroup_Z5 : add_comm_semigroup Z5 := ⟨ z5add, sorry, sorry ⟩
-- instance comm_semigroup_Z5 : comm_semigroup Z5 := ⟨ z5mul, sorry, sorry ⟩

-- instance add_comm_monoid_Z5 : add_comm_monoid Z5 := ⟨ z5add, sorry, zero, sorry, sorry, sorry ⟩  

-- instance add_comm_group_Z5 : add_comm_group Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry, sorry, sorry ⟩   


-- instance ring_Z5 : ring Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry, sorry, sorry, z5mul, sorry, one, sorry, sorry, sorry, sorry ⟩ 

-- instance comm_ring_Z5 : comm_ring Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry, sorry, sorry, z5mul, sorry, one, sorry, sorry, sorry, sorry, sorry⟩


instance field_Z5 : field Z5 := ⟨ z5add, sorry, zero, sorry, sorry, z5neg, z5sub, sorry, sorry, sorry, z5mul, sorry, one, sorry, sorry, sorry, sorry, sorry, z5inv, sorry, sorry, sorry ⟩

#check field Z5



 

-- HERE



/-
B. [15 points]

Given that you've now presumably
established that Z5 is a field,
let z5scalr be an abbreviation for
Z5, and z5vectr for Z5 ⨯ Z5. Then
use #eval to evaluate an expression
(that you make up) involving vector 
addition and scalar multiplication
using our new z5vectr objects, i.e., 
vectors over Z5. These vectors will
look like, e.g., (one, three). Work 
out the right answer by hand and
test your code to gain confidence 
that it's working correctly.
-/

-- HERE

abbreviation z5scalr := Z5
abbreviation z5vectr := Z5 × Z5 

instance inhabited_Z5 : inhabited Z5 := ⟨ zero ⟩  

def v5 : z5vectr := ⟨ one, three ⟩ 
def v6 : z5vectr := ⟨ four, two ⟩
def v7 : z5vectr := ⟨ zero, two ⟩
def v8 : z5vectr := ⟨ one, one ⟩   

def s0 : z5scalr := zero 
def s1 : z5scalr := one 
def s2 : z5scalr := two 
def s3 : z5scalr := three

def v9 : z5vectr := s2 • v6 + v7 

def v10 : z5vectr := s2 • v7 + s3 • v8


/-
v9 = s2 • v6 + v7 
   = two • (four, two) + (zero, two)
   = (three, four) + (zero, two)
   = (three, one)

v10 = s2 • v7 + s3 • v8
    = two • (zero, two) + three • (one, one)
    = (zero, four) + (three, three)
    = (three, two)   

-/


#reduce v9 -- (three, one)
#reduce v10 -- (three, two)

/-
Take away: Instantiating a typeclass
for a given type can provide a whole
set of operations and notations that
you can use to "do algebra" with that
type. The underlying types themselves
can be very diverse. That is, we can
impose the same abstract interface on
sets of objects of different kinds, 
just as we previously imposed a group
API on the elements of the symmetry 
group, D4, of a square. Here we've now
seen that we can write vector space
algebra computations involving 2-D
vectors over both the rational and
the integers mod 5. It's in this 
sense that instantiating a typeclass
for a type provides a new "API" for
manipulating values of that type.

And while languages such as Haskell
do provide typeclasses, they don't
provide a language in which you can
declaratively express and give proofs
of the "rules" that structures have 
to follow to be valid instances. So,
welcome to Lean, a language in which
you can write mathematics and code,
with strong automated type checking
of both code and proofs. If it has to
be right (which is the case for much
crypto code), maybe write it like so!
-/

end lin2k 

