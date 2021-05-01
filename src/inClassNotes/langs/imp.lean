import .arith_expr
import .bool_expr

/-
A little PL in which we have mutable
state and an update (assignment) operation.
-/

/-
We don't have mutable state in a pure functional language
-/
def x := 1
-- def x := 2


-- structure avar : Type := (idx : nat)

def X := avar.mk 0
def Y := avar.mk 1
def Z := avar.mk 2

def init : a_state := λ (v : avar), 0

/-
{ (X,0), (Y,0), (Z,0), ... }  st
X = 7;
{ (X,7), (Y,0), (Z,0), ... } st'
Y = 8
{ (X,7), (Y,8), (Z,0), ... } st'' 
Z = 9
{ (X,7), (Y,8), (Z,9), ... } st'''
X = 10
{ (X,10), (Y,8), (Z,9), ... } st'''


Π (v : avar), if v = X then st' v = 7 else st' v = st v
-/

def var_eq : avar → avar → bool 
| (avar.mk n1) (avar.mk n2) := n1 = n2 


def override : a_state → avar → aexp → a_state 
| st v exp := 
    λ (v' : avar), 
      if (var_eq v v') 
      then (aeval exp st) 
      else (st v')


def st' := override init X [7]

#eval st' X
#eval st' Y
#eval st' Z

def st'' := override st' Y [8]

#eval st'' X
#eval st'' Y
#eval st'' Z

def st''' := override st'' Z [9]

#eval st''' X
#eval st''' Y
#eval st''' Z
 

 def st'''' := override st''' X [10]

#eval st'''' X
#eval st'''' Y
#eval st'''' Z


inductive cmd : Type
| skip 
| assn (v : avar) (e : aexp) 
| seq (c1 c2 : cmd) : cmd
-- | cond (b : bool_expr) (c1 c2 : cmd) : cmd
-- | while (b : bool_expr) (c : cmd) : cmd

open cmd

notation v = a := assn v a 
notation c1 ; c2  := seq c1 c2 


def a1 : cmd := X = [7]
def a2 := Y = [8]
def a3 := Z = [9]
def a4 := X = [10]

def program : cmd := -- a1; a2; a3; a4
  X = [7];
  Y = [8];
  Z = [9];
  X = [10];
  skip

def c_eval : cmd → a_state → a_state
| skip st := st
| (v = e) st  := override st v e
| (c1 ; c2) st  := c_eval c2 (c_eval c1 st) 

/-
We implement assignment using function override,
converting a given (initial) state into a new state
by binding a given variable to the value of a given
arithmetic expression.

We implement sequential composition of c1 and c2 by 
evaluating c2 in the state obtained by evaluating
c1 in the given (initial) state. Note that c1 and
c2 can each themselves be complex programs (in our
little language).
-/


def res := c_eval program init

#reduce res X
#reduce res Y
#reduce res Z

-- Yay!


inductive c_sem : cmd → a_state → a_state → Prop
| c_sem_skip : ∀ (st : a_state), 
    c_sem skip st st

| c_sem_assm :
  ∀ (pre post : a_state) (v : avar) (e : aexp),
    (override pre v e = post) → 
    c_sem (v = e) pre post

| c_sem_seq :
  ∀ (pre is post : a_state) (c1 c2 : cmd),
  c_sem c1 pre is → 
  c_sem c2 is post →
  c_sem (c1 ; c2) pre post

  /-
  {pre}
  (c1
  {is}
  c2) 
  {post}
  -/


-- proof broken because we added skip at end of "program"
  theorem t1 : 
    ∀ (post : a_state), c_sem program init post → post X = 10 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    apply rfl,
  end

-- here we fix it
  theorem t2 : 
    ∀ (post : a_state), c_sem program init post → post X = 10 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ_1,
    cases h_ᾰ,
    cases h_ᾰ_ᾰ_1,
    rw <- h_ᾰ_ᾰ_1_ᾰ,
    apply rfl,
  end

-- program broken because we added skip at end of "program"
-- homework: you fix it
  example : 
    ∀ (post : a_state), c_sem program init post → post Z = 9 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
  _
  end


/-
BEHAVIORAL SPECIFICATION
-/


/-
In our model, the meaning of a program
is given by a relation associating states
before program execution with states after.
We represent this relation using the c_sem
family of propositions. In particular, the
proposition, c_sem cmd pre post, will
have a proof if and only if running cmd in
the state, pre, leaves the memory in the
state, post.


We now generalize this notion, yielding 
the concept of a declarative (logical) 
specification of the behavior of an 
imperative program.

What we want to say is the following:
For a program, C, if the state of the
memory is correctly set up for C to 
run then the state of the memory after
C runs will contain the information we
want.

The idea is that we'll encode the 
necessary inputs and starting conditions
in the state and we then expect that 
running the program in that state will
produce a state that satisfies our 
needs.

We are thus concerned with *properties*
of states. We want to say that if the
state before a program runs satisfies 
a certain "pre-condition", then if
we run the program in such a state, the
memory will be left in a state that
satisfies a desired "post-condition."

A pre-condition or a post-condition in
this sense is a predicate on the state
of the memory, and is thus of the type
a_state -> Prop. We will call such a
condition an "assertion."
-/

def Assertion := a_state → Prop

/-
Here are some examples.
-/


def pre1 : Assertion := λ st, true
def post1 : Assertion := λ st, st X = 10 

/-
Any state satisfies pre1.
-/

lemma pre1_trivial : ∀ st : a_state, pre1 st :=
begin
  intro st,
  unfold pre1,
end

/-
Multiple states satisfy post1.

{ (X,10), (Y,0), (Z, 0) }
{ (X,10), (Y,1), (Z, 2) }
{ (X,10), (Y,20), (Z, 100) }
{ (X,0), (Y,9), (Z, 100) }
etc.
-/

/-
Let's draw some set diagrams
showing subsets of states that
satisfy various assertions.
-/

/-
We now formulate specifications
of program as pairs of assertions: 
pre-condition/post-condition pairs!
Given a program C and assertions 
pre and post, we can formulate
the assertion that if you run C
in a state satisfying pre then 
you will end up in a state that
satisfies post. This is itself a
proposition that might or might
not be true given pre, post, 
and C. We can now formalize what
it means for a program to satisfy
a pre-condition/post-condition
specification!
-/

def satisfies (c : cmd) (pre post : a_state → Prop) :=
  ∀ st st' : 
    a_state, pre st → 
    c_sem c st st' →  
    post st'

/-
Examples
-/

def p2 : cmd := 
  X = [10]

def a_pre := λ st : a_state, st X = 10

/-
def pre1 : Assertion := λ st, true
def post1 : Assertion := λ st, st X = 10 
-/

lemma v1 : satisfies p2 pre1 post1 := 
begin
  unfold satisfies,
  intros,
  cases ᾰ_1,
  rw <- ᾰ_1_ᾰ,
  simp [post1],
  apply rfl,
end

notation pre {c} post := satisfies c pre post

example : pre1 {p2} post1 := v1

/-
We have thus arrived at the critical concept
of a Hoare triple. A Hoare triple is simply 
a proposition that *asserts* that if you run
a program c in a state satisfying a speficied
precondition then the final state will satisfy
the postcondition. 
-/

/-
There are several fundamental ways in which we
use such triples. One is that we give all three
elements (pre, c, post), and then prove it! This
is the task of *verification*. A second is that
we give pre and post, and now the task is to
*produce* a progrma C that makes the triple true.
This is the fundamental task of the practicing
programmer! Turn specifications into verified
programs. There are other possibilities. We 
can for example give C and post and ask what
is the weakest precondition (most permissive
condition on the initial state) the sufficies
to make the triple true?

Note that in general, there are many programs
that satisfy a given pre/post specification.
Exercise: produce another program, p3, that
satisfies the same pre/post specification: 
i.e., for which pre1 {p3} post1.
-/
