/-
Alice is looking at Bob. Bob is looking at Charlie.
Alice is married. Charlie is not. 

Theorem to Prove: Some (∃) married person is looking at some unmarried person

(A) Yes
(B) No
(C) Cannot be determined
(D) It depends
-/

example : ∀ (P : Prop), P ∨ ¬P := 
begin
  assume P,
  apply or.inr _,
  intro p,
  _
end

/-
In constructive logic, ∀ (P : Prop), P ∨ ¬ P, 
is not provable.
-/

axioms
(Person : Type)
(Married : Person → Prop)
(LookingAt : Person → Person → Prop)
(alice bob charlie : Person)
(alab : LookingAt alice bob)
(blac : LookingAt bob charlie)
(am : Married alice)
(ncm : ¬Married charlie)

example : _ : _

/-
forall p1 p2, Married p1 and not married p2 and looking at p1 p2
-/

example : ∀ (p1 p2 : Person), 
    Married p1 → ¬ Married p2 → LookingAt p1 p2 := _

/- 
Every married person is looking at every unmarried person. X.
-/


/-
Some married person, p1, is looking at some unmarried person, p2.
-/
example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 := 
begin
apply exists.intro alice,
apply exists.intro bob,
split,
apply am,
split,
end

example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 := 
begin
apply exists.intro bob,
apply exists.intro charlie,
split,
end

/-
In constructive logic, we don't know whether 
Bob is married or not.

In constructive logic, for any proposition, P:

(1) We have a proof of P
(2) We have a proof of ¬P
(3) We don't have a proof either way! This is the "MIDDLE!"
  - polynomial time (P) = non-deterministic polynomial time (NP), TSP, Boolean SAT
  - Collatz conjecture -- aka hailstone problem
-/

/-
meta def HS (n : nat) :=
if (n = 1 ∨ n = 0) return 0
else (if n%2 = 0) (HS n/2)
else (if n%2 = 1) (HS n*3+1)

Does this function terminate for all inputs n?

5 -> 8 -> 4 -> 2 -> 1 .
-/

axiom em : ∀ (P : Prop), P ∨ ¬ P

axiom mnm : ∀ (p : Person), Married p ∨ ¬ Married p

example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 :=
begin
  cases (/-proof of bis or bnm-/ em (Married bob)),
  -- Married bob
  apply exists.intro bob,
  apply exists.intro charlie,
  split,
  assumption,
  split,
  exact ncm,
  exact blac,
  apply exists.intro alice,
  apply exists.intro bob,
  split, 
  exact am,
  split,
  assumption,
  exact alab,
end

#check classical.em