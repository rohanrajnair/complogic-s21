/-
If P is a proposition, then so is ¬P.
We judge ¬P to be true when P is false:
when there is no proof of it at all. 
-/

#check not

/-
def not (a : Prop) := a → false
prefix `¬` := not
-/

lemma not_false' : ¬ false := λ f, f

/-
For any proposition, P, to prove ¬P,
assume that P is true and show that
that leads to a contradiction (in the
form of a proof of false). This is 
called "proof by negation." Remember:
¬P means P → false.
-/


-- neg elimination is not constructively valid

theorem neg_elim : ∀ (P : Prop), ¬(¬P) → P := 
λ P h, _  -- have proof of this "(P → false) → false", how to get to a proof of P?

-- not constructively valid 
-- law excluded middle 


/-
  P
¬ P → false
¬ (¬ P) → P   -- negation elimination
              -- double negation elimination
-/
