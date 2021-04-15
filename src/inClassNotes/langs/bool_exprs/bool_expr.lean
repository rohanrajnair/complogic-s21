/-
true, 
false, 
true && false, 
(true && false) && true
-/

inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| and_expr : bool_expr → bool_expr → bool_expr
| or_expr : bool_expr → bool_expr → bool_expr 
| not_expr : bool_expr → bool_expr 

open bool_expr 

notation e1 && e2 := and_expr e1 e2
notation e1 || e2 := or_expr e1 e2 
notation !e1 := not_expr e1 
notation `[` b `]` := lit_expr b

def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e3 := and_expr (lit_expr tt) [ff]
def e4 := and_expr e3 [tt]

def e3' := [tt] && [ff]
def e4' := e3 && [tt]
def e5' := e3' || [tt]
def e6 := !e5' 

-- That's the syntax

-- Now for the semantics

def bool_eval : bool_expr → bool
| (lit_expr b) := b
| (and_expr e1 e2) := band (bool_eval e1) (bool_eval e2)
| (or_expr e1 e2) := bor (bool_eval e1) (bool_eval e2)
| (not_expr e1) := bnot (bool_eval e1)

#eval bool_eval e4'   -- ff
#eval bool_eval e5'   -- tt
#eval bool_eval e6    -- ff


theorem and_expr_symm : ∀ (e1 e2 : bool_expr), bool_eval (and_expr e1 e2) = bool_eval (and_expr e2 e1) := 
begin
  assume e1 e2,
  simp [bool_eval],
  cases bool_eval e1,
  cases bool_eval e2,
  apply rfl,
  apply rfl,
  cases bool_eval e2,
  apply rfl,
  apply rfl,
end 