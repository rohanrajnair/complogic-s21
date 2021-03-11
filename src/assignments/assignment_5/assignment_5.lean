
namespace hidden 

universes u₁ u₂ u₃ 

def foldr {α : Type u₁} {β : Type u₂} : β → (α → β → β) → (list α → β)
| b f list.nil := b
| b f (h::t) := f h (foldr b f t) 

inductive group : Type  -- each value of type is a symmetry 
| R0 : group 
| R90 : group 
| R180 : group 
| R270 : group 
| H : group 
| V : group 
| D : group 
| D' : group 

open group 

def comp : group → group → group -- defining return type for 8*8 values in caley table
| R0 F := F
| F R0 := F
| R90 R90 := R180 
| R90 R180 := R270 
| R90 R270 := R0 
| R90 H := D'
| R90 V := D 
| R90 D := H 
| R90 D' := V 
| R180 R90 := R270 
| R180 R180 := R0 
| R180 R270 := R90
| R180 H := V 
| R180 V := H 
| R180 D := D' 
| R180 D' := D
| R270 R90 := R0 
| R270 R180 := R90 
| R270 R270 := R180 
| R270 H := D
| R270 V := D' 
| R270 D := V 
| R270 D' := H
| H R90 := D
| H R180 := V
| H R270 := D'
| H H := R0   
| H V := R180 
| H D := R90 
| H D' := R270 
| V R90 := D'  
| V R180 := H
| V R270 := D 
| V H := R180 
| V V := R0 
| V D := R270 
| V D' := R90 
| D R90 := V 
| D R180 := D' 
| D R270 := H 
| D H := R270 
| D V := R90 
| D D := R0 
| D D' := R180 
| D' R90 := H 
| D' R180 := D 
| D' R270 := V 
| D' H := R90 
| D' V := R270 
| D' D := R180 
| D' D' := R0


def comp_list : list group → group 
| list.nil := R0 
| l := foldr R0 comp l



def list1 : list group := [H, R90, R90, D]
def list2 : list group := [R90, R90, H]

#reduce comp_list list1 -- R270 
#reduce comp_list list2 -- V 


end hidden 