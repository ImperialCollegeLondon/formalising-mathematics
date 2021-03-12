import group_theory.group_action.sub_mul_action

set_option old_structure_cmd true

structure sub_distrib_mul_action (G M : Type)
  [monoid G] [add_comm_group M]
  [distrib_mul_action G M]
extends sub_mul_action G M, add_subgroup M

variables {G M : Type}
  [monoid G] --`*`
  [add_comm_group M] --`+`
  [distrib_mul_action G M] --`•`

namespace sub_distrib_mul_action

-- now copy theorems from sub_mul_action if you want

def bot : sub_distrib_mul_action G M :=
{ carrier := {x | x = 0},
  smul_mem' := begin
    sorry,
  end,
  zero_mem' := sorry,
  add_mem' := sorry,
  neg_mem' := sorry }

variables {N : Type} [add_comm_group N] [distrib_mul_action G N]

def ker (φ : M →+[G] N) : sub_distrib_mul_action G M :=
{ carrier := {m | φ m = 0},
  smul_mem' := sorry,
  zero_mem' := sorry,
  add_mem' := sorry,
  neg_mem' := sorry }

def range (φ : M →+[G] N) : sub_distrib_mul_action G N :=
{ carrier := set.range φ,
  smul_mem' := sorry,
  zero_mem' := sorry,
  add_mem' := sorry,
  neg_mem' := sorry }
-- and range (φ : M →+[G] N) : sub_distrib_mul_action G N

-- that's what we're after

end sub_distrib_mul_action