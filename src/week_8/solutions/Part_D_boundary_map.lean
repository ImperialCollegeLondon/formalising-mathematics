/-

Boundary map
-/
import week_8.solutions.Part_C_H1
/-

# Boundary maps

If 0 → A → B → C → 0 is exact, we want
a boundary map `H0 G C →+ H1 G A`

We're going to use the axiom of choice in our definition.
Whenever we invoke the axiom of choice we are using something
noncomputable, so it's important that we make a proper API
for the object we construct.

-/

  [add_comm_group N] [distrib_mul_action G N]
namespace boundary_map

variables {G M N P : Type} [monoid G]
  [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N]
  [add_comm_group P] [distrib_mul_action G P]
  (φ : M →+[G] N) (ψ : N →+[G] P) (hφψ : is_short_exact φ ψ)

-- goal
def boundary_map : H0 G P →+ H1 G M :=
{ to_fun := λ p, Z1.quotient (_ : Z1 G M),
  map_zero' := _,
  map_add' := _ } 

/-

todo

boundary map def

boundary map API

7 term exact sequnce

inf-res

-/

def bound