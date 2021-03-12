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

namespace boundary_map

variables {G M N P : Type} [monoid G]
  [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N]
  [add_comm_group P] [distrib_mul_action G P]
  (φ : M →+[G] N) (ψ : N →+[G] P) (hφψ : is_short_exact φ ψ)


-- goal -- currently sorried definition!
def boundary_map : H0 G P →+ H1 G M :=
{ to_fun := λ p, Z1.quotient (
  { to_fun := λ g, (sorry : M),
    is_cocycle := sorry } : Z1 G M),
  map_zero' := sorry,
  map_add' := sorry } 

/-

todo
In Part D of this week's workshop we will define
a boundary map `H0 G C →+ H1 H A` coming from a short
exact sequence of `G`-modules. In this definition we make
a choice of sign ("do we use `g b - b` or `b - g b`?"). 
The final boss of this course
is verifying the first seven terms of the long exact sequence
of group cohomology associated to a short exact sequence of
G-modules.

TODO

boundary map def

boundary map API

7 term exact sequnce

inf-res

-/

def bound