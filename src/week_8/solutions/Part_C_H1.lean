import week_8.solutions.Part_B_H0

/-

# A crash course in H¹(G,M)

We stick to the conventions that `G` is a group (or even
a monoid, we never use inversion) and that `M` is a `G`-module,
that is, an additive abelain group with a `G`-action.

A 1-cocycle, or a twisted homomorphism, is a function
`f : G → M` satisfying the axiom
`∀ (g h : G), f (g * h) = f g + g • f h`. These things
naturally form an abelian group under pointwise addition
and negation, by which I mean "operate on the target":
`(f₁ + f₂) g = f₁ g + f₂ g`. We're not going to do higher
cocycles today so let me just call these things cocycles.

Let `Z1 G M` denote the abelian group of cocycles. 
There is a subgroup `B1 G M` of coboundaries, consisting
of the functions `f` for which there exists `m : M`
such that `f g = g • m - m` (one easily checks that
such functions are cocycles). The quotient group `H1 G M`,
written `H¹(G,M)` by mathematicians, the main definition
in this file. The first two theorems we shall prove about it here
are that it is functorial (i.e. a map `φ : M →+[G] N` gives
rise to a map `φ.H1_hom : H1 G M →+ H1 G N`), and exact in the
middle (i.e. if `0 → A → B → C → 0` is a short exact sequence
of `G`-modules then the sequence `H1 G A →+ H1 G B →+ H1 G C`
is exact).

The final boss of this course is verifying the first seven
terms of the long exact sequence of group cohomology
associated to a short exact sequence of groups, and this
involves one final definition, namely the connecting map
from `H0 G C` to `H1 G A` associated to a short exact
sequence `0 → A → B → C → 0`. We define the map explicitly
(there is a choice of sign) and make a small API for it.

Further work would be to verify "inf-res", otherwise known
as the beginning of the long exact
sequence of terms of low degree in the Hochschild-Serre
spectral sequence for group cohomology (i.e.
`0 → H¹(G/N, Aᴺ) → H¹(G, A) → H¹(N, A)` ) and of course to
construct the Hochschild-Serre spectral sequence itself,
which would involve defining group cohomology in all degrees
rather than just degrees zero and one. I have no doubt that
these kinds of results could be turned into a research paper.

Let's start with a definition of `H1 G M`
-/

-- 1-cocycles
def Z1 (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : Type :=
{m : M // ∀ g : G, g • m = m }

#exit

To do

H1 def

H1 exact in the middle

boundary map def

boundary map API

7 term exact sequnce

inf-res