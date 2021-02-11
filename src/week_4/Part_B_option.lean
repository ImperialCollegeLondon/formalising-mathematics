import tactic

/-

# Option

Much of this part is optional, if you just want to get to the
topology.

## The definition

If `X : Type` then `option X : Type` is a type with "one more element than `X`".
The disadvantage of type theory over set theory is that distinct types
are always disjoint. So if `x : X` then `x : option X` can't make sense.
The way it's set up is that there's a map called `some : X → option X`
which is an injection, and there's exactly one element of `option X`
which is not in the image, and it's called `none`.

## The API

Injectivity of `some` is 

`option.some_injective X : injective (some : X → option X)`

and it's implied by 

`option.some_inj : some a = some b ↔ a = b`

To define a function `option X → Y` we have to say  where `some x` goes
for `x : X`, and also where `none` goes. So we need a function `X → Y`
for `some` and a term `y : Y` for `none`. You make the function itself
with the recursor for `option`, namely `option.rec`. 

-/
variables {X Y : Type}

def g (f : X → Y) (y : Y) : option X → Y := λ t, option.rec y f t

-- I claim that `g` is the function we require. Note
-- that `g` takes `f` and `y` as explicit inputs 
-- so it's `g f y`. Its values on `none` and `some x` are *by definition*
-- what we want them to be:

variables (f : X → Y) (y : Y)

example : (g f y) none = y := 
begin
  refl
end

example (x : X) : (g f y) (some x) = f x :=
begin
  refl
end

-- That's all you need to know about `option` really, but 
-- it turns out that `option` is a `monad` so if you want to put
-- off doing topology you could do this instead.

-- https://en.wikipedia.org/wiki/Monad_%28category_theory%29

-- look at "formal definition"

-- option is a functor `Type → Type`; we've defined it on objects
-- so let's define it on morphisms:

def option_func (f : X → Y) : option X → option Y :=
λ t, option.rec none (some ∘ f) t

-- now check two functor axioms, `option_id` and `option_comp`

-- NB you can do `cases ox with x` on `ox : option X` to break down into the
-- `none` and `some x` cases.
lemma option_id : ∀ ox : option X, option_func (id : X → X) ox = ox :=
begin
  intro ox,
  cases ox with x,
  { refl },
  { refl }
end

variable (Z : Type)

lemma option_comp (f : X → Y) (g : Y → Z) (ox : option X) :
  option_func (g ∘ f) ox = (option_func g) (option_func f ox) :=
begin
  cases ox with x,
  { refl },
  { refl },
end


def eta {X : Type} : X → option X := some 

def mu {X : Type} : option (option X) → option X :=
-- function which sends `none` to `none` and `some ox` to `ox`
λ t, option.rec none id t

-- eta is a natural transformation

lemma eta_nat (f : X → Y) (x : X) : option_func f (eta x) = eta (f x) :=
begin
  refl,
end

-- mu is a natural transformation

lemma mu_nat (f : X → Y) (oox : option (option X)) :
  option_func f (mu oox) = mu (option_func (option_func f) oox) :=
begin
  cases oox,
  { refl },
  { refl }
end

-- coherence conditions (if I got them right!)

lemma coherence1 (ooox : option (option (option X))) :
  mu ((option_func mu) ooox) = mu (mu ooox) :=
begin
  cases ooox,
  { refl },
  { refl },
end

lemma coherence2a (ox : option X) : mu (eta ox) = ox :=
begin
  refl
end

lemma coherence2b (ox : option X) : mu (option_func eta ox) = ox :=
begin
  cases ox,
  { refl },
  { refl },
end