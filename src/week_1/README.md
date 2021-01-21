# Introduction and terminology.

Here's an overview of some of the language I'll use in this document.

The Lean files in this directory contain
a bunch of little puzzle games. The aim is
to solve the puzzles. Let me start by
explaining some of the language I will use
below.

The "Lean infoview", or "infoview", is the
window on the right of Visual Studio Code,
which will typically be displaying
something like this in the middle of a proof:

```
P Q : Prop
hPQ : P → Q
hnQ : ¬Q
⊢ ¬P
```

This is the Tactic State -- the current state of Lean's brain in the middle of a proof.
You usually want to have "Tactic state"
open (triangle pointing down), and "All Messages" folded up (triangle pointing to the right).

If you have managed to close the infoview,
you can open it by clicking on the weird
symbol which looks like four rectangles piled
on top of each other in the top right of VS Code.
You can also press Ctrl-Shift-Enter (at least on a PC).

The Tactic State has two parts. There are the *local hypotheses*, or *assumptions*, e.g.

```
P Q : Prop
hPQ : P → Q
hnQ : ¬Q
```

In this case, they say that P and Q are
Propositions, i.e. true-false statements,
and that we have two hypotheses, namely
that `P` implies `Q` and that `not Q` is true.

As well as the hypotheses, there
is the *goal*, a true-false statement
written on the bottom line, and preceded
by a "turnstile", the sideways T. For
example, in the tactic state above, the goal
is

```
⊢ ¬P
```

The object of the game is to prove the goal.
When you do it, you will get the message

`goals accomplished`

accompanied by an adrenaline buzz.

You can cheat in the Lean game, by using
the `sorry` tactic, which closes the goal
for you. However, Lean keeps track of how
many times you have cheated: in the bottom
left of VS Code Lean will report how many
errors there are in your file (an x in a circle)
and how many warnings there are (an exclamation
mark in a triangle). Each `sorry` triggers a new
warning.

If your file is reporting no warnings and no
errors, you have proved all the theorems in the file!

# Tactics

Here are the tactics you will need to
prove this week's theorems.

## Part A : Logic

## The `intro` tactic.

If your goal is

```
⊢ P → Q
```

then the tactic

`intro hP,`

will turn your tactic state into

```
hP : P
⊢ Q
```

Variant: `intros` can be used to introduce
more than one assumption at once. Don't forget
to name your hypotheses, e.g. `intros hP hQ`.

## The `exact` tactic

If your tactic state is

```
hP : P
⊢ P
```

then the tactic

`exact hP,`

will close your goal.

Note: `exact P` does not work. Don't confuse
the *statement* `P` with its *proof* `hP`.

Note: The `assumption` tactic will also work. 

## The `apply` tactic

If your tactic state is

```
hPQ : P → Q
⊢ Q
```

then the tactic

`apply hPQ,`

will change it to

```
hPQ : P → Q
⊢ P
```

The `apply` tactic is useful for *arguing backwards*. It reduces the goal to a potentially easier goal, without changing any hypotheses.

## The `rw` tactic

The "rewrite" tactic can be used to "substitute in". The syntax is `rw h`, where `h` can be
either a local hypothesis, or a theorem.
However, `h` **must**  be either an equality or a bi-implication (an "iff"). You can use it on goals, but also on hypotheses (by adding `at`).

### Examples

1) If your local context is 

```
h : a = b
⊢ a + 1 = 37
```

then `rw h` will change it to
```
h : a = b
⊢ b + 1 = 37
```

2) If your assumptions contain 

```
h1 : P ↔ Q 
h2 : P → (R ∨ ¬ S) 
```

then `rw h1 at h2` will change them to
```
h1 : P ↔ Q 
h2 : Q → (R ∨ ¬ S) 
```

3) If `not_iff_imp_false` is a proof
of `¬ P ↔ (P → false)` and your goal
is 

```
⊢ ¬P → Q
```

then `rw not_iff_imp_false` will change
your goal to

```
⊢ (P → false) → Q
```

4) If your local context is
```
h : P ↔ Q 
⊢ ¬Q
```

then `rw h` will fail, because there are no
`P`s to be changed into `Q`s, and `rw` works
by default from left to right. To change the
goal from `¬Q` to `¬P`, try `rw ← h`. You
get the left arrow with `\l` (that's a little
letter L, not a number 1 or letter I).

### Note

`rw` works (**only**) with hypotheses of the
form `a = b` or `P ↔ Q`. A common mistake
is for users to try to use it with *implications*,
that is, hypotheses of the form `P → Q`. That is
what the `apply` tactic is for.

### Warning

The `rw` tactic tries `refl` 

## The `cases` tactic

`cases` is a very general-purpose
tactic for deconstructing hypotheses. If `h` is a hypothesis which 
somehow "bundles up" information, then
`cases h with h1 h2` (or perhaps `...with h1 h2 h3 h4` depending on how much is bundled) will make hypothesis `h` vanish and will replace it with the "components" which made the proof of `h` in the first place.

### Examples

If you have a hypothesis

```
hPaQ : P ∧ Q
```

then

`cases hPaQ with hP hQ` 

will delete `hPaQ` and replace it with

```
hP : P
hQ : Q
```

## The `split` tactic

If your goal is an "and" goal:

```
⊢ P ∧ Q
```

then the `split` tactic will turn it
into *two* goals


```
⊢ P
```

and

```
⊢ Q
```

It is best practice to indicate when you are working with two goals, either by using squiggly brackets like this:

```
...
split,
{ working on P,
  end of proof of P },
{ working on Q,
  end of proof of Q },
```

or by using indentation like this:

```
split,
  working on P,
  end of proof of P,
working on Q,
...
```

## The `left` and `right` tactics

If your goal is

```
⊢ P ∨ Q
```

then the `left` tactic will change it to

```
⊢ P
```

and the `right` tactic will change it to

```
⊢ Q
```

Note that these tactics are "dangerous" in the
sense that they can change a true goal into
a false one, and hence can stop you solving
a level. Use them wisely!