# Workshop 8 -- group cohomology

This is the final workshop of Kevin Buzzard's EPSRC Taught
Course Centre course on formalising matheamtics.

We're going to do group cohomology in low degrees,
developing the theory of 1-cocycles and coboundaries
from first principles and chasing some exact sequences around.
It's rather satisfying.

# Necessary background

Mathematically it would be useful if you were happy with the
concept of a group acting on an abelian group.

For Lean if you've played the natural number game then this would
help, -- you need to know what `rw h` means.

If you've done some of the earlier workshops then this
will help for some of the harder problems in this workshop.

# Lofty goals

- [ ] Definitions of `H0 G M` and `H1 G M` (the latter as 1-cocycles `Z1 G M` modulo 1-boundaries)

- [ ] G-module hom `M -> N` induces `H0 G M -> H0 G N` and `H1 G M -> H1 G N`.

- [ ] Connecting map `H0 G C` -> `H1 G A` coming from short exact sequence.

- [ ] Short exact sequence of G-modules gives seven term long-exact sequence of cohomology.

- [ ] Inf-res

- [ ] H2, more Inf-res, ten term long exact sequence of cohomology.

- [ ] n-cocycles and n-coboundaries.

- [ ] Hochshild-Serre spectral sequence.

# How do I do the workshop?

## The low-budget way

It's slow but it works. You have to wait until it says "Lean is ready" (not "Lean is busy") and you have to enable some cookies.

[click here to play Part A online](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_8%2FPart_A_G_modules.lean)

## The proper way

Step 1) Get started with Lean by installing the leanprover-community tool `leanproject`.
Follow the instructions at the [leanprover-community.github.io](https://leanprover-community.github.io/get_started.html) website.


Step 2) Install this Lean project by typing

```
leanproject get ImperialCollegeLondon/formalising-mathematics
```

Step 3) Check it's working: open any of the files in `src/week_8`, perhaps `Part_A_G_modules.lean`,
in VS Code. The orange bars should appear and then disappear fairly quickly.

Step 4) Fill in the sorrys. Hints are in the comments in the Lean file.

# I did a cool thing and would be fine about having it up on the Imperial College formalising-mathematics public github repo

Nice! Switch to a new branch of the project and we can try to get it there.

If you don't know about git: in the bottom left of VS Code (the editor you're using
to play Lean) there's a git weird-V-symbol and it probably says `master`. Click
on `master` and create a new branch, for example you could call your branch
`John_Smith-solutions_to_part_B` or `leanhacker237-some_stuff_on_cocycles` or whatever.
The only rule: the branch MUST COMPILE WITH NO ERRORS. The most professional-looking
files have no warnings either -- all mathlib files have no warnings, for example.

Now find the git symbol on the left hand bar of VS Code and go in there and commit
your changes to your branch. Then talk to me about ways to get your branch onto github.
You'll need to make a github account.
