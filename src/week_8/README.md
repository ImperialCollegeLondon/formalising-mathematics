# Workshop 8 -- group cohomology

This is the final workshop of Kevin Buzzard's EPSRC Taiught
Course Centre. We're going to do group cohomology in low
degrees.

# Necessary background

Mathematically it would be useful if you were happy with the
concept of a group acting on an abelian group.

For Lean if you've played the natural number game then this would
help, and if you've done some of the earlier workshops, for example
workshop 4 on sets, then this would probably also help. A lot of the
earlier stuff doesn't need too much background at all, just a certain
amount of mathematical maturity.

# Installing the project

Step 1) Install the leanprover-community tool `leanproject` by following the
instructions at the leanprover-community.github.io website.


Step 2)

```
leanproject get ImperialCollegeLondon/formalising-mathematics
```

Step 3) Check it's working: open any of the files in `src/week_8`, perhaps `Part_A_G_modules`.
The orange bars should disappear fairly quickly.

# I did a cool thing and would be fine about having it up on the Imperial College formalising-mathematics public github repo

Nice! Switch to a new branch of the project and we can get it there.

If you don't know about git: in the bottom left of VS Code (the editor you're using
to play Lean) there's a git weird-V-symbol and it probably says `master`. Click
on `master` and create a new branch, for example you could call your branch
`John_Smith-solutions_to_part_B` or `leanhacker237-some_stuff_on_cocycles` or whatever.
The only rule: the branch MUST COMPILE WITH NO ERRORS. The most professional-looking
files have no warnings either -- all mathlib files have no warnings, for example.

Now find the git symbol on the left hand bar of VS Code and go in there and commit
your changes to your branch. To get further you will need to create an account at
github and then there are a couple of ways to proceed but let's worry about
that stuff later. The branch is the important thing. You can make more than one branch.

