# Formalising Mathematics

Repository for the Jan-Mar 2021 EPSRC TCC course on formalising mathematics, delivered to mathematicians at Imperial, Oxford, Bristol, Bath and Warwick.

## What is this?

In this course, we're going to be turning maths theorems into levels of a computer game called Lean. We'll start off with proving basic stuff like composite of injective functions is injective. We'll move on to harder mathematics as the course goes on. The course comprises 8 workshops. You don't have to do all the questions in each workshop.

## What mathematics is covered?

I took the slightly unconventional approach of blogging about each workshop rather than writing a formal document. Here are links to the eight workshop blog posts (plus an introductory post which explains my motivations for teaching the course):

0) [Introduction](https://xenaproject.wordpress.com/2021/01/21/formalising-mathematics-an-introduction/)
1) [Logic, sets, functions, relations](https://xenaproject.wordpress.com/2021/01/24/formalising-mathematics-workshop-1/)
2) [Groups and subgroups](https://xenaproject.wordpress.com/2021/01/28/formalising-mathematics-workshop-2/)
3) [Sequences and limits](https://xenaproject.wordpress.com/2021/02/04/formalising-mathematics-workshop-3/)
4) [Topology](https://xenaproject.wordpress.com/2021/02/10/formalising-mathematics-workshop-4/)
5) [Filters](https://xenaproject.wordpress.com/2021/02/18/formalising-mathematics-workshop-5-filters/)
6) [Limits](https://xenaproject.wordpress.com/2021/02/25/formalising-mathematics-workshop-6-limits/)
7) [Quotients](https://xenaproject.wordpress.com/2021/03/04/formalising-mathematics-workshop-7-quotients/)
8) [Group cohomology](https://xenaproject.wordpress.com/2021/03/15/formalising-mathematics-workshop-8-group-cohomology/)

# Prerequisites?

You should know some mathematics. For example if you're a second year undergraduate you should easily be able to be able to solve the levels from first few weeks.

You should also get Lean 3 and the community tools installed on your computer. This is unfortunately not as simple as it could be. [Here are the instructions](https://leanprover-community.github.io/get_started.html) . It's recommended that you follow them to the letter.

# How to play?

Assuming you have Lean and the user tools installed, first install the repository by firing up a command line, navigating to the directory you want to install this project in, and then typing

```
leanproject get ImperialCollegeLondon/formalising-mathematics

code formalising-mathematics
```

and then open up some of the files in `src/week1` and you're up and running. Look at the `README.md` file in `src/week1` for more instructions. Fill in the `sorry`s. Try a couple of levels of the [natural number game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/) if you're not sure what's going on.

Important note: if you just use `git clone` or some "download zip file" option on github then it won't work; you will not have access to Lean's maths library if you try this way (so imports won't work etc). 

# I failed/couldn't be bothered to install Lean

Well, you can always play along using the community web editor. Here are the four worlds for week 1. You might have to wait for a minute or so until "Lean is busy..." becomes "Lean is ready!". Also, feel free to ask for assistance on the [Lean Zulip chat](https://leanprover.zulipchat.com/) (login required, real names preferred, be nice). 

[logic](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_A_logic.lean)

[sets](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_B_sets.lean)

[functions](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_C_functions.lean)

[relations](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_D_relations.lean)
