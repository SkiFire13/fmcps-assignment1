#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#let G = math.class("unary", sym.square.stroked)
#let F = math.class("unary", sym.lozenge.stroked)

#let Init = $I n i t$
#let Reach = $R e a c h$
#let New = $N e w$
#let Frontiers = $F r o n t i e r s$

#let Pre = text(font: "", smallcaps("Pre"))
#let Post = text(font: "", smallcaps("Post"))
#let Diff = text(font: "", smallcaps("Diff"))
#let Union = text(font: "", smallcaps("Union"))
#let Intersect = text(font: "", smallcaps("Intersect"))
#let IsSubset = text(font: "", smallcaps("IsSubset"))
#let IsEmpty = text(font: "", smallcaps("IsEmpty"))

#set text(size: 12pt, font: "New Computer Modern")

#align(center)[
  #heading[
    Formal Methods for Cyberphysical systems \
    Assignment 1
  ]

  #v(1em)

  #text(size: 15pt, "Stevanato Giacomo")

  #text(size: 15pt, "29/11/2023")
]

== Model checking strategy

The task requires us to check whether a given model satisfies a given reactivity formula, that is a formula in the following form:

$
  and.big_(i=1)^n (#G #F f_i -> #G #F g_i)
$

and if it doesn't provide a counterexample.

As usual, it is easier to try to falsify the formula and look for a counterexample, rather than proving that the formula always holds. By falsifying the formula we get:

$
  not and.big_(i=1)^n (#G #F f_i -> #G #F g_i)
  &= or.big_(i=1)^n not (#G #F f_i -> #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and not #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and #F #G not g_i)
$

Since the outer operand is a disjunction it sufficies to find a trace that satisfies one of the inner formulas, and that will be a valid counterexample.

The problem thus reduces to showing a trace that satisfies a formula in the form $#G #F f_i and #F #G not g_i$, that is a trace where $f_i$ is satisfied repeatedly and $not g_i$ is satisfied persistently.

If there exist a trace that satisfies the following property then it must eventually always satisfy $not g_i$, and from that point onward it must also repeatedly satisfy $f_i$. Hence it's enough to consider the set of reachable states that satisfy $not g_i$ and look there for a loop that includes a state that satisfies $f_i$, similarly to how it's possible to check Repeatedly formulas, that is formulas in the form $#G #F h$.

== Implementation

The implementation is made up of the following steps:

- parse the reactivity formula;

- computing the set of reachable states;

- for each pair of subformulas $(f_i, g_i)$, find a loop in the reachable states that satisfy $not g_i$ and contains at least a state that that satisfies $f_i$;

- if a loop is found, compute the counterexample trace containing it.

=== Parsing

The provided code already does implements the required checks to ensure a formula is a reactivity formula, however that is not enough since all the $f_i$ and $g_i$ are needed in order to implement the model checking. Hence the parsing function has been modified to return those formulas. In particular:

- `parse_react` has been modified to return a list of tuples, each containing a pair $(f_i, g_i)$ if the given formula is a reactivity formula, or `None` otherwise;

- `parse_implication` has been modified to return a tuple containing the pair $(f_i, g_i)$ if the given formula has the form $#G #F f_i -> #G #F g_i$ or `None` otherwise;

- `parse_GF_formula` has been modified to return the formula $f$ in case the given formula is in the form $G F f$ and $f$ is a boolean formula, or `None` otherwise.

=== Reachability

The set of reachable states is computed by repeatedly applying the #Post operator to the current frontier and removing all the states already seen from it. The frontiers are also incrementally combined in order to form the set of reachable states. The list of frontiers is also kept since it will be useful when computing the counterexample trace.

#algorithm({
  import algorithmic: *
  Assign[$Reach$][$Init$]
  Assign[$New$][$Init$]
  Assign[$Frontiers$][[ ]]
  While(cond: [*not* $IsEmpty(New)$], {
    ([Append #New to #Frontiers],)
    Assign[$New$][$Diff(Post(New), Reach)$]
    Assign[$Reach$][$Union(Reach, New)$]
  })
  ([*end while*],)
})

=== Loop detection

=== Building the counterexample

