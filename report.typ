#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#let G = math.class("unary", sym.square.stroked)
#let F = math.class("unary", sym.lozenge.stroked)

#let Init = $I n i t$
#let Reach = $R e a c h$
#let New = $N e w$
#let Frontiers = $F r o n t i e r s$
#let Recur = $R e c u r$
#let PreReach = $P r e R e a c h$

#let Pre = text(font: "", smallcaps("Pre"))
#let Post = text(font: "", smallcaps("Post"))
#let Diff = text(font: "", smallcaps("Diff"))
#let Union = text(font: "", smallcaps("Union"))
#let Intersect = text(font: "", smallcaps("Intersect"))
#let IsSubset = text(font: "", smallcaps("IsSubset"))
#let IsEmpty = text(font: "", smallcaps("IsEmpty"))

#let Comment(comment) = ( [\/\/ #comment],)

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

As usual, it's easier to try to falsify the formula and look for a counterexample, rather than proving that the formula always holds. By falsifying the formula we get:

$
  not and.big_(i=1)^n (#G #F f_i -> #G #F g_i)
  &= or.big_(i=1)^n not (#G #F f_i -> #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and not #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and #F #G not g_i)
$

Since the outer operand is a disjunction it sufficies to find a trace that satisfies one of the inner formulas, and that will be a valid counterexample.

The problem thus reduces to showing a trace that satisfies a formula in the form $#G #F f_i and #F #G not g_i$, that is a trace where $f_i$ is satisfied repeatedly and $not g_i$ is satisfied persistently.

This is true if and only if there's a set of reachable states that satisfy $f_i$ and $not g_i$ and each state in the set can reach another state in the set by only going through states that satisfy $not g_i$.

To see why it is sufficient, consider a trace that first reaches one of the states in the set, which is possible because it is only made up of reachable states, and then repeatedly reaches another element of the set by only going through states that satify $not g_i$, which is possible by definition. This trace repeatedly visits states in the set, which satisfy $f_i$ and hence the trace satisfies $#G #F f_i$. It also persistently visits states that satisfy $not g_i$, because both the states in the sets and the states visited when reaching other states in the set all satisfy $not g_i$, and hence the trace satisfies $#F #G g_i$. Hence the criteria proposed is sufficient. 

To see why it is necessary, consider a trace that satisfies $#G #F f_i and #F #G not g_i$. Since it satisfies $#F #G not g_i$, that is persistently $not g_i$, there must exist a state $s_x$ in the trace from which point onward all states will satisfy $g_i$. Since the trace also satisfies $#G #F f_i$, that is repeatedly $f_i$, it means there must exist infinite states (possibly repeating) in the trace after $s_x$ that satisfy $f_i$. The set of those states is composed of states that:

- are reachable, because part of a trace;
- satisfy $f_i$, by definition;
- satisfy $not g_i$, because they appear after $s_x$ in the trace;
- can reach other states of the set going through only states that satisfy $not g_i$, because there is always another state further in the trace that's part of the set, and every state in the trace between them satisfy $not g_i$ due to appearing after $s_x$.

Hence the criteria proposed is necessary.

== Implementation

The implementation is made up of the following steps:

- parse the reactivity formula;

- compute the set of reachable states;

- for each pair of subformulas $(f_i, g_i)$, try to find a set of reachable states that satisfy $f_i$ and $not g_i$ and can reach a state in the set by only going through states that satisfy $g_i$;

- if it is found, try to find a loop in it to create the counterexample.

=== Parsing

The provided code already does implements the required checks to ensure a formula is a reactivity formula, however that is not enough since all the $f_i$ and $g_i$ are needed in order to implement the model checking. Hence the parsing function has been modified to return those formulas. In particular:

- `parse_react` has been modified to return a list of tuples, each containing a pair $(f_i, g_i)$ if the given formula is a reactivity formula, or `None` otherwise;

- `parse_implication` has been modified to return a tuple containing the pair $(f_i, g_i)$ if the given formula has the form $#G #F f_i -> #G #F g_i$ or `None` otherwise;

- `parse_GF_formula` has been modified to return the formula $f$ in case the given formula is in the form $G F f$ and $f$ is a boolean formula, or `None` otherwise.

=== Reachability

The set of reachable states is computed by repeatedly applying the #Post operator to the current frontier and removing all the states already seen from it in order to get the new frontier. The frontiers are also incrementally combined in order to form the set of reachable states. The list of frontiers is also kept since it will be useful when computing the counterexample trace.

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

=== Compute the repeating set of states

The repeating set detection works similarly to the repeating set detection for the formula $#G #F f_i$, that is it tries to compute the set of states $Recur$ that can reach another state in the same set $Recur$. The additional constraint that all the states needs to satisfy $not g_i$ is guaranteed by filtering out all the states that satisfy $g_i$ from the set of reachable states and the set of predecessors used in the search, that is replacing $Reach$ with $Diff(Reach, g_i)$ and $Pre(S)$ with $Diff(Pre(S), g_i)$.

#algorithm({
  import algorithmic: *
  Assign[$Recur$][$Intersect(Diff(Reach, g_i), f_i)$]
  While(cond: [*not* $IsEmpty(Recur)$], {
    Assign[$New$][$Diff(Pre(Recur), g_i)$]
    Assign[$PreReach$][$emptyset$]
    While(cond: [*not* $IsEmpty(New)$], {
      Assign[$PreReach$][$Union(PreReach, New)$]
      If(cond: [$IsSubset(Recur, PreReach)$], {
        Comment[Every state in $Recur$ can reach another]
        Comment[state in $Recur$ with at least 1 step and]
        Comment[only visiting states satisfying $g_i$.]
      })
      ([*end if*],)
      Assign[$New$][$Diff(Diff(Pre(New), g_i), PreReach)$]
    })
    Assign[$Recur$][$Intersect(Recur, PreReach)$]
    ([*end while*],)
  })
  ([*end while*],)
  ([ \/\/ There's no repeating set of states ],)
})

=== Building the counterexample

For building the counterexample the same approach as for building counterexamples for Repeatedly formulas is used. // TODO: continue explaining why the same approach works

#algorithm({
  import algorithmic: *
  // TODO
  // s = model.pick_one_state(recur)
  //   r = BDD.false()
  //   while True:
  //       new = model.post(s) & prereach
  //       frontiers = []
  //       while new.isnot_false():
  //           frontiers.append(new)
  //           if s.entailed(new):
  //               return execution_from_frontiers(model, frontiers, s)
  //           r = r + new
  //           new = (model.post(new) & prereach) - r
  //       r = r & recur
  //       s = model.pick_one_state(r)
})
