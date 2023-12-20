#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#let G = math.class("unary", sym.square)
#let F = math.class("unary", sym.lozenge)

#let var(s) = math.equation(s.clusters().map(s => [#s]).join([ ]))

#let Init = var("Init")
#let Reach = var("Reach")
#let New = var("New")
#let Frontier = var("Frontier")
#let Frontiers = var("Frontiers")
#let LoopFrontiers = var("LoopFrontiers")
#let Recur = var("Recur")
#let PreReach = var("PreReach")
#let True = var("True")
#let Trace = var("Trace")
#let Last = var("Last")

#let func(s) = text(font: "", smallcaps(s))

#let Pre = func("Pre")
#let Post = func("Post")
#let Diff = func("Diff")
#let Union = func("Union")
#let Intersect = func("Intersect")
#let IsSubset = func("IsSubset")
#let IsEmpty = func("IsEmpty")
#let PickOneState = func("PickOneState")
#let Reversed = func("Reversed")

#let emptyset = text("\u{2205}", font: ())

#set text(size: 12pt, font: "New Computer Modern")

#set page(numbering: "1")

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

The task asks to check whether a given model satisfies a given reactivity formula, that is a formula in the following form:

$
  and.big_(i=1)^n (#G #F f_i -> #G #F g_i)
$

and if it doesn't provide a counterexample.

It's easier to try to falsify the formula and look for a counterexample, rather than proving that the formula always holds. By falsifying the formula it becomes:

$
  not and.big_(i=1)^n (#G #F f_i -> #G #F g_i)
  &= or.big_(i=1)^n not (#G #F f_i -> #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and not #G #F g_i) = \
  &= or.big_(i=1)^n (#G #F f_i and #F #G not g_i)
$

Since the outer operand is a disjunction it sufficies to find a trace that satisfies one of the inner $#G #F f_i and #F #G not g_i$ formulas, and that will be a valid counterexample. The problem thus reduces to showing a trace where $f_i$ is satisfied repeatedly and $not g_i$ is satisfied persistently.

This is true if and only if there's a set $S$ of reachable states that satisfy $f_i$ and $not g_i$ and each state in $S$ can reach another state $S$ by only going through states that satisfy $not g_i$.

To see why this is sufficient, consider a trace that first reaches one of the states in $S$, which is possible because it is only made up of reachable states, and then repeatedly reaches another element of $S$ by only going through states that satify $not g_i$, which is possible by definition. This trace repeatedly visits states in $S$, which all satisfy $f_i$ and hence the trace satisfies $#G #F f_i$. It also persistently visits states that satisfy $not g_i$, because both the states in $S$ and the states visited when reaching other states in $S$ all satisfy $not g_i$, and hence the trace satisfies $#F #G g_i$. Hence the criteria proposed is sufficient. 

To see why it is necessary, consider a trace that satisfies $#G #F f_i and #F #G not g_i$. Since it satisfies $#F #G not g_i$ there must exist a state $s_x$ in the trace from which point onward all states $s_y$ with $y >= x$ will satisfy $g_i$. Since the trace also satisfies $#G #F f_i$ it means there must exist infinite states in the trace after $s_x$ that satisfy $f_i$. Let $S$ be the set of those states. $S$ is the required set because:

- all its states are reachable, because part of a trace;
- all its states satisfy $f_i$, by definition;
- all its states satisfy $not g_i$, because they appear after $s_x$ in the trace;
- any of its states can reach another state of $S$ by going through only states that satisfy $not g_i$, because there is always another state further in the trace that's part of the set, and every state in the trace between them satisfy $not g_i$ due to appearing after $s_x$.

Hence the property is necessary.

== Implementation

The implementation is made up of the following steps:

- parse the reactivity formula;
- compute the set of reachable states;
- for each pair of subformulas $(f_i, g_i)$, try to find a nonempty set $Recur$ of reachable states that satisfy $f_i$ and $not g_i$ and can reach a state in $Recur$ with at least one step and by only going through states that satisfy $g_i$;
  - if it is found, then the initial formula is false and try to find a state in $Recur$ that can reach itself with at least one step and by only going through states that satisfy $g_i$;
  - then use it to build the counterexample.
- if no set $Recur$ can be found for any subformula, then the initial formula must be true.

=== Parsing

The provided code already does implements the required checks to ensure a formula is a reactivity formula. The model checking however needs all the $f_i$ and $g_i$ formulas, hence the parsing function has been modified to return them in a list. In particular:

- `parse_GF_formula` has been modified to return the formula $f$ in case the given formula is in the form $G F f$ and $f$ is a boolean formula, or `None` otherwise.
- `parse_implication` has been modified to return a tuple containing the pair $(f_i, g_i)$ if the given formula has the form $#G #F f_i -> #G #F g_i$ or `None` otherwise;
- `parse_react` has been modified to return a list of tuples, each containing a pair $(f_i, g_i)$ if the given formula is a reactivity formula, or `None` otherwise;

=== Reachability

The set of reachable states is computed by repeatedly applying the #Post operator to the current frontier, starting from the initial set of states, and removing all the states already seen from it in order to get the new frontier. The frontiers are also incrementally combined to form the set of reachable states. The list of frontiers is kept in order to be used when computing the counterexample trace. The pseudocode for the algorithm is the following:

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

=== Computing the $Recur$ set

Computing the $Recur$ set is done in a very similar way to how it is computed for a simplier $#G #F f_i$ formula. The only difference in requirements is that both the states in $Recur$ and those visited while going from one state in $Recur$ to another must now satisfy $not g_i$. This is ensured by modifying the original algorithm to wrap any formula that may contain states not satisfying $g_i$ into a $Diff(-, g_i)$, namely $Reach$ and the results of the application of the $Pre$ operator. The result is that all the $PreReach$ and $New$ set of states are limited to contain only states that satisfy $not g_i$.

To compute $Recur$:

- initially the candidates are all the reachable states satisfying $f_i$ and $not g_i$;
- at each iteration the set $PreReach$ of states that can reach $Recur$ in at least one step and by only visiting states satisfying $not g_i$ is computed;
- if $Recur$ is a subset of $PreReach$ is must satisfy the criteria explained at the start of the report, hence it is evidence that the formula $#G #F f_i -> #G #F g_i$ is false;
- otherwise the states in $Recur$ that are not in $PreReach$ cannot be in the set satisfying the criteria and must be removed by intersecting $Recur$ and $PreReach$;
- if $Recur$ becomes empty then there's no set satisfying the criteria and the formula holds.

In each iteration the set $PreReach$ is also computed iteratively:

- it starts considering the set of state able to reach $Recur$ in exactly one step and satisfying $not g_i$;
- at each iteration it is updated with the states able to reach the previous $PreReach$ and satisfying $not g_i$, that is the states that can reach $Recur$ in at least exactly one more step than in the iteration before;
- this process stops when it reaches a fixpoint, that is no new state is added to $PreReach$.

The pseudocode for the algorithm is the following:

#algorithm({
  import algorithmic: *
  Assign[$Recur$][$Intersect(Diff(Reach, g_i), f_i)$]
  While(cond: [*not* $IsEmpty(Recur)$], {
    Assign[$New$][$Diff(Pre(Recur), g_i)$]
    Assign[$PreReach$][$emptyset$]
    While(cond: [*not* $IsEmpty(New)$], {
      Assign[$PreReach$][$Union(PreReach, New)$]
      If(cond: [$IsSubset(Recur, PreReach)$], {
        Cmt[Find a loop in $Recur$]
      })
      ([*end if*],)
      Assign[$New$][$Diff(Diff(Pre(New), g_i), PreReach)$]
    })
    ([*end while*],)
    Assign[$Recur$][$Intersect(Recur, PreReach)$]
  })
  ([*end while*],)
  Cmt[No repeating set of states]
})

=== Finding the loop

Finding the loop is also done very similarly to how it is built for simplier $#G #F f_i$ formulas. It picks a random state $S$ and tries to find a loop in $PreReach$ that leads back to $S$. Note that the use of $PreReach$ is both an optimization (if the loop exist then it must be in $PreReach$ because all the states in the loop satisfy its property) and needed to satisfy the requirement of every state in the trace having to satisfy $not g_i$, which states in $PreReach$ all do.

The algorithm thus reduces to:

- pick a random $S$ in $Recur$;
- compute the set of reachable states in $PreReach$ from $S$;
- if it contains $S$, then a loop has been found;
- if it doesn't contain $S$ then update $Recur$ to remove all the states not reached and try picking again.

To see why the last step is correct, consider the set of states in $Recur$ and reachable by $S$: they must reach another state in $Recur$, which is also reachable by $S$ and in $PreReach$, so it is in the new $Recur$. This other state in turn must also be able to reach another state in $Recur$, which is thus reachable by $S$ and also in $PreReach$. This process can continue until one of two situations happen:
- one state is able to reach a state already seen, which hence forms a loop;
- there are infinite states and this process continues forever, hence the algorithm will also continue forever, but will not return a wrong answer.

#algorithm({
  import algorithmic: *
  Assign[$S$][$PickOneState(Recur)$]
  Assign[$R$][$emptyset$]
  While(cond: [$True$], {
    Assign[$New$][$Intersect(Post(S), PreReach)$]
    Assign[$LoopFrontiers$][[ ]]
    While(cond: [*not* $IsEmpty(New)$], {
      ([Append #New to #LoopFrontiers],)
      If(cond: [$IsSubset(S, New)$], {
        Cmt[Build counterexample]
      })
      ([*end if*],)
      Assign[$R$][$Union(R, New)$]
      Assign[$New$][$Diff(Intersect(Post(New), PreReach), R)$]
    })
    Assign[$R$][$Intersect(R, Recur)$]
    Assign[$S$][$PickOneState(R)$]
    ([*end while*],)
  })
  ([*end while*],)
})

=== Build counterexample

In this step the frontiers from the loop reachability check and the initial reachability check are combined to create a trace that:

- reacheas the looping state $S$;
- reachaes again the looping state $S$ through states in $PreReach$, hence states satisfying $not g_i$.

Which is a trace that satisfies $#G #F f_i and #F #G not g_i$ and hence the counterexample to produce.

This is built backward:
- it starts by adding $S$ to the trace;
- it picks a random state that is in the second to last looping frontier and can reach $S$, assigns it to $S$ and add it to the trace;
  - note: the last frontier is the one containing $S$, which is already in the trace.
- it repeats this for all the previous looping frontiers;
- it finds the frontier from the initial reachability computation that first reached $S$;
- it picks a random state that is in the frontier and can reach $S$, assigns it to $S$ and add it to the trace;
- it repeats this for all the previous looping frontiers;
- it reverses the produced sequence of states to get the trace in the correct order.

This is correct because:
- by picking states in the frontiers the states picked are guaranteed reachable from the previous frontier;
- by picking states until the very first one in the frontiers of the initial reachibility computation they are guaranteed to end with a state in the initial set of states;
- by picking states that can reach the previous picked state the trace is guaranteed to be able to continue.

Hence this produces a valid trace reaching $S$ and its loop.

#algorithm({
  import algorithmic: *
  Assign[$Trace$][[$S$]]
  ([Remove the last frontier from $LoopFrontiers$],)
  For(cond: [$Frontier$ *in* $Reversed(LoopFrontiers)$], {
    Assign[$S$][$PickOneState(Intersect(Pre(S), Frontier))$]
    ([Append $S$ to $Trace$],)
  })
  ([*end for*],)

  While(cond: [*not* $IsSubset(S, Last(Frontiers))$], {
    ([Pop the last frontier from $Frontiers$],)
  })
  ([*end while*],)
  For(cond: [$Frontier$ *in* $Reversed(Frontiers)$], {
    Assign[$S$][$PickOneState(Intersect(Pre(S), Frontier))$]
    ([Append $S$ to $Trace$],)
  })
  ([*end for*],)
  ([Reverse $Trace$],)
})
