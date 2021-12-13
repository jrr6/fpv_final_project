# Non-Monadic Continuation Passing Style in Lean

For this project, I implemented a variety of continuation-passing-style
functions over common datatypes and proved their equivalence with non-CPS
analogues, with an eye toward detecting patterns in these proofs that might
enable their automation via metaprogramming. To this end, I placed considerable
value on minimality: I avoided using the simplifier or introducing any
additional axioms (especially classical ones) in my proofs (with one exception,
mentioned later), and I largely avoided using Lean's standard library (except
for in those cases in which I specifically wanted to examine the interaction
between user CPS code and standard-library built-ins). For this reason, I also
opted to consider CPS "purely," rather than in the context of Lean's system of
monads. To keep this project focused, and to work toward a thorough
understanding of the format of these proofs, I concentrated on specific
instances of CPS equivalences and observing the patterns therein, rather than
attempting to jump straight to metaprogramming.

Each section of my project is contained within a Lean file. Due to restrictions
on importable file names, the files are "lettered" rather than numbered (i.e.,
`A_lists.lean` corresponds to §1. Lists). Additionally, a summary of the data
structures and algorithms I considered, along with some highlights from each, is
provided below.

## A Table of Contents

1. Lists (`A_lists.lean`)
  1.1. `append`
  1.2. `map`
    1.2.1. `map_cps`
    1.2.2. `map_full_cps`
  1.3. `filter`
    1.3.1. `filter_cps`
    1.3.2. `filter_full_cps`
  1.4. `foldr`
    1.4.1. `foldr_cps`
    1.4.2. `foldr_full_cps`
2. Trees (`B_trees.lean`)
  2.1. `inord`
  2.2. `fold`
  2.3. `find`
3. Streams (`C_streams.lean`)
  3.1. The `stream_cps` Type
    3.1.1. Basic Stream Operations
    3.1.2. Basic Stream Equivalences
  3.2. CPS Functions on CPS Streams
    3.2.1. A(nother) Notion of Equivalence
    3.2.2. `map`
    3.2.3. The Corecursor Term (and Friends)
    3.2.4. The Big Finale: `cycle`
  3.3. CPS Functions on Non-CPS Streams
4. (Work in Progress) CPS Transform (`D_cps_transform.lean`)

## Lists: Highlights

TODO: highlights!

## Trees: Highlights

TODO: Highlights!

## Streams: Highlights

TODO: Highlights!
