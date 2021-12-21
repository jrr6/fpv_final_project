# Continuation Passing Style in Lean

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
attempting to jump straight to metaprogramming, with the hope that familiarizing
myself with the properties of this proofs would more effectively allow me to
recognize the commonalities among them.

Each section of my project is contained within a Lean file. Due to restrictions
on importable file names, the files are "lettered" rather than numbered (i.e.,
`A_lists.lean` corresponds to §1. Lists). Additionally, a summary of the data
structures and algorithms I considered, along with some highlights from each, is
provided below. Finally, each file contains comments throughout each section,
summarizing the intent and methodology (and hopefully making some of the more
abstruse code a bit more digestible) in each portion of the project.

## A Table of Contents

(This outline is best viewed in plain text.)

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
4. (Work in Progress) CPS Transformation (`D_cps_transform.lean`)

## Lists

These proofs tended to follow a fairly straightforward pattern: induct on the
input list with the continuation free; handle the base case with reflexivity;
then in the inductive step (1) expand the CPS function definition, (2) apply the
IH with the continuation provided in the expanded definition, then (3) apply the
continuation to obtain the expansion of the non-CPS definition. "Full-CPS"
variations required the extra step of defining a CPS version of the given
function and then stepping its application, although this generally did not
prove to be especially challenging.

`filter` was somewhat more complicated due to the necessity of handling
conditional expressions. Rather than handle these through casework, I opted to
prove a lemma regarding the "distributivity" of function application over an
if-then-else expression. In the "non-full-CPS" `filter` that took only a single
continuation, this allowed the whole if-then-else expression to be treated as an
input to the continuation matching the form of the body of the non-CPS function.
In the full-CPS version, a similar maneuver is eventually possible once the
success and failure continuations have each individually been stepped. (This
makes more sense when actually examining the calc-mode proof.)

Lastly, I encountered a couple of quirks of Lean that would appear throughout
the project. For some reason, writing a CPS fold function using pattern-matching
results in an error message saying that Lean "failed to generate helper
declaration for smart unfolding." As a result, I ended up having to write my
fold functions with the `llist` recursor directly. (Traditional clausal
definitions are provided in comments in the file.) Additionally, due to how Lean
handles type class instance caching, some proofs require the `resetI` tactic to
ensure that decidability type class instances are recognized.

## Trees

The main feature differentiating tree proofs from list proofs was simply the
difference in the induction principle -- the general structure is now (1) step
the CPS function definition, (2) apply *both* IHs, and (3) step the direct-style
function definition. `inord` introduced the need to draw on existing CPS
equivalence lemmas (namely, `llist.append_cps_equiv_append`), another recurrent
theme of CPS equivalence proofs. `fold` encountered the same issue as
`llist.foldr` necessitating the use of the natural number recursor rather than
pattern matching.

`find` was the most interesting of the tree functions, largely because the
natural notion of equivalence (passing `some` and `const none` as continuations
to `find_cps`) is not the most general one -- and, in fact, it is not
sufficiently general to admit the inductive generality required to actually
prove it. As a result, the "natural" result had to be recovered as an instance
of a more general lemma considering arbitrary continuations.

## Streams

Since Lean does not support coinductive types outside of `Prop`, streams can't
be implemented using a coinductive declaration as in some other functional
languages. Instead, Lean implements streams as functions; for the CPS
implementation, therefore, I focused on considering CPS functions as a
*datatype* themselves. Unlike in prior sections, this one works with
mathlib-provided definitions, although this ended up having little effect on the
proofs themselves (some major initial issues were avoided by upgrading to the
latest version of mathlib, which moves streams out of the core library and
publicizes some previously private functions that rendered proofs extremely
difficult).

I initially consider direct-style functions that work with CPS streams and prove
their equivalence to their non-CPS mathlib counterparts, defining a notion of
CPS/non-CPS stream equivalence. I then move onto CPS functions over CPS streams,
defining a new notion of equivalence between CPS functions on CPS streams and
non-CPS functions on non-CPS streams, which requires a considerable amount of
abstraction in order to provide usable results (this is a much more involved
instance of the principle seen in the tree `find` proof: "natural" CPS
equivalences often aren't general enough to admit inductive use or use in other
proofs). Finally, I briefly note the uninteresting nature of implementing CPS
functions over direct-style mathlib streams.

Quite a few of the stream functions proved to be quite involved. Even the simple
`drop_equiv_not_bicond` required handling some type-universe headaches to
maintain the lemma's generality. `stream_cps.iterate`, which (to maintain full
CPS) required the implementation of a CPS recursor function `nat.rec_on_cps`,
ended up having type `(α → (α → β) → β) → α → ((ℕ → (α → β) → β) → γ) → γ`.
Note, however, that many of the CPS-on-CPS functions have types more general
than strict CPS would permit. This is due to the ambiguity of CPS when working
with a CPS datatype: if one treats CPS streams as a black-box datatype, then the
second type argument to the `stream_cps` type constructor is opaque, as is the
very fact that the streams are operating in CPS under the hood; therefore, the
continuation result type of any CPS stream operation need not be restricted by
the continuation type of the CPS stream itself. If, however, one considers CPS
streams as CPS functions themselves, then the continuation type of the overall
CPS function on the CPS stream must mirror that of the CPS stream itself; for
instance, the type of `iterate` could be "simplified" to
`(α → (α → β) → β) → α → ((ℕ → (α → β) → β) → β) → β`. This doesn't end up
having too much of an impact (beyond occasionally requiring one to turn to SML's
type inference to figure out which types go where in some untenably large and
convoluted expression) on the implementation of the functions and proofs
themselves, however.

The streams file culminates in the `stream_cps.cycle` function, which makes use
of the iterator, corecursor, and map functions defined previously in the file;
the CPS stream-CPS equivalence lemma uses the functions' associated lemmas to
produce a relatively painless proof (though this concision required the
introduction of the `funext` axiom, which a proof of the lemma statement need
not require). As mentioned, this was another theme of CPS equivalence proofs:
especially for larger functions, it was often a matter of defining a chain of
CPS equivalence lemmas for every helper function involved, then stringing those
together in an appropriate manner.

I cannot possibly envision a practical use case for CPS streams. But for trying
to wrap one's brain around continuation-passing style and proofs thereover,
they're an excellent exercise.

## (Work in Progress) CPS Transformation

(Because this work is ongoing and still rough around the edges, it has been
moved to the `development` branch of this repository.)

This portion of the project is still a work in progress -- there are almost
certainly still a plethora of bugs, slightly-off theorem statements, and
less-than-optimal design choices. The basic idea was to (1) define (very simple)
CPS transforms over the untyped lambda calculus in both direct and
continuation-passing styles; (2) prove that the CPS and non-CPS transforms are
CPS-equivalent; (3) prove that the (direct-style) CPS transform produces a
program equivalent to its input; and finally (4) prove, using (2) and (3), that
the CPS CPS transform also produces an equivalent program. I was able to
complete steps 1 and 2, although my ongoing work on step 3 suggests that my work
in step 1 may still have some bugs to iron out.

Since the file is still under development, it's a bit messier than those that
precede it. The lemma `cps_transform_cps_equiv_cps_transform` proves the
CPS-equivalence of `cps_transform` and `cps_transform_cps`. The `sorry`-filled
lemma `transform_spec` is intended to be a proof that `cps_transform` obeys its
specification, although it appears that it currently may not.

Much of the headache in this section is due to de Bruijn indexing, in part
because it makes the `repr` expressions generated during debugging relatively
inscrutable. (It might be worth trying to pretty-print a little more
effectively.) It also creates a lot of indexing overhead whenever transforming
or stepping expressions. The decision not to create any formal scaffolding
around the CPS transformation also increases the difficulty of reasoning and
debugging.
