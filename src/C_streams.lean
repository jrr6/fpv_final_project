import tactic.induction
import data.stream.init
import .A_lists

/-
# 3. Streams
We'll prove CPS equivalences for the following stream functions:
* `map`
* `filter`

We require that all stream functions be *maximally lazy*; that is, that they
perform no computation until it is necessary to produce a requested value.
-/

/- ## 3.1. The `stream_cps` Type
Due to the nature of streams (and Lean's current lack of support for coinductive
types over non-Prop universes), we can do something a little different here:
rather than re-write our *functions* to be in CPS, we can rewrite our *type* to
be in CPS. In this section, the functions are actually in direct style (as
explained further in §3.2, it wouldn't be very interesting for them to be in CPS
anyway), and we're interested in proving that a CPS *representation* of our data
is equivalent to a non-CPS representation. This was deceptively tricky to get
right!
-/

-- ### 3.1.1. Basic Stream Operations
-- We begin by defining a type of CPS streams and a few basic operations
-- thereupon
def stream_cps (α : Type _) {β : Type _} := ℕ → (α → β) → β

def stream_cps.expose {α β : Type _} (s : stream_cps α) (k : α → β) : β := s 0 k

def stream_cps.const {α β : Type _} (x : α) : stream_cps α :=
  (λ (n : ℕ) (k' : α → β), k' x)

def stream_cps.cons {α β : Type _} (x : α) (s : stream_cps α) : stream_cps α :=
  (λ (n : ℕ) (k' : α → β),
    match n with
    | 0 := k' x
    | nat.succ n := s n k'
    end)

def stream_cps.drop {α β : Type _} (n : ℕ) (s : stream_cps α) : stream_cps α :=
  λ (n' : ℕ) (k' : α → β), s (n' + n) k'

-- We define a notion of equivalence between a CPS stream and a regular stream
-- (I haven't quite wrapped my head around how Lean handles coinduction and
-- corecursion, but we can still use this to prove some interesting lemmas)
def stream_equiv {α β : Type _} (s_cps : stream_cps α) (s : stream α) :=
  ∀(n : ℕ) (k : α → β), k (s n) = s_cps n k

-- And use that equivalence to prove various equivalences between the primitive
-- CPS and non-CPS functions:
lemma const_cps_equiv_const {β : Type _} :
  @stream_equiv ℕ β (stream_cps.const 2) (stream.const 2) :=
λ _ _, rfl

lemma cons_cps_equiv_cons {α β : Type _} :
  ∀ (s_cps : @stream_cps α β) (s : stream α) (x : α),
  stream_equiv s_cps s ↔ stream_equiv (stream_cps.cons x s_cps) (stream.cons x s) :=
begin
  intros s_cps s x,
  apply iff.intro,
  {
    intros h_equiv n k,
    rw [stream_cps.cons, stream.cons],
    dsimp only,
    cases' n,
    { refl, },
    {
      rw [stream_cps.cons._match_1, stream.cons._match_1],
      exact h_equiv n k,
    }
  },
  {
    intros h_equiv n k,
    rw [stream_cps.cons, stream.cons] at h_equiv,
    have h_e_inst := h_equiv (nat.succ n) k,
    dsimp only at h_e_inst,
    rw [stream.cons._match_1, stream_cps.cons._match_1] at h_e_inst,
    exact h_e_inst,
  }
end

lemma drop_cps_equiv_drop {α β : Type _} :
  ∀ (s_cps : @stream_cps α β) (s : stream α) (n : ℕ),
    stream_equiv s_cps s → stream_equiv (stream_cps.drop n s_cps) (stream.drop n s) :=
begin
  intros s_cps s n,
  {
    intros h_equiv n' k',
    rw [stream_cps.drop, stream.drop],
    dsimp only,
    exact h_equiv (n' + n) k',
  }
end


-- Note that the `drop` lemma, unlike `cons_cps_equiv_cons`, isn't biconditional
lemma drop_equiv_not_bicond :
  -- TODO: why can't it be `Type _`?
  ¬(∀ α β : Type, ∀ (s_cps : @stream_cps α β) (s : stream α) (n : ℕ),
    stream_equiv (stream_cps.drop n s_cps) (stream.drop n s) → stream_equiv s_cps s) :=
begin
  intro h,
  let s_cps := @stream_cps.cons ℕ ℕ 4 (stream_cps.const 3),
  let s := stream.cons 2 (stream.const 3),

  have h_drop_equiv :
    stream_equiv (stream_cps.drop 1 s_cps) (stream.drop 1 s) :=
    λ_ _, rfl,

  have h_not_equiv : ¬(stream_equiv s_cps s) :=
  begin
    intro h_s_cps_equiv_s,
    dsimp only [s, s_cps] at h_s_cps_equiv_s,  -- expands s and s_cps defns
    have h_equiv_at_0 := h_s_cps_equiv_s 0 id,
    rw [stream.const, stream.cons, stream_cps.const, stream_cps.cons, id]
      at h_equiv_at_0,
    dsimp only at h_equiv_at_0,
    rw [stream.cons._match_1, stream_cps.cons._match_1, id] at h_equiv_at_0,
    -- Because where's the fun in using the simplifier?
    apply (@nat.no_confusion false 2 4 h_equiv_at_0)
          (λh', (@nat.no_confusion false 1 3 h') (λh'', nat.no_confusion h'')),
  end,
  have h_for_contra := h ℕ ℕ (@stream_cps.cons ℕ ℕ 4 (stream_cps.const 3))
                             (stream.cons 2 (stream.const 3)),
  exact absurd (h_for_contra 1 h_drop_equiv) h_not_equiv,
end

-- ### 3.1.2. `map`
-- A simple, maximally-lazy stream map
-- Again, this is in direct style, since the interesting part is dealing with
-- the CPS-ness of the streams themselves
def stream_cps.map {α β γ : Type _} (f : α → (β → γ) → γ) (s : stream_cps α) :
  stream_cps β :=
(λ(n : ℕ) (k' : β → γ), s n (λel, f el k'))

lemma map_cps_equiv_map {α β γ : Type _} (f : α → β) :
  ∀(s : stream α) (s_cps : @stream_cps α γ),
    stream_equiv s_cps s → stream_equiv (stream_cps.map (λx k, k (f x)) s_cps)
                                        (stream.map f s) :=
begin
  intros s s_cps hequiv n k,
  rw stream_cps.map,
  dsimp only,
  -- Technically, we could skip directly to "rw ←hequiv" at this point,
  -- but I leave the intervening steps as illustration of what's going on
  rw stream.map,
  dsimp only,
  rw stream.nth,
  -- rw conveniently decides to do β-reduction for us...for once
  rw ←hequiv n (λ (el : α), k (f el)),
end

/-
## 3.2. CPS Functions on Non-CPS Streams
We can also consider a more traditional case: our functions are in CPS, and we
abstract away the datatype. (Note that it wouldn't be very intersting to have a
"CPS functions on CPS streams" section since the only meaningful notions of
equivalence would involve reducing CPS calls to direct-style ones by passing
`id` as a continuation.)

Unfortunately, this turned out to be relatively uninteresting -- since streams
aren't inductively defined, the CPS functions essentially amount to applying
a continuation to a re-implementation of a library function. Just to illustrate
this point, I've included `boring_map_cps` below (note that it's pointless to
take a CPS `f` since the stream is not in CPS, so we'd just have to "de-CPS-ify"
`f` by passing `id` as a continuation), but the reader can imagine analogous
cases for most other stream functions:
-/

def boring_map_cps {α β γ : Type _} (f : α → β)
                                    (s : stream α)
                                    (k : stream β → γ) :=
  k (λn, f (s n))

lemma boring_map_cps_equiv_map {α β γ : Type _} :
  ∀ (f : α → β) (s : stream α) (k : stream β → γ),
  k (stream.map f s) = boring_map_cps f s k := λ_ _ _, rfl
