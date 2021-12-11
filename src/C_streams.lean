import tactic.induction
import data.stream.init
import .A_lists

set_option pp.generalized_field_notation false

/-
# 3. Streams
We'll prove CPS equivalences for a variety of non-CPS and CPS functions over CPS
streams (i.e., streams that are themselves implemented as a CPS type).

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
  stream_equiv s_cps s ↔
    stream_equiv (stream_cps.cons x s_cps) (stream.cons x s) :=
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
    stream_equiv s_cps s →
      stream_equiv (stream_cps.drop n s_cps) (stream.drop n s) :=
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
    stream_equiv (stream_cps.drop n s_cps) (stream.drop n s)
      → stream_equiv s_cps s) :=
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
-- Because we'll be using this in the next section, it is implemented as a full
-- CPS function, but we trivialize its continuation in the proof
-- def stream_cps.map {α β γ : Type _} (f : α → (β → γ) → γ)
--                                     (s : stream_cps α)
--                                     (k : stream_cps β → γ) : γ :=
def stream_cps.map {α β γ δ : Type _} (f : α → (β → γ) → γ)
                                    (s : stream_cps α)
                                    (k : stream_cps β → δ) : δ :=
k (λ(n : ℕ) (k' : β → γ), s n (λel, f el k'))

-- DELETE THIS once new one is working
-- lemma map_cps_equiv_map_old {α β γ : Type _} (f : α → β) :
--   ∀(s : stream α) (s_cps : @stream_cps α γ),
--   stream_equiv s_cps s → stream_equiv (stream_cps.map (λx k, k (f x)) s_cps id)
--                                         (stream.map f s) :=
-- begin
--   intros s s_cps hequiv n k,
--   rw [stream_cps.map,
--       id,
--       stream.map],
--   dsimp only,
--   rw stream.nth,
--   -- rw conveniently decides to do β-reduction for us...for once
--   rw ←hequiv n (λ (el : α), k (f el)),
-- end

lemma map_cps_equiv_map {α β γ δ : Type _} (f : α → β) :
  ∀(s : stream α) (s_cps : @stream_cps α γ)
    (k : @stream_cps β γ → δ)
    (k' : stream β → δ)
    (hks : ∀(s : stream_cps β) (s' : stream β),
        stream_equiv s s' → k s = k' s')
    (hequiv : stream_equiv s_cps s),
      stream_cps.map (λ(x : α) (k'' : β → γ), k'' (f x)) s_cps k =
      k' (stream.map f s) :=
begin
  intros s s_cps k k' hks hequiv,
  rw stream_cps.map,
  rw hks,
  intros n_se k_se,
  rw stream.map,
  dsimp only,
  rw stream.nth,
  -- rw conveniently decides to do β-reduction for us...for once
  rw ←hequiv n_se (λ (el : α), k_se (f el)),
end

/-
## 3.1.3. The corecursor term
TODO: explain!
-/

-- We implement a new rec_on that's in CPS
-- (I'm drawing the line at "type-level CPS" -- we'll leave the `motive`
-- as-is...)
def nat.rec_on_cps : Π {α : Sort _} {motive : ℕ → Sort _} (n : ℕ), motive 0 → (Π (n : ℕ), motive n → (motive n.succ → α) → α) → (motive n → α) → α
| α motive 0 val0 fn_succ k := k val0
| α motive (nat.succ n) val0 fn_succ k := nat.rec_on_cps n val0 fn_succ (λv_prev, fn_succ n v_prev k)

/-
This function got...interesting. To see what's going on, here are
implementations using the regular nat recursor (or an analogue) in SML (which
I think is a bit easier to parse in this instance) and Lean.

SML:
```
type ('a, 'b) stream_cps = int -> ('a -> 'b) -> 'b

fun stream_cps_iterate (f : 'a -> ('a -> 'b) -> 'b)
                       (a : 'a)
                       (outer_k : ('a, 'b) stream_cps -> 'c) = outer_k
(fn (n : int) => fn (k : 'a -> 'b) => let
  val rec res = (fn 0 => (fn (k' : 'a -> 'b) => k' a)
                  | n' => (fn (k' : 'a -> 'b) => res (n - 1)
                                                  (fn (prev : 'a) => f prev k'))
                )
in
  res n k
end)
```

Lean:
```
def stream_cps.iterate {α β γ : Type _} (f : α → (α → β) → β)
                                        (a : α)
                                        (outer_k : @stream_cps α β → γ) : γ :=
outer_k (λ(n : ℕ) (k : α → β),
@nat.rec_on (λ_, (α → β) → β)
              n
              (λ (k' : α → β), k' a)
              (λ (_ : ℕ) (r : (α → β) → β) (k' : α → β), r (λ(prev : α), f prev k'))
              k)
```

For wrapping your head around the full-CPS version, it's helpful to consider
that `motive n = ((α → β) → β)`, so `fn_succ` has type `(((α → β) → β) → γ) → γ`
-/
def stream_cps.iterate {α β γ : Type _} (f : α → (α → β) → β) (a : α) (outer_k : @stream_cps α β → γ) : γ :=
outer_k (λ(n : ℕ) (k : α → β),
  @nat.rec_on_cps _ (λ_, (α → β) → β)
              n
              (λ (k' : α → β), k' a)
              (λ (_ : ℕ) (r : (α → β) → β) (k' : ((α → β) → β) → β),
                k' (λ(inner_k : α → β), r (λ(prev : α), f prev inner_k)))
              (λnth_el_accessor, nth_el_accessor k)
                 -- the motive type takes a continuation; we ultimately need to
                 -- produce a β, so we use k to pass the value from the nat
                 -- recursion to the stream caller (but since here we're
                 -- effectively getting )
)

-- This is the analogue of the corecursor term stream.corec. The mathlib
-- implementation is a bit weird, but to make my proofs a little less painful,
-- I've decided just to mirror their dual-argument approach
def stream_cps.corec {α β γ δ : Type _} (f : α → (β → γ) → γ)
                                      (g : α → (α → γ) → γ) :
                                      α → (stream_cps β → δ) → δ :=
λ (a : α) (k : stream_cps β → δ),
  k (λ(n : ℕ) (k : β → γ),
    stream_cps.iterate g a (λs_seeds,
      stream_cps.map f s_seeds (λs, s n k)))

lemma nat_rec_on_cps_equiv_nat_rec_on {α β : Sort _} :
  ∀ {mot : ℕ → Sort _}
    (n : ℕ)
    (el0 : mot 0)
    (f_succ : Π(n' : ℕ), mot n' → mot (nat.succ n'))
    (k : mot n → α),
  k (@nat.rec_on mot n el0 f_succ) = nat.rec_on_cps n el0 (λn' x (k'), k' (f_succ n' x)) k
:=
begin
  intros mot n el0 f_succ k,
  induction' n,
  { refl, },
  {
    rw nat.rec_on_cps,
    dsimp only,  -- unfold nat.rec_on definition
    rw ←(ih el0 (λ (n' : ℕ) (x : mot n'), f_succ n' x)
                (λ (v_prev : mot n), k (f_succ n v_prev))),
  }
end

lemma iterate_cps_equiv_iterate {α β γ : Type _} :
  ∀ (f : α → α)
    (a : α)
    (k : stream_cps α → γ)
    (k' : stream α → γ)
    (hks : ∀(s : stream_cps α) (s' : stream α),
        stream_equiv s s' → k s = k' s'),
      (stream_cps.iterate (λ(x : α) (k'' : α → β), k'' (f x)) a k) =
      k' (stream.iterate f a) :=
begin
  intros f a k k' hks,
  rw stream_cps.iterate,
  rw hks,
  intros n k,
  dsimp only,
  rw ←(@nat_rec_on_cps_equiv_nat_rec_on β α),
  rw stream.iterate,
  dsimp only,
  -- FIXME: I really don't think we should need induction given that
  -- n_r_o_c_e_n_r_o "handles" the induction for us
  induction' n,
  { refl },
  {
    rw ←(ih f a k k' hks),
  },
end

lemma corec_cps_equiv_corec {α β γ δ : Type _} :
  ∀ (f : α → β) (g : α → α) (a : α) (k : @stream_cps β δ → γ) (k' : stream β → γ)
    (hks : ∀(s : stream_cps β) (s' : stream β),
        stream_equiv s s' → k s = k' s'),
    stream_cps.corec (λx k, k (f x)) (λx k, k (g x)) a k =
                 k' (stream.corec f g a) :=
begin
  intros f g a k k' hks,
  rw stream_cps.corec,
  dsimp only,
  rw hks,
  intros n_se k_se,
  rw stream.corec,
  dsimp only,
  let k_cand := λ (s : stream α), k_se ((stream.map f s) n_se),
  rw (iterate_cps_equiv_iterate g a _ k_cand),  -- _ = the CPS continuation
  {
    -- Proving that k_cand is an appropriate analogue of the CPS continuation
    intros s_candpf s'_candpf hequiv_candpf,
    dsimp only [k_cand],
    resetI,
    apply (map_cps_equiv_map f s'_candpf s_candpf _  -- _ = CPS continuation
            (λ(s : stream β), k_se (s n_se))),
    {
      -- Proving that the candidate continuation matches the CPS one for map
      intros s_map s'_map hequiv_map,
      dsimp only,
      apply eq.symm (hequiv_map n_se k_se),
    },
    exact hequiv_candpf,
  }
end

-- ### 3.1.4. cycle
-- Using our fancy new iterator and corecursor, we implement `cycle` analogously
-- to the built-in library (but in CPS, of course!) and then prove its
-- equivalence to the library implementation over regular streams
def stream_cps.cycle_f {α β : Type _} : α × list α × α × list α → (α → β) → β
| (v, _, _, _) k := k v

def stream_cps.cycle_g {α β : Type _} :
  α × list α × α × list α → (α × list α × α × list α → β) → β
| (v₁, [], v₀, l₀) k := k (v₀, l₀, v₀, l₀)
| (v₁, list.cons v₂ l₂, v₀, l₀) k := k (v₂, l₂, v₀, l₀)

def stream_cps.cycle {α β γ : Type _} :
  Π (l : list α), l ≠ [] → (@stream_cps α γ → β) → β
| []              h := absurd rfl h
| (list.cons a l) h := stream_cps.corec stream_cps.cycle_f stream_cps.cycle_g (a, l, a, l)

-- Just to "prove" it all works:
#eval @nat.rec_on (λ_, list ℕ)
                  20
                  []
                  (λn r, stream_cps.cycle [1, 9, 5, 1, 120]
                                          (by simp)
                                          (λs, s n (λel, r ++ [el])))

-- And now to **prove** it all works...
lemma cycle_cps_equiv_cycle {α β : Type _} :
  ∀ (l : list α) (hl : l ≠ []) (k : stream_cps α → β), stream_cps.cycle l hl k
-- TODO: this

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
