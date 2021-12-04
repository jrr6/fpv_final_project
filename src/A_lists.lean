import tactic.induction
import tactic.ring_exp  -- this gets us split_ifs, apparently

/-
# 1. Lists
We'll prove CPS equivalences for the following list functions:
* `append`
* `map`
* `filter`
* `foldr`

For higher-order functions, two CPS versions are provided:
* A "partial CPS" version, where higher-order arguments are taken in direct
  style; and
* A "higher-order CPS" version, where both the function and its function
  arguments are in CPS.

In this file, proofs are written out verbosely in calc mode to proide some
insight into where patterns that will hopefully emerge in more complex CPS-
equivalence proofs come from in simpler instances.
-/

inductive llist (α : Sort _)
| nil : llist
| cons : α → llist → llist

namespace llist

-- ## 1.1. `append`
-- A basic list append function
def append {α : Sort _} : llist α → llist α → llist α
| llist.nil ys := ys
| (llist.cons x xs) ys := llist.cons x (append xs ys)

-- List append in continuation-passing style
def append_cps {α β : Sort _} : llist α → llist α → (llist α → β) → β
| llist.nil ys k := k ys
| (llist.cons x xs) ys k := append_cps xs ys (λas, k (llist.cons x as))

lemma append_cps_equiv_append {α β : Sort _} :
  ∀ (xs ys : llist α) (k : llist α → β),
    append_cps xs ys k = k (append xs ys) :=
begin
  intros xs ys,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    calc append_cps (llist.cons x xs) ys k
         = append_cps xs ys (λas, k (llist.cons x as)) : rfl
     ... = (λas, k (llist.cons x as)) (append xs ys) : ih ys (λas, k
                                                              (llist.cons x as))
     ... = k (llist.cons x (append xs ys)) : rfl
     ... = k (append (llist.cons x xs) ys) : rfl
  }
end

-- ## 1.2. `map`
-- A basic list map function
def map {α β : Sort _} (f : α → β) : llist α → llist β
| llist.nil := llist.nil
| (llist.cons x xs) := llist.cons (f x) (map xs)

-- ### 1.2.1. `map_cps`
-- A "partial-CPS" map function: it returns via a continuation, but the mapping
-- function is not in CPS
def map_cps {α β γ : Sort _} (f : α → β) : llist α → (llist β → γ) → γ
| llist.nil k := k llist.nil
| (llist.cons x xs) k := map_cps xs (λxs', k (llist.cons (f x) xs'))

lemma map_cps_equiv_map {α β γ : Sort _} :
  ∀ (f : α → β) (xs : llist α) (k : llist β → γ),
    map_cps f xs k = k (map f xs) :=
begin
  intros f xs,
  -- The key is to induct *without* binding k!
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    calc map_cps f (llist.cons x xs) k
         = map_cps f xs (λxs', k (llist.cons (f x) xs')) : rfl
     ... = (λxs', k (llist.cons (f x) xs')) (map f xs) : ih f (λxs', k
                                                         (llist.cons (f x) xs'))
     ... = k (llist.cons (f x) (map f xs)) : rfl
     ... = k (map f (llist.cons x xs)) : by rw ←map
  }
end

-- ### 1.2.2. `map_full_cps`
-- A full ("higher-order") CPS map: it returns via a continuation, and its
-- function argument must also be in CPS
def map_full_cps {α β γ : Sort _}
  -- TODO: should we enforce parametricity of continuation over result type (since Lean, unlike SML, lets us)?
  -- (f : ∀ {δ : Sort _}, α → (β → δ) → δ) : llist α → (llist β → γ) → γ
  (f : α → (β → γ) → γ) : llist α → (llist β → γ) → γ
| llist.nil k := k llist.nil
| (llist.cons x xs) k := map_full_cps xs (λxs', f x (λx', k (llist.cons x' xs')))

-- TODO: remove me!
#check ∀ {α β δ : Sort _}, (∀ {γ : Sort _}, α → (β → γ) → γ) → llist α → (llist β → δ) → δ

lemma map_full_cps_equiv_map {α β γ : Sort _} :
  ∀ (f : α → β)
    (xs : llist α)
    (k : llist β → γ),
    map_full_cps (λx kf, kf (f x)) xs k = k (map f xs) :=
begin
  intros f xs,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    let f_cps := (λx (kf : β → γ), kf (f x)),
    calc map_full_cps f_cps (llist.cons x xs) k
         = map_full_cps f_cps xs (λxs', f_cps x (λx', k (llist.cons x' xs')))
            : rfl
         -- the below avoids having to rewrite f_cps
     ... = (λxs', f_cps x (λx', k (llist.cons x' xs'))) (map f xs) : by apply ih
     ... = f_cps x (λx', k (llist.cons x' (map f xs))) : rfl
     -- The lines below are technically superfluous, but nonetheless reassuring
     ... = (λx', k (llist.cons x' (map f xs))) (f x) : rfl
     ... = k (llist.cons (f x) (map f xs)) : rfl
     ... = k (map f (llist.cons x xs)) : rfl
  }
end

-- ## 1.3. `filter`
-- A basic list filter function
def filter {α : Sort _} (p : α → Prop) [decidable_pred p] : llist α → llist α
| llist.nil := llist.nil
| (llist.cons x xs) := if p x then llist.cons x (filter xs) else filter xs

-- ### 1.3.1 `filter_cps`
-- A "partial CPS" filter function: the result is returned using a continuation,
-- but the predicate returns a Prop directly
def filter_cps {α β : Sort _} (p : α → Prop) [decidable_pred p] :
    llist α → (llist α → β) → β
| llist.nil k := k llist.nil
| (llist.cons x xs) k := filter_cps xs (λxs', if p x  
                                              then k (llist.cons x xs')
                                              else k xs')

-- We'll use the fact that function application "distributes" over ite to enable
-- calc-mode proofs about filter to go through cleanly without casework
lemma ite_distro (γ δ : Sort _) (f : γ → δ) (x y : γ) (b : Prop) [decidable b] :
  (if b then f x else f y) = f (if b then x else y) := by split_ifs; refl

lemma filter_cps_equiv_filter {α β : Sort _} (p : α → Prop) [decidable_pred p] :
  ∀ (xs : llist α) (k : llist α → β),
    filter_cps p xs k = k (filter p xs) :=
begin
  intro xs,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    resetI,  -- deal with decidability type-class synthesis issues
    calc filter_cps p (llist.cons x xs) k 
         = filter_cps p xs (λxs', if p x then k (llist.cons x xs') else k xs')
            : rfl
     ... = (λxs', if p x then k (llist.cons x xs') else k xs') (filter p xs)
            : by rw ih
     ... = if p x then k (llist.cons x (filter p xs)) else k (filter p xs)
            : rfl
     ... = k (if p x then llist.cons x (filter p xs) else filter p xs)
            : by apply ite_distro
     ... = k (filter p (llist.cons x xs)) : by rw ←filter
  }
end

-- ### 1.3.2 `filter_full_cps`
-- A "full"/"higher order" CPS filter: the predicate is now also in CPS
def filter_full_cps {α β : Sort _} (p : α → (unit → β) → (unit → β) → β) :
  llist α → (llist α → β) → β
| llist.nil k := k llist.nil
| (llist.cons x xs) k := filter_full_cps xs
                                         (λxs', p x (λ _, k (llist.cons x xs'))
                                         (λ _, k xs'))

lemma filter_full_cps_equiv_filter {α β : Sort _}
                                   (p : α → Prop)
                                   [decidable_pred p] :
  ∀ (xs : llist α) (k : llist α → β),
  filter_full_cps (λ (x : α) (sk : unit → β) (fk : unit → β),
                    if p x then sk () else fk ())
                  xs
                  k
  = k (filter p xs) :=
begin
  intro xs,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    resetI,  -- deal with decidability type-class synthesis issues
    let p_cps := (λ (x : α) (sk fk : unit → β), if p x then sk () else fk ()),
    calc filter_full_cps p_cps (llist.cons x xs) k
         = filter_full_cps p_cps xs (λxs', p_cps x (λ _,
              k (llist.cons x xs')) (λ _, k xs')) : rfl
     ... = (λxs', p_cps x (λ _, k (llist.cons x xs')) (λ _, k xs'))
              (filter p xs) : by apply ih
     ... = p_cps x (λ _, k (llist.cons x (filter p xs)))
              (λ _, k (filter p xs)) : rfl
     ... = if p x then (λ _, k (llist.cons x (filter p xs))) ()
                  else (λ _, k (filter p xs)) () : rfl
     ... = if p x then k (llist.cons x (filter p xs)) else k (filter p xs) : rfl
     ... = k (if p x then llist.cons x (filter p xs) else filter p xs)
              : by apply ite_distro
     ... = k (filter p (llist.cons x xs)) : rfl
  }
end

-- ## 1.4. `foldr`
-- A standard list (right) fold
def foldr {α β : Sort _} (g : α → β → β) (z : β) : llist α → β
| llist.nil := z
| (llist.cons x xs) := g x (foldr xs)

-- ### 1.4.1 `foldr_cps`
-- A partial-CPS right fold: the result is returned via a continuation, but the
-- argument g is in direct style

-- Unfortunately, some compilation issues in Lean prevent this version from
-- working (we'd need to needlessly restrict β and γ to the same universe):
-- def foldr_cps {α β γ : Sort _} (g : α → β → β) (z : β)
--     : llist α → (β → γ) → γ
-- | llist.nil k := k z
-- | (llist.cons x xs) k := foldr_cps xs (λz', k (g x z'))

def foldr_cps {α β γ : Sort _} (g : α → β → β) (z : β) (l : llist α)
  : (β → γ) → γ :=
@llist.rec_on α (λ _, (β → γ) → γ) l
(λk, k z)
(λx xs r k, r (λ z', k (g x z')))

lemma foldr_cps_equiv_foldr {α β γ : Sort _} :
  ∀ (g : α → β → β) (z : β) (xs : llist α) (k : β → γ),
    foldr_cps g z xs k = k (foldr g z xs) :=
begin
  intros g z xs,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    calc foldr_cps g z (llist.cons x xs) k
         = foldr_cps g z xs (λz', k (g x z')) : rfl
     ... = (λz', k (g x z')) (foldr g z xs) : ih g z (λz', k (g x z'))
     ... = k (g x (foldr g z xs)) : rfl
     ... = k (foldr g z (llist.cons x xs)) : by rw foldr
  }
end

-- ### 1.4.2 `foldr_full_cps`
-- A full-CPS right fold: both g and the fold function are in CPS

-- Same issue as above
-- def foldr_full_cps {α β γ : Sort _} (g : α → β → (β → γ) → γ) (z : β)
--     : llist α → (β → γ) → γ
-- | llist.nil k := k z
-- | (llist.cons x xs) k := foldr_full_cps xs (λz', g x z' (λz'', k z''))

def foldr_full_cps {α β γ : Sort _} (g : α → β → (β → γ) → γ)
                                    (z : β)
                                    (l : llist α) : (β → γ) → γ :=
@llist.rec_on α (λ _, (β → γ) → γ) l
(λk, k z)
(λx xs r k, r (λz', g x z' (λz'', k z'')))

lemma foldr_full_cps_equiv_foldr {α β γ : Sort _} :
  ∀ (g : α → β → β) (z : β) (xs : llist α) (k : β → γ),
    foldr_full_cps (λa b k, k (g a b)) z xs k = k (foldr g z xs) :=
begin
  intros g z xs,
  induction' xs,
  {
    intro k,
    refl,
  },
  {
    intro k,
    let g_cps := (λ(a : α) (b : β) (k : β → γ), k (g a b)),
    calc foldr_full_cps g_cps z (llist.cons x xs) k
         = foldr_full_cps g_cps z xs (λz', g_cps x z' (λz'', k z'')) : rfl
     ... = (λz', g_cps x z' (λz'', k z'')) (foldr g z xs) : ih g z (λz',
                                                              g_cps x z'
                                                              (λz'', k z''))
     ... = g_cps x (foldr g z xs) (λz'', k z'') : rfl
     ... = k (g x (foldr g z xs)) : rfl
     ... = k (foldr g z (llist.cons x xs)) : rfl
  }
end

end llist
