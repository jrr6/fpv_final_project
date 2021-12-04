import tactic.induction
import tactic.ring_exp  -- for split_ifs
import .A_lists

/-
# 2. Trees
We'll prove CPS equivalences for the following tree functions:
* `inord`
* `fold`
* `find`

All higher-order functions are written as "fully-CPS" HOFs -- in particular,
any functional arguments must also be in CPS.
-/

inductive tree (α : Sort _)
| empty : tree
| node : α → tree → tree → tree

namespace tree

-- ## 2.1. `inord`
-- A basic inorder traversal of a tree
def inord {α : Sort _} : tree α → llist α
| tree.empty := llist.nil
| (tree.node x l r) := llist.append (inord l) (llist.cons x (inord r))

def inord_cps {α β : Sort _} : tree α → (llist α → β) → β
| tree.empty k := k llist.nil
| (tree.node x l r) k :=
  inord_cps l (λll,
    inord_cps r (λlr,
      llist.append_cps ll (llist.cons x lr) k
    )
  )

lemma inord_cps_equiv_inord {α β : Sort _} :
  ∀ (t : tree α) (k : llist α → β), inord_cps t k = k (inord t) :=
begin
  intro t,
  induction' t,
  case empty {
    intro k,
    refl,
  },
  case node : x l r ihl ihr {
    intro k,
    rw inord_cps,
    rw (ihl (λ (ll : llist α), r.inord_cps (λ (lr : llist α), ll.append_cps (llist.cons x lr) k))),
    dsimp only,  -- perform β-reduction
    rw (ihr (λ (lr : llist α), l.inord.append_cps (llist.cons x lr) k)),
    dsimp only,
    rw llist.append_cps_equiv_append,
    refl,  -- equivalently, rw ←inord
  }
end

-- ## 2.2. `fold`
-- A basic tree fold function
def fold {α β : Sort _} (f : α → β → β → β) (z : β) : tree α → β
| tree.empty := z
| (tree.node x l r) := f x (fold l) (fold r)

universe u
-- This has the same issue as the list foldr regarding type universes
-- def fold_cps {α : Sort _} {β γ : Sort u} (f : α → β → β → (β → γ) → γ) (z : β) :
--     tree α → (β → γ) → γ
-- | tree.empty k := k z
-- | (tree.node x l r) k := fold_cps l (λxl, fold_cps r (λxr, f x xl xr k))

def fold_cps {α β γ : Sort _} (f : α → β → β → (β → γ) → γ) (z : β) (t : tree α) :
    (β → γ) → γ :=
@tree.rec_on α (λ _, (β → γ) → γ) t
(λk, k z)
(λx l r lrec rrec k, lrec (λxl, rrec (λxr, f x xl xr k)))

-- Since using the recursor manually doesn't generate equation lemmas, we must
-- provide them manually
lemma fold_cps_eqn {α β γ : Sort _} (f : α → β → β → (β → γ) → γ) (z : β) (x l r) (k : β → γ) :
  fold_cps f z (tree.node x l r) k = fold_cps f z l (λxl, fold_cps f z r (λxr, f x xl xr k)) := rfl

lemma fold_cps_equiv_fold {α β γ : Sort _} :
  ∀ (f : α → β → β → β) (z : β) (t : tree α) (k : β → γ),
    fold_cps (λx l r k, k (f x l r)) z t k = k (fold f z t) :=
begin
  intros f z t,
  induction' t,
  case empty {
    intro k,
    refl,
  },
  case node : x l r ihl ihr {
    intro k,
    let f_cps := (λ(x : α) (l : β) (r : β) (k : β → γ), k (f x l r)),
    rw fold_cps_eqn,  -- would be "rw fold_cps" if we'd defined fold_cps normally
    rw (ihl f z (λxl, fold_cps f_cps z r (λxr, f_cps x xl xr k))),
    -- per the guidance at https://leanprover-community.github.io/extras/simp.html,
    -- we avoid simp in the middle of a proof; this is merely to achieve β-reduction
    dsimp only,
    rw (ihr f z (λ (xr : β), f_cps x (fold f z l) xr k)),
    refl,
  }
end


-- ## 2.3. `find`
-- A basic find function on a tree: finds the first (preordered) element
-- satisfying a decidable predicate p
def find {α : Sort _} (p : α → Prop) [decidable_pred p] : tree α → option α
| tree.empty := none
| (tree.node x l r) :=
  if p x
  then x
  else match find l with
       | none := find r
       | res := res
       end

/-
 A CPS version of find. We opt here for a simple success/failure continuation
 format; an alternative implementation might allow the predicate to pass
 "evidence" of success or failure to each continuation. For our purposes,
 however, this implementation seems reasonable (and already sufficiently
 complicated).
-/
def find_cps {α β : Sort _} (p : α → (unit → β) → (unit → β) → β) :
  tree α → (α → β) → (unit → β) → β
| tree.empty sk fk := fk ()
| (tree.node x l r) sk fk := p x (λ_, sk x) (λ_, find_cps l sk (λ_, find_cps r sk fk))

/-
 This helper lemma is slightly more general than the equivalence we want to
 prove because we need a more general induction hypothesis (namely, the failure
 continuation is not always (λ_, none) in recursive calls, so we can't restrict
 ourselves to that in the general proposition); we'll recover
 find_cps_equiv_find as an instance of this.
-/
lemma find_cps_equiv_find_helper {α : Sort _} (p : α → Prop) [decidable_pred p]  :
  ∀ (t : tree α) (fk : unit → option α),
    find_cps (λx sk fk, if p x then sk () else fk ()) t some fk = (find p t <|> fk ()) :=
begin
  intro t,
  induction' t,
  case empty {
    intro fk,
    rw [find_cps, find],
    unfold has_orelse.orelse,
    rw option.none_orelse',
  },
  case node : x l r ihl ihr {
    intro fk,
    rw find_cps,
    split_ifs,
    {
      -- case p x true
      rw find,
      split_ifs,
      exact with_top.some_eq_coe x,
    },
    {
      -- case p x false
      resetI,  -- deal with bug in synthesis of decidability type-class
      rw (ihr p fk),
      rw (ihl p (λ (_x : unit), find p r <|> fk ())),
      rw find,
      split_ifs, -- by case assumption, p x ==> false
      cases' (find p l),
      case some {
        -- case find p l ==> some x
        rw find._match_1,
        refl,
      },
      case none {
        -- case find p l ==> none
        rw find._match_1,
        unfold has_orelse.orelse,
        cases' (find p r),
        case some {
          -- case find p l ==> none AND find p r ==> some x
          rw option.none_orelse',
        },
        case none {
          -- case find p r ==> none AND find p r ==> none
          rw option.none_orelse',
        }
      }
    }
  }
end

-- We recover the desired equivalence as an instance of the helper
lemma find_cps_equiv_find {α : Sort _} (p : α → Prop) [decidable_pred p]  :
  ∀ (t : tree α),
    find_cps (λx sk fk, if p x then sk () else fk ()) t some (λ_, none) = find p t :=
begin
  intro t,
  have h := find_cps_equiv_find_helper p t (λ_, none),
  unfold has_orelse.orelse at h,
  have h_orelse : ∀(x : option α), option.orelse x none = x := λx, by cases' x; refl,
  rw h_orelse at h,
  exact h,
end

end tree
