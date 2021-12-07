import tactic.induction
import tactic.ring_exp  -- for split_ifs

def var_t := string

inductive term
-- | const : ℕ → term
| var : var_t → term  -- TODO: use de Bruijn indexing to avoid the shadowing madness
| lam : var_t → term → term
| app : term → term → term

namespace term
def repr : term → string
-- | (const c) := nat.repr c
| (var s) := s
| (lam x b) := "(λ" ++ x ++ ", " ++ repr b ++ ")"
| (app f x) := "(" ++ repr f ++ " " ++ repr x ++ ")"

instance : has_repr term := {repr := repr}

def cps_transform : term → term
-- | (const n) := const n
| (var x) := var x
| (lam x b) := lam x (lam "k" (match cps_transform b with
                               | (app f x) := app (app f x) (var "k")
                               | t := app (var "k") t
                               end))
-- Lean isn't able to prove these recursive calls well-founded if they're in a
-- match expression, so we have to do all pattern matching at top level
| (app f (app g y)) := app (app (cps_transform g) (cps_transform y))
                           (cps_transform f)
| (app f x) := app (cps_transform f) (cps_transform x)

/-
This takes the place of a match expression that would look like:
  match b' with
  | (app f x) := app (app f x) (var "k")
  | t := app (var "k") t
  end
-/
def cps_transform_cps_match_helper {α : Sort _} : term → (term → α) → α
| (app f x) k := k (app (app f x) (var "k"))
| t k := k (app (var "k") t)

def cps_transform_cps {α : Sort _} : term → (term → α) → α
-- | (const n) := const n
| (var x) k := k (var x)
| (lam x b) k := cps_transform_cps b (λb',
                   cps_transform_cps_match_helper b' (λl',
                     k (lam x (lam "k" (l')))))
-- Lean isn't able to prove these recursive calls well-founded if they're in a
-- match expression, so we have to do all pattern matching at top level
| (app f (app g y)) k := cps_transform_cps g (λg',
                           cps_transform_cps y (λy',
                             cps_transform_cps f (λf',
                               k (app (app g' y') f'))))
| (app f x) k := cps_transform_cps f (λf',
                   cps_transform_cps x (λx',
                     k (app f' x')))

-- TODO: define an eval function, then prove the CPS transform correct
-- def subst (v : var_t)
-- | (var s) := s

def subst (vname : var_t) (vval : term) : term → term
| (var x) := if x = vname then vval else var x
| (lam x b) := if x = vname then lam x b else lam x (subst b)
| (app f g) := app (subst f) (subst g)

#eval subst "x" (var "oops") (lam "y" (app (lam "q" (var "x")) (lam "x" (lam "x" (var "x")))))

inductive step : term → term → Prop
| app {x v b} : step (app (lam v b) x) (subst v x b)

def is_value (t : term) := ¬∃(t' : term), step t t'
def id_term := lam "x" (var "x")

#eval cps_transform (id_term)

lemma transform_spec : ∀ (t : term) (t' : term) (ht' : is_value t'), 
  step t t' → step (app (cps_transform t) id_term) t' :=
begin
  intros t t' ht' hstep,
  unfold is_value at ht',
  dsimp only [id_term],
  induction' t,
  case var {
    cases' hstep,
    -- TODO: this feels wrong
    -- rw cps_transform,
    -- dsimp only [id_term],
    -- have h : step ((lam "k" ((var "k").app (var x))).app (lam "x" (var "x"))) ((lam "x" (var "x")).app (var x)) :=
    -- begin
    --   have hh : ((lam "x" (var "x")).app (var x)) = subst "k" (lam "x" (var "x")) ((var "k").app (var x)) := begin
    --     cases' hstep,
    --     simp [subst],
    --     split_ifs,
    --     {
    --       cases' hstep,
    --     },
    --     {
    --       refl,
    --     }
    --   end
    -- end
  },
  case lam {
    cases' hstep,
    -- TODO: this also feels wrong - we should have some spec for where t (= t')
    -- is already a value
  },
  case app : t1 t2 ih_t1 ih_t2 {
    cases' hstep,
    -- Use an IH? IDK?
  }
end

def test := app (lam "x" (var "x")) (app (lam "y" (var "y")) ((lam "q" (var "q"))))

def s := repr test

#eval s

#eval (cps_transform test)

end term
