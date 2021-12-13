import tactic.induction
import tactic.ring_exp  -- for split_ifs

set_option pp.generalized_field_notation false

inductive term
| var : ℕ → term
| lam : term → term
| app : term → term → term

namespace term
def repr : term → string
| (var n) := nat.repr n
| (lam b) := "(λ. " ++ repr b ++ ")"
| (app f x) := "(" ++ repr f ++ " " ++ repr x ++ ")"

instance : has_repr term := {repr := repr}

def incr_indices : term → term
| (var n) := var (n + 1)
| (lam b) := lam (incr_indices b)
| (app f x) := app (incr_indices f) (incr_indices x)

def cps_transform : term → term
| (var n) := var n
| (lam b) := lam (lam (match incr_indices (cps_transform b) with
                       | (app f x) := app (app f x) (var 0)
                       | t := app (var 0) t
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
| (app f x) k := k (app (app f x) (var 0))
| t k := k (app (var 0) t)

def incr_indices_cps {α : Sort _} : term → (term → α) → α
| (var n) k := k (var (n + 1))
| (lam b) k := incr_indices_cps b (λb', k (lam b'))
| (app f x) k := incr_indices_cps f (λf', incr_indices_cps x (λx', k (app f' x')))

def cps_transform_cps {α : Sort _} : term → (term → α) → α
| (var x) k := k (var x)
| (lam b) k := cps_transform_cps b (λb',
                 incr_indices_cps b' (λb'',
                   cps_transform_cps_match_helper b'' (λl',
                     k (lam (lam l')))))
-- Lean isn't able to prove these recursive calls well-founded if they're in a
-- match expression, so we have to do all pattern matching at top level
| (app f (app g y)) k := cps_transform_cps g (λg',
                           cps_transform_cps y (λy',
                             cps_transform_cps f (λf',
                               k (app (app g' y') f'))))
| (app f x) k := cps_transform_cps f (λf',
                   cps_transform_cps x (λx',
                     k (app f' x')))

-- Helper function for variable binding
-- The parameter is the variable to substitute in; the next argument is the
-- current binder depth (initially 0); and the last argument is the term into
-- which we're substituting
-- TODO: do we need to worry about de Bruijn indices here?
def subst_helper (vval : term) : ℕ → term → term
| vid (var n) := if n = vid then vval else var n
| vid (lam b) := lam (subst_helper (vid + 1) b)
| vid (app f g) := app (subst_helper vid f) (subst_helper vid g)

-- Substitutes the first argument as (var 0) of the second (i.e., this assumes
-- that the second argument is the *body* of some lambda -- do not include the
-- outermost binder!)
def subst : term → term → term := (λt, subst_helper t 0)

#eval lam (lam (app (lam (var 2)) (lam (lam (var 0)))))
#eval subst (var 42) (lam (app (lam (var 2)) (lam (lam (var 0)))))

inductive step : term → term → Prop
| app {x b} : step (app (lam b) x) (subst x b)

-- For testing:
def eval : term → term
| (app (lam b) x) := (subst x b)
| x := x

def is_value (t : term) := ¬∃(t' : term), step t t'
def id_term := lam (var 0)

#eval cps_transform (id_term)

-- We first prove some auxiliary lemmas about helper functions
lemma incr_indices_cps_equiv_incr_indices {α : Sort _} :
  ∀ (t : term) (k : term → α), incr_indices_cps t k = k (incr_indices t) :=
begin
  intros t k,
  induction' t,
  case var { refl, },
  case lam {
    rw [incr_indices_cps, ih],
    refl,
  },
  case app : f x ihf ihx {
    rw [incr_indices_cps, ihf, ihx],
    refl,
  }
end
lemma match_helper_cps_equiv_match {α : Sort _} :
  ∀ (t : term) (k : term → α),
    cps_transform_cps_match_helper t k = k (cps_transform._match_1 t) :=
begin
  intros t k,
  cases' t; refl,
end

-- Then prove that the CPS and non-CPS versions of the transform are equivalent
-- (Because Lean's well-foundedness checker *really* doesn't like strong
-- structural induction, we rely on term mode and its pattern-matching as much
-- as possible here)
lemma cps_transform_cps_equiv_cps_transform {α : Sort _} :
  ∀ (t : term) (k : term → α), cps_transform_cps t k = k (cps_transform t)
| (var n) k := rfl
| (lam b) k :=
  begin
    rw [cps_transform_cps,
        (cps_transform_cps_equiv_cps_transform b),
        incr_indices_cps_equiv_incr_indices,
        match_helper_cps_equiv_match],
    refl,
  end
| (app f (app g y)) k :=
  begin
    rw [cps_transform_cps,
        cps_transform_cps_equiv_cps_transform g,
        cps_transform_cps_equiv_cps_transform y,
        cps_transform_cps_equiv_cps_transform f],
    refl,
  end
| (app f (var n)) k :=
  begin
    rw [cps_transform_cps,
        cps_transform_cps_equiv_cps_transform f,
        cps_transform_cps_equiv_cps_transform (var n)],
    refl,
  end
| (app f (lam b)) k :=
  begin
    rw [cps_transform_cps,
        cps_transform_cps_equiv_cps_transform f,
        cps_transform_cps_equiv_cps_transform (lam b)],
    refl,
  end

-- A predicate enforcing the constraint that a term can only have de Bruijn
-- indices matching the number of nested binders at any given depth (the ℕ
-- parameter)
inductive valid_vars_at_depth : ℕ → term → Prop
| bound : valid_vars_at_depth 0 (lam (var 0))
| lam {b : term} : valid_vars_at_depth 1 b → valid_vars_at_depth 0 (lam b)
| app {f x : term} : valid_vars_at_depth 0 f →
                     valid_vars_at_depth 0 x →
                     valid_vars_at_depth 0 (app f x)

-- For a top-level expression, asserts that all de Bruijn indices are valid
def valid_vars := valid_vars_at_depth 0

-- TODO: may need to prove that stepping preserves valid var indices
-- (i.e., has_valid_var_indices t ∧ t => t' → has_valid_var_indices t')

def not_free_var (t : term) := ¬∃n, t = var n
-- Now we prove that the non-CPS transform does what it's supposed to
-- FIX(ED...I think)ME: this spec isn't nearly good enough. We need to be able to use IHs
-- about intermediate terms, so the var/lam cases need to say something useful
-- lemma transform_spec : ∀ (t : term) (t' : term) (ht' : is_value t'), 
--   step t t' → step (app (cps_transform t) id_term) t'
-- Take 2 - New spec:
#eval lam (lam (app (var 0) (var 1)))
#eval subst (lam (var 0)) (lam (app (var 0) (var 1)))
#eval (lam (app (var 0) (lam (var 0))))
lemma transform_spec : ∀ (t : term)
                         (ht : valid_vars t)
                         (t' : term)
                         (k : term), 
  step (app k t) t' → step (app (cps_transform t) k) t'
| (var n) ht t' k hstep := by cases' ht
| (lam b) ht t' k hstep :=
  begin
    rw cps_transform,
    cases' hstep,
    cases' b,
    {
      rw cps_transform,
      rw incr_indices,
      rw cps_transform._match_1,
      rw subst,
      dsimp only,
      cases' b_1,
      {
        rw subst_helper,
        cases' m,
        {
          split_ifs,
          {
            have hn : n = 0 := begin
              cases' ht,
              refl,
              cases' ht,
            end,
            rw hn,
            unfold has_add.add,
            dsimp only [nat.add],
            have h : subst (lam (app (var 0) (var 1))) (lam (var 0)) = (lam (app (var 0) (lam (var 0)))) := begin
              -- TODO: this
              sorry,
            end,
            have hstep1 : step (app (lam (lam (app (var 0) (var 1)))) (lam (var 0))) (lam (app (var 0) (lam (var 0)))) := step.app,
            -- TODO: something's not right...hstep1 doesn't step to the goal...
          },
          { apply false.elim (h rfl), }
        }
      }
    }
    /-
    cases' (cps_transform b),
    {
      rw incr_indices,
      rw cps_transform._match_1,
      cases' hstep,
      rw subst,
      dsimp only,
      cases' b_1,
      {
        rw subst_helper,
        cases' m,
        {
          simp,
          
        }
      }
    },
    apply transform_spec b,
    -/
  end
| (app f (app g y)) ht t' k hstep :=
  begin
    rw cps_transform,
  end
/-
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
    cases' x,
    {
      rw cps_transform,
      
      -- TODO: maybe the IH goes here?
      rw cps_transform,
      rw (ih_t1),
      rw cps_transform.incr_indices,
    }
    -- Use an IH? IDK?
  }
end
-/

def test := app (lam (var 0)) (app (lam (var 0)) ((lam (var 0))))

def s := repr test

#eval s

#eval (cps_transform test)

end term
