import Mathlib.Data.Set.Basic

open Std

-- Define atomic propositions as a type (can be extended as needed)
inductive PropVar : Type
| hasStop | isStopped  -- Example propositional variables

deriving instance DecidableEq for PropVar

-- Define LTLf syntax
inductive LTLf : Type
| tt  -- True
| ff  -- False
| atom (p : PropVar)  -- Atomic proposition
| neg (φ : LTLf)  -- Negation
| conj (φ ψ : LTLf)  -- Conjunction
| disj (φ ψ : LTLf)  -- Disjunction
| impl (φ ψ : LTLf)  -- Implication
| next (φ : LTLf)  -- X (Next)
| until_ (φ ψ : LTLf)  -- U (Until)
| eventually (φ : LTLf)  -- F (Eventually, defined as U with true)
| globally (φ : LTLf)  -- G (Globally, defined via !F!φ)

-- Previous constructor definitions with special characters:
-- | ◯ (φ : LTLf)  -- X (Next)
-- | U (φ ψ : LTLf)  -- U (Until)
-- | ◇ (φ : LTLf)  -- F (Eventually)
-- | □ (φ : LTLf)  -- G (Globally)

-- Notation definitions
notation:max "¬" φ => LTLf.neg φ
notation:35 φ "∧" ψ => LTLf.conj φ ψ
notation:30 φ "∨" ψ => LTLf.disj φ ψ
notation:25 φ "→" ψ => LTLf.impl φ ψ
notation:40 "◯" φ => LTLf.next φ
notation:20 φ "U" ψ => LTLf.until_ φ ψ
notation:15 "◇" φ => LTLf.eventually φ
notation:15 "□" φ => LTLf.globally φ
notation "{hasStop}" => LTLf.atom PropVar.hasStop
notation "{isStopped}" => LTLf.atom PropVar.isStopped

open LTLf

-- Finite trace model: A trace is a list of state valuations
abbrev State := Set PropVar  -- A state is a set of true propositions
abbrev Trace := List State  -- A trace is a finite sequence of states

instance : DecidableEq PropVar := inferInstance
instance {α} [DecidableEq α] : DecidableEq (Set α) := fun s t => by sorry -- exactI inferInstance
instance {α} [DecidableEq α] : ∀ (s : Set α) (x : α), Decidable (x ∈ s) := fun s x => sorry -- Set.decidableMem s x

-- Satisfaction relation for LTLf semantics over finite traces
def satisfies : Trace → Nat → LTLf → Bool
| _, _, tt => true
| _, _, ff => false
| σ, i, atom p => (i < σ.length) && decide (p ∈ σ.get! i)
| σ, i, neg φ => ¬satisfies σ i φ
| σ, i, conj φ ψ => satisfies σ i φ ∧ satisfies σ i ψ
| σ, i, disj φ ψ => satisfies σ i φ ∨ satisfies σ i ψ
| σ, i, impl φ ψ => (!satisfies σ i φ) ∨ satisfies σ i ψ
| σ, i, ◯ φ => i + 1 < σ.length ∧ satisfies σ (i + 1) φ
| σ, i, until_ φ ψ => let indices := List.range' i (σ.length - i); List.any indices (λ j => satisfies σ j ψ && List.all (List.range' i (j - i)) (λ k => satisfies σ k φ))
| σ, i, eventually φ => let indices := List.range' i (σ.length - i); List.any indices (λ j => satisfies σ j φ)  -- Fφ ≡ true U φ
| σ, i, globally φ => let indices := List.range' i (σ.length - i); List.all indices (λ j => satisfies σ j φ)  -- Gφ ≡ ¬F¬φ

-- Example formula
def treyFormula : LTLf :=
  □ (
      (¬ {hasStop} ∧ ◯ {hasStop}) →
      (◯ {hasStop} U ({isStopped} ∨ □ {hasStop}))
    )

-- TODO: Improve this
-- Example trace check
-- Should return true
-- Provided some missing pieces are provided, provided, provided ...
#reduce satisfies [{PropVar.hasStop}, {PropVar.isStopped}, {}] 0 treyFormula
