import Mathlib.Data.Set.Basic

open Std

-- Define atomic propositions as a type (can be extended as needed)
inductive PropVar : Type
|  hasStop | isStopped -- Example propositional variables

deriving instance DecidableEq for PropVar

-- Define LTLf syntax
inductive LTLf : Type
| tt  -- True
| ff  -- False
| atom (p : PropVar)  -- Atomic proposition
| not (φ : LTLf)  -- Negation
| and (φ ψ : LTLf)  -- Conjunction
| or (φ ψ : LTLf)  -- Disjunction
| implies (φ ψ : LTLf)  -- Implication
| next (φ : LTLf)  -- X (Next)
| until (φ ψ : LTLf)  -- U (Until)
| eventually (φ : LTLf)  -- F (Eventually, defined as U with true)
| globally (φ : LTLf)  -- G (Globally, defined via !F!φ)

open LTLf

-- Finite trace model: A trace is a list of state valuations
abbrev State := Set PropVar  -- A state is a set of true propositions
abbrev Trace := List State  -- A trace is a finite sequence of states

instance : DecidableEq PropVar := inferInstance
instance {α} [DecidableEq α] : DecidableEq (Set α) := fun s t => by sorry -- exactI inferInstance
instance {α} [DecidableEq α] : ∀ (s : Set α) (x : α), Decidable (x ∈ s) := fun s x => sorry --Set.decidableMem s x


-- Satisfaction relation for LTLf semantics over finite traces
def satisfies : Trace → Nat → LTLf → Bool
| _, _, LTLf.tt => true
| _, _, LTLf.ff => false
| σ, i, LTLf.atom p => (i < σ.length) && decide (p ∈ σ.get! i)
| σ, i, LTLf.not φ => ¬satisfies σ i φ
| σ, i, LTLf.and φ ψ => satisfies σ i φ ∧ satisfies σ i ψ
| σ, i, LTLf.or φ ψ => satisfies σ i φ ∨ satisfies σ i ψ
| σ, i, LTLf.implies φ ψ => ¬satisfies σ i φ ∨ satisfies σ i ψ
| σ, i, LTLf.next φ => i + 1 < σ.length ∧ satisfies σ (i + 1) φ
| σ, i, LTLf.until φ ψ => let indices := List.range' i (σ.length - i); List.any indices (λ j => satisfies σ j ψ && List.all (List.range' i (j - i)) (λ k => satisfies σ k φ))
| σ, i, LTLf.eventually φ => let indices := List.range' i (σ.length - i); List.any indices (λ j => satisfies σ j φ)  -- Fφ ≡ true U φ
| σ, i, LTLf.globally φ => let indices := List.range' i (σ.length - i); List.all indices (λ j => satisfies σ j φ)  -- Gφ ≡ ¬F¬φ

-- Example trace
-- hasStop | isStopped
-- -- G((¬ 𝒉𝒂𝒔𝑺𝒕𝒐𝒑∧X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑)→(X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑 U (𝒊𝒔𝑺𝒕𝒐𝒑𝒑𝒆𝒅∨G 𝒉𝒂𝒔𝑺𝒕𝒐𝒑))

-- def hasStop :

def treyFormula : LTLf :=
  let hasStop : PropVar := sorry
  let isStopped : PropVar := sorry
  LTLf.globally
  (
    LTLf.implies
    (
      LTLf.and
      (LTLf.not (LTLf.atom hasStop))
      (LTLf.next (LTLf.atom hasStop))
    )
    (
      LTLf.until
      (LTLf.next (LTLf.atom hasStop))
      (LTLf.or
        (LTLf.atom isStopped)
        (LTLf.globally (LTLf.atom hasStop))
      )
    )
  )

-- TODO: Replace the example code with the what it is that we see and seek
#reduce satisfies [{PropVar.hasStop}, {PropVar.isStopped}, {}] 0 (LTLf.eventually (LTLf.atom PropVar.isStopped))  -- Should return true
