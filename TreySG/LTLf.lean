import Mathlib.Data.Finset.Basic
import TreySG.SGTrey

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

open LTLf

-- Previous constructor definitions with special characters:
--
-- | Constructor | Symbol | Meaning |
-- |------------|--------|---------|
-- | ◯ (φ : LTLf) | X | Next |
-- | U (φ ψ : LTLf) | U | Until |
-- | ◇ (φ : LTLf) | F | Eventually |
-- | □ (φ : LTLf) | G | Globally |

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
abbrev State := Finset PropVar  -- A state is a set of true propositions
abbrev Trace := List State  -- A trace is a finite sequence of states

instance [DecidableEq PropVar] : ∀ (s : Finset PropVar) (x : PropVar), Decidable (x ∈ s) := fun s x => s.decidableMem x

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

-- Check if the trace is satisfying starting at the beginning and running the full trace
def satisfyingTrace (σ : Trace) (ℓ : LTLf) : Bool := satisfies σ 0 ℓ


------------------
-- TREY SG EXAMPLE
------------------
def stopAtStopSigns : LTLf :=
-- Trey's Example: G((¬ 𝒉𝒂𝒔𝑺𝒕𝒐𝒑 ∧ X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑) → (X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑 U (𝒊𝒔𝑺𝒕𝒐𝒑𝒑𝒆𝒅 ∨ G 𝒉𝒂𝒔𝑺𝒕𝒐𝒑))
  □((¬{hasStop}) ∧ (◯{hasStop})) → (◯{hasStop}) U ({isStopped} ∨ (□{hasStop}))
  -- It must always be the case that (the outer □):
  -- whenever you encounter a new stop sign (you transition from not having a stop sign to next having a stop sign: (¬{hasStop}) ∧ (◯{hasStop}))
  -- then (→) starting from the time you have the stop sign (◯), you must continue to have the stop sign until you are stopped ((◯{hasStop}) U ({isStopped} ∨ ...)
  --          OR, you must have that stop sign for the rest of time (∨ (□{hasStop}))
  -- NB: the usage of hasStop until isStopped might better be understood as "isStopped must become true before hasStopped becomes false",
  -- i.e. you must stop (isStopped) before passing the stop sign (¬hasStop)
  -- NB: the final □{hasStop} is required so that it is not a violation if the trace ends while you are still stopped at the stop sign.

def eventuallyIsStopped : LTLf := (◇{isStopped})

-- Example trace
#reduce satisfyingTrace [{PropVar.hasStop}, {PropVar.isStopped}, {}] eventuallyIsStopped  -- Should return true
#reduce satisfyingTrace [{PropVar.hasStop}, {PropVar.isStopped}, {}] stopAtStopSigns  -- Should return true
-- this is the minimal non-accepting trace, no stop sign, then stop sign, then no stop sign, without stopping
#reduce satisfyingTrace [{}, {PropVar.hasStop}, {}] stopAtStopSigns  -- Should return false


-- Interface to extract state data from SceneGraphs
def extractFrame (sg : TreySG.SG.SceneGraph) : State := (if TreySG.SG.hasStop sg then {PropVar.hasStop} else {}) ∪ (if TreySG.SG.isStopped sg then {PropVar.isStopped} else {})

abbrev SGTrace := List TreySG.SG.SceneGraph
def extractTrace (sgs : SGTrace) : Trace := sgs.map extractFrame

def satisfyingSGTrace (sgs : SGTrace) (ℓ : LTLf) : Bool := satisfyingTrace (extractTrace sgs) ℓ
