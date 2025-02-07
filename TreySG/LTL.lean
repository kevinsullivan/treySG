import Mathlib.Data.Set.Basic

/- @@@
-- 1. Atomic Propositions (`prop`). To be replaced.
@@@ -/
inductive prop
  | hasStop | isStopped     -- Regular atomic propositions
  | TrueProp     -- Special proposition representing "true"
deriving Repr, BEq

/- @@@
-- 2. Define LTL Syntax
@@@ -/

inductive LTL (prop : Type) : Type where
  | atom : prop → LTL prop
  | neg  : LTL prop → LTL prop
  | and  : LTL prop → LTL prop → LTL prop
  | or   : LTL prop → LTL prop → LTL prop
  | implies : LTL prop → LTL prop → LTL prop  -- Added implication
  | next : LTL prop → LTL prop
  | globally : LTL prop → LTL prop
  | eventually : LTL prop → LTL prop
  | until : LTL prop → LTL prop → LTL prop
deriving Repr, BEq

/- @@@
-- 3. Define Büchi Automaton Structure
@@@ -/
structure BuchiAutomaton (State prop : Type) where
  states : Set (Set (LTL prop))  -- Each state is a subset of the LTL closure
  alphabet : Set (Set prop)       -- Each letter is a set of atomic propositions
  transitions : Set (Set (LTL prop) × Set prop × Set (LTL prop))  -- Transition relation
  initial : Set (LTL prop)        -- Initial state (contains original formula)
  accepting : Set (Set (LTL prop)) -- Accepting states (ensure fairness)

/- @@@
4. Compute the Closure of an LTL Formula
@@@ -/
def closure {prop : Type} [BEq prop] (trueProp : prop) : LTL prop → Set (LTL prop)
  | LTL.atom p => {LTL.atom p, LTL.neg (LTL.atom p)}
  | LTL.neg φ  => closure trueProp φ ∪ {LTL.neg φ, φ}
  | LTL.and φ ψ => closure trueProp φ ∪ closure trueProp ψ ∪ {LTL.and φ ψ}
  | LTL.or φ ψ => closure trueProp φ ∪ closure trueProp ψ ∪ {LTL.or φ ψ}
  | LTL.implies φ ψ => closure trueProp φ ∪ closure trueProp ψ ∪ {LTL.implies φ ψ}
  | LTL.next φ => closure trueProp φ ∪ {LTL.next φ}
  | LTL.globally φ => closure trueProp φ ∪ {LTL.globally φ, LTL.next (LTL.globally φ)}
  | LTL.eventually φ => closure trueProp φ ∪ {LTL.eventually φ, LTL.until (LTL.atom trueProp) φ}
  | LTL.until φ ψ => closure trueProp φ ∪ closure trueProp ψ ∪ {LTL.until φ ψ, ψ}

/- @@@
-- 5. Construct Büchi Automaton from an LTL Formula
@@@ -/
def ltlToBuchi {prop : Type} [BEq prop] (trueProp : prop) (φ : LTL prop) : BuchiAutomaton (Set (LTL prop)) prop :=
  let cl := closure trueProp φ  -- Compute closure (all subformulas)
  let states := { s | s ⊆ cl }  -- States are subsets of the closure

  -- Define possible atomic propositions (Fix: Explicitly define `alphabet`)
  let alphabet := { pSet : Set prop | ∀ p, p ∈ pSet → ∃ q, q = LTL.atom p ∧ q ∈ cl }

  -- Transition Relation
  let transitions := { triple |
    ∃ s1 s2 pSet, s1 ⊆ cl ∧ s2 ⊆ cl ∧ pSet ∈ alphabet ∧ -- Ensure `pSet` is explicitly introduced
    triple = (s1, pSet, s2) ∧
    (∀ q ∈ s1, match q with
      | LTL.next ψ => ψ ∈ s2  -- If X ψ is in s1, then ψ must be in s2
      | LTL.globally ψ => ψ ∈ s1 ∧ LTL.next (LTL.globally ψ) ∈ s2
      | LTL.eventually ψ => ψ ∈ s2 ∨ LTL.until (LTL.atom trueProp) ψ ∈ s2  -- FIXED: Pass `trueProp`
      | LTL.until ψ1 ψ2 => ψ2 ∈ s2 ∨ (ψ1 ∈ s1 ∧ q ∈ s2)
      | _ => True) }

  -- Initial state contains the original formula
  let initial := {φ}

  -- Accepting states: ensure fairness (ψ in U(φ, ψ) must eventually hold)
  let accepting := { s | ∀ q, q ∈ s → match q with
    | LTL.until ψ1 ψ2 => ψ2 ∈ s
    | _ => True }

  -- Construct and return the Büchi automaton
  { states := states, alphabet := alphabet, transitions := transitions, initial := initial, accepting := accepting }

--------------------------------------------------
-- 6. Example: Convert an LTL Formula to a Büchi Automaton
--------------------------------------------------

-- Example LTL formula: G(p → F q) (Globally: if p holds, q must eventually hold)
def myFormula : LTL prop := LTL.globally (LTL.implies (LTL.atom prop.p) (LTL.eventually (LTL.atom prop.q)))

-- G((¬ 𝒉𝒂𝒔𝑺𝒕𝒐𝒑∧X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑)→(X 𝒉𝒂𝒔𝑺𝒕𝒐𝒑 U (𝒊𝒔𝑺𝒕𝒐𝒑𝒑𝒆𝒅∨G 𝒉𝒂𝒔𝑺𝒕𝒐𝒑))
def treyFormula : LTL prop :=
  LTL.globally
  (
    LTL.implies
    (
      LTL.and
      (LTL.neg (LTL.atom prop.hasStop))
      (LTL.next (LTL.atom prop.hasStop))
    )
    (
      LTL.until
      (LTL.next (LTL.atom prop.hasStop))
      (LTL.or
        (LTL.atom prop.isStopped)
        ((LTL.atom prop.hasStop))
      )
    )
  )


-- Construct Büchi automaton for the given LTL formula
def treyBuchiAutomaton : BuchiAutomaton (Set (LTL prop)) prop := ltlToBuchi prop.TrueProp treyFormula

-- Display result
#reduce treyBuchiAutomaton
