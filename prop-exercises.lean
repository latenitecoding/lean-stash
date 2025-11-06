-- The following source file includes proofs for the exercises
-- from Ch. 3 of the Theorem Proving in Lean book.
-- These proofs show the theorems that are available
-- for propositional logic in the Lean standard library.

variable (p q r : Prop)

-- Commutativity
section CommutativityExercises

  -- And.comm
  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q ↦ show q ∧ p from ⟨h.right, h.left⟩)
      (fun h : q ∧ p ↦ show p ∧ q from ⟨h.right, h.left⟩)

  -- Or.comm
  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (fun h : p ∨ q ↦
        Or.elim h
          (fun hp : p ↦ show q ∨ p from Or.inr hp)
          (fun hq : q ↦ show q ∨ p from Or.inl hq))
      (fun h : q ∨ p ↦
        Or.elim h
          (fun hq : q ↦ show p ∨ q from Or.inr hq)
          (fun hp : p ↦ show p ∨ q from Or.inl hp))

end CommutativityExercises

-- General Theorems

section GeneralPropositionalExercises

  -- iff_not_self
  example : ¬(p ↔ ¬p) :=
    fun h : p ↔ ¬p ↦
      suffices h₁ : p ∧ ¬p from absurd h₁.left h₁.right
      have hnp : ¬p :=
        fun hp : p ↦ show False from absurd hp (h.mp hp)
      have hp : p := h.mpr hnp
      show p ∧ ¬p from ⟨hp, hnp⟩

end GeneralPropositionalExercises

-- Self-Proposed Exercises
section SelfProposedPropositionalExercises

  -- not_not_of_not_imp
  example : ¬(p → q) → ¬¬p :=
    fun h : ¬(p → q) ↦
    fun hnp : ¬p ↦
      suffices h₁ : p → q from absurd h₁ h
      fun hp : p ↦
        show q from absurd hp hnp

end SelfProposedPropositionalExercises

-- Classical Reasoning
section ClassicalExercises
  open Classical

  -- and_or_imp
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    fun h : p → q ∨ r ↦
      Or.elim (em (p → q))
        (fun h₁ : p → q ↦ show (p → q) ∨ (p → r) from Or.inl h₁)
        (fun h₁ : ¬(p → q) ↦
          suffices h₂ : p ∧ ¬q from
            Or.elim (h h₂.left)
              (fun hq : q ↦ show (p → q) ∨ (p → r) from absurd hq h₂.right)
              (fun hr : r ↦ show (p → q) ∨ (p → r) from Or.inr (fun _ : p ↦ hr))
          show p ∧ ¬q from not_imp.mp h₁)

  -- not_imp
  example : ¬(p → q) → p ∧ ¬q :=
    fun h : ¬(p → q) ↦
      have hp : p :=
        have h₁ : ¬¬p := not_not_of_not_imp h
        show p from not_not.mp h₁
      have hnq : ¬q := not_of_not_imp h
      show p ∧ ¬q from ⟨hp, hnq⟩

end ClassicalExercises

-- Self-Proposed Exercises

section SelfPrposedClassicalExercises
  open Classical

  -- not_not
  example : ¬¬p → p :=
    fun h : ¬¬p ↦
      Or.elim (em p)
        (fun hp : p ↦ show p from hp)
        (fun hnp : ¬p ↦ show p from absurd hnp h)

end SelfPrposedClassicalExercises
