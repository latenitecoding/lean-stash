-- The following source file includes proofs for the exercises
-- from Ch. 3 of the Theorem Proving in Lean book.
-- These proofs show the theorems that are available
-- for propositional logic in the Lean standard library.

variable (p q r : Prop)

-- Commutativity of ∧ and ∨
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

-- Associativity of ∧ and ∨
section AssociativityExercises

  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (fun h : (p ∧ q) ∧ r ↦ show p ∧ (q ∧ r) from ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
      (fun h : p ∧ (q ∧ r) ↦ show (p ∧ q) ∧ r from ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      (fun h : (p ∨ q) ∨ r ↦
        Or.elim h
          (fun h₁ : p ∨ q ↦
            Or.elim h₁
              (fun hp : p ↦ show p ∨ (q ∨ r) from Or.inl hp)
              (fun hq : q ↦ show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
          (fun hr : r ↦ show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
      (fun h : p ∨ (q ∨ r) ↦
        Or.elim h
          (fun hp : p ↦ show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
          (fun h₁ : q ∨ r ↦
            Or.elim h₁
              (fun hq : q ↦ show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
              (fun hr : r ↦ show (p ∨ q) ∨ r from Or.inr hr)))

end AssociativityExercises

-- Distributivity of ∧ and ∨
section DistributivityExercises

  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      (fun h : p ∧ (q ∨ r) ↦
        Or.elim h.right
          (fun hq : q ↦ show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨h.left, hq⟩)
          (fun hr : r ↦ show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨h.left, hr⟩))
      (fun h : (p ∧ q) ∨ (p ∧ r) ↦
        Or.elim h
          (fun h₁ : p ∧ q ↦ show p ∧ (q ∨ r) from ⟨h₁.left, Or.inl h₁.right⟩)
          (fun h₁ : p ∧ r ↦ show p ∧ (q ∨ r) from ⟨h₁.left, Or.inr h₁.right⟩))

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
      (fun h : p ∨ (q ∧ r) ↦
        Or.elim h
          (fun hp : p ↦ show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩)
          (fun h₁ : q ∧ r ↦ show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr h₁.left, Or.inr h₁.right⟩))
      (fun h : (p ∨ q) ∧ (p ∨ r) ↦
        Or.elim h.left
          (fun hp : p ↦ show p ∨ (q ∧ r) from Or.inl hp)
          (fun hq : q ↦
            Or.elim h.right
              (fun hp : p ↦ show p ∨ (q ∧ r) from Or.inl hp)
              (fun hr : r ↦ show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)))

end DistributivityExercises

-- General Theorems

section GeneralPropositionalExercises

  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
      (fun h : p → (q → r) ↦
        fun h₁ : p ∧ q ↦ show r from (h h₁.left) h₁.right)
      (fun h : p ∧ q → r ↦
        fun hp : p ↦
        fun hq : q ↦
          show r from h ⟨hp, hq⟩)

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
      (fun h : p ∨ q → r ↦
        have h₁ : p → r := (fun hp : p ↦ h (Or.inl hp))
        have h₂ : q → r := (fun hq : q ↦ h (Or.inr hq))
        show (p → r) ∧ (q → r) from ⟨h₁, h₂⟩)
      (fun h : (p → r) ∧ (q → r) ↦
        fun h₁ : p ∨ q ↦
          Or.elim h₁
            (fun hp : p ↦ show r from h.left hp)
            (fun hq : q ↦ show r from h.right hq))

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro
      (fun h : ¬(p ∨ q) ↦
        have hnp : ¬p := (fun hp : p ↦ h (Or.inl hp))
        have hnq : ¬q := (fun hq : q ↦ h (Or.inr hq))
        show ¬p ∧ ¬q from ⟨hnp, hnq⟩)
      (fun h : ¬p ∧ ¬q ↦
        fun h₁ : p ∨ q ↦
          Or.elim h₁
            (fun hp : p ↦ show False from absurd hp h.left)
            (fun hq : q ↦ show False from absurd hq h.right))

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h : ¬p ∨ ¬q ↦
    fun h₁ : p ∧ q ↦
      Or.elim h
        (fun hnp : ¬p ↦ show False from absurd h₁.left hnp)
        (fun hnq : ¬q ↦ show False from absurd h₁.right hnq)

  example : ¬(p ∧ ¬p) :=
    fun h : p ∧ ¬p ↦
      show False from absurd h.left h.right

  example : p ∧ ¬q → ¬(p → q) :=
    fun h : p ∧ ¬q ↦
    fun h₁ : p → q ↦
      have hq : q := h₁ h.left
      show False from absurd hq h.right

  example : ¬p → (p → q) :=
    fun hnp : ¬p ↦
    fun hp : p ↦
      show q from absurd hp hnp

  example : (¬p ∨ q) → (p → q) :=
    fun h : ¬p ∨ q ↦
    fun hp : p ↦
      Or.elim h
        (fun hnp : ¬p ↦ show q from absurd hp hnp)
        (fun hq : q ↦ show q from hq)

  example : p ∨ False ↔ p :=
    Iff.intro
      (fun h : p ∨ False ↦
        Or.elim h
          (fun hp : p ↦ show p from hp)
          (fun hf : False ↦ show p from False.elim hf))
      (fun hp : p ↦ show p ∨ False from Or.inl hp)

  example : p ∧ False ↔ False :=
    Iff.intro
      (fun h : p ∧ False ↦ show False from h.right)
      (fun hf : False ↦ show p ∧ False from False.elim hf)

  example : (p → q) → (¬q → ¬p) :=
    fun h : p → q ↦
    fun hnq : ¬q ↦
    fun hp : p ↦
      have hq : q := h hp
      show False from absurd hq hnq

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

  -- not_and_iff_not_or_not
  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun h : ¬(p ∧ q) ↦
      Or.elim (em p)
        (fun hp : p ↦
          Or.elim (em q)
            (fun hq : q ↦ show ¬p ∨ ¬q from absurd ⟨hp, hq⟩ h)
            (fun hnq : ¬q ↦ show ¬p ∨ ¬q from Or.inr hnq))
        (fun hnp : ¬p ↦ show ¬p ∨ ¬q from Or.inl hnp)

  -- not_imp
  example : ¬(p → q) → p ∧ ¬q :=
    fun h : ¬(p → q) ↦
      have hp : p :=
        have h₁ : ¬¬p := not_not_of_not_imp h
        show p from not_not.mp h₁
      have hnq : ¬q := not_of_not_imp h
      show p ∧ ¬q from ⟨hp, hnq⟩

  example : (p → q) → (¬p ∨ q) :=
    fun h : p → q ↦
      Or.elim (em p)
        (fun hp : p ↦ show ¬p ∨ q from Or.inr (h hp))
        (fun hnp : ¬p ↦ show ¬p ∨ q from Or.inl hnp)

  example : (¬q → ¬p) → (p → q) :=
    fun h : ¬q → ¬p ↦
    fun hp : p ↦
      Or.elim (em q)
        (fun hq : q ↦ show q from hq)
        (fun hnq : ¬q ↦
          have hnp : ¬p := h hnq
          show q from absurd hp hnp)

  -- em
  example : p ∨ ¬p :=
    show p ∨ ¬p from em p

  example : (((p → q) → p) → p) :=
    fun h : (p → q) → p ↦
      Or.elim (em p)
        (fun hp : p ↦ show p from hp)
        (fun hnp : ¬p ↦
          have h₁ : ¬p → (p → q) :=
            fun _ : ¬p ↦
            fun hp : p ↦ show q from absurd hp hnp
          have h₂ : p → q := h₁ hnp
          show p from h h₂)

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
