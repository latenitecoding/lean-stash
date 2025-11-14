variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h : ∀x, p x ∧ q x ↦
      have hp : ∀ x, p x := (fun x : α ↦ (h x).left)
      have hq : ∀ x, q x := (fun x : α ↦ (h x).right)
      show (∀ x, p x) ∧ (∀ x, q x) from ⟨hp, hq⟩)
    (fun h : (∀ x, p x) ∧ (∀ x, q x) ↦
      fun x : α ↦
      have hp : p x := h.left x
      have hq : q x := h.right x
      show p x ∧ q x from ⟨hp, hq⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : ∀ x, p x → q x ↦
  fun h₁ : ∀ x, p x ↦
  fun x : α ↦
    have h₂ : p x → q x := h x
    have hp : p x := h₁ x
    show q x from h₂ hp

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) ↦
  fun x : α ↦
    Or.elim h
      (fun h₁ : ∀ x, p x ↦ show p x ∨ q x from Or.inl (h₁ x))
      (fun h₁ : ∀ x, q x ↦ show p x ∨ q x from Or.inr (h₁ x))

open Classical

example : α → ((∀ _ : α, r) ↔ r) :=
  fun x : α ↦
    Iff.intro
      (fun h : ∀ _, r ↦ show r from h x)
      (fun hr : r ↦ show ∀ _, r from (fun _ : α ↦ hr))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h : ∀ x, p x ∨ r ↦
      Or.elim (em r)
        (fun hr : r ↦ show (∀ x, p x) ∨ r from Or.inr hr)
        (fun hnr : ¬r ↦
          suffices h₁ : ∀ x, p x from Or.inl h₁
          fun x : α ↦
          have h₁ : p x ∨ r := h x
          Or.elim h₁
            (fun hp : p x ↦ show p x from hp)
            (fun hr : r ↦ show p x from absurd hr hnr)))
    (fun h : (∀ x, p x) ∨ r ↦
      Or.elim h
        (fun h₁ : ∀ x, p x ↦
          fun x : α ↦
            have hp : p x := h₁ x
            show p x ∨ r from Or.inl hp)
        (fun hr : r ↦
          show ∀ x, p x ∨ r from (fun _ : α ↦ Or.inr hr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : ∀ x, r → p x ↦
      fun hr : r ↦
      fun x : α ↦
        have h₁ : r → p x := h x
        show p x from h₁ hr)
    (fun h : r → ∀ x, p x ↦
      fun x : α ↦
      fun hr : r ↦
        have h₁ : ∀ x, p x := h hr
        show p x from h₁ x)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have hnb : ¬ shaves barber barber :=
    (fun hb : shaves barber barber ↦ absurd hb (h₁.mp hb))
  have hb : shaves barber barber := h₁.mpr hnb
  show False from absurd hb hnb

def even (n : Nat) : Prop := ∃ d, n = 2 * d

def prime (n : Nat) : Prop := (∀ d, ∃ b, n = d * b ↔ d = 1 ∨ d = n)

def infinitely_many_primes : Prop := (∀ n : Nat, prime n → ∃ m, prime m ∧ m > n)
