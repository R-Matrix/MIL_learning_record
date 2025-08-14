import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rw[le_abs]
  left
  simp

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw[le_abs]
  right
  linarith

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw[abs_le]
  constructor
  · have :  |x| +  |y| ≥ - x + - y := by
      apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
    linarith
  · apply add_le_add (le_abs_self _) (le_abs_self _)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases le_or_gt y 0 with h' | h'
    · right ; rw[abs_eq_neg_self.mpr h'] at h ; exact h
    · left ; rw[abs_of_pos h'] at h;exact h
  · intro h
    rcases le_or_gt y 0 with h₁ | h₂
    · rw[abs_of_nonpos h₁]
      rcases h with h' | h'
      · have ylen : y ≤ -y := by linarith
        linarith
      · linarith
    · rw [abs_of_pos h₂]
      rcases h with h' | h'
      · linarith
      · have ylep : -y < y := by linarith
        linarith


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    rcases le_or_gt 0 x with h' | h'
    · rw [abs_of_nonneg h'] at h
      constructor
      · linarith
      · linarith
    constructor
    · linarith[abs_of_neg h']
    · linarith[abs_of_neg h']
  · intro h
    rcases le_or_gt 0 x with h' | h'
    · rw [abs_of_nonneg h']
      linarith
    · rw [abs_of_neg h']
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h|h⟩ <;> linarith[pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hx : (x - 1) * (x + 1) = 0 := by
    calc _= x ^ 2 -1 := by linarith
    _= 0 := by linarith
  rw[mul_eq_zero] at hx
  rcases hx with h₁ | h₂
  · left ; linarith
  · right ; linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hx : (x + y) * (x - y) = 0 := by linarith
  rw[mul_eq_zero] at hx
  rcases hx with h₁ | h₁
  · right;linarith
  · left ; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hx : (x - 1) * (x + 1) = 0 := by
    calc _= x ^ 2 -1 := by ring
    _= 0 := by rw[h] ;ring
  rw[mul_eq_zero] at hx
  rcases hx with h₁ | h₂
  · left
    apply eq_of_sub_eq_zero h₁
  · right
    apply eq_neg_of_add_eq_zero_left h₂

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hx : (x + y) * (x - y) = 0 := by
    ring_nf
    apply sub_eq_zero_of_eq h
  rw[mul_eq_zero] at hx
  rcases hx with h₁ | h₁
  · right
    apply add_eq_zero_iff_eq_neg.mp h₁
  · left
    apply eq_of_sub_eq_zero h₁

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      apply h h'
    · left
      exact h'
  · intro h h'
    rcases h with h | h
    · contradiction
    · exact h
