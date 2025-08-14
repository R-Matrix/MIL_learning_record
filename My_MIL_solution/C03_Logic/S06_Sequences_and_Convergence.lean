import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hst
  have h'1 : |s n - a| < ε / 2 := by apply hs n (le_trans (le_max_left Ns Nt) hst)
  have h'2 : |t n - b| < ε / 2 := by apply ht n (le_trans (le_max_right Ns Nt) hst)
  calc
    _ = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := by apply abs_add_le
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

-- example (a : ℝ) (b : ℝ): |a| * |b| = |a * b| := by
--   exact Eq.symm (abs_mul a b)
#check mul_lt_mul_left _

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε epos
  have ecpos : ε / |c| > 0 := by simp[acpos,epos]
  rcases cs (ε / |c|) ecpos with ⟨N,ns⟩
  use N
  simp
  intro n nst
  rcases ns n nst with hs
  have cnezero : |c| ≠ 0 := by linarith
  calc
    _= |c * (s n - a)| := by ring_nf
    _= |c| * |s n - a| := by apply abs_mul c (s n - a)
    _< |c| * (ε / |c|) := by apply (mul_lt_mul_left acpos).2 hs
    _= ε := by rw[mul_div_cancel₀];exact cnezero


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n h'
  rcases h n h' with hx
  calc
    _= |s n - a + a| := by simp [sub_add_cancel]
    _≤ |s n - a| + |a| := by apply abs_add
    _< |a| + 1 := by linarith[hx]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nlemax
  have ngeN0 : N₀ ≤ n := by apply le_trans (le_max_left N₀ N₁) (nlemax)
  have ngeN1 : N₁ ≤ n := by linarith[le_max_right N₀ N₁, nlemax]
  rcases h₀ n ngeN0 with h₀
  rcases h₁ n ngeN1 with h₁
  rw[sub_zero] at h₁
  calc
    _= |s n * t n| := by simp
    _= |s n| * |t n| := by apply abs_mul
    _< B * (ε / B) := by apply mul_lt_mul'' h₀ h₁ (abs_nonneg _ ) (abs_nonneg _)
    _= ε := by rw[mul_div_cancel₀ ε] ; linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

#check abs_eq_abs.mpr

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply abs_pos.mpr; intro h' ; apply abne; linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b| := by
    calc
      _= |a - s N + (s N - b)| := by ring
      _≤ |a - s N| + |s N - b| := by apply abs_add
      _= |s N - a| + |s N - b| := by
          simp
          apply abs_eq_abs.mpr
          simp
      _< ε + ε := by linarith[absa,absb]
      _= |a - b| := by ring

  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- 推广了数列的定义域

end
