import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · rintro fsinv x xins
    apply fsinv; use x
  · rintro sininvv y ⟨x,xs,fxeqy⟩
    have h : x ∈ f ⁻¹' v := by apply sininvv xs
    simp at h;rw[fxeqy] at h
    exact h

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨z,zins,fzeqfx⟩
  have : x = z := by apply h;simp[fzeqfx]
  rwa[this]

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨z,zinfinvu,fzeqy⟩
  have : f z ∈ u := by apply zinfinvu
  rwa[←fzeqy]

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yinu
  rcases h y with⟨x,fxeqy⟩
  have : x ∈ f ⁻¹' u := by apply mem_preimage.mpr;rwa[fxeqy]
  rw[mem_image]
  use x

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x,xs,fxeqy⟩
  --simp
  use x
  exact ⟨(h xs),(fxeqy)⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x xu
  --simp at *
  apply h xu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor <;>
  · rintro (finu | finv)
    left;apply finu
    right;apply finv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x,⟨xs,xt⟩,fxeqy⟩
  --simp
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x,xs,fxeqy⟩,z,zt,fzeqy⟩
  use x
  constructor
  · constructor
    · exact xs
    · have : x = z := by apply h; rw[fxeqy,fzeqy]
      rwa[this]
  · assumption

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x,xs,fxeqy⟩,ynint⟩
  --simp only [mem_image, mem_diff]
  use x
  constructor
  · constructor
    · exact xs
    · intro h
      apply ynint
      use x
  · exact fxeqy

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨fxinu,fxnotinv⟩
  rw [mem_preimage] at *
  exact ⟨fxinu,fxnotinv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x,xs,fxeqy⟩,yv⟩
    use x
    constructor
    · constructor
      · exact xs
      · rw[mem_preimage,fxeqy];exact yv
    · exact fxeqy
  · rintro ⟨x,⟨xs,fxinv⟩,fxeqy⟩
    constructor
    · use x
    · rw[mem_preimage] at fxinv
      rw[← fxeqy];exact fxinv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x,⟨xs,fxinu⟩,fxeqy⟩
  constructor
  · use x
  · rw[mem_preimage,fxeqy] at fxinu; trivial

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs,fxinu⟩
  rw[mem_preimage] at *
  constructor
  · use x
  · exact fxinu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs|fxinu)
  · rw[mem_preimage];left;use x
  · rw[mem_preimage] at *;right;exact fxinu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y;simp
  constructor
  · rintro ⟨x,⟨i,xai⟩,fxeqy⟩
    use i,x
  · rintro ⟨i,⟨x,xai,fxeqy⟩⟩
    use x
    constructor
    · use i
    · exact fxeqy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y;simp
  rintro x xai fxeqy i
  use x
  constructor
  · apply xai i
  · exact fxeqy

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y h
  simp at *
  rcases h i with ⟨x,xai,fxeqy⟩
  use x
  constructor
  · intro j
    rcases h j with ⟨z,zaj,fzeqy⟩
    have : x = z := by apply injf; simp [fxeqy,fzeqy]
    rwa[this]
  · exact fxeqy

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro h
    rw[mem_preimage,mem_iUnion] at h
    rcases h with ⟨i,fxinBi⟩
    rw[mem_iUnion]
    use i;apply fxinBi
  · intro h
    rw[mem_preimage,mem_iUnion]
    rw[mem_iUnion]at h
    rcases h with ⟨i,fxinBi⟩
    use i
    apply fxinBi

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro h
    rw[mem_preimage,mem_iInter] at h
    rw[mem_iInter]
    intro i
    rw[mem_preimage]
    apply h
  · intro h
    rw[mem_iInter] at h
    rw[mem_preimage,mem_iInter]
    intro i
    apply h

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x₁ x1nonneg x₂ x2nonneg hxeq
  calc
    _= (√ x₁ ) ^ 2 := by rw[sq_sqrt x1nonneg]
    _= (√ x₂ ) ^ 2 := by rw[hxeq]
    _= x₂ := by rw[sq_sqrt x2nonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x₁ x1nonneg x₂ x2nonneg hx
  dsimp at hx
  calc
    _= √ (x₁ ^ 2) := by rw[sqrt_sq x1nonneg]
    _= √ (x₂ ^ 2) := by rw[hx]
    _= x₂ := by rw[sqrt_sq x2nonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x,xnonneg,rfl⟩
    apply sqrt_nonneg
  · rintro ynonneg
    rw[mem_image]
    use y ^ 2
    exact ⟨pow_two_nonneg y,sqrt_sq ynonneg⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    apply pow_two_nonneg x
  · intro ynonneg
    rw[mem_range]
    use √ y
    apply sq_sqrt ynonneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · rintro injf x
    apply injf
    apply inverse_spec
    use x
  · rintro linv x y feq
    -- rw[LeftInverse] at linv
    rw[← linv x,← linv y,feq]

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun injf x ↦ injf (inverse_spec _ ⟨x,rfl⟩),fun linv x y feq ↦ by rw[← linv x,← linv y,feq]⟩

--===================--

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · rintro surjf y
    apply inverse_spec
    apply surjf _
  · intro rinv y
    use inverse f y
    apply rinv

example : Surjective f ↔ RightInverse (inverse f) f :=
   ⟨fun surjf _ ↦ inverse_spec _ (surjf _),fun rinv _ ↦ ⟨inverse f _, rinv _⟩⟩


end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    apply h₁
  have h₃ : j ∉ S := by
    rwa[← h]
  contradiction

-- COMMENTS: TODO: improve this
end
