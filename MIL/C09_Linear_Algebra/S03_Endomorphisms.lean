import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap End

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=       --- 将多项式中的 x 替换为线性映射 φ, 构造出新的线性映射
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw[Submodule.eq_bot_iff]
  intro x hx
  simp [Submodule.mem_inf, mem_ker] at hx
  rcases h with ⟨a, b, e1⟩
  apply_fun (aeval φ) at e1
  simp [aeval_add, aeval_mul] at e1
  have := LinearMap.ext_iff.mp e1 x
  dsimp at this; rw[hx.1, hx.2, map_zero, map_zero, zero_add 0] at this;
  exact this.symm


#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by   ---- 关键 : 多项式乘法可交换
  ext x
  rw[Submodule.mem_sup]
  constructor
  · intro ⟨y,hy,z,hz,xyz⟩
    apply mem_ker.mpr
    rw[←xyz, map_mul, map_add]
    simp [mem_ker] at *
    rw[hz, map_zero, add_zero]
    rw[←comp_apply, ←mul_eq_comp,←map_mul, mul_comm P Q, map_mul, mul_eq_comp, comp_apply, hy, map_zero]
  ·
    rcases h with ⟨a, b, e1⟩
    apply_fun (aeval φ) at e1
    have := LinearMap.ext_iff.mp e1 x
    simp only [mem_ker, aeval_one, one_apply] at *
    /-思路 : 已知 PQ(x) = 0 , (aP + bQ) (x) = x
            求证 x=y+z, P(y)=0 ∧ Q(z) = 0

            令 y = bQ(x), z = aQ(x), 满足 x = y + z
            同时利用交换性得证
     -/
    intro h; use ((aeval φ) (b * Q)) x
    constructor
    · rw[←mul_apply, ←map_mul, mul_comm, mul_assoc, mul_comm Q, map_mul, mul_apply, h, map_zero]
    · use ((aeval φ) (a * P)) x
      constructor
      · rw[←mul_apply, ←map_mul, mul_comm, mul_assoc, map_mul, mul_apply, h, map_zero]
      · rw[←add_apply, ←map_add, add_comm, this]

example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def


example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
