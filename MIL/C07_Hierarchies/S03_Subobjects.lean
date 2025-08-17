import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

/-作为练习，您应该定义一个 Subgroup₁ 结构，为其赋予一个 SetLike 实例和一个 SubmonoidClass₁ 实例，
在与 Subgroup₁ 相关联的子类型上放置一个 Group 实例，并定义一个 SubgroupClass₁ 类。-/

@[ext]
structure Subgroup₁ (G : Type) [Group G] where
  carrier : Set G
  mul_mem : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem : a⁻¹ ∈ carrier

instance (G : Type) [Group G] : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _:= Subgroup₁.ext

example [Group G] (G' : Subgroup₁ G) : Group G' where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, G'.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩↦ SetCoe.ext (mul_assoc _ _ _)
  one := ⟨1, G'.one_mem⟩
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one _)
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul _)
  inv := fun ⟨x, _⟩ ↦ ⟨x⁻¹, G'.inv_mem⟩
  inv_mul_cancel := fun ⟨x, _⟩ ↦ SetCoe.ext (inv_mul_cancel _)

 class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] : Prop where
  mul_mem : ∀ (s : S) {a b : G}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem

/-My Exercise End-/


instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where   --等价关系 : 自反性, 对称性, 传递性
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro a b c ⟨w,hw,z,hz,h1⟩ ⟨x,hx,y,hy,h2⟩
      use (w*x),(mul_mem hw hx),(y*z),(mul_mem hy hz)
      rw[←mul_assoc, h1, ←mul_assoc, ←h2, mul_assoc, mul_comm z x, ←mul_assoc]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
      intro a1 a2 ⟨w,hw,z,hz,h1⟩ b1 b2 ⟨x,hx,y,hy,h2⟩
      dsimp
      use (x*w), mul_mem hx hw, y*z, mul_mem hy hz
      rw[mul_assoc, ←mul_assoc b1, h2, mul_comm, mul_assoc, mul_comm w, h1, mul_comm, mul_assoc, mul_comm z, ←mul_assoc, ←mul_assoc, ←mul_assoc]
      )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩        ---- rintro ⟨a⟩  := 把商元展开为代表元
      apply Quotient.sound    ---- 证明商元等价, 只需证代表元等价
      -- theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=  Quot.sound
      use 1, N.one_mem, 1, N.one_mem
      dsimp
      rw[mul_one, mul_one, mul_assoc]

  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw[one_mul]
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw[mul_one]
      apply @Setoid.refl M N.Setoid
