import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where   ----  共轭
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem
    group
  inv_mem' := by
    dsimp
    intro b ⟨a,ha, xcoa⟩
    use a⁻¹, H.inv_mem ha
    rw[xcoa]
    group
  mul_mem' := by
    dsimp
    intro a b ⟨a1, ha1, acoa1⟩ ⟨b1, hb1, bcob1⟩
    use a1*b1, H.mul_mem ha1 hb1
    rw[acoa1, bcob1]
    group

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  rintro y hy
  -- rw[mem_comap] at *
  apply hST hy

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  rintro x ⟨y,yS, yex⟩
  use y,hST yS, yex

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext x
  rw[mem_comap, mem_comap, mem_comap]
  rfl


-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x
  rw[mem_map, mem_map]
  constructor
  · intro ⟨y, yS, yx⟩
    use φ y,(by apply mem_map.mpr; use y) , yx
  · intro ⟨y, ⟨a, aS, ea⟩, e⟩
    use a, aS, (by rw[←e,←ea]; rfl)


end exercises

open scoped Classical


example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  --⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩
  by
  --rw[dvd_iff_exists_eq_mul_left]
  use G'.index
  rw[mul_comm, G'.index_mul_card]

open Subgroup

example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  constructor
  · intro hx; use 1, H.one_mem, hx
  · intro ⟨x, hx, aex⟩ t ht
    rw[aex _ H.one_mem, aex _ ht]

#check card_dvd_of_le

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
  have h1: Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have h2: Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  apply eq_bot_iff_card.mpr
  apply Nat.dvd_one.mp;rw[Nat.coprime_iff_gcd_eq_one,←h] at *; apply dvd_gcd h1 h2

open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle

#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]



section FreeGroup

---- 这章FreeGroup 没看懂

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]


def myGroup := PresentedGroup {.of () ^ 3} deriving Group   --?

def myMap : Unit → Perm (Fin 5)   --?
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by   --?
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap  --?

-- `Remark` : 大致是 自由群可能类似于自由线性空间 ? 给定一个集合 A, A 中的每一个元素看成一个生成元素从而构成一个自由群(若A中有大于等于2个元素, 非交换)
--          这是一个最自由的群, A 中的元素没有任何关系, 像一个字母表, 而 FreeGroup A 中的每个元素称为 字(word )
--          card A = 1 => (FreeGroup A, ·) ≅ (Z, +) || card A = 0 => FreeGroup A 仅包含单位元
--          满足**泛性质** : 从 A 到 FreeGroup A 有一个自然的嵌入 e , 对 A 中的每一个元素 a, e (a : A) = a : FreeGroup
--          对任意一个从 A 到群 G 的映射 f, 都存在从 FreeGroup A 到 G 的**唯一的群同态 H**, 使得下面的图交换, 也即 H ∘ e = f
/-                                  A   -----(e)---->  FreeGroup A
                                    |                     |
                                    |                     |
                                  (∀ f)           (∃! homomorphism H)
                                    |                     |
                                    ↓                     ↓
                                    G                     G
-/
end FreeGroup


noncomputable section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm

open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out ω)) :=
  MulAction.selfEquivSigmaOrbits G X

/-↑ 更具体地说，我们得到一个集合 X 与一个依赖乘积类型 (dependent product) (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) 之间的双射, 其中, Quotient.out' ω 简单地选择一个元素，该元素映射到 ω。

请注意，该依赖积的元素是形如 ⟨ω, x⟩ 的对，其中 x 的类型 orbit G (Quotient.out' ω) 依赖于 ω。

特别是，当 X 是有限集时，可以结合 Fintype.card_congr 和 Fintype.card_sigma 推导出 X 的基数等于其轨道 (orbits) 基数之和。
-/


example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

/-↑ 此外，这些轨道与 G 在稳定子 (stabilizers) 的左平移作用下的商集 (quotient) 一一对应 (存在双射关系)。 这种通过子群的左平移作用定义的商集通常使用符号 / 来表示，因此可以用以上简洁的表述来说明。-/


example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  rw[conjugate]
  simp

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    apply conjugate_one
  mul_smul := by
    rintro a b S
    ext x
    constructor
    · intro ⟨z, zs, xe⟩
      use b*z*b⁻¹,(by use z),(by rw[xe]; group)
    · intro ⟨z,⟨w,ws,ze⟩,xe⟩
      use w, ws,(by rw[xe,ze]; group)

-- `Remark`: 共轭(conjugate) 也是群 G 对自身的群作用, 轨道称为 共轭类(Conjugate Class), 稳定子称为 中心化子(Centralizer), 说明稳定子中的元素与 G 中的元素乘积可交换

end GroupActions

noncomputable section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  rw[←Subgroup.index_mul_card H, mul_comm _ (Nat.card K)] at h'
  rw[←Subgroup.index_eq_card H]
  apply Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ : K ≃* G ⧸ H := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw[Nat.bijective_iff_injective_and_card]
  constructor
  · rwa[←ker_eq_bot_iff, ker_restrict, QuotientGroup.ker_mk', subgroupOf_eq_bot]
  · apply eq_comm.mp
    exact aux_card_eq h'

/-现在我们可以定义第二个部分。 我们将需要 MonoidHom.prod，它可以根据从 G₀ 到 G₁ 和 G₂ 的态射构建一个从 G₀ 到 G₁ × G₂ 的态射-/
#check MonoidHom.prod

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  apply MulEquiv.ofBijective (MonoidHom.prod (QuotientGroup.mk' K) (QuotientGroup.mk' H))
  rw[Nat.bijective_iff_injective_and_card]
  constructor
  · rw[←ker_eq_bot_iff, ker_prod,QuotientGroup.ker_mk', QuotientGroup.ker_mk', Disjoint.eq_bot]
    apply Disjoint.symm h
  · rw[Nat.card_prod, aux_card_eq h']
    rw[mul_comm] at h'
    rw[aux_card_eq h']
    rw[mul_comm] at h'
    exact h'

#check MulEquiv.prodCongr

def finalIso : G ≃* H × K :=
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm
-- by
--   apply MulEquiv.trans (iso₂ h h')
--   apply MulEquiv.symm
--   apply MulEquiv.prodCongr
--   · apply iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')
--   · apply iso₁ h h'
