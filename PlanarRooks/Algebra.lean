/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import PlanarRooks.Diagrams
import PlanarRooks.Finsupp
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance

variable {k : Type} [Field k] (δ : k)

-- The paramter δ is "unused" but must be carried around to define multiplication
set_option linter.unusedVariables false

namespace PlanarRook

/-- The planar rook algebra over a field `k` with parameter `δ` consists of elements which are
formal `k`-linear combinations of planar rook diagrams on `n` strands.

The multiplication is more complicated and is given by monoid multiplication of diagrams, with
a factor of `δ` raised to the number of dangling strands after multiplication.
-/
structure Algebra (n : ℕ) (δ : k) where
  ofCoeff ::
  coeff : (PlanarRook.Diagram n n) → k)

namespace Algebra

@[simp]
def coeffEquiv : Algebra n δ ≃ (PlanarRook.Diagram n n →₀ k) where
  toFun := Algebra.coeff
  invFun := Algebra.ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

lemma coeff_inj {x y : Algebra n δ} : x.coeff = y.coeff ↔ x = y := (coeffEquiv δ).injective.eq_iff

@[ext]
def ext {n : ℕ} {δ : k} {x y : Algebra n δ} :
    (∀ d : Diagram n n, x.coeff d = y.coeff d) → x = y := fun h => (coeff_inj δ).mp (Finsupp.ext h)

@[ext]
def ext' {n : ℕ} {δ : k} {x y : Algebra n δ} :
    (x.coeff = y.coeff) → x = y := fun h => (coeff_inj δ).mp h

@[to_additive]
noncomputable instance : AddCommGroup (Algebra n δ) := Equiv.addCommGroup (coeffEquiv _)
instance [DecidableEq k] : DecidableEq  (Algebra n δ) := Equiv.decidableEq (coeffEquiv _)

@[simp]
theorem zero_coeff (d : Diagram n n) : (0 : Algebra n δ).coeff d = 0 := rfl

@[simp]
theorem add_coeff (x₁ x₂ : Algebra n δ) (d : Diagram n n) :
    (x₁ + x₂).coeff d = (x₁.coeff d) + (x₂.coeff d) := rfl

/-- The planar rook algebra is a vector space over k.
-/
noncomputable instance instKModule : Module k (Algebra n δ) := Equiv.module k (coeffEquiv _)

/-- The obvious `k` basis of the `PlanarRookAlgebra` is the diagram basis.

In fact, this is how it is naturally defined, as the maps from diagrams to the underlying ring.
However, the "basis" also requires some assurances about finiteness that we provide explicitly
in this instance.

Note: This could probably be made more general for arbitrary fintypes.
-/
def diagram_basis [DecidableEq k] : Module.Basis (Diagram n n) k (Algebra n δ) := {
    repr := {
      toFun := (coeffEquiv δ).toFun
      invFun := (coeffEquiv δ).invFun
      map_add' := fun x y => by ext d; rfl
      map_smul' := fun m x => by ext d; rfl
    }
  }

noncomputable def single : (PlanarRook.Diagram n n) → k → Algebra n δ :=
  fun a b => (coeffEquiv δ).invFun (Finsupp.single a b)

@[simp]
def single_apply (d₁ d₂ : PlanarRook.Diagram n n) (c : k) :
  (single δ d₁ c).coeff d₂ = if d₁ = d₂ then c else 0 := Finsupp.single_apply

def diagram_basis_apply [DecidableEq k] (a : Algebra n δ) (d₁ : PlanarRook.Diagram n n) :
  ((diagram_basis δ).repr x) d = x.coeff d := rfl

def diagram_basis_is_single [DecidableEq k] (d₁ : PlanarRook.Diagram n n) :
  (diagram_basis δ d₁) = single δ d₁ 1 := by
    ext d₂
    simp only [diagram_basis, single_apply]
    by_cases h : d₁ = d₂
    · simp [h]
    · simp [h]

theorem smul_inner (f : Diagram n n →₀ k) (c : k) :
  c • ((coeffEquiv δ).invFun f) = (coeffEquiv δ).invFun (c • f) :=  rfl

theorem smul_inner' (a : Algebra n δ) (c : k) (d : Diagram n n) :
  (c • a).coeff d = c * (a.coeff d) :=  rfl

@[simp]
theorem smul_single (d₁ : PlanarRook.Diagram n n) (c₁ c₂ : k) :
  c₁ • (Algebra.single δ d₁ c₂) = Algebra.single δ d₁ (c₁ * c₂) := by
    ext d
    rw[smul_inner']
    simp

@[simp]
theorem smul_single' (d₁ : PlanarRook.Diagram n n) (c : k) :
  c • (Algebra.single δ d₁ 1) = Algebra.single δ d₁ c := by
    simp only [Algebra.smul_single δ d₁ c 1, mul_one]

@[simp]
theorem sum_coeff (f : ι → Algebra n δ) (s : Finset ι) :
  (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff := by sorry

theorem sum_single (x : Algebra n δ) :
  x = ∑ d : (PlanarRook.Diagram n n), Algebra.single δ d (x.coeff d) := by
    ext d'
    simp[sum_coeff _ _]

theorem add_single (d : PlanarRook.Diagram n n) (c₁ c₂ : k) :
  Algebra.single δ d (c₁ + c₂) = Algebra.single δ d c₁ + Algebra.single δ d c₂ := by
    ext x
    simp only [single_apply, add_coeff]
    by_cases h: d = x
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, add_zero]

noncomputable def one : Algebra n δ := single δ (Diagram.id n) 1

noncomputable instance hasOne : One (Algebra n δ) := ⟨one δ⟩

theorem one_def : (1 : Algebra n δ) = one δ := rfl

def one_apply (d : Diagram n n) : (1 : Algebra n δ).coeff d = if Diagram.id n = d then 1 else 0 := by
    simp[one_def, one]

def one_is : (1 : Algebra n δ) = single δ (Diagram.id n) 1 := rfl

noncomputable instance addGroupWithOne : AddGroupWithOne (Algebra n δ) := {}

/-- Multiplication in the planar rook algebra depends on a paramter δ

This paramter is raised to the exponent of the number of dangling strands
after monoid multiplication. -/
noncomputable def mul (x y : Algebra n δ) : Algebra n δ :=
  ∑ d₁ : (Diagram n n), ∑ d₂ : (Diagram n n),
    ((x.coeff d₁) * (y.coeff d₂)) • (Algebra.single δ (d₁ * d₂) (δ ^ Monoid.mul_exponent d₁ d₂))

noncomputable instance : Mul (Algebra n δ) := ⟨mul δ⟩

theorem mul_def (x y : Algebra n δ) :
  x * y = ∑ d₁ : (Diagram n n), ∑ d₂ : (Diagram n n),
    ((x.coeff d₁) * (y.coeff d₂)) • (single δ (d₁ * d₂) (δ ^ Monoid.mul_exponent d₁ d₂)) := rfl

theorem mul_apply (x y : Algebra n δ) :
  (x * y).coeff m = ∑ d₁, ∑ d₂,
    if d₁ * d₂ = m then (x.coeff d₁) * (y.coeff d₂) * (δ ^ Monoid.mul_exponent d₁ d₂) else 0 := by
  simp[mul_def]

noncomputable instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Algebra n δ) := {
  left_distrib := fun a b c => by
    ext d
    simp only [add_coeff, mul_apply, ←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : x * y = d
    · simp[h]
      ring
    · simp [h]
  right_distrib := fun a b c => by
    ext d
    simp only [add_coeff, mul_apply, ←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : x * y = d
    · simp[h]
      ring
    · simp [h]
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]
}

theorem mul_single (x : Algebra n δ) (d₁ : Diagram n n) (c : k) :
  x * (single δ d₁ c) =
    ∑ d₂ : (Diagram n n),  (x.coeff d₂) • (single δ (d₂ * d₁) (c * (δ ^ Monoid.mul_exponent d₂ d₁))) := by
  simp only [mul_def, single_apply, mul_ite, mul_zero, ite_smul, smul_single, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr
  ext x
  ring_nf

theorem single_mul (x : Algebra n δ) (d₁ : Diagram n n) (c : k) :
  (single δ d₁ c) * x =
    ∑ d₂ : (Diagram n n), (x.coeff d₂) • (single δ (d₁ * d₂) (c * (δ ^ Monoid.mul_exponent d₁ d₂))) := by
  rw [mul_def]
  conv => {
    lhs
    arg 2
    ext d₁
    arg 2
    ext d₂
    arg 1
    rw [single_apply]
    simp
  }
  conv => {
    lhs
    arg 2
    ext d₁
    simp [Finset.univ.sum_ite_eq']
  }
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, smul_single]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  ring_nf

theorem mul_single_single (d₁ d₂ : Diagram n n) (c₁ c₂ : k) :
    (single δ d₁ c₁) * (single δ d₂ c₂) =
        single δ (d₁ * d₂) (c₁ * c₂ * (δ ^ Monoid.mul_exponent d₁ d₂)) := by
  simp[mul_single δ, single_apply]
  ring_nf

/-! ## Associativity of multiplication

We can now show that multiplication is associative. That is, we have a non-unital semiring structure
on the planar rook algebra. We will later show that it is unital, and hence a ring.
-/
noncomputable instance nonUnitalSemiring :
    NonUnitalSemiring (Algebra n δ) := {
  mul_assoc := fun a b c => by
    rw [sum_single _ a]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    rw [sum_single _ b]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    rw [sum_single _ c]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₃ hd₃
    simp only [mul_single_single]
    rw [←Monoid.mul_assoc]
    ring_nf
    conv => {
      rhs
      arg 3
      arg 1
      rw [mul_assoc]
      arg 2
      rw [← pow_add (a := δ) (m:= Monoid.mul_exponent d₂ d₃)]
      arg 2
      rw [add_comm]
      rw [←Monoid.mul_exponent_assoc d₁ d₂ d₃]
    }
    ring_nf
}



noncomputable instance is_semiring :
    Semiring (Algebra (k:=k) n δ) := {
  one_mul := fun a => by
    ext d
    rw [mul_apply]
    simp only [one_apply, ite_mul, one_mul, zero_mul]
    conv => {
      lhs
      arg 2
      ext x
      arg 2
      ext y
      rw [←ite_and]
      arg 1
      rw [and_comm]
    }
    conv => {
      lhs
      arg 2
      ext x
      arg 2
      ext y
      rw [ite_and]
    }
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Diagram.id_mul]
    conv => {
      lhs
      rw [Finset.univ.sum_ite_eq']
    }
    simp [Monoid.mul_exponent_eq_zero_of_id']
  mul_one := by
    intro a
    ext d
    rw [mul_apply]
    simp only [one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    conv => {
      lhs
      arg 2
      ext x
      arg 2
      ext y
      rw [←ite_and]
      simp [and_comm (a := x * y = d) (b :=PlanarRook.Diagram.id n = y)]
    }
    conv => {
      lhs
      arg 2
      ext x
      arg 2
      ext y
      rw [ite_and]
    }
    conv => {
      lhs
      arg 2
      ext x
      rw [Finset.univ.sum_ite_eq]
    }
    conv => {
      lhs
      arg 2
      ext x
      simp [Diagram.mul_id]
    }
    simp [Monoid.mul_exponent_eq_zero_of_id]
}

noncomputable def single_one_ring_hom : k →+* Algebra n δ :=
  {
    toFun := fun c => c • (1 : Algebra n δ)
    map_one' := one_smul _ _
    map_mul' := fun x y => by
      simp only [one_is, smul_single, mul_single_single, Diagram.mul_id]
      rw [Monoid.mul_exponent_eq_zero_of_id']
      simp [←Monoid.one_def]
    map_zero' := by simp
    map_add' := fun x y => by simp [one_is, add_single]
  }

noncomputable instance is_algebra (δ : k) :
    _root_.Algebra k (PlanarRook.Algebra n δ) := {
  algebraMap := single_one_ring_hom δ,
  commutes' := fun r x => by
    unfold single_one_ring_hom
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [one_is]
    rw [smul_single]
    simp only [mul_one]
    rw [single_mul]
    rw [mul_single]
    conv => {
      lhs
      arg 2
      ext d₂
      rw [PlanarRook.Monoid.mul_exponent_eq_zero_of_id']
      simp
    }
    conv => {
      rhs
      arg 2
      ext d₁
      rw [PlanarRook.Monoid.mul_exponent_eq_zero_of_id]
      simp
    }
  smul_def' := fun r x => by
    unfold single_one_ring_hom
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [one_is]
    rw [smul_single δ (Diagram.id n) r (1 : k)]
    rw [single_mul]
    conv => {
      rhs
      arg 2
      ext d₁
      arg 2
      rw [PlanarRook.Monoid.mul_exponent_eq_zero_of_id']
      rw [←PlanarRook.Monoid.one_def]
      rw [PlanarRook.Monoid.one_mul d₁]
      simp
    }
    rw [sum_single δ (r • x)]
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    ext d₂
    simp only [single_apply, smul_single δ]
    by_cases h : x₁ = d₂
    · simp only [h, ↓reduceIte]
      simp only [smul_inner']
      exact mul_comm (G:=k) _ _
    · simp [h]
}

theorem algebra_map : algebraMap k (Algebra n δ) = single_one_ring_hom δ := rfl

/-- The planar rook algebra is independent of the parameter δ, up to algebra isomorphism, as long as
it is not zero.

This is to say, there are only "two" planar rook algebras, the one where δ = 0 and the one where δ
is nonzero (and might as well be 1).
-/
noncomputable def parameter_independence (n : ℕ) (δ₁ : k) (δ₁_nonzero : δ₁ ≠ 0) [DecidableEq k] :
    (Algebra n δ₁) ≃ₐ[k] (Algebra n (1 : k)) := {
      toFun := fun x => ∑ d , ((x.coeff d) * (δ₁^ ((n : ℤ) - ↑d.through_index))) • (diagram_basis 1 d)
      invFun := fun y => ∑ d, (y.coeff d / (δ₁^ ((n : ℤ) - ↑d.through_index))) • (diagram_basis δ₁ d)
      left_inv := by
        intro x
        simp only [diagram_basis_is_single, smul_single, mul_one]
        conv => {
          lhs
          arg 2
          intro x₁
          arg 3
          simp [δ₁_nonzero]
          rw[←mul_div]
          rw[div_self (zpow_ne_zero (n - x₁.through_index) δ₁_nonzero)]
          simp
        }
        rw [←sum_single δ₁ x]
      right_inv := by
        intro x
        simp only [diagram_basis_is_single, smul_single, mul_one]
        conv => {
          lhs
          arg 2
          intro x₁
          arg 3
          simp [δ₁_nonzero]
          rw[div_mul]
          rw[div_self (zpow_ne_zero (n - x₁.through_index) δ₁_nonzero)]
          simp
        }
        rw [←sum_single 1 x]
      map_mul' := by
        intro x y
        simp only [diagram_basis_is_single, smul_single]
        simp [Finset.sum_mul_sum, mul_single_single]
        ring_nf
        simp only [mul_assoc]
        apply ext
        intro d
        sorry
        -- conv => {
        --   lhs
        --   simp only [sum_coeff]
        --   simp [Finset.sum_apply (a:=d) (s:=Finset.univ)]
        --   rw [Finset.sum_ite_eq_of_mem (h:=Finset.mem_univ d)]
        --   rw [mul_apply]
        --   rw [Finset.sum_mul]
        --   arg 2
        --   ext x₁
        --   rw [Finset.sum_mul]
        -- }
        -- apply Finset.sum_congr rfl
        -- intro x₁ hx₁
        -- apply Finset.sum_congr rfl
        -- intro x₂ hx₂
        -- rw [ite_mul]
        -- by_cases h : d = x₁ * x₂
        -- · simp only [h, ↓reduceIte]
        --   rw [←zpow_natCast]
        --   rw [←Int.ofNat_sub (Diagram.through_index_le_left x₁)]
        --   rw [←Int.ofNat_sub (Diagram.through_index_le_left x₂)]
        --   ring_nf
        --   conv => {
        --     rhs
        --     rw [mul_assoc]
        --     arg 2
        --     rw [←zpow_add' (Or.inl δ₁_nonzero)]
        --   }
        --   simp only [mul_assoc, ←zpow_add' (Or.inl δ₁_nonzero)]
        --   simp only [Monoid.mul_exponent, Finset.compl_union, Diagram.through_degree_of_mul,
        --     mul_eq_mul_left_iff]
        --   apply Or.inl
        --   apply Or.inl
        --   rw [Int.ofNat_sub (Diagram.through_index_le_left _)]
        --   rw [Int.ofNat_sub (Diagram.through_index_le_left _)]
        --   rw [←Finset.compl_union]
        --   rw [Finset.cast_card_inter]
        --   rw [Finset.compl_eq_univ_sdiff]
        --   rw [Finset.cast_card_sdiff (Finset.subset_univ _)]
        --   simp [Finset.card_univ]
        --   ring_nf
        --   rw[Diagram.through_index_eq_right]
        --   rw[Diagram.through_index_eq_left]
        -- · simp [h, eq_comm]
      map_add' := by
        intro x y
        simp only [diagram_basis_is_single, smul_single]
        simp only [add_coeff, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        rw [←add_single 1 x₁, ←add_mul]
        ring_nf
      commutes' := by
        intro r
        simp only [diagram_basis_is_single, smul_single]
        simp only [algebra_map, single_one_ring_hom, one_is,
          RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        ext x
        simp [Finset.univ.sum_apply x, single_apply]
        by_cases h : (PlanarRook.Diagram.id n) = x
        · simp [h.symm, PlanarRook.Diagram.through_index_of_id]
        · simp [h]
    }

noncomputable instance ringConGen : Ring (Algebra n δ) := {is_semiring _, addGroupWithOne _ with}

variable [DecidableEq k]

theorem diagram_basis_mul (a b : PlanarRook.Diagram n n) :
  (diagram_basis δ a) * (diagram_basis δ b) =
    (δ ^ PlanarRook.Monoid.mul_exponent a b) • (diagram_basis δ) (a * b) := by
    unfold diagram_basis
    have q := mul_single_single δ a b 1 1
    simp only [mul_one, one_mul] at q
    rw[←smul_single' (c:= δ ^ _)] at q
    unfold single at q
    simp[q]
    rw[mul_def]
    simp
    conv_lhs => {
      arg 2
      ext x
      arg 2
      ext y
      arg 3
      rw[Finsupp.single_apply]
      rw[Finsupp.single_apply]
    }
    sorry

def diagram_basis' :
  Module.Basis
    (Σ μ : Fin (n + 1), {S : Finset (Fin n) // S.card = μ} × {S : Finset (Fin n) // S.card = μ})
    k (Algebra n δ) :=
    Module.Basis.reindex (diagram_basis _) PlanarRook.Diagram.pi_iso₂

theorem diagram_basis'_mul
  (a b : Σ μ : Fin (n + 1), {S : Finset (Fin n) // S.card = μ} × {S : Finset (Fin n) // S.card = μ})
  :
  (diagram_basis' δ a) * (diagram_basis' δ b) =
    (δ ^ PlanarRook.Monoid.mul_exponent
      (PlanarRook.Diagram.pi_iso₂.invFun a)
      (PlanarRook.Diagram.pi_iso₂.invFun b)) •
    (diagram_basis' δ) (PlanarRook.Diagram.pi_iso₂.toFun
      (PlanarRook.Diagram.pi_iso₂.invFun a * PlanarRook.Diagram.pi_iso₂.invFun b)) := by
    unfold diagram_basis'
    simp [Module.Basis.reindex_apply, diagram_basis_mul]

/-! ## The algebra anti-involution
-/
noncomputable def ι {δ : k} : (Algebra n δ) →ₗ[k] (Algebra n δ) :=
  (diagram_basis δ).constr k ((diagram_basis δ) ∘ PlanarRook.Diagram.ι)

def diagram_basis_swap :
  (Σ μ : Fin (n + 1), {S : Finset (Fin n) // S.card = μ} × {S : Finset (Fin n) // S.card = μ}) →
  (Σ μ : Fin (n + 1), {S : Finset (Fin n) // S.card = μ} × {S : Finset (Fin n) // S.card = μ}) :=
  fun ⟨i, S, T⟩ => ⟨i, T, S⟩

theorem diagram_basis'_ι : ι (n:=n) =
  (diagram_basis' δ).constr k ((diagram_basis' δ) ∘ diagram_basis_swap) := by
    apply Module.Basis.constr_eq
    intro d
    simp [diagram_basis, diagram_basis_swap, diagram_basis', Finsupp.single_apply]
    congr

def foobar : (fun x => match x with
    | ⟨μ, (s, t)⟩ => (diagram_basis' δ (n:=n)) ⟨μ, (t, s)⟩) =
      ((diagram_basis' δ) ∘ diagram_basis_swap) := rfl

theorem ι_anti (a b : Algebra n δ) : ι (a * b) = (ι b) * (ι a) := by
  rw [←(diagram_basis δ).sum_repr a]
  rw[Finset.sum_mul]
  have qq := map_sum (f := fun i => ((diagram_basis δ).repr a) i • (diagram_basis δ) i * b) ι
  rw[qq]
  have qq := map_sum (f := fun i => ((diagram_basis δ).repr a) i • (diagram_basis δ) i) ι
  rw[qq]
  rw[Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Algebra.smul_mul_assoc, map_smul, Algebra.mul_smul_comm]
  congr
  rw[←(diagram_basis δ).sum_repr b]
  rw[Finset.mul_sum]
  have qq := map_sum (f := fun i =>
    (diagram_basis δ) x * ((diagram_basis δ).repr b) i • (diagram_basis δ) i) ι
  rw [qq]
  have qq := map_sum (f := fun i => ((diagram_basis δ).repr b) i • (diagram_basis δ) i) ι
  rw [qq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Algebra.mul_smul_comm, map_smul, Algebra.smul_mul_assoc]
  congr
  rw [diagram_basis_mul]
  simp only [map_smul]
  unfold ι
  simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_self, Function.comp_apply,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw[diagram_basis_mul]
  simp [PlanarRook.Diagram.ι_mul]

end Algebra
end PlanarRook
