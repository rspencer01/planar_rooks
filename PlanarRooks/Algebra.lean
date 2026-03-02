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

variable {k : Type} [Field k] (δ : k)

-- The paramter δ is "unused" but must be carried around to define multiplication
set_option linter.unusedVariables false

namespace PlanarRook

/-- The planar rook algebra over a field `k` with parameter `δ` consists of elements which are
formal `k`-linear combinations of planar rook diagrams on `n` strands.

The multiplication is more complicated and is given by monoid multiplication of diagrams, with
a factor of `δ` raised to the number of dangling strands after multiplication.
-/
def Algebra (n : ℕ) (δ : k) := ((PlanarRook.Diagram n n) → k)

namespace Algebra

@[ext]
def ext {n : ℕ} {δ : k} {x y : Algebra n δ} :
    (∀ d : Diagram n n, x d = y d) → x = y := fun h => by simp [funext h]

instance : AddCommMonoid (Algebra n δ) := inferInstanceAs (AddCommMonoid (_ → k))

instance : AddCommGroup (Algebra n δ) := inferInstanceAs (AddCommGroup (_ → k))

@[simp]
theorem zero_coeff (d : Diagram n n) : (0 : Algebra n δ) d = 0 := rfl

@[simp]
theorem add_coeff (x₁ x₂ : Algebra n δ) (d : Diagram n n) :
    (x₁ + x₂) d = (x₁ d) + (x₂ d) := rfl

/-- The planar rook algebra is a vector space over k.
-/
instance : Module k (Algebra n δ) := Pi.module _ _ k

/-- The obvious `k` basis of the `PlanarRookAlgebra` is the diagram basis.

In fact, this is how it is naturally defined, as the maps from diagrams to the underlying ring.
However, the "basis" also requires some assurances about finiteness that we provide explicitly
in this instance.

Note: This could probably be made more general for arbitrary fintypes.
-/
instance diagram_basis [DecidableEq k] : Module.Basis (Diagram n n) k (Algebra n δ) := {
    repr := {
      toFun := equivFunOnFinite.symm
      invFun := equivFunOnFinite.toFun
      map_add' := fun x y => by ext d; rfl
      map_smul' := fun m x => by ext d; rfl
    }
  }

def single : (PlanarRook.Diagram n n) → k → Algebra n δ := Pi.single

@[simp]
def single_apply (d₁ d₂ : PlanarRook.Diagram n n) (c : k) :
  (Algebra.single δ d₁ c) d₂ = if d₂ = d₁ then c else 0 := Pi.single_apply _ _ _

@[simp]
theorem smul_single (d₁ : PlanarRook.Diagram n n) (c₁ c₂ : k) :
  c₁ • (Algebra.single δ d₁ c₂) = Algebra.single δ d₁ (c₁ * c₂) := by
    unfold single
    rw [←Pi.single_smul]
    simp only [smul_eq_mul]

@[simp]
theorem smul_single' (d₁ : PlanarRook.Diagram n n) (c : k) :
  c • (Algebra.single δ d₁ 1) = Algebra.single δ d₁ c := by
    simp only [Algebra.smul_single δ d₁ c 1, mul_one]

theorem sum_single (x : Algebra n δ) :
  x = ∑ d : (PlanarRook.Diagram n n), Algebra.single δ d (x d) := by
    ext m
    rw [Finset.univ.sum_apply m]
    simp [single_apply]

theorem add_single (d : PlanarRook.Diagram n n) (c₁ c₂ : k) :
  Algebra.single δ d (c₁ + c₂) = Algebra.single δ d c₁ + Algebra.single δ d c₂ := by
    ext x
    simp only [single_apply, add_coeff]
    by_cases h: x = d
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, add_zero]

/-- Multiplication in the planar rook algebra depends on a paramter δ

This paramter is raised to the exponent of the number of dangling strands
after monoid multiplication. -/
def mul (x y : Algebra n δ) : Algebra n δ :=
  ∑ d₁ : (Diagram n n), ∑ d₂ : (Diagram n n),
    ((x d₁) * (y d₂)) • (Algebra.single δ (d₁ * d₂) (δ ^ Monoid.mul_exponent d₁ d₂))

def one : Algebra n δ := single δ (Diagram.id n) 1

def one_apply (d : Diagram n n) : (one δ) d = if Diagram.id n = d then 1 else 0 := by
    simp only [one, single_apply]
    by_cases h : Diagram.id n = d
    · simp [h]
    · rw [eq_comm] at h
      simp only [h, ↓reduceIte, right_eq_ite_iff, zero_ne_one, imp_false]
      rw [eq_comm] at h
      exact h

instance : Mul (Algebra n δ) := ⟨mul δ⟩

theorem mul_def (x y : Algebra n δ) :
  x * y = ∑ d₁ : (Diagram n n), ∑ d₂ : (Diagram n n),
    ((x d₁) * (y d₂)) • (single δ (d₁ * d₂) (δ ^ Monoid.mul_exponent d₁ d₂)) := rfl

theorem mul_apply (x y : Algebra n δ) :
  (x * y) m = ∑ d₁, ∑ d₂,
    if d₁ * d₂ = m then (x d₁) * (y d₂) * (δ ^ Monoid.mul_exponent d₁ d₂) else 0 := by
  rw [mul_def]
  conv => {
    lhs
    rw [Fintype.sum_apply m]
    arg 2
    simp [Finset.sum_apply m (s := Finset.univ), smul_single δ]
  }
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  simp[eq_comm]

instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Algebra n δ) := {
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
    ∑ d₂ : (Diagram n n),  (x d₂) • (single δ (d₂ * d₁) (c * (δ ^ Monoid.mul_exponent d₂ d₁))) := by
  simp only [mul_def, single_apply, mul_ite, mul_zero, ite_smul, smul_single,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr
  ext x
  ring_nf

theorem single_mul (x : Algebra n δ) (d₁ : Diagram n n) (c : k) :
  (single δ d₁ c) * x =
    ∑ d₂ : (Diagram n n), (x d₂) • (single δ (d₁ * d₂) (c * (δ ^ Monoid.mul_exponent d₁ d₂))) := by
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
  simp only [Finset.univ.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  simp [smul_single]
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
instance nonUnitalSemiring :
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

instance hasOne : One (Algebra n δ) := ⟨one δ⟩

theorem one_def : (1 : Algebra n δ) = one δ := rfl

def one_is : (1 : Algebra n δ) = single δ (Diagram.id n) 1 := rfl

instance addGroupWithOne : AddGroupWithOne (Algebra n δ) := {}

instance is_semiring :
    Semiring (Algebra (k:=k) n δ) := {
  one_mul := fun a => by
    ext d
    rw [one_def]
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
    rw [one_def]
    rw [mul_apply]
    simp only [one_apply, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul]
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

def single_one_ring_hom : k →+* Algebra n δ :=
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

instance is_algebra (δ : k) :
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
    by_cases h : d₂ = x₁
    · simp only [h, ↓reduceIte]
      rw [Pi.smul_apply]
      simp
      simp [mul_comm r (x x₁)]
    · simp [h]
}

theorem algebra_map : algebraMap k (Algebra n δ) = single_one_ring_hom δ := rfl

/-- The planar rook algebra is independent of the parameter δ, up to algebra isomorphism, as long as
it is not zero.

This is to say, there are only "two" planar rook algebras, the one where δ = 0 and the one where δ
is nonzero (and might as well be 1).
-/
def parameter_independence (n : ℕ) (δ₁ : k) (δ₁_nonzero : δ₁ ≠ 0) :
    (Algebra n δ₁) ≃ₐ[k] (Algebra n (1 : k)) := {
      toFun := fun x => ∑ d , single 1 d (x d * (δ₁^ ((n : ℤ) - ↑d.through_index)))
      invFun := fun y => ∑ d, single δ₁ d (y d / (δ₁^ ((n : ℤ) - ↑d.through_index)))
      left_inv := by
        intro x
        simp only [Finset.univ.sum_apply, single_apply, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte]
        conv => {
          lhs
          arg 2
          intro x₁
          arg 3
          rw [←Int.ofNat_sub (Diagram.through_index_le_left _)]
          simp [δ₁_nonzero]
        }
        rw [←sum_single δ₁ x]
      right_inv := by
        intro x
        simp only [Finset.univ.sum_apply, single_apply, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte]
        conv => {
          lhs
          arg 2
          intro x₁
          arg 3
          rw [←Int.ofNat_sub (Diagram.through_index_le_left _)]
          simp [δ₁_nonzero]
        }
        rw [←sum_single 1 x]
      map_mul' := by
        intro x y
        simp only [Finset.sum_mul_sum, mul_single_single]
        ring_nf
        simp only [mul_assoc]
        apply ext
        intro d
        simp only [Finset.sum_apply d, single_apply]
        conv => {
          lhs
          rw [Finset.sum_ite_eq_of_mem (h:=Finset.mem_univ d)]
          rw [mul_apply]
          rw [Finset.sum_mul]
          arg 2
          ext x₁
          rw [Finset.sum_mul]
        }
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        apply Finset.sum_congr rfl
        intro x₂ hx₂
        rw [ite_mul]
        by_cases h : d = x₁ * x₂
        · simp only [h, ↓reduceIte]
          rw [←zpow_natCast]
          rw [←Int.ofNat_sub (Diagram.through_index_le_left x₁)]
          rw [←Int.ofNat_sub (Diagram.through_index_le_left x₂)]
          ring_nf
          conv => {
            rhs
            rw [mul_assoc]
            arg 2
            rw [←zpow_add' (Or.inl δ₁_nonzero)]
          }
          simp only [mul_assoc, ←zpow_add' (Or.inl δ₁_nonzero)]
          simp only [Monoid.mul_exponent, Finset.compl_union, Diagram.through_degree_of_mul,
            mul_eq_mul_left_iff]
          apply Or.inl
          apply Or.inl
          rw [Int.ofNat_sub (Diagram.through_index_le_left _)]
          rw [Int.ofNat_sub (Diagram.through_index_le_left _)]
          rw [←Finset.compl_union]
          rw [Finset.cast_card_inter]
          rw [Finset.compl_eq_univ_sdiff]
          rw [Finset.cast_card_sdiff (Finset.subset_univ _)]
          simp [Finset.card_univ]
          ring_nf
          rw[Diagram.through_index_eq_right]
          rw[Diagram.through_index_eq_left]

        · simp [h, eq_comm]
      map_add' := by
        intro x y
        simp only [add_coeff, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        rw [←add_single 1 x₁, ←add_mul]
      commutes' := by
        intro r
        simp only [algebra_map, single_one_ring_hom, one_is,
          RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        ext x
        simp [Finset.univ.sum_apply x, single_apply]
        by_cases h : x = (PlanarRook.Diagram.id n)
        · simp [h, PlanarRook.Diagram.through_index_of_id]
        · simp [h]
    }

instance ringConGen : Ring (Algebra n δ) := {is_semiring _, addGroupWithOne _ with}

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
