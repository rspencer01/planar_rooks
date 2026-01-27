import PlanarRooks.Diagrams
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators

variable {k : Type} [Field k] (δ : k)

-- The paramter δ is "unused" but must be carried around to define multiplication
set_option linter.unusedVariables false

def PlanarRookAlgebra (k : Type) (n : ℕ) (δ : k) := ((PlanarRookDiagram n n) → k)

@[ext]
def PlanarRookAlgebra.ext {n : ℕ} {δ : k} {x y : PlanarRookAlgebra k n δ} :
    (∀ d : PlanarRookDiagram n n, x d = y d) → x = y := fun h => by simp [funext h]

instance : AddCommMonoid (PlanarRookAlgebra k n δ) :=
  inferInstanceAs (AddCommMonoid ((PlanarRookDiagram n n) → k))

@[simp]
theorem PlanarRookAlgebra.zero_coeff (d : PlanarRookDiagram n n) :
    (0 : PlanarRookAlgebra k n δ) d = 0 :=
  rfl

@[simp]
theorem PlanarRookAlgebra.add_coeff (x₁ x₂ : PlanarRookAlgebra k n δ) (d : PlanarRookDiagram n n) :
    (x₁ + x₂) d = (x₁ d) + (x₂ d) :=
  rfl

instance : Module k (PlanarRookAlgebra k n δ) :=
  Pi.module _ _ k

def PlanarRookAlgebra.single : (PlanarRookDiagram n n) → k → PlanarRookAlgebra k n δ :=
  Function.update 0

def PlanarRookAlgebra.single_apply (d₁ d₂ : PlanarRookDiagram n n) (c : k) :
  (PlanarRookAlgebra.single δ d₁ c) d₂ = if d₂ = d₁ then c else 0 := by
    simp [PlanarRookAlgebra.single, Function.update]

theorem PlanarRookAlgebra.smul_single (d₁ : PlanarRookDiagram n n) (c₁ c₂ : k) :
  c₁ • (PlanarRookAlgebra.single δ d₁ c₂) = PlanarRookAlgebra.single δ d₁ (c₁ * c₂) := by
    ext x
    unfold PlanarRookAlgebra.single
    rw [←Function.update_smul]
    simp

theorem PlanarRookAlgebra.sum_single (x : PlanarRookAlgebra k n δ) :
  x = ∑ d : (PlanarRookDiagram n n), PlanarRookAlgebra.single δ d (x d) := by
    ext m
    rw [Finset.univ.sum_apply m]
    simp [PlanarRookAlgebra.single_apply]

theorem PlanarRookAlgebra.add_single (d : PlanarRookDiagram n n) (c₁ c₂ : k) :
  PlanarRookAlgebra.single δ d (c₁ + c₂) =
    PlanarRookAlgebra.single δ d c₁ + PlanarRookAlgebra.single δ d c₂ := by
    ext x
    simp [PlanarRookAlgebra.single_apply]
    by_cases h: x = d
    · simp [h]
    · simp [h]

/-- Multiplication in the planar rook algebra depends on a paramter δ

This paramter is raised to the exponent of the number of dangling strands
after monoid multiplication. -/
noncomputable def PlanarRookAlgebra.mul' (x y : PlanarRookAlgebra k n δ) :
    PlanarRookAlgebra k n δ :=
  ∑ d₁ : (PlanarRookDiagram n n),
    ∑ d₂ : (PlanarRookDiagram n n),
      ((x d₁) * (y d₂)) •
        (PlanarRookAlgebra.single δ (d₁ * d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂))

def PlanarRookAlgebra.one : PlanarRookAlgebra k n δ :=
  PlanarRookAlgebra.single δ (PlanarRookDiagram.id n) 1

def PlanarRookAlgebra.one_apply (d : PlanarRookDiagram n n) :
  (PlanarRookAlgebra.one δ) d = if PlanarRookDiagram.id n = d then 1 else 0 := by
    simp only [one, single_apply]
    by_cases h : PlanarRookDiagram.id n = d
    · simp [h]
    · rw [eq_comm] at h
      simp only [h, ↓reduceIte, right_eq_ite_iff, zero_ne_one, imp_false]
      rw [eq_comm] at h
      exact h


noncomputable instance : Mul (PlanarRookAlgebra k n δ) :=
  ⟨PlanarRookAlgebra.mul' δ⟩

theorem PlanarRookAlgebra.mul_def (x y : PlanarRookAlgebra k n δ) :
    x * y =
      ∑ d₁ : (PlanarRookDiagram n n),
        ∑ d₂ : (PlanarRookDiagram n n),
          ((x d₁) * (y d₂)) •
            (PlanarRookAlgebra.single δ (d₁ * d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂)) :=
  rfl

theorem PlanarRookAlgebra.mul_apply (x y : PlanarRookAlgebra k n δ) :
  (x * y) m = ∑ d₁, ∑ d₂,
    if d₁ * d₂ = m then (x d₁) * (y d₂) * (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂) else 0 := by
  rw [PlanarRookAlgebra.mul_def]
  conv => {
    lhs
    rw [Fintype.sum_apply m]
    arg 2
    simp [Finset.sum_apply m (s := Finset.univ)]
    simp [PlanarRookAlgebra.smul_single δ]
    simp [PlanarRookAlgebra.single_apply]
  }
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  simp[eq_comm]

-- Disable notation for now
--set_option pp.notation false
noncomputable instance PlanarRookAlgebra.nonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (PlanarRookAlgebra k n δ) := {
  left_distrib := fun a b c => by
    ext d
    simp only [PlanarRookAlgebra.add_coeff]
    rw [PlanarRookAlgebra.mul_apply]
    rw [PlanarRookAlgebra.mul_apply]
    rw [PlanarRookAlgebra.mul_apply]
    rw [←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : x * y = d
    · simp[h]
      ring
    · simp only [h]
      simp
  right_distrib := fun a b c => by
    ext d
    simp only [PlanarRookAlgebra.add_coeff]
    rw [PlanarRookAlgebra.mul_apply]
    rw [PlanarRookAlgebra.mul_apply]
    rw [PlanarRookAlgebra.mul_apply]
    rw [←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [←Finset.univ.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : x * y = d
    · simp[h]
      ring
    · simp only [h]
      simp
  zero_mul := by simp [PlanarRookAlgebra.mul_def]
  mul_zero := by simp [PlanarRookAlgebra.mul_def]
}

theorem PlanarRookAlgebra.mul_single (x : PlanarRookAlgebra k n δ)
    (d₁ : PlanarRookDiagram n n) (c : k) :
    x * (PlanarRookAlgebra.single δ d₁ c) =
      ∑ d₂ : (PlanarRookDiagram n n),
        (x d₂) •
          (PlanarRookAlgebra.single δ (d₂ * d₁)
            (c * (δ ^ PlanarRookMonoid.mul_exponent d₂ d₁))) := by
  rw [PlanarRookAlgebra.mul_def]
  conv => {
    lhs
    arg 2
    ext d₁
    arg 2
    ext d₁
    arg 1
    rw [PlanarRookAlgebra.single_apply]
    simp
  }
  conv => {
    lhs
    arg 2
    ext d₁
    simp [Finset.univ.sum_ite_eq']
  }
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  simp[PlanarRookAlgebra.smul_single δ]
  ring_nf

theorem PlanarRookAlgebra.single_mul (x : PlanarRookAlgebra k n δ)
    (d₁ : PlanarRookDiagram n n) (c : k) :
    (PlanarRookAlgebra.single δ d₁ c) * x =
      ∑ d₂ : (PlanarRookDiagram n n),
        (x d₂) •
          (PlanarRookAlgebra.single δ (d₁ * d₂)
            (c * (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂))) := by
  rw [PlanarRookAlgebra.mul_def]
  conv => {
    lhs
    arg 2
    ext d₁
    arg 2
    ext d₂
    arg 1
    rw [PlanarRookAlgebra.single_apply]
    simp
  }
  conv => {
    lhs
    arg 2
    ext d₁
    simp [Finset.univ.sum_ite_eq']
  }
  simp only [Finset.univ.sum_ite_eq', Finset.mem_univ, ↓reduceIte, PlanarRookDiagram.hmul_eq_mul]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  simp[PlanarRookAlgebra.smul_single δ]
  ring_nf


theorem PlanarRookAlgebra.mul_single_single (d₁ d₂ : PlanarRookDiagram n n) (c₁ c₂ : k) :
    (PlanarRookAlgebra.single δ d₁ c₁) *
      (PlanarRookAlgebra.single δ d₂ c₂) =
        PlanarRookAlgebra.single δ (d₁ * d₂)
          (c₁ * c₂ * (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂)) := by
  rw [PlanarRookAlgebra.mul_single δ]
  conv => {
    lhs
    arg 2
    ext d₁
    rw [PlanarRookAlgebra.single_apply]
    simp
  }
  rw [Finset.univ.sum_ite_eq']
  simp [PlanarRookAlgebra.smul_single δ]
  ring_nf

noncomputable instance PlanarRookAlgebra.nonUnitalSemiring :
    NonUnitalSemiring (PlanarRookAlgebra k n δ) := {
  mul_assoc := by
    intro a b c
    rw [PlanarRookAlgebra.sum_single _ a]
    rw [Finset.sum_mul (a:=b)]
    rw [Finset.sum_mul (a:=c)]
    rw [Finset.sum_mul (a:=b * c)]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    rw [PlanarRookAlgebra.sum_single _ b]
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul (a:=c)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    rw [PlanarRookAlgebra.sum_single _ c]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₃ hd₃
    rw [PlanarRookAlgebra.mul_single_single]
    rw [PlanarRookAlgebra.mul_single_single]
    rw [PlanarRookAlgebra.mul_single_single]
    rw [PlanarRookAlgebra.mul_single_single]
    rw [←PlanarRookMonoid.mul_assoc]
    ring_nf
    conv => {
      rhs
      arg 3
      arg 1
      rw [mul_assoc]
      arg 2
      rw [← pow_add (a := δ) (m:= PlanarRookMonoid.mul_exponent d₂ d₃)]
      arg 2
      rw [add_comm]
      rw [←PlanarRookMonoid.mul_exponent_assoc d₁ d₂ d₃]
    }
    conv => {
      lhs
      arg 3
      ring_nf
    }
    conv => {
      rhs
      arg 3
      ring_nf
    }
}

instance PlanarRookAlgebra.hasOne : One (PlanarRookAlgebra k n δ) :=
  ⟨PlanarRookAlgebra.one δ⟩

theorem PlanarRookAlgebra.one_def : (1 : PlanarRookAlgebra k n δ) = PlanarRookAlgebra.one δ :=
  rfl

noncomputable instance PlanarRookAlgebra.is_semiring :
    Semiring (PlanarRookAlgebra (k:=k) n δ) := {
  one_mul := fun a => by
    ext d
    rw [PlanarRookAlgebra.one_def]
    rw [PlanarRookAlgebra.mul_apply]
    simp only [PlanarRookDiagram.hmul_eq_mul, PlanarRookAlgebra.one_apply, ite_mul, one_mul,
      zero_mul]
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
      ↓reduceIte]
    conv => {
      arg 1
      arg 2
      ext x
      arg 1
      rw [←PlanarRookDiagram.hmul_eq_mul,PlanarRookDiagram.id_mul]
    }
    conv => {
      lhs
      rw [Finset.univ.sum_ite_eq']
    }
    rw [PlanarRookMonoid.mul_exponent_eq_zero_of_id']
    simp
  mul_one := by
    classical
    intro a
    ext d
    rw [PlanarRookAlgebra.one_def]
    rw [PlanarRookAlgebra.mul_apply]
    simp only [PlanarRookDiagram.hmul_eq_mul, one_apply, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul]
    conv => {
      lhs
      arg 2
      ext x
      arg 2
      ext y
      rw [←ite_and]
      simp [and_comm (a := x.mul y = d) (b :=PlanarRookDiagram.id n = y)]
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
      simp [←PlanarRookDiagram.hmul_eq_mul,PlanarRookDiagram.mul_id]
    }
    simp [@PlanarRookMonoid.mul_exponent_eq_zero_of_id n]
}

def PlanarRookAlgebra.one_is : (1 : PlanarRookAlgebra k n δ) =
  PlanarRookAlgebra.single δ (PlanarRookDiagram.id n) 1 :=
  rfl

def PlanarRookAlgebra.single_one_ring_hom : k →+* PlanarRookAlgebra k n δ :=
  {
    toFun := fun c => c • (1 : PlanarRookAlgebra k n δ)
    map_one' := one_smul _ _
    map_mul' := fun x y => by
      rw [PlanarRookAlgebra.one_is]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) x (1 : k)]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) y (1 : k)]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) (x * y) (1 : k)]
      rw [PlanarRookAlgebra.mul_single_single]
      rw [PlanarRookMonoid.mul_exponent_eq_zero_of_id']
      rw [←PlanarRookMonoid.one_def]
      simp
    map_zero' := by simp
    map_add' := fun x y => by
      rw [PlanarRookAlgebra.one_is]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) x (1 : k)]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) y (1 : k)]
      rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) (x + y) (1 : k)]
      simp only [mul_one]
      exact PlanarRookAlgebra.add_single δ _ _ _
  }

noncomputable instance (δ : k) : Algebra k (PlanarRookAlgebra k n δ) := {
  algebraMap := PlanarRookAlgebra.single_one_ring_hom δ,
  commutes' := fun r x => by
    unfold PlanarRookAlgebra.single_one_ring_hom
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [PlanarRookAlgebra.one_is]
    rw [PlanarRookAlgebra.smul_single]
    simp only [mul_one]
    rw [PlanarRookAlgebra.single_mul]
    rw [PlanarRookAlgebra.mul_single]
    conv => {
      lhs
      arg 2
      ext d₂
      rw [PlanarRookMonoid.mul_exponent_eq_zero_of_id']
      simp
      rw [←PlanarRookDiagram.hmul_eq_mul, PlanarRookDiagram.id_mul]
    }
    conv => {
      rhs
      arg 2
      ext d₁
      rw [PlanarRookMonoid.mul_exponent_eq_zero_of_id]
      simp
      rw [←PlanarRookDiagram.hmul_eq_mul, PlanarRookDiagram.mul_id]
    }
  smul_def' := fun r x => by
    unfold PlanarRookAlgebra.single_one_ring_hom
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [PlanarRookAlgebra.one_is]
    rw [PlanarRookAlgebra.smul_single δ (PlanarRookDiagram.id n) r (1 : k)]
    rw [PlanarRookAlgebra.single_mul]
    conv => {
      rhs
      arg 2
      ext d₁
      arg 2
      rw [PlanarRookMonoid.mul_exponent_eq_zero_of_id']
      rw [←PlanarRookMonoid.one_def]
      rw [PlanarRookMonoid.one_mul d₁]
      simp
    }
    rw [PlanarRookAlgebra.sum_single δ (r • x)]
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    ext d₂
    simp only [PlanarRookAlgebra.single_apply, PlanarRookAlgebra.smul_single δ]
    by_cases h : d₂ = x₁
    · simp only [h, ↓reduceIte]
      rw [Pi.smul_apply]
      simp
      simp [mul_comm r (x x₁)]
    · simp [h]
}
