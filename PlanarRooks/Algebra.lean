import PlanarRooks.Diagrams
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators

variable {k : Type} [Field k] (δ : k)

-- The paramter δ is "unused" but must be carried around to define multiplication
set_option linter.unusedVariables false

def PlanarRookAlgebra (n : ℕ) (δ : k) := ((PlanarRookDiagram n n) → k)

@[ext]
def PlanarRookAlgebra.ext {n : ℕ} {δ : k} {x y : PlanarRookAlgebra n δ} :
    (∀ d : PlanarRookDiagram n n, x d = y d) → x = y := fun h => by simp [funext h]

instance : AddCommMonoid (PlanarRookAlgebra n δ) :=
  inferInstanceAs (AddCommMonoid ((PlanarRookDiagram n n) → k))

@[simp]
theorem PlanarRookAlgebra.zero_coeff (d : PlanarRookDiagram n n) :
    (0 : PlanarRookAlgebra n δ) d = 0 :=
  rfl

@[simp]
theorem PlanarRookAlgebra.add_coeff (x₁ x₂ : PlanarRookAlgebra n δ) (d : PlanarRookDiagram n n) :
    (x₁ + x₂) d = (x₁ d) + (x₂ d) :=
  rfl

instance : Module k (PlanarRookAlgebra n δ) :=
  Pi.module _ _ k

def PlanarRookAlgebra.single : (PlanarRookDiagram n n) → k → PlanarRookAlgebra n δ :=
  Function.update 0

def PlanarRookAlgebra.single_apply (d₁ d₂ : PlanarRookDiagram n n) (c : k) :
  (PlanarRookAlgebra.single δ d₁ c) d₂ = if d₂ = d₁ then c else 0 := by
    simp [PlanarRookAlgebra.single, Function.update]

def PlanarRookAlgebra.smul_single (d₁ : PlanarRookDiagram n n) (c₁ c₂ : k) :
  c₁ • (PlanarRookAlgebra.single δ d₁ c₂) = PlanarRookAlgebra.single δ d₁ (c₁ * c₂) := by
    ext x
    unfold PlanarRookAlgebra.single
    rw [←Function.update_smul]
    simp

theorem PlanarRookAlgebra.sum_single (x : PlanarRookAlgebra n δ) :
  x = ∑ d : (PlanarRookDiagram n n), PlanarRookAlgebra.single δ d (x d) := by
    ext m
    rw [Finset.univ.sum_apply m]
    simp [PlanarRookAlgebra.single_apply]

/-- Multiplication in the planar rook algebra depends on a paramter δ

This paramter is raised to the exponent of the number of dangling strands
after monoid multiplication. -/
noncomputable def PlanarRookAlgebra.mul' (x y : PlanarRookAlgebra n δ) : PlanarRookAlgebra n δ :=
  ∑ d₁ : (PlanarRookDiagram n n),
    ∑ d₂ : (PlanarRookDiagram n n),
      ((x d₁) * (y d₂)) •
        (PlanarRookAlgebra.single δ (d₁.mul₂ d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂))

def PlanarRookAlgebra.one : PlanarRookAlgebra n δ :=
  PlanarRookAlgebra.single δ (PlanarRookDiagram.id n) 1

def PlanarRookAlgebra.one_apply (d : PlanarRookDiagram n n) :
  (PlanarRookAlgebra.one δ) d = if d = PlanarRookDiagram.id n then 1 else 0 := by
    simp [PlanarRookAlgebra.one, PlanarRookAlgebra.single_apply]

noncomputable instance : Mul (PlanarRookAlgebra n δ) :=
  ⟨PlanarRookAlgebra.mul' δ⟩

theorem PlanarRookAlgebra.mul_def (x y : PlanarRookAlgebra n δ) :
    x * y =
      ∑ d₁ : (PlanarRookDiagram n n),
        ∑ d₂ : (PlanarRookDiagram n n),
          ((x d₁) * (y d₂)) •
            (PlanarRookAlgebra.single δ (d₁.mul₂ d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂)) :=
  rfl

theorem PlanarRookAlgebra.mul_apply (x y : PlanarRookAlgebra n δ) :
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
  have mul_def : x₁ * x₂ = x₁.mul₂ x₂ := rfl
  simp[eq_comm, mul_def]


noncomputable instance (δ : k) : NonUnitalSemiring (PlanarRookAlgebra n δ) := {
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
    · simp[h]
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
    · simp[h]
  zero_mul := by simp [PlanarRookAlgebra.mul_def]
  mul_zero := by simp [PlanarRookAlgebra.mul_def]
  mul_assoc := sorry
}

instance PlanarRookAlgebra.hasOne : One (PlanarRookAlgebra n δ) :=
  ⟨PlanarRookAlgebra.one δ⟩

theorem PlanarRookAlgebra.one_def : (1 : PlanarRookAlgebra n δ) = PlanarRookAlgebra.one δ :=
  rfl

noncomputable instance (δ : k) : Semiring (PlanarRookAlgebra n δ) := {
  one_mul := fun a => sorry
  mul_one := sorry
}

noncomputable instance (δ : k) : Algebra k (PlanarRookAlgebra n δ) := {
  algebraMap := sorry
  commutes' := sorry
  smul_def' := sorry
}
