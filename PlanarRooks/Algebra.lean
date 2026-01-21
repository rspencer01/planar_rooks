import PlanarRooks.Diagrams
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators

variable {k : Type} [Field k] (δ : k)

-- The paramter δ is "unused" but must be carried around to define multiplication
set_option linter.unusedVariables false

def PlanarRookAlgebra (n : ℕ) (δ : k) := ((PlanarRookDiagram n n) → k)

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

noncomputable instance : Mul (PlanarRookAlgebra n δ) :=
  ⟨PlanarRookAlgebra.mul' δ⟩

theorem PlanarRookAlgebra.mul_def (x y : PlanarRookAlgebra n δ) :
    x * y =
      ∑ d₁ : (PlanarRookDiagram n n),
        ∑ d₂ : (PlanarRookDiagram n n),
          ((x d₁) * (y d₂)) •
            (PlanarRookAlgebra.single δ (d₁.mul₂ d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂)) :=
  rfl

noncomputable instance (δ : k) : NonUnitalSemiring (PlanarRookAlgebra n δ) := {
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := by simp [PlanarRookAlgebra.mul_def]
  mul_zero := by simp [PlanarRookAlgebra.mul_def]
  mul_assoc := sorry
}

instance PlanarRookAlgebra.hasOne : One (PlanarRookAlgebra n δ) :=
  ⟨PlanarRookAlgebra.one δ⟩

theorem PlanarRookAlgebra.one_def : (1 : PlanarRookAlgebra n δ) = PlanarRookAlgebra.one δ :=
  rfl

noncomputable instance (δ : k) : Semiring (PlanarRookAlgebra n δ) := {
  one_mul :=  sorry
  mul_one := sorry
}

#check Algebra
noncomputable instance (δ : k) : Algebra k (PlanarRookAlgebra n δ) := {
  algebraMap := sorry
  commutes' := sorry
  smul_def' := sorry
}
