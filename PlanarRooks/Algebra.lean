import PlanarRooks.Diagrams
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators

variable (k : Type) [Field k] (δ : k)

def PlanarRookAlgebra (n : ℕ) := ((PlanarRookDiagram n n) → k)

instance : AddCommMonoid (PlanarRookAlgebra k n) :=
  inferInstanceAs (AddCommMonoid ((PlanarRookDiagram n n) → k))

instance : Module k (PlanarRookAlgebra k n) :=
  Pi.module _ _ k

def PlanarRookAlgebra.single (n : ℕ) : (PlanarRookDiagram n n) → k → PlanarRookAlgebra k n :=
  Function.update 0

noncomputable def PlanarRookAlgebra.mul' (x y : PlanarRookAlgebra k n) : PlanarRookAlgebra k n :=
  ∑ d₁ : (PlanarRookDiagram n n),
    ∑ d₂ : (PlanarRookDiagram n n),
      ((x d₁) * (y d₂)) •
        (PlanarRookAlgebra.single k n (d₁.mul₂ d₂) (δ ^ PlanarRookMonoid.mul_exponent d₁ d₂))

def PlanarRookAlgebra.one : PlanarRookAlgebra k n :=
  PlanarRookAlgebra.single k n (PlanarRookDiagram.id n) 1

noncomputable instance muinst (δ : k) : Semiring (PlanarRookAlgebra k n) := {
  mul := PlanarRookAlgebra.mul' k δ,
  one := PlanarRookAlgebra.one k,
  left_distrib := sorry
  right_distrib := sorry
  mul_one := sorry
  one_mul := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
}

noncomputable instance (δ : k) : @Algebra k (PlanarRookAlgebra k n) _ (muinst k δ) := sorry
