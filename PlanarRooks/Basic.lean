import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.PEquiv
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.Order.Defs.PartialOrder

import PlanarRooks.Diagrams

-- When two diagrams are composed, they form a number of dangling strings
def danglingStringsCount {n m p : ℕ}
  (d1 : PlanarRookDiagram n m) (d2 : PlanarRookDiagram m p) : ℕ :=
  let left_stubs : Finset (Fin m) := d1.right_defectsᶜ
  let right_stubs : Finset (Fin m) := d2.left_defectsᶜ
  let barbells : Finset (Fin m) := left_stubs ∩ right_stubs
  barbells.card

noncomputable def HomSpaceBasis (n m : ℕ) (k : Type) [Field k] :
  Module.Basis (PlanarRookDiagram n m) k ((PlanarRookDiagram n m) → k) :=
  Pi.basisFun k (PlanarRookDiagram n m)

variable (k : Type) [Field k] (δ : k) {x y z : ℕ}

noncomputable def compBasis :
      PlanarRookDiagram x y →
      PlanarRookDiagram y z →
      ((PlanarRookDiagram x z) → k) :=
      fun dxy dyz => (δ ^ danglingStringsCount dxy dyz) • (Pi.basisFun k _ (dxy.mul₂ dyz))


noncomputable def compLinear :
    ((PlanarRookDiagram x y) → k) →
    ((PlanarRookDiagram y z) → k) →
    ((PlanarRookDiagram x z) → k) := by
    classical
    refine ((Module.Basis.constr (HomSpaceBasis x y k) k ) ?_).toFun
    intro bxy
    refine ((Module.Basis.constr (HomSpaceBasis y z k) k) ?_).toFun
    intro byz
    exact compBasis k δ bxy byz

#check compLinear k δ

-- Now we construct a category.  The objects are natural numbers, and the morphisms
-- from n to m are linear spans of planar rook diagrams from n to m. We need to specify
-- a field and a fugicity parameter δ.

noncomputable def PlanarRookCategory (k : Type) [Field k] (δ : k) : CategoryTheory.Category ℕ where
  Hom := fun n m => (PlanarRookDiagram n m) → k
  id := fun n => fun d => if d = (PlanarRookDiagram.id n) then 1 else 0
  comp := compLinear k δ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

def PlanarRookAlgebra (k : Type) [Field k] (δ : k) (n : ℕ) :=
  (PlanarRookCategory k δ).Hom n n
deriving Module k, AddCommMonoid
