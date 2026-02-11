/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import PlanarRooks.Cellular
import PlanarRooks.Algebra

/-! # Planar rooks algebras as a cellular algebra
-/

variable (k : Type) [Field k] (δ : k)
variable (n : ℕ)

noncomputable instance : CellularAlgebra k (PlanarRookAlgebra n δ) where
  Λ := Fin n
  Λ_order := by infer_instance
  Λ_fintype := by infer_instance
  tableau := fun k => {S : Finset (Fin n) // S.card = k}
  fintype_tableau := by infer_instance
  decidable_eq_tableau := by infer_instance
  c := Module.Basis.reindex (PlanarRookAlgebra.diagram_basis _) sorry
  ι_antiinvolution := sorry
  r := sorry
  multiplication_rule := sorry
