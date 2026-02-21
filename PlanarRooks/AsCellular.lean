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
variable (n : ℕ) [NeZero n]

noncomputable instance : CellularAlgebra k (PlanarRookAlgebra n δ) where
  Λ := Fin (n + 1)
  Λ_order := by infer_instance
  Λ_fintype := by infer_instance
  tableau := fun k => {S : Finset (Fin n) // S.card = k}
  fintype_tableau := by infer_instance
  decidable_eq_tableau := by infer_instance
  inhabited_tableau := fun μ => ⟨(Finset.range μ).attachFin
    (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) (Nat.le_of_lt_succ μ.is_lt)), by simp⟩
  c := PlanarRookAlgebra.diagram_basis' δ
  ι_antiinvolution := by
    intro a b
    have q := PlanarRookAlgebra.diagram_basis'_ι δ (n:= n)
    rw [←PlanarRookAlgebra.foobar] at q
    rw [←q]
    exact PlanarRookAlgebra.ι_anti _ a b
  r := sorry
  multiplication_rule := sorry
