/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import PlanarRooks.Cellular
import PlanarRooks.Algebra
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.FunLike.Equiv

/-! # Planar rooks algebras as a cellular algebra
-/

variable (k : Type) [Field k] (δ : k)
variable (n : ℕ)


theorem SModEq.refl' {R : Type u_1} [Ring R] {M : Type u_4} [AddCommGroup M] [Module R M] {U : Submodule R M} (x y : M) (h : x = y) :
  x ≡ y [SMOD U] := by rw [h]

noncomputable def my_r : (Σ ν : Fin (n + 1), {S : Finset (Fin n) // S.card = ↑ν } ×
                            {S : Finset (Fin n) // S.card = ↑ν }) →
        (μ : Fin (n + 1)) → { S : Finset (Fin n) // S.card = ↑μ } →
                            { S : Finset (Fin n) // S.card = ↑μ } → k := fun ⟨ν, S, T⟩ μ U V => by
    have a := PlanarRook.Diagram.mk S.val T.val (by rw[S.prop, T.prop])
    have cst := PlanarRook.Diagram.mk U.val U.val rfl
    have prod := a * cst
    by_cases prod.left_defects = V
    · exact δ ^ (PlanarRook.Monoid.mul_exponent a cst)
    · exact 0

noncomputable instance aasdf: CellularAlgebra k (PlanarRookAlgebra n δ) where
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
  r_basis := my_r k δ n
  multiplication_rule_basis := fun ⟨μ, S₁, T₁⟩ s t a => by
    unfold PlanarRookAlgebra.diagram_basis'
    simp
    rw [PlanarRookAlgebra.diagram_basis_mul]
    unfold my_r
    sorry
