/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import PlanarRooks.Cellular
import PlanarRooks.Algebra
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.FunLike.Equiv
import Mathlib.Algebra.Module.Submodule.Defs

/-! # Planar rooks algebras as a cellular algebra
-/

variable (k : Type) [Field k] (δ : k) [DecidableEq k]
variable (n : ℕ)


theorem SModEq.refl' {R : Type u_1} [Ring R] {M : Type u_4} [AddCommGroup M]
  [Module R M] {U : Submodule R M} (x y : M) (h : x = y) :
  x ≡ y [SMOD U] := by rw [h]

noncomputable def my_r : (Σ ν : Fin (n + 1), {S : Finset (Fin n) // S.card = ↑ν } ×
                            {S : Finset (Fin n) // S.card = ↑ν }) →
        (μ : Fin (n + 1)) → { S : Finset (Fin n) // S.card = ↑μ } →
                            { S : Finset (Fin n) // S.card = ↑μ } → k := fun ⟨ν, S, T⟩ μ U V => by
    have a := PlanarRook.Diagram.mk S.val T.val (by rw[S.prop, T.prop])
    have cst := PlanarRook.Diagram.mk U.val U.val rfl
    have prod := a * cst
    exact if (prod.left_defects = V) then δ ^ (PlanarRook.Monoid.mul_exponent a cst) else 0

noncomputable instance : CellularAlgebra k (PlanarRook.Algebra n δ) where
  Λ := Fin (n + 1)
  Λ_order := by infer_instance
  Λ_fintype := by infer_instance
  tableau := fun k => {S : Finset (Fin n) // S.card = k}
  fintype_tableau := by infer_instance
  decidable_eq_tableau := by infer_instance
  inhabited_tableau := fun μ => ⟨(Finset.range μ).attachFin
    (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) (Nat.le_of_lt_succ μ.is_lt)), by simp⟩
  c := PlanarRook.Algebra.diagram_basis' δ
  ι_antiinvolution := by
    intro a b
    have q := PlanarRook.Algebra.diagram_basis'_ι δ (n:= n)
    rw [←PlanarRook.Algebra.foobar] at q
    rw [←q]
    exact PlanarRook.Algebra.ι_anti _ a b
  r_basis := my_r k δ n
  multiplication_rule_basis := fun ⟨ν, S₁, T₁⟩ μ s t => by
    unfold PlanarRook.Algebra.diagram_basis'
    simp only [Module.Basis.coe_reindex, Function.comp_apply]
    rw [PlanarRook.Algebra.diagram_basis_mul]
    unfold my_r
    by_cases h : ((@PlanarRook.Diagram.mk (n:=n) (m:=n) S₁.val T₁.val (by simp[S₁.prop, T₁.prop])) *
                  (@PlanarRook.Diagram.mk (n:=n) (m:=n) s.val s.val rfl)).through_index = μ
    · have q (x : {S : Finset (Fin n) // S.card = ↑μ}): (h' :
      ((PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]))  * (
              PlanarRook.Diagram.mk s.val s.val rfl)).left_defects.card =
        ↑μ) →
      (x =
        ⟨((PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]) *
              PlanarRook.Diagram.mk s.val s.val rfl)).left_defects,
          h'⟩) ↔
        ((PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]) *
              PlanarRook.Diagram.mk s.val s.val rfl)).left_defects = ↑x := by
            intro h'
            constructor
            · intro h''
              rw [h'']
            · intro h'''
              conv => {
                rhs
                arg 1
                rw [h''']
              }
      conv => {
        rhs
        arg 2
        ext x
        arg 1
        simp only
        rw [←@ite_cond_congr _ _ _ (s:= by infer_instance) (h₁ := propext_iff.mpr (q x h))]
      }
      conv => {
        rhs
        arg 2
        ext x
        rw [ite_zero_smul]
      }
      rw [Finset.sum_ite_eq_of_mem' (h:=by simp)]
      conv => {
        lhs
        unfold PlanarRook.Diagram.pi_iso₂
        unfold PlanarRook.Diagram.pi_iso'
        unfold PlanarRook.Diagram.pi_iso
        simp
      }
      rw [PlanarRook.Monoid.mul_exponent_of_right_arbitrary
        (PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]))
        (PlanarRook.Diagram.mk s.val s.val (by simp[s.prop]))
        (PlanarRook.Diagram.mk s.val t.val (by simp [s.prop, t.prop])) rfl]
      apply SModEq.smul
      apply SModEq.refl'
      congr
      simp only [PlanarRook.Diagram.pi_iso₂, PlanarRook.Diagram.pi_iso, PlanarRook.Diagram.pi_iso',
        Subtype.coe_eta, Prod.mk.eta, PlanarRook.Diagram.hmul_left_defects, Equiv.symm_trans_apply,
        Equiv.coe_fn_symm_mk]
      apply PlanarRook.Diagram.ext
      · simp
      · conv => {
          rhs
          simp
        }
        apply (Finset.eq_of_subset_of_card_le (PlanarRook.Diagram.mul_right_subset _ _))
        apply le_of_eq
        unfold PlanarRook.Diagram.through_index at h
        rw [PlanarRook.Diagram.consistant] at h
        conv => {
          lhs
          rw[t.prop]
          rw[←h]
        }
        rw [←PlanarRook.Diagram.consistant]
        rw [←PlanarRook.Diagram.consistant]
        rw [←PlanarRook.Diagram.through_index]
        rw [←PlanarRook.Diagram.through_index]
        exact PlanarRook.Diagram.through_index_of_mul_independent_of_right _ _ _ (by simp)
    · have q (x : {S : Finset (Fin n) // S.card = ↑μ}): (h' :
      ¬((PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]))  * (
              PlanarRook.Diagram.mk s.val s.val rfl)).left_defects.card =
        ↑μ) →
      False ↔
        ((PlanarRook.Diagram.mk S₁.val T₁.val (by simp[S₁.prop, T₁.prop]) *
              PlanarRook.Diagram.mk s.val s.val rfl)).left_defects = ↑x := by
            intro h'
            constructor
            · intro h
              contradiction
            · intro j
              have jj := congr_arg (Finset.card) j
              conv at jj => {
                rhs
                rw[x.prop]
              }
              contradiction
      conv => {
        rhs
        arg 2
        ext x
        arg 1
        simp only
        rw [←@ite_cond_congr _ _ _ (s:= by infer_instance) (h₁ := propext_iff.mpr (q x h))]
      }
      simp only [↓reduceIte, zero_smul, Finset.sum_const_zero]
      apply SModEq.zero.mpr
      apply Submodule.smul_mem
      conv => {
        arg 2
        simp [PlanarRook.Diagram.pi_iso₂, PlanarRook.Diagram.pi_iso', PlanarRook.Diagram.pi_iso]
      }
      have q (d : PlanarRook.Diagram n n) (h₁ : d.through_index < ↑μ ) :
        (PlanarRook.Algebra.diagram_basis δ) d ∈
        tableau_linear_span (PlanarRook.Algebra n δ) (Fin (n + 1)) {ν | ν < μ}
        (fun k ↦ { S : Finset (Fin n) // S.card = ↑k })
        ((PlanarRook.Algebra.diagram_basis δ).reindex PlanarRook.Diagram.pi_iso₂) := by
          unfold tableau_linear_span
          apply Submodule.mem_span_of_mem
          unfold all_tableaux_range
          apply (Set.mem_image _ _ _).mpr
          unfold double_tableaux_in
          simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, Module.Basis.coe_reindex,
            Function.comp_apply, Sigma.exists, exists_and_left, Prod.exists, Subtype.exists]
          use ⟨d.through_index, Nat.lt_succ_iff.mpr (PlanarRook.Diagram.through_index_le_left d)⟩
          constructor
          · rw [Fin.lt_def]
            simp [h₁]
          · use d.left_defects
            use rfl
            use d.right_defects
            use d.through_index_eq_right.symm
            congr
      apply q
      rw [PlanarRook.Diagram.through_index_of_mul_independent_of_right _
          (PlanarRook.Diagram.mk s.val t.val (by simp [s.prop, t.prop]))
          (PlanarRook.Diagram.mk s.val s.val rfl) (by simp)]
      apply lt_of_le_of_ne _ h
      apply (PlanarRook.Monoid.mul_not_increase_through_degree _ _).trans
      simp[PlanarRook.Diagram.through_index, s.prop]
