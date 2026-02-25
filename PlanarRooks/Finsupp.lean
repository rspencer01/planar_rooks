/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/

import Mathlib.Data.Finsupp.Basic

/-!
# Finite support functions

This module is almost exactly the same as `Mathlib.Data.Finsupp.Defs` but uses `Fintype`
instead of `Finite` to make certain equivalences computable.
-/


variable [DecidableEq k]

variable {α M : Type*} [Fintype α] [DecidableEq M] [Zero M]

@[simps]
def equivFunOnFinite : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := Finsupp.mk (Finset.univ.filter (f · ≠ 0)) f fun _a  => (by simp)

@[simp]
theorem equivFunOnFinite_symm_coe (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

@[simp]
lemma coe_equivFunOnFinite_symm (f : α → M) : ⇑(equivFunOnFinite.symm f) = f := rfl


@[simp]
theorem equivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]
theorem equivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single, Equiv.symm_apply_apply]
