/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Lemmata for module bases

This file just exists until the project can update to mathlib version 4.29 as it has
been proven (along with other useful lemmata) there.
-/

namespace Module.Basis

variable {ι : Type*} {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
variable (b : Module.Basis ι R M)

lemma linearIndepOn (s : Set ι) : LinearIndepOn R b s :=
  b.linearIndependent.linearIndepOn.mono s.subset_univ

end Module.Basis
