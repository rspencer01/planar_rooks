/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Cellular algebras

This file defines cellular algebras, in the style of Graham and Lehrer. The definition is not
exactly the same as in their paper, but it is close enough for our purposes. We also define cell
modules and the resultant representation theory.
-/

variable (k : Type) [Field k]
variable (A : Type) [Ring A] [Algebra k A]

def spanall (Λ : Type) (S : Set Λ) (tableau : Λ → Type)
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  : Submodule k A :=
  Submodule.span k (Set.range (ι :=  Σ μ : S, tableau μ × tableau μ)
    (fun ⟨μ, (s, t)⟩ => c ⟨μ, (s, t)⟩))

def antiinvolution (A : Type) [Ring A] (f : A → A) : Prop := ∀ (a b : A), f (a * b) = f b * f a

/- A definition of a cellular algebra, in the style of Graham and Lehrer.
-/
class CellularAlgebra (k : Type) [Field k] (A : Type) [Ring A] [Algebra k A] where
  (Λ : Type)
  [Λ_order : PartialOrder Λ]
  [x: Fintype Λ]
  (tableau : Λ → Type)
  [fintype_tableau : ∀ μ : Λ, Fintype (tableau μ)]
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  (ι_antiinvolution : antiinvolution A (c.constr (S := k) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)))
  (r : Π (μ : Λ), (a : A) → tableau μ → tableau μ → k)
  (multiplication_rule : ∀ (μ : Λ) (s t : tableau μ) (a : A),
    a * (c ⟨μ, (s, t)⟩) ≡ ∑ (u : tableau μ), r μ a s u • (c ⟨μ, (u, t)⟩)
      [SMOD spanall k A Λ {ν : Λ | ν < μ} tableau c]
  )

variable [cellular : CellularAlgebra k A]

instance (μ : cellular.Λ) : Fintype (cellular.tableau μ) := cellular.fintype_tableau μ

theorem CellularAlgebra.c_injective {μ : Λ k A} {s₁ t₁ s₂ t₂ : tableau μ}
    (h : c ⟨μ, (s₁, t₁)⟩ = c ⟨μ, (s₂, t₂)⟩) :
  s₁ = s₂ ∧ t₁ = t₂ := by
    have k := Module.Basis.injective cellular.c h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at k
    exact k

noncomputable def CellularAlgebra.ι : A →ₗ[k] A :=
  c.constr (S := k) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)

-- Cellular algebras are equipped with an involution, which is the linear map that swaps
-- the two tableaux in the basis elements.
theorem CellularAlgebra.ι_involution : Function.Involutive (ι k A) := by
    unfold Function.Involutive
    have h := Module.Basis.constr_self (cellular.c) k  (LinearMap.id)
    have j (a: A): LinearMap.id (R:=k) a = a := rfl
    conv => {
      ext x
      arg 2
      rw[←j x]
      rw[←h]
    }
    conv => {
      ext x
      lhs
      rw [←LinearMap.comp_apply]
    }
    apply LinearMap.ext_iff.mp
    have q := Module.Basis.constr_comp (cellular.c) k (ι k A) (fun ⟨μ, (s,t)⟩ => c ⟨μ, (t, s)⟩)
    conv => {
      lhs
      arg 2
      unfold CellularAlgebra.ι
    }
    rw[← q]
    apply congrArg
    ext x
    have q := Module.Basis.constr_basis (cellular.c) k (fun ⟨μ, (s,t)⟩ => c ⟨μ, (t, s)⟩)
    conv => {
      lhs
      unfold CellularAlgebra.ι
      arg 2
      ext x
      rw[←q x]
    }
    simp

section CellularAlgebra

variable (k : Type) [Field k]
variable (A : Type) [Ring A] [Algebra k A]
variable [cellular : CellularAlgebra k A]

/-! ## Cell modules
-/

/-- A cell module can be thought of as being build on the basis of tableaux -/
def cell_module (μ : cellular.Λ) : Type := cellular.tableau μ →₀ k

noncomputable instance : AddCommMonoid (cell_module k A μ) :=
  inferInstanceAs (AddCommMonoid (cellular.tableau μ →₀ k))

noncomputable instance : Module k (cell_module k A μ) :=
  inferInstanceAs (Module k (cellular.tableau μ →₀ k))

noncomputable instance cell_module_basis (μ : cellular.Λ) :
  Module.Basis (cellular.tableau μ) k (cell_module k A μ) := {
  repr := LinearEquiv.refl k (CellularAlgebra.tableau μ →₀ k)
}

noncomputable instance cell_module_module (μ : cellular.Λ) : Module A (cell_module k A μ) where
  smul := fun a x => Module.Basis.constr (cell_module_basis k A μ) k
    (fun s => ∑ (u : cellular.tableau μ), (cellular.r μ a s u) • (cell_module_basis k A μ u))
    x
  mul_smul := sorry
  one_smul := sorry
  add_smul := sorry
  smul_add := sorry
  zero_smul := sorry
  smul_zero := sorry

end CellularAlgebra
