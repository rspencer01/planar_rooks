import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Basis.Defs

variable (k : Type) [Field k]
variable (A : Type) [Ring A] [Algebra k A]

def spanall (Λ : Type) (S : Set Λ) (tableau : Λ → Type)
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  : Submodule k A :=
  Submodule.span k (Set.range (ι :=  Σ μ : S, tableau μ × tableau μ)
    (fun ⟨μ, (s, t)⟩ => c ⟨μ, (s, t)⟩))

-- A definition of a cellular algebra, in the style of Graham and Lehrer.
class CellularAlgebra (k : Type) [Field k] (A : Type) [Ring A] [Algebra k A] where
  (Λ : Type)
  [Λ_order : PartialOrder Λ]
  [x: Fintype Λ]
  (tableau : Λ → Type)
  [fintype_tableau : ∀ μ : Λ, Fintype (tableau μ)]
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  (r : Π (μ : Λ), (a : A) → tableau μ → tableau μ → k)
  (multiplication_rule : ∀ (μ : Λ) (s t : tableau μ) (a : A),
    a * (c ⟨μ, (s, t)⟩) ≡ ∑ (u : tableau μ), r μ a s u • (c ⟨μ, (u, t)⟩)
      [SMOD spanall k A Λ {ν : Λ | ν < μ} tableau c]
  )

variable [cellular : CellularAlgebra k A]

theorem CellularAlgebra.c_injective {μ : Λ k A} {s₁ t₁ s₂ t₂ : tableau μ}
    (h : c ⟨μ, (s₁, t₁)⟩ = c ⟨μ, (s₂, t₂)⟩) :
  s₁ = s₂ ∧ t₁ = t₂ := by
    have h₂ := Module.Basis.injective cellular.c
    have k := h₂ h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at k
    exact k

noncomputable def CellularAlgebra.ι : A →ₗ[k] A :=
  Module.Basis.constr (S := k) (cellular.c) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)

theorem CellularAlgebra.ι_involution:
  Function.Involutive (ι k A) := by
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
    simp
    conv => {
      lhs
      unfold CellularAlgebra.ι
      rw [Module.Basis.constr_basis (cellular.c) k (fun ⟨μ, (s,t)⟩ => c ⟨μ, (t, s)⟩) ]
    }
    apply LinearMap.ext
    sorry

#check congrArg
