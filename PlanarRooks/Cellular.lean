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
import Mathlib.Algebra.Quotient
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Cellular algebras

This file defines cellular algebras, in the style of Graham and Lehrer. The definition is not
exactly the same as in their paper, but it is close enough for our purposes. We also define cell
modules and the resultant representation theory.
-/

variable (k : Type) [Field k]
variable (A : Type) [Ring A] [Algebra k A]

/-! ## Preliminary and helper definitions

To speak naturally about cellular algebras it will be useful to have some shorthands for tableaux
sets and spans. Here, as in the definition that follows, $\Lambda$ is some type of "weights" and
there is map that takes a weight to a set of "tableaux" for that weight.
-/

/- The set of all triples ${}^\mu_{s_1, s_2}$ where $\mu$ is a weight in some set and $s_1, s_2$ are
tableaux of shape $\mu$.

We express it here as the preimage of the set $S$ under the map from all triples ${}^\mu_{s_1, s_2}$
to their weight $\mu$.
-/
def double_tableaux_in (Λ : Type) (S : Set Λ) (tableau : Λ → Type) :
  Set (Σ μ : Λ, tableau μ × tableau μ) :=
  Sigma.fst⁻¹' S

lemma double_tableaux_in_mono {Λ : Type} {S₁ S₂ : Set Λ} {tableau : Λ → Type} (h : S₁ ⊆ S₂) :
  double_tableaux_in Λ S₁ tableau ⊆ double_tableaux_in Λ S₂ tableau :=
    Set.preimage_mono h

def all_tableaux_range (Λ : Type) (S : Set Λ) (tableau : Λ → Type)
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A) :=
     c '' double_tableaux_in Λ S tableau

def tableau_span' (Λ : Type) (S : Set Λ) (tableau : Λ → Type)
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  : Submodule k A :=
  Submodule.span k (all_tableaux_range k A Λ S tableau c)

/- An anti-involution is a linear involution that reverses the order of multiplication .
-/
def antiinvolution (f : A →ₗ[k] A) : Prop :=
  (Function.Involutive f) ∧ ∀ (a b : A), f (a * b) = f b * f a

/-! ## Main definition
-/

/- A definition of a cellular algebra, in the style of Graham and Lehrer.
-/
class CellularAlgebra (k : Type) [Field k] (A : Type) [Ring A] [Algebra k A] where
  (Λ : Type)
  [Λ_order : PartialOrder Λ]
  [Λ_fintype: Fintype Λ]
  (tableau : Λ → Type)
  [fintype_tableau : ∀ μ : Λ, Fintype (tableau μ)]
  [decidable_eq_tableau : ∀ μ : Λ, DecidableEq (tableau μ)]
  [inhabited_tableau : ∀ μ : Λ, Inhabited (tableau μ)]
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  (ι_antiinvolution : antiinvolution k A (c.constr (S := k) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)))
  (r : Π (μ : Λ), A →ₗ[k] tableau μ → tableau μ → k)
  (multiplication_rule : ∀ (μ : Λ) (s t : tableau μ) (a : A),
    a * (c ⟨μ, (s, t)⟩) ≡ ∑ (u : tableau μ), r μ a s u • (c ⟨μ, (u, t)⟩)
      [SMOD tableau_span' k A Λ {ν : Λ | ν < μ} tableau c]
  )

variable [cellular : CellularAlgebra k A]

/-! ### Instances and restatements

For convenience, we restate some of the data of a cellular algebra as instances, so that we can use
them without having to refer to the `cellular` namespace.
-/
instance (μ : cellular.Λ) : Fintype (cellular.tableau μ) := cellular.fintype_tableau μ
instance (μ : cellular.Λ) : DecidableEq (cellular.tableau μ) := cellular.decidable_eq_tableau μ
instance : PartialOrder cellular.Λ := cellular.Λ_order
instance : LE cellular.Λ := cellular.Λ_order.toLE
instance : LT cellular.Λ := cellular.Λ_order.toLT
instance (μ : cellular.Λ) : Inhabited (cellular.tableau μ) := cellular.inhabited_tableau μ

/- The subspace of $A$ spanned by the basis elements corresponding to tableaux of weights in a set
$S$.
-/
def CellularAlgebra.tableau_span (S : Set cellular.Λ) : Submodule k A :=
  tableau_span' k A cellular.Λ S cellular.tableau cellular.c

def CellularAlgebra.tableau_span_mono (S₁ S₂ : Set cellular.Λ) (h : S₁ ⊆ S₂) :
  CellularAlgebra.tableau_span k A S₁ ≤ CellularAlgebra.tableau_span k A S₂ :=
    Submodule.span_mono (Set.image_mono (double_tableaux_in_mono h))

def CellularAlgebra.tableau_span_mono' (S₁ S₂ : Set cellular.Λ) (h : S₁ ⊂ S₂) :
  CellularAlgebra.tableau_span k A S₁ < CellularAlgebra.tableau_span k A S₂ := by
    apply lt_of_le_of_ne
    · exact tableau_span_mono k A S₁ S₂ h.subset
    · have ⟨q, ⟨hq₁, hq₂⟩⟩ := Set.exists_of_ssubset h
      unfold tableau_span
      unfold tableau_span'
      simp only [ne_eq]
      intro h
      have k₁ := Submodule.ext_iff.mp h
      let t : tableau q × tableau q := Inhabited.default
      have kk := (k₁ (c ⟨q, t⟩)).mpr
      rw[all_tableaux_range] at kk
      have q : c ⟨q, t⟩ ∈ Submodule.span k (all_tableaux_range k A _ S₂ tableau c) := by
        apply Submodule.mem_span_of_mem
        unfold all_tableaux_range
        unfold double_tableaux_in
        apply (Set.mem_image _ _ _).mpr
        use ⟨q, t⟩
        simp [hq₁]
      have kk₂ := kk q
      have jj := (Module.Basis.self_mem_span_image cellular.c).mp kk₂
      unfold double_tableaux_in at jj
      simp at jj
      contradiction

theorem CellularAlgebra.c_injective {μ : Λ k A} {s₁ t₁ s₂ t₂ : tableau μ}
    (h : c ⟨μ, (s₁, t₁)⟩ = c ⟨μ, (s₂, t₂)⟩) :
  s₁ = s₂ ∧ t₁ = t₂ := by
    have k := Module.Basis.injective cellular.c h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at k
    exact k

theorem CellularAlgebra.r_of_id {μ} {s u : cellular.tableau μ} :
  r μ (1 : A) s u = if s = u then 1 else 0 := sorry

theorem CellularAlgebra.r_of_zero {μ} {s u : cellular.tableau μ} :
  r μ (0 : A) s u = 0 := by simp only [map_zero, Pi.zero_apply]

theorem CellularAlgebra.action_doesnt_increase_μ
  (a : A) (μ : cellular.Λ) (s t : cellular.tableau μ) :
  a * c ⟨μ, (s, t)⟩ ∈ cellular.tableau_span k A {ν | ν ≤ μ} := by
    have h := cellular.multiplication_rule μ s t a
    have q := SModEq.sub_mem.mp h
    have ss : ({ν | ν < μ} ⊆ {ν | ν ≤ μ}) := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact le_of_lt ha
    have sst := tableau_span_mono k A _ _ ss
    have tt : ∀ x, x∈ tableau_span k A {ν | ν < μ} → x ∈ tableau_span k A {ν | ν ≤ μ} := by
      intro x hx
      exact sst hx
    apply tt at q
    have ttt: ∑ u, (r μ) a s u • c ⟨μ, (u, t)⟩ ∈ tableau_span k A {ν | ν ≤ μ} := by
      apply Submodule.sum_mem
      intro sc hsc
      apply Submodule.smul_mem
      unfold tableau_span
      unfold tableau_span'
      apply Submodule.mem_span_of_mem
      unfold all_tableaux_range
      simp only [Set.mem_image, Sigma.exists, Prod.exists]
      use μ
      use sc
      use t
      constructor
      · unfold double_tableaux_in
        simp
      · rfl
    have tttu := Submodule.add_mem _ q ttt
    simp only [sub_add_cancel] at tttu
    exact tttu

def CellularAlgebra.celluar_ideal (μ : cellular.Λ) : Submodule A A := {
  carrier := CellularAlgebra.tableau_span k A {ν | ν ≤ μ} ,
  add_mem' := Submodule.add_mem _,
  zero_mem' := Submodule.zero_mem _,
  smul_mem' := by
    intro c x hx
    have k := (Finsupp.mem_span_image_iff_linearCombination _).mp hx
    simp only at k
    obtain ⟨l, ⟨hl₁, hl₂⟩⟩ := k
    rw [←hl₂]
    simp only [smul_eq_mul, SetLike.mem_coe]
    rw[Finsupp.linearCombination_apply]
    rw[Finsupp.mul_sum]
    simp only [Algebra.mul_smul_comm]
    apply Submodule.sum_mem
    intro c₁ hc₁
    simp only
    apply Submodule.smul_mem
    have tt := hl₁ hc₁
    unfold double_tableaux_in at tt
    simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at tt
    have q := action_doesnt_increase_μ k A c c₁.fst c₁.snd.1 c₁.snd.2
    have s : {ν | ν ≤ c₁.fst} ⊆ {ν | ν ≤ μ } := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact ha.trans tt
    have t := tableau_span_mono k A _ _ s
    apply t
    have c₁def : c₁ = ⟨c₁.fst, (c₁.snd.1, c₁.snd.2)⟩ := rfl
    rw [←c₁def] at q
    exact q
}
def CellularAlgebra.subcelluar_ideal (μ : cellular.Λ) : Submodule A A := {
  carrier := CellularAlgebra.tableau_span k A {ν | ν < μ} ,
  add_mem' := Submodule.add_mem _,
  zero_mem' := Submodule.zero_mem _,
  smul_mem' := by
    intro c x hx
    have k := (Finsupp.mem_span_image_iff_linearCombination _).mp hx
    simp only at k
    obtain ⟨l, ⟨hl₁, hl₂⟩⟩ := k
    rw [←hl₂]
    simp only [smul_eq_mul, SetLike.mem_coe]
    rw[Finsupp.linearCombination_apply]
    rw[Finsupp.mul_sum]
    simp only [Algebra.mul_smul_comm]
    apply Submodule.sum_mem
    intro c₁ hc₁
    simp only
    apply Submodule.smul_mem
    have tt := hl₁ hc₁
    unfold double_tableaux_in at tt
    simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at tt
    have q := action_doesnt_increase_μ k A c c₁.fst c₁.snd.1 c₁.snd.2
    have s : {ν | ν ≤ c₁.fst} ⊆ {ν | ν < μ } := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact lt_of_le_of_lt ha tt
    have t := (tableau_span_mono k A _ _ s)
    apply t
    have c₁def : c₁ = ⟨c₁.fst, (c₁.snd.1, c₁.snd.2)⟩ := rfl
    rw [←c₁def] at q
    exact q
}

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

noncomputable instance : AddCommGroup (cell_module k A μ) :=
  inferInstanceAs (AddCommGroup (cellular.tableau μ →₀ k))

noncomputable instance : Module k (cell_module k A μ) :=
  inferInstanceAs (Module k (cellular.tableau μ →₀ k))

noncomputable instance cell_module_basis (μ : cellular.Λ) :
  Module.Basis (cellular.tableau μ) k (cell_module k A μ) := {
  repr := LinearEquiv.refl k (CellularAlgebra.tableau μ →₀ k)
}

noncomputable instance cellular_action {μ} : SMul A (cell_module k A μ) := {
  smul := fun a x => Module.Basis.constr (cell_module_basis k A μ) k
    (fun s => ∑ (u : cellular.tableau μ), (cellular.r μ a s u) • (cell_module_basis k A μ u))
    x
  }

--disable notation
noncomputable instance cell_module_module (μ : cellular.Λ) : Module A (cell_module k A μ) where
  mul_smul := by
    intro x y b
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    sorry
  one_smul := by
    intro b
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp only [cellular_action, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
      CellularAlgebra.r_of_id k A, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Module.Basis.sum_repr]
  add_smul := by
    intro a b y
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp only [cellular_action]
    have k : cellular.r μ (a + b) = cellular.r μ a + cellular.r μ b := sorry
    conv => {
      lhs
      arg 1
      arg 2
      ext s
      arg 2
      ext u
      rw [k]
    }
    simp only [Pi.add_apply, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply]
    rw[←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.smul_sum]
    rw [Finset.smul_sum]
    rw [Finset.smul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [←smul_add]
    conv => {
      lhs
      arg 2
      rw [add_smul]
    }
  smul_add := by
    intro a x y
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp only [cellular_action]
    rw [LinearMap.map_add]
  zero_smul := by
    intro x
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    unfold cellular_action
    simp[CellularAlgebra.r_of_zero k A]
  smul_zero := by
    intro a
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp[cellular_action]

def cell_module_form (μ : cellular.Λ) : cell_module k A μ →ₗ[k] (cell_module k A μ) →ₗ[k] k :=
  sorry

def cell_module_form_contravariant (μ : cellular.Λ) (a : A) (x y : cell_module k A μ) :
  cell_module_form k A μ (a • x) y = cell_module_form k A μ x (cellular.ι k A a • y) := sorry

def cell_module_radical (μ : cellular.Λ) : Submodule A (cell_module k A μ) := {
  carrier := {x | ∀ y, cell_module_form k A μ x y = 0},
  add_mem' := by
    intro x₁ x₂ hx₁ hx₂
    simp only [Set.mem_setOf_eq] at hx₁ hx₂
    simp only [Set.mem_setOf_eq, map_add, LinearMap.add_apply]
    intro y
    have hy₁ := hx₁ y
    have hy₂ := hx₂ y
    simp [hy₁, hy₂]
  zero_mem' := by
    intro y
    simp only [map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c x hx y
    rw [cell_module_form_contravariant k A μ c x y]
    exact hx _
  }

def simple_module (μ : cellular.Λ) : Type := (cell_module k A μ) ⧸ (cell_module_radical k A μ)

/- Note these should be able to be removed once some sorries are filled in -/
instance : AddCommGroup (simple_module k A μ) := sorry
instance : Module A (simple_module k A μ) := sorry

theorem simple_module_simple (μ : cellular.Λ) : IsSimpleModule A (simple_module k A μ) := sorry

end CellularAlgebra
