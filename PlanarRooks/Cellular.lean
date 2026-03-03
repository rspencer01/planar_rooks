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
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Quotient
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import PlanarRooks.Basis

/-! # Cellular algebras

This file defines cellular algebras, in the style of Graham and Lehrer. The definition is not
exactly the same as in their paper, but it is close enough for our purposes. We also define cell
modules and the resultant representation theory.
-/

variable {k : Type} [Field k]
variable (A : Type) [Ring A] [Algebra k A]

/-! ## Preliminary and helper definitions

To speak naturally about cellular algebras it will be useful to have some shorthands for tableaux
sets and spans. Here, as in the definition that follows, $\Lambda$ is some type of "weights" and
there is map that takes a weight to a set of "tableaux" for that weight.
-/

/-- The set of all triples ${}^\mu_{s_1, s_2}$ where $\mu$ is a weight in some set and $s_1, s_2$
are tableaux of shape $\mu$.

We express it here as the preimage of the set $S$ under the map from all triples ${}^\mu_{s_1, s_2}$
to their weight $\mu$.
-/
def double_tableaux_in {Λ : Type} (S : Set Λ) (tableau : Λ → Type) :
  Set (Σ μ : Λ, tableau μ × tableau μ) := Sigma.fst⁻¹' S

/-- Increasing the set of weights increases the set of all double-tableaux. -/
lemma double_tableaux_in_mono {Λ : Type} {S₁ S₂ : Set Λ} {tableau : Λ → Type} (h : S₁ ⊆ S₂) :
  double_tableaux_in S₁ tableau ⊆ double_tableaux_in S₂ tableau := Set.preimage_mono h

def all_tableaux_range {Λ : Type} (S : Set Λ) {tableau : Λ → Type}
  (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A) :=
     c '' double_tableaux_in S tableau

/-- The `k`-linear span of a subset of tableaux.

When this is a subset of weights closed under the partial order, we will show taht this is a
two-sided ideal of the cellular algebra. However, we need a definition now so that we can talk
about the multiplication rule for the basis elements.
-/
def tableau_linear_span {A : Type} [Ring A] [Algebra k A] {Λ : Type} (S : Set Λ)
  {tableau : Λ → Type} (c : Module.Basis (ι := Σ μ : Λ, tableau μ × tableau μ) k A)
  : Submodule k A := Submodule.span k (all_tableaux_range A S c)

notation:50  c "over" S  => tableau_linear_span S c

/-- An anti-involution is a linear involution that reverses the order of multiplication.
-/
def antiinvolution (f : A →ₗ[k] A) : Prop := ∀ (a b : A), f (a * b) = f b * f a

/-! ## Main definition
-/

/-- A definition of a cellular algebra, in the style of Graham and Lehrer.

In this definition, instead of asking for a linear form $r$ over all of $A$, we just ask
for an arbitrary function defined on the basis elements. This is extended to all of $A$
by linearity in `CellularAlgebra.r`.

Similarly, the multiplication condition is most often written as a condition on
$a \cdot c^\mu_{s, t}$, but we ask for a condition on $c^ν_{s', t'} \cdot c^\mu_{s, t}$ for
simplicity, and then extend it to all of $A$ in `CellularAlgebra.multiplication_rule`.
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
  (ι_antiinvolution : antiinvolution A (c.constr (S := k) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)))
  (r_basis : (Σ ν : Λ, tableau ν × tableau ν) → (μ : Λ) → tableau μ → tableau μ → k)
  (multiplication_rule_basis : ∀ (a : Σ μ : Λ, tableau μ × tableau μ) (μ : Λ) (s t : tableau μ),
    (c a) * (c ⟨μ, (s, t)⟩) ≡ ∑ (u : tableau μ), r_basis a μ s u • (c ⟨μ, (u, t)⟩)
      [SMOD c over {ν : Λ | ν < μ} ]
  )

variable [cellular : CellularAlgebra k A]

/-! ### Instances and restatements

For convenience, we restate some of the data of a cellular algebra as instances, so that we can use
them without having to refer to the `cellular` namespace.
-/
instance : Fintype (cellular.Λ) := cellular.Λ_fintype
instance (μ : cellular.Λ) : Fintype (cellular.tableau μ) := cellular.fintype_tableau μ
instance (μ : cellular.Λ) : DecidableEq (cellular.tableau μ) := cellular.decidable_eq_tableau μ
instance : PartialOrder cellular.Λ := cellular.Λ_order
instance : LE cellular.Λ := cellular.Λ_order.toLE
instance : LT cellular.Λ := cellular.Λ_order.toLT
instance (μ : cellular.Λ) : Inhabited (cellular.tableau μ) := cellular.inhabited_tableau μ
instance : Fintype ((μ : cellular.Λ) × cellular.tableau μ × cellular.tableau μ) := inferInstanceAs _

namespace CellularAlgebra
/-- The subspace of $A$ spanned by the basis elements corresponding to tableaux of weights in a set
$S$.
-/
def tableau_span (S : Set cellular.Λ) : Submodule k A := cellular.c over S

/-! ## Unfolding some linear maps

Some of the conditions on cellular algebras in the definition are written in terms of the basis
elements but have obvious extensions to the entire algebra.
 -/

/-- The multiplication map `r_basis` extended to all of `A` by linearity.
-/
noncomputable def r : (μ : cellular.Λ) → cellular.tableau μ → cellular.tableau μ →
  A →ₗ[k] k := fun μ s t => (cellular.c.constr k (fun b => cellular.r_basis b μ s t))

/-- The key requirement for cellular algebras.

This is the extension of `CellularAlgebra.multiplication_rule_basis` to all of `A` by linearity.
-/
theorem multiplication_rule : ∀ (a : A) (μ : cellular.Λ) (s t : cellular.tableau μ),
  a * (cellular.c ⟨μ, (s, t)⟩) ≡
  ∑ (u : cellular.tableau μ), cellular.r A μ s u a • (cellular.c ⟨μ, (u, t)⟩)
  [SMOD tableau_span A {ν | ν < μ} ] := by
       intro a μ s t
       rw [←cellular.c.sum_repr a]
       simp only [Finset.sum_mul, smul_mul_assoc]
       simp only [map_sum, LinearMap.map_smul]
       simp only [Finset.univ.sum_smul, smul_assoc]
       rw[Finset.sum_comm]
       simp only [←Finset.univ.smul_sum]
       apply SModEq.sum
       intro i hi
       apply SModEq.smul
       unfold r
       simp only [Module.Basis.constr_basis]
       exact cellular.multiplication_rule_basis i μ s t

/-- Increasing the set of weights increases the span.
-/
def tableau_span_mono (S₁ S₂ : Set cellular.Λ) (h : S₁ ⊆ S₂) :
  tableau_span A S₁ ≤ tableau_span A S₂ :=
    Submodule.span_mono (Set.image_mono (double_tableaux_in_mono h))

/-- The span of a strictly smaller set of weights is strictly smaller.
-/
def tableau_span_mono' (S₁ S₂ : Set cellular.Λ) (h : S₁ ⊂ S₂) :
  tableau_span A S₁ < tableau_span A S₂ := by
    apply lt_of_le_of_ne
    · exact tableau_span_mono A S₁ S₂ h.subset
    · have ⟨q, ⟨hq₁, hq₂⟩⟩ := Set.exists_of_ssubset h
      unfold tableau_span
      unfold tableau_linear_span
      simp only [ne_eq]
      intro h
      have k₁ := Submodule.ext_iff.mp h
      let t : tableau q × tableau q := Inhabited.default
      have kk := (k₁ (c ⟨q, t⟩)).mpr
      rw[all_tableaux_range] at kk
      have q : c ⟨q, t⟩ ∈ Submodule.span k (all_tableaux_range A S₂ c) := by
        apply Submodule.mem_span_of_mem
        unfold all_tableaux_range
        unfold double_tableaux_in
        apply (Set.mem_image _ _ _).mpr
        use ⟨q, t⟩
        simp [hq₁]
      have kk₂ := kk q
      have jj := (Module.Basis.self_mem_span_image cellular.c).mp kk₂
      simp [double_tableaux_in] at jj
      contradiction

theorem c_injective {μ : Λ k A} {s₁ t₁ s₂ t₂ : tableau μ}
    (h : c ⟨μ, (s₁, t₁)⟩ = c ⟨μ, (s₂, t₂)⟩) :
  s₁ = s₂ ∧ t₁ = t₂ := by
    have k := Module.Basis.injective cellular.c h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at k
    exact k

theorem r_of_id {μ} {s u : cellular.tableau μ} :
  r A μ s u (1 : A) = if s = u then 1 else 0 := sorry

theorem r_of_zero {μ} {s u : cellular.tableau μ} :
  r A μ s u (0 : A) = 0 := by simp only [r, map_zero]

theorem action_doesnt_increase_μ
  (a : A) (μ : cellular.Λ) (s t : cellular.tableau μ) :
  a * c ⟨μ, (s, t)⟩ ∈ cellular.tableau_span A {ν | ν ≤ μ} := by
    have h := cellular.multiplication_rule A a μ s t
    have q := SModEq.sub_mem.mp h
    have ss : ({ν | ν < μ} ⊆ {ν | ν ≤ μ}) := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact le_of_lt ha
    have sst := tableau_span_mono A _ _ ss
    have tt : ∀ x, x∈ tableau_span A {ν | ν < μ} → x ∈ tableau_span A {ν | ν ≤ μ} := by
      intro x hx
      exact sst hx
    apply tt at q
    have ttt: ∑ u, (r A μ) s u a • c ⟨μ, (u, t)⟩ ∈ tableau_span A {ν | ν ≤ μ} := by
      apply Submodule.sum_mem
      intro sc hsc
      apply Submodule.smul_mem
      unfold tableau_span
      unfold tableau_linear_span
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

def cellular_ideal (μ : cellular.Λ) : Submodule A A := {
  carrier := tableau_span A {ν | ν ≤ μ} ,
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
    have q := action_doesnt_increase_μ A c c₁.fst c₁.snd.1 c₁.snd.2
    have s : {ν | ν ≤ c₁.fst} ⊆ {ν | ν ≤ μ } := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact ha.trans tt
    have t := tableau_span_mono A _ _ s
    apply t
    have c₁def : c₁ = ⟨c₁.fst, (c₁.snd.1, c₁.snd.2)⟩ := rfl
    rw [←c₁def] at q
    exact q
}

notation:50 A "[≤" μ "]" => cellular_ideal A μ

def subcelluar_ideal (μ : cellular.Λ) : Submodule A A := {
  carrier := tableau_span A {ν | ν < μ} ,
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
    have q := action_doesnt_increase_μ A c c₁.fst c₁.snd.1 c₁.snd.2
    have s : {ν | ν ≤ c₁.fst} ⊆ {ν | ν < μ } := by
      simp only [Set.setOf_subset_setOf]
      intro a ha
      exact lt_of_le_of_lt ha tt
    have t := (tableau_span_mono A _ _ s)
    apply t
    have c₁def : c₁ = ⟨c₁.fst, (c₁.snd.1, c₁.snd.2)⟩ := rfl
    rw [←c₁def] at q
    exact q
}

notation:50 A "[<" μ "]" => subcelluar_ideal A μ

noncomputable def ι : A →ₗ[k] A :=
  c.constr (S := k) (fun ⟨μ, (s, t)⟩ => c ⟨μ, (t, s)⟩)

@[simp]
theorem ι_on_basis (μ : cellular.Λ) (s t : cellular.tableau μ) :
  ι (k:=k) A (c ⟨μ, (s, t)⟩) = c ⟨μ, (t, s)⟩ := by
    unfold ι
    simp only [Module.Basis.constr_basis]

/-- Cellular algebras are equipped with an involution, which is the linear map that swaps
the two tableaux in the basis elements.
-/
theorem ι_involution : Function.Involutive (ι (k:=k) A) := by
    unfold Function.Involutive
    have h := Module.Basis.constr_self (cellular.c) k (LinearMap.id)
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
    have q := Module.Basis.constr_comp (cellular.c) k (ι (k:=k) A) (fun ⟨μ, (s,t)⟩ => c ⟨μ, (t, s)⟩)
    conv => {
      lhs
      arg 2
      unfold ι
    }
    rw[← q]
    apply congrArg
    ext x
    have q := Module.Basis.constr_basis (cellular.c) k (fun ⟨μ, (s,t)⟩ => c ⟨μ, (t, s)⟩)
    conv => {
      lhs
      unfold ι
      arg 2
      ext x
      rw[←q x]
    }
    conv => {
      lhs
      simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, Function.comp_apply]
      rw[Module.Basis.constr_basis]
      rw[Module.Basis.constr_basis]
      simp
    }
    simp

theorem ι_antiinvolution' (a b : A) : ι (k:=k) A (a * b) = ι (k:=k) A b * ι (k:=k) A a := by
    have h := cellular.ι_antiinvolution a b
    unfold ι
    exact h

end CellularAlgebra

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

noncomputable def cell_module_basis (μ : cellular.Λ) :
  Module.Basis (cellular.tableau μ) k (cell_module k A μ) := {
  repr := LinearEquiv.refl k (CellularAlgebra.tableau μ →₀ k)
}

noncomputable instance cellular_action {μ} : SMul A (cell_module k A μ) := {
  smul := fun a x => Module.Basis.constr (cell_module_basis k A μ) k
    (fun s => ∑ (u : cellular.tableau μ), (cellular.r A μ s u a) • (cell_module_basis k A μ u))
    x
  }

def cellular_action_is {μ} (a : A) (x : cell_module k A μ) :
  a • x = Module.Basis.constr (cell_module_basis k A μ) k
    (fun s => ∑ (u : cellular.tableau μ), (cellular.r A μ s u a) • (cell_module_basis k A μ u))
    x := rfl


namespace CellularAlgebra

/-- The set of basis vectors $\{c^\mu_{s,t} : s ∈ M(μ)\}$ is linearly independent modulo $A^{<\mu}$.
-/
theorem left_basis_mod_lesser_linear_indep :
   LinearIndependent k ((A[<μ].mkQ ∘ cellular.c) ∘ fun x => ⟨μ, (x, t)⟩) := by
  apply linearIndepOn_univ.mp
  apply LinearIndepOn.comp_of_image (hf := by simp[Function.Injective])
  have h := (linearIndepOn_union_iff_quotient (R:=k) (s := Sigma.fst ⁻¹' {ν | ν < μ})
    (t := Sigma.fst ⁻¹' {μ}) (f:= cellular.c) (Disjoint.preimage _ (by simp))).mp
    (Module.Basis.linearIndepOn cellular.c _)
  apply LinearIndepOn.mono h.2
  grind only [= Set.subset_def, = Set.mem_image, = Set.mem_preimage, = Set.mem_singleton_iff]

theorem left_basis_sum_mod_lesser {f₁ f₂ : cellular.tableau μ → k} :
  ∑ u, (f₁ u) • c ⟨μ, (u, t)⟩ ≡ ∑ u, (f₂ u) • c ⟨μ, (u, t)⟩ [SMOD A[<μ]] → f₁ = f₂ := by
  rw [SModEq.def]
  repeat rw [←Submodule.mkQ_apply, map_sum]
  simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply]
  intro h
  have tuw := left_basis_mod_lesser_linear_indep k A (t:=t)
  have jj := linearIndependent_iff'ₛ.mp tuw _ f₁ f₂ h
  simp only [Finset.mem_univ, forall_const] at jj
  exact funext jj

/-- The set of basis vectors $\{c^\mu_{s,t} : t ∈ M(μ)\}$ is linearly independent modulo $A^{<\mu}$.
-/
theorem right_basis_mod_lesser_linear_indep :
   LinearIndependent k ((A[<μ].mkQ ∘ cellular.c) ∘ fun x => ⟨μ, (s, x)⟩) := by
  apply linearIndepOn_univ.mp
  apply LinearIndepOn.comp_of_image (hf := by simp[Function.Injective])
  have h := (linearIndepOn_union_iff_quotient (R:=k) (s := Sigma.fst ⁻¹' {ν | ν < μ})
    (t := Sigma.fst ⁻¹' {μ}) (f:= cellular.c) (Disjoint.preimage _ (by simp))).mp
    (Module.Basis.linearIndepOn cellular.c _)
  apply LinearIndepOn.mono h.2
  grind only [= Set.subset_def, = Set.mem_image, = Set.mem_preimage, = Set.mem_singleton_iff]

theorem right_basis_sum_mod_lesser {f₁ f₂ : cellular.tableau μ → k} :
  ∑ u, (f₁ u) • c ⟨μ, (s, u)⟩ ≡ ∑ u, (f₂ u) • c ⟨μ, (s, u)⟩ [SMOD A[<μ]] → f₁ = f₂ := by
  rw [SModEq.def]
  repeat rw [←Submodule.mkQ_apply, map_sum]
  simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply]
  intro h
  have tuw := right_basis_mod_lesser_linear_indep k A (s:=s)
  have jj := linearIndependent_iff'ₛ.mp tuw _ f₁ f₂ h
  simp only [Finset.mem_univ, forall_const] at jj
  exact funext jj

/-- The set of basis vectors $\{c^\mu_{s,t} : s, t ∈ M(μ)\}$ is linearly independent modulo
$A^{<\mu}$.
-/
theorem basis_mod_lesser_linear_indep :
   LinearIndependent k ((A[<μ].mkQ ∘ cellular.c) ∘ fun x => ⟨μ, x⟩) := by
  apply linearIndepOn_univ.mp
  apply LinearIndepOn.comp_of_image (hf := by simp[Function.Injective])
  have h := (linearIndepOn_union_iff_quotient (R:=k) (s := Sigma.fst ⁻¹' {ν | ν < μ})
    (t := Sigma.fst ⁻¹' {μ}) (f:= cellular.c) (Disjoint.preimage _ (by simp))).mp
    (Module.Basis.linearIndepOn cellular.c _)
  apply LinearIndepOn.mono h.2
  grind only [= Set.subset_def, = Set.mem_image, = Set.mem_preimage, = Set.mem_singleton_iff]

theorem basis_sum_mod_lesser {f₁ f₂ : cellular.tableau μ → cellular.tableau μ → k} :
  ∑ s, ∑ t, (f₁ s t) • c ⟨μ, (s, t)⟩ ≡ ∑ s, ∑ t, (f₂ s t) • c ⟨μ, (s, t)⟩ [SMOD A[<μ]] → f₁ = f₂ :=
 by
  rw [SModEq.def]
  repeat rw [←Submodule.mkQ_apply, map_sum]
  simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.mkQ_apply]
  intro h
  have tuw := basis_mod_lesser_linear_indep k A (μ := μ)
  repeat rw [←Finset.sum_product'] at h
  have jj := linearIndependent_iff'ₛ.mp tuw _ (fun x => f₁ x.1 x.2) (fun x => f₂ x.1 x.2) h
  simp only [Finset.univ_product_univ, Finset.mem_univ, forall_const, Prod.forall] at jj
  grind

theorem linindep₂ (f g : cellular.tableau μ → k) :
  ∑ u, (f u) • (c ⟨μ, (s, u)⟩) ≡ ∑ v, (g v) • (c ⟨μ, (v, t)⟩) [SMOD A[<μ]] →
    f = Finsupp.single t (g s) := by
    intro h
    conv_lhs at h=> {
      rw [←Fintype.sum_ite_eq (f := fun s => ∑ u, f u • c ⟨μ, (s, u)⟩)]
      arg 2
      ext j
      rw[←Finset.sum_const_zero]
      rw[←Finset.sum_ite_irrel]
      arg 2
      ext u
      rw[←ite_zero_smul]
    }
    conv_rhs at h=> {
      rw [←Fintype.sum_ite_eq (f := fun t => ∑ u, g u • c ⟨μ, (u, t)⟩)]
      arg 2
      ext j
      rw[←Finset.sum_const_zero]
      rw[←Finset.sum_ite_irrel]
      arg 2
      ext u
      rw[←ite_zero_smul]
    }
    conv_rhs at h => {
      rw [Finset.sum_comm]
    }
    have kk := basis_sum_mod_lesser k A h
    simp only at kk
    have qq := funext_iff.mp kk s
    simp only [↓reduceIte, ← Finsupp.single_apply] at qq
    exact qq

theorem scratch (μ : cellular.Λ) : ∀ s t u v : tableau μ , (r A μ u s) (c ⟨μ, (s, t)⟩) =
 (r A μ t v) (c ⟨μ, (v, u)⟩) := by
  have h (s t u v : tableau μ) := multiplication_rule A (c ⟨μ, (s, t)⟩) μ u v
  have i (s t u v : tableau μ) : ι (k:=k) (A:=A) ((c ⟨μ, (s, t)⟩) * (c ⟨μ, (u, v)⟩)) =
    (c ⟨μ, (v, u)⟩) * (c ⟨μ, (t, s)⟩) := by
    rw [ι_antiinvolution']
    unfold ι
    repeat rw[Module.Basis.constr_basis]
  have j (s t u v : tableau μ) : ι (k:=k) (A:=A) ((c ⟨μ, (s, t)⟩) * (c ⟨μ, (u, v)⟩)) ≡
                   ∑ u_1, (r A μ u u_1) (c ⟨μ, (s, t)⟩) • c ⟨μ, (v, u_1)⟩
                  [SMOD tableau_span A {ν | ν < μ}] := by
    rw [SModEq.def]
    have hh : tableau_span A {ν | ν < μ} ≤ Submodule.comap (ι A) (tableau_span A {ν | ν < μ}) := (by
      apply Submodule.span_le.mpr
      intro x hx
      unfold all_tableaux_range at hx
      simp only [Set.mem_image, Sigma.exists, Prod.exists] at hx
      rcases hx with ⟨ha, ⟨hb, ⟨hd, he⟩⟩⟩
      rcases he with ⟨hs, ht⟩
      unfold double_tableaux_in at hs
      simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at hs
      rw [←ht]
      simp only [Submodule.comap_coe, Set.mem_preimage, ι_on_basis, SetLike.mem_coe]
      unfold tableau_span
      unfold tableau_linear_span
      apply Submodule.mem_span_of_mem
      unfold all_tableaux_range
      simp only [Set.mem_image, Sigma.exists, Prod.exists]
      use ha
      use hd
      use hb
      simp only [and_true]
      unfold double_tableaux_in
      simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
      exact hs)
    have tst := Submodule.mapQ (R:=k) (R₂:=k) (tableau_span A {ν | ν < μ})
      (tableau_span A {ν | ν < μ}) (τ₁₂ := RingHom.id _) (ι A) hh
    rw[←Submodule.mapQ_apply (tableau_span A {ν | ν < μ}) (tableau_span A {ν | ν < μ}) (f := ι A)
       (h:=hh)]
    rw [cellular.multiplication_rule]
    simp
  conv at j => {
    ext s t u v
    rw [i]
  }
  have kk (s t u v : tableau μ) := ((h s t u v).symm.trans (j v u t s)).symm
  have kki (s t u v : tableau μ) := linindep₂ k A (f := fun u_1 => (r A μ u u_1) (c ⟨μ, (s, t)⟩))
   (g := fun u_1 => (r A μ t u_1) (c ⟨μ, (v, u)⟩)) (kk v u t s)
  have result₁ (s t u v : tableau μ) : (r A μ u s) (c ⟨μ, (s, t)⟩) =
     (r A μ t v) (c ⟨μ, (v, u)⟩) := by
    have alf := kki s t u v
    simp only at alf
    have alf₂ := (funext_iff.mp alf) s
    rw[alf₂]
    simp
  exact result₁
def r_of_mul (a₁ a₂ : A) (μ : cellular.Λ) (s t : cellular.tableau μ) (u : tableau μ) : (r A μ s u)
  (a₁ * a₂) = ∑ x, (r A μ s x) a₂ * (r A μ x u) a₁ := by
  have k₁ := cellular.multiplication_rule A (a₁ * a₂) μ s t
  have k₂ := cellular.multiplication_rule A a₂ μ s t
  have h₁ := SModEq.sub_mem.mp k₁
  have h₂ := SModEq.sub_mem.mp k₂
  have foo {a : A} {x}: x ∈ tableau_linear_span {ν | ν < μ}
     CellularAlgebra.c → a * x ∈ tableau_linear_span
       {ν | ν < μ} CellularAlgebra.c :=
        Submodule.smul_mem (subcelluar_ideal A μ) a
  have q := foo (a := a₁) h₂
  rw [mul_sub a₁] at q
  have rr := SModEq.sub_mem.mpr q
  rw [←mul_assoc] at rr
  have tp := k₁.symm.trans rr
  rw [Finset.mul_sum] at tp
  have tt := cellular.multiplication_rule A a₁ μ s
  conv at tp => {
    rhs
    arg 2
    ext s
    rw [Algebra.mul_smul_comm]
    arg 2
  }
  have h : ∀ i ∈ Finset.univ, (r A μ s i) a₂ • (a₁ * c ⟨μ, (i, t)⟩) ≡
    (r A μ s i) a₂ • ∑ j, (r A μ i j) a₁ • c ⟨μ, (j, t)⟩ [SMOD tableau_span A {ν | ν < μ} ] := by
    intro i hi
    apply SModEq.smul
    exact cellular.multiplication_rule _ _ _ _ _
  have kk := SModEq.sum (h )
  have ki {t' : tableau μ}:= tp.trans (kk )
  conv at ki => {
    ext t'
    rhs
    arg 2
    ext i
    rw [Finset.smul_sum]
  }
  rw [Finset.sum_comm] at ki
  conv at ki => {
    ext t'
    rhs
    arg 2
    ext i
    arg 2
    ext j
    rw [←smul_assoc]
  }
  conv at ki => {
    ext t'
    rhs
    arg 2
    ext i
    rw [←Finset.univ.sum_smul]
  }
  have qq := left_basis_sum_mod_lesser k A (ki (t':=t))
  simp only [smul_eq_mul] at qq
  have qq := funext_iff.mp qq
  exact qq _

end CellularAlgebra

noncomputable instance cell_module_module (μ : cellular.Λ) : Module A (cell_module k A μ) where
  mul_smul := by
    intro x y b
    simp only [cellular_action_is k A, Module.Basis.constr_apply_fintype,
      Module.Basis.equivFun_apply, map_sum, map_smul, Module.Basis.equivFun_self, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply congr_arg
    conv => {
      lhs
      arg 2
      ext u
      rw [CellularAlgebra.r_of_mul k A x y μ x₁ u u]
    }
    conv => {
      rhs
      arg 2
      ext x_1
      rw [Finset.smul_sum]
    }
    conv => {
      rhs
      rw[Finset.sum_comm]
    }
    apply Finset.sum_congr rfl
    intro x₂ hx₂
    simp [smul_smul, Finset.sum_smul]
  one_smul := by
    intro b
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp only [cellular_action, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
      CellularAlgebra.r_of_id A, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Module.Basis.sum_repr]
  add_smul := by
    intro a b y
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp only [cellular_action]
    conv => {
      lhs
      arg 1
      arg 2
      ext s
      arg 2
      ext u
      rw [map_add]
    }
    simp only [ Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply]
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
    simp[CellularAlgebra.r_of_zero A]
  smul_zero := by
    intro a
    unfold HSMul.hSMul
    unfold instHSMul
    simp only
    unfold SMul.smul
    simp[cellular_action]

noncomputable def cell_module_form : cell_module k A μ →ₗ[k] (cell_module k A μ) →ₗ[k] k :=
  (cell_module_basis k A μ).constr k (fun s => (cell_module_basis k A μ).constr k (fun t =>
    cellular.r_basis ⟨μ, (s, t)⟩ μ s s
  ))

def cell_module_form_contravariant (μ : cellular.Λ) (a : A) (x y : cell_module k A μ) :
  cell_module_form k A (a • x) y = cell_module_form k A x (cellular.ι A a • y) := by

  sorry

def cell_module_radical (μ : cellular.Λ) : Submodule A (cell_module k A μ) := {
  carrier := {x | ∀ y, cell_module_form k A x y = 0},
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
