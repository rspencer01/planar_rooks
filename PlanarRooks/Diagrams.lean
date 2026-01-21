import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.PEquiv
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Filter
import Mathlib.Order.Hom.Set
import Mathlib.Order.Fin.Basic

import PlanarRooks.OrderIso

/-- A planar rook diagram with n left vertices and m right vertices is given by
    specifying which left and right vertices are "defects" (connected to eachother)
-/
structure PlanarRookDiagram (n m : ℕ) where
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (consistant: left_defects.card = right_defects.card)
deriving DecidableEq

@[ext]
theorem PlanarRookDiagram.ext {n m : ℕ}
  {d₁ d₂ : PlanarRookDiagram n m}
  (h₁ : d₁.left_defects = d₂.left_defects)
  (h₂ : d₁.right_defects = d₂.right_defects) :
  d₁ = d₂ :=
by
  cases d₁
  cases d₂
  cases h₁
  cases h₂
  rfl

-- There are only finitely many diagrams for given n and m
instance : Finite (PlanarRookDiagram n m) := by
  apply Finite.of_injective (fun d => (d.left_defects, d.right_defects))
  intro d₁ d₂ h
  simp only [Prod.mk.injEq] at h
  apply PlanarRookDiagram.ext
  · exact h.1
  · exact h.2
noncomputable instance : Fintype (PlanarRookDiagram n m) := by
  apply Fintype.ofFinite

/-- The empty diagram has no defects -/
def PlanarRookDiagram.empty (n m : ℕ) : PlanarRookDiagram n m :=
  { left_defects := ∅
  , right_defects := ∅
  , consistant := by simp }

/-- The identity diagram has all vertices as defects -/
def PlanarRookDiagram.id (n : ℕ) : PlanarRookDiagram n n :=
  { left_defects := Finset.univ
  , right_defects := Finset.univ
  , consistant := by simp }

/-- This is the diagram
```
──────╮    ╾─
────╮ │    ╾─
─╼  │ ╰-─────
─╼  ╰-───────
           ╾─
```
-/
def PlanarRookDiagram.example_1 : PlanarRookDiagram 4 5 :=
  { left_defects := {0, 2}
  , right_defects := {2, 3}
  , consistant := by simp }

def PlanarRookDiagram.example_2 : PlanarRookDiagram 5 3 :=
  { left_defects := {0, 1}
  , right_defects := {1, 2}
  , consistant := by simp }

-- A diagram has a "through-index": the number of defects on each side
-- Diagrammatically, this is the number of lines connecting left and right vertices
def PlanarRookDiagram.through_index {n m : ℕ}
  (d : PlanarRookDiagram n m) : ℕ :=
    d.left_defects.card

theorem PlanarRookDiagram.through_index_eq_right {n m : ℕ}
  (d : PlanarRookDiagram n m) :
  d.through_index = d.right_defects.card := by
    rw [PlanarRookDiagram.through_index]
    rw [d.consistant]

theorem PlanarRookDiagram.through_index_of_id {n : ℕ} :
  (PlanarRookDiagram.id n).through_index = n := by
    simp [PlanarRookDiagram.through_index, PlanarRookDiagram.id]

-- A diagram defines a bijection between left and right defects
def PlanarRookDiagram.lr_bijection {n m : ℕ}
  (d : PlanarRookDiagram n m) :
  d.left_defects ≃o d.right_defects :=
    (unique_finite_orderiso d.consistant).default

def PlanarRookDiagram.lr_bijection_of_id_is_id {n : ℕ} :
  (PlanarRookDiagram.id n).lr_bijection = OrderIso.refl _ := by
    exact Subsingleton.elim _ _

def PlanarRookDiagram.of_lr_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  PlanarRookDiagram n m :=
  {
    left_defects := left_defects,
    right_defects := right_defects,
    consistant := by
      have k := Finset.card_bij'
        (s := left_defects)
        (t := right_defects)
        (i :=  fun a ha => bijection.toFun ⟨a, ha⟩)
        (j := fun b hb => bijection.invFun ⟨b, hb⟩)
      apply k
      · exact fun a ha => by simp
      · exact fun b hb => by simp
      · exact fun a ha => by simp
      · exact fun b hb => by simp
  }

def PlanarRookDiagram.lr_bijection_of_lr_bijection {n m : ℕ}
  (d : PlanarRookDiagram n m) :
  PlanarRookDiagram.of_lr_bijection
    d.left_defects
    d.right_defects
    d.lr_bijection = d := by
      apply PlanarRookDiagram.ext
      · simp [PlanarRookDiagram.of_lr_bijection]
      · simp [PlanarRookDiagram.of_lr_bijection]

def PlanarRookDiagram.lr_bijection_of_of_lr_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  (PlanarRookDiagram.of_lr_bijection
    left_defects
    right_defects
    bijection).lr_bijection = bijection := by
      exact Subsingleton.elim _ bijection

-- Diagrams act on Fin n by sending left defects to their
-- corresponding right defect, and undefined elsewhere.
def PlanarRookDiagram.act {n m : ℕ} (d : PlanarRookDiagram n m) (i : Fin n) :
  Option (Fin m) :=
  if h : i ∈ d.left_defects then
    some (d.lr_bijection ⟨i, h⟩)
  else
    none

-- The action of the identity diagram is the identity function
def PlanarRookDiagram.act_of_id {n : ℕ}
  (i : Fin n) :
  PlanarRookDiagram.act (PlanarRookDiagram.id n) i = some i :=
by
  simp [
    PlanarRookDiagram.act,
    PlanarRookDiagram.lr_bijection_of_id_is_id,
  ]
  simp [PlanarRookDiagram.id]

-- The action of the empty diagram is nowhere defined
def PlanarRookDiagram.act_of_empty {n m : ℕ} (i : Fin n) :
  PlanarRookDiagram.act (PlanarRookDiagram.empty n m) i = none :=
by
  simp [PlanarRookDiagram.act, PlanarRookDiagram.empty]

variable {n m : ℕ}

def fi {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k) :
    ({x | ∃ (h : x ∈ d₁.left_defects),
           ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects} : Finset (Fin n)) →
     { y | ∃ (h : y ∈ d₂.right_defects),
           ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects } := fun ⟨x, hx⟩ =>
        ⟨↑(d₂.lr_bijection.toFun ⟨d₁.lr_bijection.toFun ⟨x , by
          simp at hx
          exact hx.choose
        ⟩, by
          simp at hx
          exact hx.choose_spec
        ⟩ ) , by
          simp
       ⟩
def fj {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k) :
    ({ y | ∃ (h : y ∈ d₂.right_defects),
         ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects } : Finset (Fin k)) →
     {x | ∃ (h : x ∈ d₁.left_defects),
         ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects} := fun ⟨y, hy⟩ =>
        ⟨↑(d₁.lr_bijection.invFun ⟨↑(d₂.lr_bijection.invFun ⟨y, by
          simp at hy
          exact hy.choose
        ⟩), by
          simp at hy
          exact hy.choose_spec
        ⟩ ) , by
          simp
       ⟩
def PlanarRookDiagram.mul₂ {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k) :
  PlanarRookDiagram n k := {
    left_defects :=
      { x | ∃ (h : x ∈ d₁.left_defects),
        ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects },
    right_defects :=
      { y | ∃ (h : y ∈ d₂.right_defects),
        ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects },
    consistant := by
      apply Finset.card_bij'
        (s := ({x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects}
                 : Finset (Fin n)))
        (t := ({y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects}
                 : Finset (Fin k)))
        (i := fun x hx => fi d₁ d₂ ⟨x, hx⟩)
        (j := fun y hy => fj d₁ d₂ ⟨y, hy⟩)
      · intro a ha
        unfold fi fj
        simp
      · intro a ha
        unfold fi fj
        simp
      · intro a ha
        unfold fi
        simp
      · intro a ha
        unfold fj
        simp
  }

def PlanarRookDiagram.mul₂_id {n m : ℕ}
  (d : PlanarRookDiagram n m) :
  PlanarRookDiagram.mul₂ d (PlanarRookDiagram.id m) = d := by
    unfold PlanarRookDiagram.mul₂
    apply PlanarRookDiagram.ext
    · unfold PlanarRookDiagram.id
      simp
    · simp only
      rw [PlanarRookDiagram.lr_bijection_of_id_is_id]
      unfold PlanarRookDiagram.id
      simp

def PlanarRookDiagram.id_mul₂ {n m : ℕ}
  (d : PlanarRookDiagram n m) :
  PlanarRookDiagram.mul₂ (PlanarRookDiagram.id n) d = d := by
    unfold PlanarRookDiagram.mul₂
    apply PlanarRookDiagram.ext
    · simp only
      rw [PlanarRookDiagram.lr_bijection_of_id_is_id]
      unfold PlanarRookDiagram.id
      simp
    · unfold PlanarRookDiagram.id
      simp

def PlanarRookDiagram.restate_mul₂ {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (x : Fin n)
  (hxx : x ∈ d₁.left_defects)
  (hx : ∃ (y : Fin m), d₁.lr_bijection ⟨x, hxx⟩ = y ∧ y ∈ d₂.left_defects) :
    x ∈ (d₁.mul₂ d₂).left_defects := by
      rcases hx with ⟨y, hy⟩
      unfold PlanarRookDiagram.mul₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use hxx
      rw [hy.1]
      exact hy.2

def PlanarRookDiagram.restate_mul₃ {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (x : Fin n)
  (hxx : x ∈ d₁.left_defects)
  (y : Fin m)
  (hx : d₁.lr_bijection ⟨x, hxx⟩ = y ∧ y ∈ d₂.left_defects) :
    ((d₁.mul₂ d₂).lr_bijection ⟨x, PlanarRookDiagram.restate_mul₂ d₁ d₂ x hxx ⟨y, hx⟩⟩)
     = (⟨d₂.lr_bijection ⟨y, hx.2⟩, by
         unfold PlanarRookDiagram.mul₂
         simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta, OrderIso.symm_apply_apply,
           SetLike.coe_mem, exists_const, true_and]
         rw[←hx.1]
         simp
      ⟩ : (d₁.mul₂ d₂).right_defects) := by
       rcases hx with ⟨hx₁, hx₂⟩
       conv => {
         rhs
         arg 1
         arg 1
         arg 2
         arg 1
         rw [←hx₁]
       }
       let f := (d₁.mul₂ d₂).lr_bijection
       let g : ↥(d₁.mul₂ d₂).left_defects ≃o ↥(d₁.mul₂ d₂).right_defects := {
          toFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection ⟨d₁.lr_bijection ⟨x, by
            unfold PlanarRookDiagram.mul₂ at hx
            simp at hx
            exact hx.choose
          ⟩, by
            unfold PlanarRookDiagram.mul₂ at hx
            simp at hx
            exact hx.choose_spec
          ⟩, by
            unfold PlanarRookDiagram.mul₂
            simp
          ⟩
          invFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
            unfold PlanarRookDiagram.mul₂ at hy
            simp at hy
            exact hy.choose
          ⟩, by
            unfold PlanarRookDiagram.mul₂ at hy
            simp at hy
            exact hy.choose_spec
          ⟩, by
            unfold PlanarRookDiagram.mul₂
            simp
          ⟩
          map_rel_iff' := by simp
          left_inv := by
            intro h
            simp
          right_inv := by
            intro h
            simp
       }
       have kk : ↑((d₁.mul₂ d₂).lr_bijection ⟨x, by
         unfold PlanarRookDiagram.mul₂
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hxx
         rw[hx₁]
         exact hx₂
      ⟩) = f ⟨x, by
         unfold PlanarRookDiagram.mul₂
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hxx
         rw[hx₁]
         exact hx₂⟩ := by rfl
       rw [kk]
       have kk : ⟨d₂.lr_bijection ⟨↑(d₁.lr_bijection ⟨x, hxx⟩), by
         rw [hx₁]
         exact hx₂
         ⟩, by
         unfold PlanarRookDiagram.mul₂
         simp
         ⟩ = g ⟨x, by
           unfold PlanarRookDiagram.mul₂
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use hxx
           rw [hx₁]
           exact hx₂
         ⟩ := by rfl
       rw [kk]
       have kk : f = g := by
        rw [Subsingleton.elim f]
       rw [kk]

def PlanarRookDiagram.restate_mul₄ {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (x : Fin k)
  (hxx : x ∈ d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm ⟨x, hxx⟩ = y ∧ y ∈ d₁.right_defects) :
    x ∈ (d₁.mul₂ d₂).right_defects := by
      rcases hx with ⟨y, hy⟩
      unfold PlanarRookDiagram.mul₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use hxx
      rw [y]
      exact hy

def PlanarRookDiagram.restate_mul₅ {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (x : Fin k)
  (hxx : x ∈ d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm ⟨x, hxx⟩ = y ∧ y ∈ d₁.right_defects) :
    ((d₁.mul₂ d₂).lr_bijection.symm ⟨x, PlanarRookDiagram.restate_mul₄ d₁ d₂ x hxx y hx⟩)
     = (⟨d₁.lr_bijection.symm ⟨y, hx.2⟩, by
       unfold PlanarRookDiagram.mul₂
       simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta, OrderIso.apply_symm_apply,
         SetLike.coe_mem, exists_const, true_and]
       rw [←hx.1]
       simp
       ⟩ : (d₁.mul₂ d₂).left_defects) := by
         rcases hx with ⟨hx₁, hx₂⟩
         conv => {
          rhs
          arg 1
          arg 1
          arg 2
          arg 1
          rw [←hx₁]
         }
         let f := (d₁.mul₂ d₂).lr_bijection.symm
         let g : ↥(d₁.mul₂ d₂).right_defects ≃o ↥(d₁.mul₂ d₂).left_defects := {
            toFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
              unfold PlanarRookDiagram.mul₂ at hy
              simp at hy
              exact hy.choose
            ⟩, by
              unfold PlanarRookDiagram.mul₂ at hy
              simp at hy
              exact hy.choose_spec
            ⟩, by
              unfold PlanarRookDiagram.mul₂
              simp
            ⟩
            invFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection.toFun ⟨d₁.lr_bijection.toFun ⟨x, by
              unfold PlanarRookDiagram.mul₂ at hx
              simp at hx
              exact hx.choose
            ⟩, by
              unfold PlanarRookDiagram.mul₂ at hx
              simp at hx
              exact hx.choose_spec
            ⟩, by
              unfold PlanarRookDiagram.mul₂
              simp
            ⟩
            map_rel_iff' := by simp
            left_inv := by
              intro h
              simp
            right_inv := by
              intro h
              simp
         }
         have kk : ↑((d₁.mul₂ d₂).lr_bijection.symm ⟨x, by
           unfold PlanarRookDiagram.mul₂
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use hxx
           rw[hx₁]
           exact hx₂
          ⟩) = f ⟨x, by
             unfold PlanarRookDiagram.mul₂
             simp only [Finset.mem_filter, Finset.mem_univ, true_and]
             use hxx
             rw[hx₁]
             exact hx₂⟩ := by rfl
         rw [kk]
         have kk : ⟨↑(d₁.lr_bijection.symm ⟨↑(d₂.lr_bijection.symm ⟨x, hxx⟩), by
           rw [hx₁]
           exact hx₂
           ⟩), by
             unfold PlanarRookDiagram.mul₂
             simp
          ⟩ = g ⟨x, by
             unfold PlanarRookDiagram.mul₂
             simp only [Finset.mem_filter, Finset.mem_univ, true_and]
             use hxx
             rw [hx₁]
             exact hx₂
           ⟩ := by rfl
         rw [kk]
         have kk : f = g := by
           rw [Subsingleton.elim f]
         rw [kk]

def PlanarRookDiagram.mul_assoc₃ {n m k l : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (d₃ : PlanarRookDiagram k l) :
  (d₁.mul₂ d₂).mul₂ d₃ = d₁.mul₂ (d₂.mul₂ d₃) := by
     apply PlanarRookDiagram.ext
     · conv => {
         lhs
         arg 1
         arg 0
         unfold PlanarRookDiagram.mul₂
       }
       simp only
       ext x
       constructor
       · intro h
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         conv => {
           arg 1
           arg 1
           arg 0
           unfold PlanarRookDiagram.mul₂
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         unfold PlanarRookDiagram.mul₂ at ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
         rcases ha with ⟨hc, hd⟩
         use hc
         unfold PlanarRookDiagram.mul₂
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hd
         have kk:= PlanarRookDiagram.restate_mul₃ d₁ d₂ x hc (d₁.lr_bijection ⟨x, hc⟩) ⟨rfl, hd⟩
         rw [kk] at hb
         exact hb
       · intro h
         simp only at h
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         conv at h => {
            unfold PlanarRookDiagram.mul₂
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         rcases hb with ⟨hc, hd⟩
         constructor
         · have kk := PlanarRookDiagram.restate_mul₃ d₁ d₂ x ha (d₁.lr_bijection ⟨x, ha⟩) ⟨rfl, hc⟩
           rw [kk]
           exact hd
     · conv => {
         lhs
         arg 1
         arg 0
         unfold PlanarRookDiagram.mul₂
       }
       simp only
       ext x
       constructor
       · simp only [Finset.mem_filter, Finset.mem_univ, true_and, forall_exists_index]
         intro h ha
         conv => {
           arg 1
           arg 1
           arg 0
           unfold PlanarRookDiagram.mul₂
         }
         simp
         exact ⟨
          by
           unfold PlanarRookDiagram.mul₂
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use h
           unfold PlanarRookDiagram.mul₂ at ha
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
           rcases ha with ⟨hb, hc⟩
           exact hb,
          by
           unfold PlanarRookDiagram.mul₂ at ha
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
           rcases ha with ⟨hb, hc⟩
           have kk := PlanarRookDiagram.restate_mul₅ d₂ d₃ x h (d₃.lr_bijection.symm ⟨x, h⟩)
             ⟨rfl, hb⟩
           rw [kk]
           exact hc
         ⟩
       · intro h
         conv at h => {
           arg 1
           arg 1
           arg 0
           unfold PlanarRookDiagram.mul₂
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         unfold PlanarRookDiagram.mul₂ at ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
         rcases ha with ⟨hc, hd⟩
         use hc
         unfold PlanarRookDiagram.mul₂
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hd
         have kk := PlanarRookDiagram.restate_mul₅ d₂ d₃ x hc (d₃.lr_bijection.symm ⟨x, hc⟩)
           ⟨rfl, hd⟩
         rw [kk] at hb
         exact hb

#eval (PlanarRookDiagram.mul₂ (PlanarRookDiagram.example_1) (PlanarRookDiagram.id 5)).act 4

instance PlanarRookMonoid : Monoid (PlanarRookDiagram n n) := {
  mul := PlanarRookDiagram.mul₂,
  one := PlanarRookDiagram.id n,
  mul_one := PlanarRookDiagram.mul₂_id,
  one_mul := PlanarRookDiagram.id_mul₂,
  mul_assoc := PlanarRookDiagram.mul_assoc₃
}

-- When multiplying two diagrams, we are left with a number of disconnected
-- components. The number of these is the exponent in the planar rook algebra's
-- multiplication.
def PlanarRookMonoid.mul_exponent {n m k : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k) :
  ℤ :=
    m - d₁.through_index - d₂.through_index + (d₁.mul₂ d₂).through_index

def PlanarRookMonoid.mul_exponent_eq_zero_of_id {n : ℕ}
  (d : PlanarRookDiagram n n) :
  PlanarRookMonoid.mul_exponent d (PlanarRookDiagram.id n) = 0 := by
    simp [PlanarRookMonoid.mul_exponent,
          PlanarRookDiagram.through_index_of_id,
          PlanarRookDiagram.mul₂_id]

def PlanarRookMonoid.mul_exponent_assoc {n m k l : ℕ}
  (d₁ : PlanarRookDiagram n m)
  (d₂ : PlanarRookDiagram m k)
  (d₃ : PlanarRookDiagram k l) :
  PlanarRookMonoid.mul_exponent d₁ d₂ +
  PlanarRookMonoid.mul_exponent (d₁.mul₂ d₂) d₃ =
  PlanarRookMonoid.mul_exponent d₁ (d₂.mul₂ d₃) +
  PlanarRookMonoid.mul_exponent d₂ d₃ := by
    unfold PlanarRookMonoid.mul_exponent
    simp [PlanarRookDiagram.mul_assoc₃]
    ring
