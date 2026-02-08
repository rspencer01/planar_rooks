/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/
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

/-!
# Planar Rook Diagrams

A _rook diagram_ on a $n \times m$ board is a collection of mutually non-attacking rooks.
It is _planar_ if no rook is "North-East" or "South-West" of any other.

Diagramatically, we can assign each rook to two numbers indicating its row and column. Due to
the non-attacking condition, these numbers are unique to each rook. We can then draw this as
two columns of vertices (one of $n$ points and one of $m$) with lines connecting a vertex on
the left and on the right if they label the row and column of the same rook. The planarity
condition is then equivalent to the condition that these lines do not cross.
-/

namespace PlanarRook

/-- A planar rook diagram with n left vertices and m right vertices is given by
    specifying which left and right vertices are "defects" (connected to eachother)
-/
structure Diagram (n m : ℕ) where
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (consistant: left_defects.card = right_defects.card)
deriving DecidableEq

@[ext]
theorem Diagram.ext {n m : ℕ}
  {d₁ d₂ : Diagram n m}
  (h₁ : d₁.left_defects = d₂.left_defects)
  (h₂ : d₁.right_defects = d₂.right_defects) :
  d₁ = d₂ :=
by
  cases d₁
  cases d₂
  cases h₁
  cases h₂
  rfl

namespace Diagram
-- There are only finitely many diagrams for given n and m
instance : Finite (Diagram n m) := by
  apply Finite.of_injective (fun d => (d.left_defects, d.right_defects))
  intro d₁ d₂ h
  simp only [Prod.mk.injEq] at h
  apply Diagram.ext
  · exact h.1
  · exact h.2
noncomputable instance : Fintype (Diagram n m) := by
  apply Fintype.ofFinite

/-!
## Examples
-/

/-- The empty diagram has no defects -/
def empty (n m : ℕ) : Diagram n m :=
  { left_defects := ∅
  , right_defects := ∅
  , consistant := by simp }

/-- The identity diagram has all vertices as defects -/
def id (n : ℕ) : Diagram n n :=
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
def example_1 : Diagram 4 5 :=
  { left_defects := {0, 2}
  , right_defects := {2, 3}
  , consistant := by simp }

def example_2 : Diagram 5 3 :=
  { left_defects := {0, 1}
  , right_defects := {1, 2}
  , consistant := by simp }

/-!
## Through indices

A diagram has a "through-index": the number of defects on each side
Diagrammatically, this is the number of lines connecting left and right vertices, or
equivalently the number of rooks.
-/

/-- The through index of a diagram is the size of its left (or right) defects. -/
def through_index {n m : ℕ}
  (d : Diagram n m) : ℕ :=
    d.left_defects.card

theorem through_index_eq_right {n m : ℕ}
  (d : Diagram n m) :
  d.through_index = d.right_defects.card := by
    rw [through_index, d.consistant]

/-- Through indices are bounded by the size of the left defects. -/
theorem through_index_le_left {n m : ℕ}
  (d : Diagram n m) :
  d.through_index ≤ n := by
    rw [through_index]
    conv => {
      rhs
      rw [←Fintype.card_fin n]
    }
    exact Finset.card_le_univ (α := Fin n) _

/-- Through indices are bounded by the size of the right defects. -/
theorem through_index_le_right {n m : ℕ}
  (d : Diagram n m) :
  d.through_index ≤ m := by
    rw [through_index, d.consistant]
    conv => {
      rhs
      rw [←Fintype.card_fin m]
    }
    exact Finset.card_le_univ (α := Fin m) _

theorem through_index_of_id {n : ℕ} :
  (id n).through_index = n := by
    simp [through_index, id]

theorem through_index_of_empty {n m : ℕ} :
  (empty n m).through_index = 0 := by
    simp [through_index, empty]

/-- A diagram defines a bijection between left and right defects -/
def lr_bijection {n m : ℕ}
  (d : Diagram n m) :
  d.left_defects ≃o d.right_defects :=
    (unique_finite_orderiso d.consistant).default

def lr_bijection_of_id_is_id {n : ℕ} :
  (id n).lr_bijection = OrderIso.refl _ := Subsingleton.elim _ _

def of_lr_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  Diagram n m :=
  {
    left_defects := left_defects,
    right_defects := right_defects,
    consistant := equal_size_of_orderiso bijection
  }

def lr_bijection_of_lr_bijection {n m : ℕ}
  (d : Diagram n m) :
  Diagram.of_lr_bijection
    d.left_defects
    d.right_defects
    d.lr_bijection = d := by
      rw [Diagram.of_lr_bijection]

def lr_bijection_of_of_lr_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  (Diagram.of_lr_bijection
    left_defects
    right_defects
    bijection).lr_bijection = bijection := Subsingleton.elim _ bijection

-- Diagrams act on Fin n by sending left defects to their
-- corresponding right defect, and undefined elsewhere.
def act {n m : ℕ} (d : Diagram n m) (i : Fin n) :
  Option (Fin m) :=
  if h : i ∈ d.left_defects then
    some (d.lr_bijection ⟨i, h⟩)
  else
    none

-- The action of the identity diagram is the identity function
def act_of_id {n : ℕ}
  (i : Fin n) :
  act (id n) i = some i :=
by
  simp [
    act,
    lr_bijection_of_id_is_id,
  ]
  simp [id]

-- The action of the empty diagram is nowhere defined
def act_of_empty {n m : ℕ} (i : Fin n) :
  Diagram.act (Diagram.empty n m) i = none :=
by
  simp [Diagram.act, Diagram.empty]

end Diagram

def Diagram.mul {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  Diagram n k := {
    left_defects :=
      { x | ∃ (h : x ∈ d₁.left_defects),
        ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects },
    right_defects :=
      { y | ∃ (h : y ∈ d₂.right_defects),
        ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects },
    consistant := by
      let fi {n m k : ℕ}
        (d₁ : Diagram n m)
        (d₂ : Diagram m k) :
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
      let fj {n m k : ℕ}
        (d₁ : Diagram n m)
        (d₂ : Diagram m k) :
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
      apply Finset.card_bij'
        (s := ({x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects}
                 : Finset (Fin n)))
        (t := ({y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects}
                 : Finset (Fin k)))
        (i := fun x hx => fi d₁ d₂ ⟨x, hx⟩)
        (j := fun y hy => fj d₁ d₂ ⟨y, hy⟩)
      · intro a ha
        simp [fi, fj]
      · intro a ha
        simp [fi, fj]
      · intro a ha
        simp [fi]
      · intro a ha
        simp [fj]
  }

instance Diagram.has_hmul :
  HMul (Diagram n m) (Diagram m k) (Diagram n k)  :=
  ⟨Diagram.mul⟩

@[simp]
def Diagram.hmul_eq_mul {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  d₁ * d₂ = Diagram.mul d₁ d₂ := by
    rfl

def Diagram.mul_id {n m : ℕ}
  (d : Diagram n m) :
  d * (Diagram.id m) = d := by
    rw [Diagram.hmul_eq_mul]
    unfold Diagram.mul
    apply Diagram.ext
    · unfold Diagram.id
      simp
    · simp only
      rw [Diagram.lr_bijection_of_id_is_id]
      unfold Diagram.id
      simp

def Diagram.id_mul {n m : ℕ}
  (d : Diagram n m) :
  (Diagram.id n) * d = d := by
    rw [Diagram.hmul_eq_mul]
    unfold Diagram.mul
    apply Diagram.ext
    · simp only
      rw [Diagram.lr_bijection_of_id_is_id]
      unfold Diagram.id
      simp
    · unfold Diagram.id
      simp

def Diagram.restate_mul₂ {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (x : Fin n)
  (hxx : x ∈ d₁.left_defects)
  (hx : ∃ (y : Fin m), d₁.lr_bijection ⟨x, hxx⟩ = y ∧ y ∈ d₂.left_defects) :
    x ∈ (d₁.mul d₂).left_defects := by
      rcases hx with ⟨y, hy⟩
      unfold Diagram.mul
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use hxx
      rw [hy.1]
      exact hy.2

def Diagram.restate_mul₃ {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (x : Fin n)
  (hxx : x ∈ d₁.left_defects)
  (y : Fin m)
  (hx : d₁.lr_bijection ⟨x, hxx⟩ = y ∧ y ∈ d₂.left_defects) :
    ((d₁.mul d₂).lr_bijection ⟨x, Diagram.restate_mul₂ d₁ d₂ x hxx ⟨y, hx⟩⟩)
     = (⟨d₂.lr_bijection ⟨y, hx.2⟩, by
         unfold Diagram.mul
         simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta, OrderIso.symm_apply_apply,
           SetLike.coe_mem, exists_const, true_and]
         rw[←hx.1]
         simp
      ⟩ : (d₁.mul d₂).right_defects) := by
       rcases hx with ⟨hx₁, hx₂⟩
       conv => {
         rhs
         arg 1
         arg 1
         arg 2
         arg 1
         rw [←hx₁]
       }
       let f := (d₁.mul d₂).lr_bijection
       let g : ↥(d₁.mul d₂).left_defects ≃o ↥(d₁.mul d₂).right_defects := {
          toFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection ⟨d₁.lr_bijection ⟨x, by
            unfold Diagram.mul at hx
            simp at hx
            exact hx.choose
          ⟩, by
            unfold Diagram.mul at hx
            simp at hx
            exact hx.choose_spec
          ⟩, by
            unfold Diagram.mul
            simp
          ⟩
          invFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
            unfold Diagram.mul at hy
            simp at hy
            exact hy.choose
          ⟩, by
            unfold Diagram.mul at hy
            simp at hy
            exact hy.choose_spec
          ⟩, by
            unfold Diagram.mul
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
       have kk : ↑((d₁.mul d₂).lr_bijection ⟨x, by
         unfold Diagram.mul
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hxx
         rw[hx₁]
         exact hx₂
      ⟩) = f ⟨x, by
         unfold Diagram.mul
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hxx
         rw[hx₁]
         exact hx₂⟩ := by rfl
       rw [kk]
       have kk : ⟨d₂.lr_bijection ⟨↑(d₁.lr_bijection ⟨x, hxx⟩), by
         rw [hx₁]
         exact hx₂
         ⟩, by
         unfold Diagram.mul
         simp
         ⟩ = g ⟨x, by
           unfold Diagram.mul
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use hxx
           rw [hx₁]
           exact hx₂
         ⟩ := by rfl
       rw [kk]
       have kk : f = g := by
        rw [Subsingleton.elim f]
       rw [kk]

def Diagram.restate_mul₄ {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (x : Fin k)
  (hxx : x ∈ d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm ⟨x, hxx⟩ = y ∧ y ∈ d₁.right_defects) :
    x ∈ (d₁.mul d₂).right_defects := by
      rcases hx with ⟨y, hy⟩
      unfold Diagram.mul
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use hxx
      rw [y]
      exact hy

def Diagram.restate_mul₅ {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (x : Fin k)
  (hxx : x ∈ d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm ⟨x, hxx⟩ = y ∧ y ∈ d₁.right_defects) :
    ((d₁ * d₂).lr_bijection.symm ⟨x, Diagram.restate_mul₄ d₁ d₂ x hxx y hx⟩)
     = (⟨d₁.lr_bijection.symm ⟨y, hx.2⟩, by
       unfold Diagram.mul
       simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta, OrderIso.apply_symm_apply,
         SetLike.coe_mem, exists_const, true_and]
       rw [←hx.1]
       simp
       ⟩ : (d₁.mul d₂).left_defects) := by
         rcases hx with ⟨hx₁, hx₂⟩
         conv => {
          rhs
          arg 1
          arg 1
          arg 2
          arg 1
          rw [←hx₁]
         }
         let f := (d₁.mul d₂).lr_bijection.symm
         let g : ↥(d₁.mul d₂).right_defects ≃o ↥(d₁.mul d₂).left_defects := {
            toFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
              unfold Diagram.mul at hy
              simp at hy
              exact hy.choose
            ⟩, by
              unfold Diagram.mul at hy
              simp at hy
              exact hy.choose_spec
            ⟩, by
              unfold Diagram.mul
              simp
            ⟩
            invFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection.toFun ⟨d₁.lr_bijection.toFun ⟨x, by
              unfold Diagram.mul at hx
              simp at hx
              exact hx.choose
            ⟩, by
              unfold Diagram.mul at hx
              simp at hx
              exact hx.choose_spec
            ⟩, by
              unfold Diagram.mul
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
         have kk : ↑((d₁ * d₂).lr_bijection.symm ⟨x, by
           rw [Diagram.hmul_eq_mul]
           unfold Diagram.mul
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use hxx
           rw[hx₁]
           exact hx₂
          ⟩) = f ⟨x, by
             unfold Diagram.mul
             simp only [Finset.mem_filter, Finset.mem_univ, true_and]
             use hxx
             rw[hx₁]
             exact hx₂⟩ := by rfl
         rw [kk]
         have kk : ⟨↑(d₁.lr_bijection.symm ⟨↑(d₂.lr_bijection.symm ⟨x, hxx⟩), by
           rw [hx₁]
           exact hx₂
           ⟩), by
             unfold Diagram.mul
             simp
          ⟩ = g ⟨x, by
             unfold Diagram.mul
             simp only [Finset.mem_filter, Finset.mem_univ, true_and]
             use hxx
             rw [hx₁]
             exact hx₂
           ⟩ := by rfl
         rw [kk]
         have kk : f = g := by
           rw [Subsingleton.elim f]
         rw [kk]

def Diagram.mul_assoc {n m k l : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (d₃ : Diagram k l) :
  (d₁.mul d₂).mul d₃ = d₁.mul (d₂ * d₃) := by
     apply Diagram.ext
     · conv => {
         lhs
         arg 1
         arg 0
         unfold Diagram.mul
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
           unfold Diagram.mul
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         unfold Diagram.mul at ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
         rcases ha with ⟨hc, hd⟩
         use hc
         rw [Diagram.hmul_eq_mul]
         unfold Diagram.mul
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hd
         have kk:= Diagram.restate_mul₃ d₁ d₂ x hc (d₁.lr_bijection ⟨x, hc⟩) ⟨rfl, hd⟩
         rw [kk] at hb
         exact hb
       · intro h
         simp only [Diagram.hmul_eq_mul] at h
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         conv at h => {
            unfold Diagram.mul
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         rcases hb with ⟨hc, hd⟩
         constructor
         · have kk := Diagram.restate_mul₃ d₁ d₂ x ha (d₁.lr_bijection ⟨x, ha⟩) ⟨rfl, hc⟩
           rw [kk]
           exact hd
     · conv => {
         lhs
         arg 1
         arg 0
         unfold Diagram.mul
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
           unfold Diagram.mul
         }
         simp only [hmul_eq_mul, Finset.mem_filter, Finset.mem_univ, true_and]
         exact ⟨
          by
           unfold Diagram.mul
           simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           use h
           unfold Diagram.mul at ha
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
           rcases ha with ⟨hb, hc⟩
           exact hb,
          by
           have ki : (d₂ * d₃) = d₂.mul d₃ := by rfl
           unfold Diagram.mul at ha
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
           rcases ha with ⟨hb, hc⟩
           have kk := Diagram.restate_mul₅ d₂ d₃ x h (d₃.lr_bijection.symm ⟨x, h⟩)
             ⟨rfl, hb⟩
           rw [kk]
           exact hc
         ⟩
       · intro h
         conv at h => {
           arg 1
           arg 1
           arg 0
           unfold Diagram.mul
         }
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         rw [Diagram.hmul_eq_mul] at ha
         unfold Diagram.mul at ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
         rcases ha with ⟨hc, hd⟩
         use hc
         unfold Diagram.mul
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         use hd
         have kk := Diagram.restate_mul₅ d₂ d₃ x hc (d₃.lr_bijection.symm ⟨x, hc⟩)
           ⟨rfl, hd⟩
         rw [kk] at hb
         exact hb

#eval (Diagram.mul (Diagram.example_1) (Diagram.id 5)).act 4

instance Monoid : Monoid (Diagram n n) := {
  mul := HMul.hMul,
  one := Diagram.id n,
  mul_one := Diagram.mul_id,
  one_mul := Diagram.id_mul,
  mul_assoc := Diagram.mul_assoc
}

theorem Monoid.one_def {n : ℕ} :
  (1 : Diagram n n) = Diagram.id n := by
    rfl

-- When multiplying two diagrams, we are left with a number of disconnected
-- components. The number of these is the exponent in the planar rook algebra's
-- multiplication.
def Monoid.mul_exponent' {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  ℤ :=
    m - d₁.through_index - d₂.through_index + (d₁ * d₂).through_index

theorem Monoid.mul_exponent_is_stubs' {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  PlanarRook.Monoid.mul_exponent' d₁ d₂ =
    Finset.card {x | x ∈ (d₁.right_defects ∪ d₂.left_defects)ᶜ} := by
      classical
      have h : (d₁ * d₂).through_index = (d₁.right_defects ∩ d₂.left_defects).card := by
        unfold Diagram.through_index
        rw [Diagram.hmul_eq_mul]
        unfold Diagram.mul
        simp only
        apply Finset.card_bij' (α := Fin n) (β := Fin m) (i := fun a ha => d₁.lr_bijection ⟨a, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            rcases ha with ⟨haa, hab⟩
            exact haa
            ⟩) (j := fun b hb => d₁.lr_bijection.symm ⟨b, by
            simp only [Finset.mem_inter] at hb
            rcases hb with ⟨hba, hbb⟩
            exact hba
            ⟩)
        · intro a ha
          simp
        · intro a ha
          simp
        · intro a ha
          simp only [Finset.mem_inter, SetLike.coe_mem, true_and]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rcases ha with ⟨haa, hab⟩
          exact hab
        · intro a ha
          simp
          simp [Finset.mem_inter.mp ha]
      unfold PlanarRook.Monoid.mul_exponent'
      rw [h]
      rw [Diagram.through_index_eq_right]
      rw [Diagram.through_index]
      have h₂ : Finset.card {x | x ∈ (d₁.right_defects ∪ d₂.left_defects)ᶜ} =
         (d₁.right_defects ∪ d₂.left_defects)ᶜ.card := by
        apply Finset.card_bij' (α := Fin m) (β := Fin m)
          (i := fun a ha => a)
          (j := fun b hb => b)
        · intro a ha
          simp at ha
          simp [ha]
        · intro b hb
          simp at hb
          simp [hb]
        · intro a ha
          rfl
        · intro b hb
          rfl
      rw [h₂]
      rw [Finset.card_compl]
      conv => {
        rhs
        rw [Nat.cast_sub (by
          apply Finset.card_le_univ
        )]
      }
      rw [Finset.card_union]
      conv => {
        rhs
        rw [Nat.cast_sub (by
          rw [Finset.card_inter]
          simp
        )]
      }
      simp
      ring

def Monoid.mul_exponent {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  ℕ :=
    Int.toNat (Monoid.mul_exponent' d₁ d₂)

def Monoid.mul_exponent_eq_zero_of_id {n : ℕ}
  (d : Diagram n n) :
  Monoid.mul_exponent d (Diagram.id n) = 0 := by
    simp only [Monoid.mul_exponent, Monoid.mul_exponent']
    simp only [Diagram.mul_id]
    simp [Diagram.through_index_of_id]

def Monoid.mul_exponent_eq_zero_of_id' {n : ℕ}
  (d : Diagram n n) :
  PlanarRook.Monoid.mul_exponent (Diagram.id n) d = 0 := by
    simp only [Monoid.mul_exponent, Monoid.mul_exponent']
    simp only [Diagram.id_mul]
    simp [Diagram.through_index_of_id]

def Monoid.mul_exponent_assoc' {n m k l : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (d₃ : Diagram k l) :
  PlanarRook.Monoid.mul_exponent' d₁ d₂ +
  PlanarRook.Monoid.mul_exponent' (d₁ * d₂) d₃ =
  PlanarRook.Monoid.mul_exponent' d₁ (d₂ * d₃) +
  PlanarRook.Monoid.mul_exponent' d₂ d₃ := by
    unfold PlanarRook.Monoid.mul_exponent'
    simp [Diagram.mul_assoc]
    ring

def Monoid.mul_exponent_ge_zero {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k) :
  0 ≤ PlanarRook.Monoid.mul_exponent' d₁ d₂ := by
    rw [PlanarRook.Monoid.mul_exponent_is_stubs' d₁ d₂]
    simp

def Monoid.mul_exponent_assoc {n m k l : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (d₃ : Diagram k l) :
  Monoid.mul_exponent d₁ d₂ +
  Monoid.mul_exponent (d₁ * d₂) d₃ =
  PlanarRook.Monoid.mul_exponent d₁ (d₂ * d₃) +
  PlanarRook.Monoid.mul_exponent d₂ d₃ := by
    unfold PlanarRook.Monoid.mul_exponent
    rw [←Int.toNat_add (PlanarRook.Monoid.mul_exponent_ge_zero _ _)
                       (PlanarRook.Monoid.mul_exponent_ge_zero _ _)]
    rw [←Int.toNat_add (PlanarRook.Monoid.mul_exponent_ge_zero _ _)
                       (PlanarRook.Monoid.mul_exponent_ge_zero _ _)]
    rw [PlanarRook.Monoid.mul_exponent_assoc']

def Diagram.ι : Diagram n m → Diagram m n := fun d =>{
  left_defects := d.right_defects,
  right_defects := d.left_defects,
  consistant := by rw [d.consistant]
}

def Diagram.ι_involutive {n m : ℕ}
  (d : Diagram n m) :
  Diagram.ι (Diagram.ι d) = d := by
    apply Diagram.ext
    · simp [Diagram.ι]
    · simp [Diagram.ι]

instance {n : ℕ} : Function.Involutive (α := Diagram n n) Diagram.ι :=
  Diagram.ι_involutive

def Diagram.ι_lr_bijection {n m : ℕ}
  (d : Diagram n m) :
  d.ι.lr_bijection = d.lr_bijection.symm := by
    exact Subsingleton.elim _ _

def Diagram.ι_mul {n m : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m n) :
  (d₁ * d₂).ι = d₂.ι * d₁.ι := by
    apply Diagram.ext
    · simp only [hmul_eq_mul]
      unfold Diagram.mul
      simp only [ι]
      ext x
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        rcases h with ⟨ha, hb⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        use ha
        rw [←Diagram.ι_lr_bijection] at hb
        exact hb
      · intro h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        rcases h with ⟨ha, hb⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        use ha
        rw [←Diagram.ι_lr_bijection]
        exact hb
    constructor

end PlanarRook
