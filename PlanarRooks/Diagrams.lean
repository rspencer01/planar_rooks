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
import Mathlib.Logic.Equiv.Defs

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
-- NOTE: I'm not sure - this might have been a better definition of a diagram:
def pi_iso :  Diagram n m ≃
  (Σ k, ({S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k})) := {
  toFun := fun d => ⟨d.left_defects.card,
                     ⟨d.left_defects, rfl⟩,
                     ⟨d.right_defects, eq_comm.mpr d.consistant⟩⟩,
  invFun := fun ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩ => Diagram.mk l r (by rw [hl, hr]),
  left_inv := fun d => by simp
  right_inv := fun ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩ => by
    simp[hl]
    cases hl
    simp
}

def pi_iso' :
  (Σ k : ℕ ,          {S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k}) ≃
  (Σ k : Fin (n + 1), {S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k}) := {
    toFun := fun ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩ => ⟨⟨h, by
      rw [←hl]
      have k := Finset.card_le_univ l
      simp only [Fintype.card_fin] at k
      simp only [gt_iff_lt]
      rw[←Nat.le_iff_lt_add_one]
      exact k
      ⟩, ⟨l, hl⟩, ⟨r, hr⟩⟩,
    invFun := fun ⟨⟨h, _⟩, ⟨l, hl⟩, ⟨r, hr⟩⟩ => ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩,
  }

def pi_iso₂ : Diagram n m ≃
  (Σ k : Fin (n + 1), {S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k}) :=
  pi_iso.trans pi_iso'

-- There are only finitely many diagrams for given n and m
instance {n m} : Finite (Diagram n m) := Finite.of_equiv _ pi_iso₂.symm
instance {n m} : Fintype (Diagram n m) := {
  elems := Finset.univ.image pi_iso₂.invFun,
  complete := by
    intro d
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    use pi_iso₂.toFun d
    simp
}

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
def through_index (d : Diagram n m) : ℕ := d.left_defects.card

def through_index_of_iso (k : ℕ)
  (s₁ : {S : Finset (Fin n) // S.card = k}) (s₂ : {S : Finset (Fin m) // S.card = k}) :
  through_index (Diagram.pi_iso.symm ⟨k, (s₁, s₂)⟩) = k := by
    simp [through_index, Diagram.pi_iso, s₁.property]

theorem through_index_eq_right (d : Diagram n m) :
  d.through_index = d.right_defects.card := by
    rw [←d.consistant]
    rfl

/-- Through indices are bounded by the size of the left defects. -/
theorem through_index_le_left (d : Diagram n m) :
  d.through_index ≤ n := by
    rw [through_index]
    conv => {
      rhs
      rw [←Fintype.card_fin n]
    }
    exact Finset.card_le_univ _

/-- Through indices are bounded by the size of the right defects. -/
theorem through_index_le_right {n m : ℕ}
  (d : Diagram n m) :
  d.through_index ≤ m := by
    rw [through_index, d.consistant]
    conv => {
      rhs
      rw [←Fintype.card_fin m]
    }
    exact Finset.card_le_univ _

theorem through_index_of_id {n : ℕ} : (id n).through_index = n := by
    simp [through_index, id]

theorem through_index_of_empty {n m : ℕ} : (empty n m).through_index = 0 := by
    simp [through_index, empty]

/-! ## Diagrams as partial bijections
-/

/-- A diagram defines a bijection between left and right defects -/
def lr_bijection {n m : ℕ}
  (d : Diagram n m) :
  d.left_defects ≃o d.right_defects :=
    (unique_finite_orderiso d.consistant).default

@[simp]
def lr_bijection_of_id_is_id {n : ℕ} : (id n).lr_bijection = OrderIso.refl _ :=
  Subsingleton.elim _ _

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

/- The bijection of a diagram is the one we started with if we construct a diagram from a bijection.
-/
def lr_bijection_of_lr_bijection {n m : ℕ} (d : Diagram n m) :
  Diagram.of_lr_bijection d.left_defects d.right_defects d.lr_bijection = d := by
    rw [Diagram.of_lr_bijection]

/- The bijection of a diagram constructed from a bijection is the original bijection.
-/
def lr_bijection_of_of_lr_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  (Diagram.of_lr_bijection left_defects right_defects bijection).lr_bijection = bijection :=
    Subsingleton.elim _ bijection

def lr_bijections_are_diagrams {n m : ℕ} :
  Diagram n m ≃ (Σ (left_defects : Finset (Fin n)) (right_defects : Finset (Fin m)),
    left_defects ≃o right_defects) := {
    invFun := fun ⟨left_defects, right_defects, bijection⟩ =>
      Diagram.of_lr_bijection left_defects right_defects bijection,
    toFun := fun d => ⟨d.left_defects, d.right_defects, d.lr_bijection⟩
    right_inv := fun d => by
      simp only [of_lr_bijection]
      apply congr_arg
      apply congr_arg
      exact lr_bijection_of_of_lr_bijection d.fst d.2.fst d.2.snd
  }

/- Diagrams act on Fin n by sending left defects to their
corresponding right defect, and undefined elsewhere.
-/
def act {n m : ℕ} (d : Diagram n m) (i : Fin n) :
  Option (Fin m) :=
  if h : i ∈ d.left_defects then
    some (d.lr_bijection ⟨i, h⟩)
  else
    none

/- The action of the identity diagram is the identity function
-/
def act_of_id {n : ℕ} (i : Fin n) : act (id n) i = some i := by
  simp [act, lr_bijection_of_id_is_id]
  simp [id]

/- The action of the empty diagram is nowhere defined
-/
def act_of_empty {n m : ℕ} (i : Fin n) : act (empty n m) i = none := rfl

/-! ## Multiplication of diagrams
-/

def mul {n m k : ℕ} (d₁ : Diagram n m) (d₂ : Diagram m k) :
  Diagram n k := {
    left_defects :=
      { x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects},
    right_defects :=
      { y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects},
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

instance has_hmul : HMul (Diagram n m) (Diagram m k) (Diagram n k) := ⟨mul⟩

@[simp]
def hmul_left_defects (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).left_defects = ({ x | ∃ (h : x ∈ d₁.left_defects),
           ↑(d₁.lr_bijection ⟨x, h⟩) ∈ d₂.left_defects } : Finset (Fin n)) := rfl

@[simp]
def hmul_right_defects (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).right_defects = ({ y | ∃ (h : y ∈ d₂.right_defects),
           ↑(d₂.lr_bijection.symm ⟨y, h⟩) ∈ d₁.right_defects } : Finset (Fin k)) := rfl

def mul_id (d : Diagram n m) : d * (id m) = d := by
    apply Diagram.ext
    · simp [id]
    · simp
      simp [id]

def id_mul (d : Diagram n m) : (id n) * d = d := by
    apply Diagram.ext
    · simp
      simp [id]
    · simp [id]

/-! ### Simple results about multiplication
-/

/-- The left defects of a product only depends on the left factor and the left defects of the
right factor.
-/
def mul_left_of_right_arbitrary (d₁ : Diagram n m)
  (s : Finset (Fin m)) (t u : Finset (Fin k)) (h₁ : s.card = t.card) (h₂ : s.card = u.card) :
  (d₁ * (Diagram.mk s t h₁)).left_defects = (d₁ * (Diagram.mk s u h₂)).left_defects := by
    rw[hmul_left_defects]
    rw[hmul_left_defects]

/-- The left defects of a product do not change if you only change the right defects of the
right factor. -/
def mul_left_of_right_arbitrary' (d₁ : Diagram n m) (d₂ d₃ : Diagram m k)
  (h : d₂.left_defects = d₃.left_defects) : (d₁ * d₂).left_defects = (d₁ * d₃).left_defects := by
    have h' : d₃ = Diagram.mk d₂.left_defects d₃.right_defects (by rw [h, d₃.consistant]) := by
      apply Diagram.ext
      · simp [h]
      · simp
    rw [h']
    exact mul_left_of_right_arbitrary _ _ _ d₃.right_defects d₂.consistant (by rw[h, d₃.consistant])

def mul_right_subset (d₁ : Diagram n m) (s : Finset (Fin m)) (t : Finset (Fin k))
  (h : s.card = t.card) : (d₁ * (Diagram.mk s t h)).right_defects ⊆ t := by
    intro x hx
    simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨h₁, h₂⟩
    exact h₁

def mul_left_subset (d₁ : Diagram m k) (s : Finset (Fin n)) (t : Finset (Fin m))
  (h : s.card = t.card) : ((Diagram.mk s t h) * d₁).left_defects ⊆ s := by
    intro x hx
    simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨h₁, h₂⟩
    exact h₁

/-! ### Lemmata for proving associativity of multiplication
-/
def restate_mul₂ (d₁ : Diagram n m) (d₂ : Diagram m k) (x : d₁.left_defects)
  (hx : ∃ (y : Fin m), d₁.lr_bijection x = y ∧ y ∈ d₂.left_defects) :
    x.val ∈ (d₁ * d₂).left_defects := by
      simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with ⟨y, hy⟩
      use x.prop
      rw [hy.1]
      exact hy.2

def restate_mul₃ (d₁ : Diagram n m) (d₂ : Diagram m k) (x : d₁.left_defects)
  (y : Fin m)
  (hx : d₁.lr_bijection x = y ∧ y ∈ d₂.left_defects) :
    ((d₁ * d₂).lr_bijection ⟨x, Diagram.restate_mul₂ d₁ d₂ x ⟨y, hx⟩⟩)
     = (⟨d₂.lr_bijection ⟨y, hx.2⟩, by
         simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta,
           OrderIso.symm_apply_apply, SetLike.coe_mem, exists_const, true_and]
         rw[←hx.1]
         simp only [SetLike.coe_mem]
      ⟩ : (d₁ * d₂).right_defects) := by
       rcases hx with ⟨hx₁, hx₂⟩
       conv => {
         rhs
         arg 1
         arg 1
         arg 2
         arg 1
         rw [←hx₁]
       }
       have xd₁d₂ : ↑x ∈ (d₁ * d₂).left_defects := by simp [hx₁, hx₂, x.prop]
       let f := (d₁ * d₂).lr_bijection
       let g : ↥(d₁ * d₂).left_defects ≃o ↥(d₁ * d₂).right_defects := {
          toFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection ⟨d₁.lr_bijection ⟨x, by
            simp at hx
            exact hx.choose
          ⟩, by
            simp at hx
            exact hx.choose_spec
          ⟩, by simp⟩
          invFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
            simp at hy
            exact hy.choose
          ⟩, by
            simp at hy
            exact hy.choose_spec
          ⟩, by simp⟩
          map_rel_iff' := by simp
          left_inv := fun h => by simp
          right_inv := fun h => by simp
       }
       have kk : ↑((d₁ * d₂).lr_bijection ⟨x, xd₁d₂⟩) = f ⟨x, xd₁d₂⟩ := rfl
       rw [kk]
       have kk : ⟨d₂.lr_bijection ⟨↑(d₁.lr_bijection x), by
         rw [hx₁]
         exact hx₂
         ⟩, by simp ⟩ = g ⟨x, xd₁d₂⟩ := rfl
       rw [kk]
       have kk : f = g := by rw [Subsingleton.elim f]
       rw [kk]

def restate_mul₄ (d₁ : Diagram n m) (d₂ : Diagram m k) (x : d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm x = y ∧ y ∈ d₁.right_defects) :
    x.val ∈ (d₁ * d₂).right_defects := by
      simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with ⟨y, hy⟩
      use x.prop
      rw [y]
      exact hy

def restate_mul₅ {n m k : ℕ}
  (d₁ : Diagram n m)
  (d₂ : Diagram m k)
  (x : d₂.right_defects)
  (y : Fin m)
  (hx : d₂.lr_bijection.symm x = y ∧ y ∈ d₁.right_defects) :
    ((d₁ * d₂).lr_bijection.symm ⟨x, Diagram.restate_mul₄ d₁ d₂ x y hx⟩)
     = (⟨d₁.lr_bijection.symm ⟨y, hx.2⟩, by
       simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, Subtype.coe_eta,
         OrderIso.apply_symm_apply, SetLike.coe_mem, exists_const, true_and]
       rw [←hx.1]
       simp
       ⟩ : (d₁ * d₂).left_defects) := by
         rcases hx with ⟨hx₁, hx₂⟩
         conv => {
          rhs
          arg 1
          arg 1
          arg 2
          arg 1
          rw [←hx₁]
         }
         have xd₁d₂ : ↑x ∈ (d₁ * d₂).right_defects := by simp [hx₁, hx₂, x.prop]
         let f := (d₁ * d₂).lr_bijection.symm
         let g : ↥(d₁ * d₂).right_defects ≃o ↥(d₁ * d₂).left_defects := {
            toFun := fun ⟨y, hy⟩ => ⟨d₁.lr_bijection.symm ⟨d₂.lr_bijection.symm ⟨y, by
              simp at hy
              exact hy.choose
            ⟩, by
              simp at hy
              exact hy.choose_spec
            ⟩, by simp⟩
            invFun := fun ⟨x, hx⟩ => ⟨d₂.lr_bijection.toFun ⟨d₁.lr_bijection.toFun ⟨x, by
              simp at hx
              exact hx.choose
            ⟩, by
              simp at hx
              exact hx.choose_spec
            ⟩, by simp⟩
            map_rel_iff' := by simp
            left_inv := fun h => by simp
            right_inv := fun h => by simp
         }
         have kk : ↑((d₁ * d₂).lr_bijection.symm ⟨x, xd₁d₂⟩) = f ⟨x, xd₁d₂⟩ := rfl
         rw [kk]
         have kk : ⟨↑(d₁.lr_bijection.symm ⟨↑(d₂.lr_bijection.symm x), by
           rw [hx₁]
           exact hx₂
           ⟩), by simp⟩ = g ⟨x, xd₁d₂⟩ := rfl
         rw [kk]
         have kk : f = g := by rw [Subsingleton.elim f]
         rw [kk]
/-! ### Associativity of multiplication
-/
def mul_assoc (d₁ : Diagram n m) (d₂ : Diagram m k) (d₃ : Diagram k l) :
  (d₁ * d₂) * d₃ = d₁ * (d₂ * d₃) := by
     apply Diagram.ext
     · rw[hmul_left_defects]
       ext x
       constructor
       · intro h
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and]
         simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and] at ha
         rcases ha with ⟨hc, hd⟩
         use hc
         use hd
         have kk:= Diagram.restate_mul₃ d₁ d₂ ⟨x, hc⟩ (d₁.lr_bijection ⟨x, hc⟩) ⟨rfl, hd⟩
         rw [kk] at hb
         exact hb
       · intro h
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and] at h
         rcases h with ⟨ha, hb⟩
         rcases hb with ⟨hc, hd⟩
         constructor
         · have kk := Diagram.restate_mul₃ d₁ d₂ ⟨x, ha⟩ (d₁.lr_bijection ⟨x, ha⟩) ⟨rfl, hc⟩
           rw [kk]
           exact hd
     · rw[hmul_right_defects]
       ext x
       constructor
       · simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, true_and,
         hmul_left_defects, forall_exists_index]
         intro h ha hb
         use ⟨h, ha⟩
         have kk := Diagram.restate_mul₅ d₂ d₃ ⟨x, h⟩ (d₃.lr_bijection.symm ⟨x, h⟩) ⟨rfl, ha⟩
         have kk₂ := SetCoe.ext_iff.mpr kk
         simp only [hmul_left_defects, hmul_right_defects] at kk₂
         rw [←kk₂] at hb
         exact hb
       · intro h
         simp only [hmul_right_defects, hmul_left_defects, Finset.mem_filter, Finset.mem_univ,
           true_and] at h
         rcases h with ⟨ha, hb⟩
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         rcases ha with ⟨hc, hd⟩
         use hc
         simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, true_and]
         use hd
         have kk := Diagram.restate_mul₅ d₂ d₃ ⟨x, hc⟩ (d₃.lr_bijection.symm ⟨x, hc⟩)
           ⟨rfl, hd⟩
         have kk₂ := SetCoe.ext_iff.mpr kk
         simp only [hmul_left_defects, hmul_right_defects] at kk₂
         rw [kk₂] at hb
         exact hb

#eval (mul (example_1) (id 5)).act 4

end Diagram

/-! ## The monoid of planar rook diagrams

We can now show that the planar rook diagrams with n vertices on each side form a monoid under
multiplication.
-/
instance Monoid : Monoid (Diagram n n) := {
  mul := HMul.hMul,
  one := Diagram.id n,
  mul_one := Diagram.mul_id,
  one_mul := Diagram.id_mul,
  mul_assoc := Diagram.mul_assoc
}
namespace Monoid

theorem one_def {n : ℕ} : (1 : Diagram n n) = Diagram.id n := by rfl

/-! ## Through degree of multiplication
-/

/-- Multiplication does not increase the through degree of either diagram. -/
theorem mul_not_increase_through_degree (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).through_index ≤ min d₁.through_index d₂.through_index := by
    unfold Diagram.through_index
    simp only [le_inf_iff]
    constructor
    · apply Finset.card_le_card
      exact Diagram.mul_left_subset _ _ _ _
    · rw[PlanarRook.Diagram.consistant]
      rw[PlanarRook.Diagram.consistant]
      apply Finset.card_le_card
      exact Diagram.mul_right_subset _ _ _ _

/-! ## The twist factor in the monoid

There is a natural number that arises when multiplying two diagrams,
`PlanarRook.Monoid.mul_exponent`, which counts the number of disconnected components in the
resulting diagram. This can be used when defining `PlanarRook.Algebra` to determine the
"twist": the power of `δ` that appears. Here we collate some results about this number.
-/

/-- When multiplying two diagrams, we are left with a number of disconnected
components. The number of these is the exponent in the planar rook algebra's
multiplication.
-/
def mul_exponent' (d₁ : Diagram n m) (d₂ : Diagram m k) : ℤ :=
  m - d₁.through_index - d₂.through_index + (d₁ * d₂).through_index

theorem mul_exponent_is_stubs' (d₁ : Diagram n m) (d₂ : Diagram m k) :
  PlanarRook.Monoid.mul_exponent' d₁ d₂ =
    Finset.card {x | x ∈ (d₁.right_defects ∪ d₂.left_defects)ᶜ} := by
      have h : (d₁ * d₂).through_index = (d₁.right_defects ∩ d₂.left_defects).card := by
        unfold Diagram.through_index
        simp only [Diagram.hmul_left_defects]
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

def mul_exponent (d₁ : Diagram n m) (d₂ : Diagram m k) : ℕ :=
    Int.toNat (Monoid.mul_exponent' d₁ d₂)

/-- The identity diagram invokes zero twist when multiplied on the right. -/
def mul_exponent_eq_zero_of_id (d : Diagram n m) :
  Monoid.mul_exponent d (Diagram.id m) = 0 := by
    simp only [Monoid.mul_exponent, Monoid.mul_exponent']
    simp only [Diagram.mul_id]
    simp [Diagram.through_index_of_id]

/-- The identity diagram invokes zero twist when multiplied on the left. -/
def mul_exponent_eq_zero_of_id' (d : Diagram n m) :
  PlanarRook.Monoid.mul_exponent (Diagram.id n) d = 0 := by
    simp only [Monoid.mul_exponent, Monoid.mul_exponent']
    simp only [Diagram.id_mul]
    simp [Diagram.through_index_of_id]

/-- The twist is additive over associated multipliation as an integer. -/
def mul_exponent_assoc' (d₁ : Diagram n m) (d₂ : Diagram m k) (d₃ : Diagram k l) :
  PlanarRook.Monoid.mul_exponent' d₁ d₂ +
  PlanarRook.Monoid.mul_exponent' (d₁ * d₂) d₃ =
  PlanarRook.Monoid.mul_exponent' d₁ (d₂ * d₃) +
  PlanarRook.Monoid.mul_exponent' d₂ d₃ := by
    unfold PlanarRook.Monoid.mul_exponent'
    rw[Diagram.mul_assoc]
    ring

/-- The twist is non-negative. -/
def mul_exponent_ge_zero (d₁ : Diagram n m) (d₂ : Diagram m k) :
  0 ≤ PlanarRook.Monoid.mul_exponent' d₁ d₂ := by
    rw [PlanarRook.Monoid.mul_exponent_is_stubs' d₁ d₂]
    simp

/-- The twist is additive over associated multiplication as a natural number. -/
def mul_exponent_assoc (d₁ : Diagram n m) (d₂ : Diagram m k) (d₃ : Diagram k l) :
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

def mul_exponent_of_right_arbitrary (d₁ : Diagram n m)
  (s : Finset (Fin m)) (t u : Finset (Fin k)) (h₁ : s.card = t.card) (h₂ : s.card = u.card) :
  Monoid.mul_exponent d₁ (Diagram.mk s t h₁) = Monoid.mul_exponent d₁ (Diagram.mk s u h₂) := by
    unfold mul_exponent
    rw [mul_exponent_is_stubs']
    rw [mul_exponent_is_stubs']

end Monoid

/-! ## The monoid involution

There is a natural involution on diagrams, given by reflecting them across the vertical axis.
This sends left defects to right defects and vice versa, and reverses the order of multiplication.
-/

def Diagram.ι : Diagram n m → Diagram m n := fun d =>{
  left_defects := d.right_defects,
  right_defects := d.left_defects,
  consistant := d.consistant.symm
}

def Diagram.ι_involutive {n m : ℕ} (d : Diagram n m) :
  Diagram.ι (Diagram.ι d) = d := by
    apply Diagram.ext
    · simp [Diagram.ι]
    · simp [Diagram.ι]

instance {n : ℕ} : Function.Involutive (α := Diagram n n) Diagram.ι :=
  Diagram.ι_involutive

def Diagram.ι_lr_bijection {n m : ℕ} (d : Diagram n m) :
  d.ι.lr_bijection = d.lr_bijection.symm :=
     Subsingleton.elim _ _

/-- The involution reverses the order of multiplication. -/
def Diagram.ι_mul {n m k : ℕ} (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).ι = d₂.ι * d₁.ι := by
    apply Diagram.ext
    · simp only [ι, hmul_right_defects, hmul_left_defects]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases h with ⟨ha, hb⟩
        use ha
        rw [←Diagram.ι_lr_bijection] at hb
        exact hb
      · intro h
        rcases h with ⟨ha, hb⟩
        use ha
        rw [←Diagram.ι_lr_bijection]
        exact hb
    constructor

/-- The involution preserves the through index. -/
theorem Monoid.ι_through_index (d : Diagram n m) :
  (Diagram.ι d).through_index = d.through_index := by
    simp [Diagram.ι, Diagram.through_index, d.consistant]

/-- The involution preserves the multiplication exponent. -/
theorem Monoid.mul_exponent_of_ι (d₁ : Diagram n m) (d₂ : Diagram m k) :
  Monoid.mul_exponent d₁ d₂ = Monoid.mul_exponent d₂.ι d₁.ι := by
    simp only [Monoid.mul_exponent, Monoid.mul_exponent']
    rw[←Diagram.ι_mul]
    rw[Monoid.ι_through_index (d₁ * d₂)]
    rw[Monoid.ι_through_index d₁]
    rw[Monoid.ι_through_index d₂]
    ring_nf

def Diagram.ι_of_iso {n m : ℕ}
  (k : ℕ)
  (s₁ : {S : Finset (Fin n) // S.card = k}) (s₂ : {S : Finset (Fin m) // S.card = k}) :
  Diagram.ι (Diagram.pi_iso.symm ⟨k, (s₁, s₂)⟩) = Diagram.pi_iso.symm ⟨k, (s₂, s₁)⟩ := by
    simp [Diagram.ι, Diagram.pi_iso]

def Diagram.ι_of_iso₂ {n : ℕ}
  (k : Fin (n + 1))
  (s₁ : {S : Finset (Fin n) // S.card = k}) (s₂ : {S : Finset (Fin n) // S.card = k}) :
  Diagram.ι (Diagram.pi_iso.symm ⟨k, (s₁, s₂)⟩) = Diagram.pi_iso₂.symm ⟨k, (s₂, s₁)⟩ := by
    simp [Diagram.ι, Diagram.pi_iso₂, Diagram.pi_iso, Diagram.pi_iso']

end PlanarRook
