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
import Mathlib.Data.Set.Defs
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
import Mathlib.Data.Finset.CastCard
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
  left_inv := fun d => by simp only
  right_inv := fun ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩ => by
    simp only [Sigma.mk.injEq, hl, true_and]
    cases hl
    simp only [heq_eq_eq]
}

def pi_iso' :
  (Σ k : ℕ ,          {S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k}) ≃
  (Σ k : Fin (n + 1), {S : Finset (Fin n) // S.card = k} × {S : Finset (Fin m) // S.card = k}) := {
    toFun := fun ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩ => ⟨⟨h, by
      have k := Finset.card_le_univ l
      simp only [Fintype.card_fin] at k
      simp only [←hl, ←Nat.le_iff_lt_add_one, k]
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
  complete := fun d => by
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

theorem through_index_eq_left (d : Diagram n m) :
  d.through_index = d.left_defects.card := rfl

theorem through_index_eq_right (d : Diagram n m) :
  d.through_index = d.right_defects.card := d.consistant

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
theorem through_index_le_right (d : Diagram n m) : d.through_index ≤ m := by
    rw [through_index, d.consistant]
    conv => {
      rhs
      rw [←Fintype.card_fin m]
    }
    exact Finset.card_le_univ _

theorem through_index_of_id : (id n).through_index = n := by simp [through_index, id]

theorem through_index_of_empty : (empty n m).through_index = 0 := by simp [through_index, empty]

/-! ## Diagrams as partial bijections
-/

/-- A diagram defines a bijection between left and right defects -/
def bijection (d : Diagram n m) : d.left_defects ≃o d.right_defects :=
    (unique_finite_orderiso d.consistant).default

@[simp]
def bijection_of_id_is_id {n : ℕ} : (id n).bijection = OrderIso.refl _ :=
  Subsingleton.elim _ _

def of_bijection (left_defects : Finset (Fin n)) (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) : Diagram n m := {
    left_defects := left_defects,
    right_defects := right_defects,
    consistant := equal_size_of_orderiso bijection
  }

/- The bijection of a diagram is the one we started with if we construct a diagram from a bijection.
-/
def bijection_of_bijection {n m : ℕ} (d : Diagram n m) :
  Diagram.of_bijection d.left_defects d.right_defects d.bijection = d := by
    rw [Diagram.of_bijection]

/- The bijection of a diagram constructed from a bijection is the original bijection.
-/
def bijection_of_of_bijection {n m : ℕ}
  (left_defects : Finset (Fin n))
  (right_defects : Finset (Fin m))
  (bijection : left_defects ≃o right_defects) :
  (Diagram.of_bijection left_defects right_defects bijection).bijection = bijection :=
    Subsingleton.elim _ bijection

def bijections_are_diagrams {n m : ℕ} :
  Diagram n m ≃ (Σ (left_defects : Finset (Fin n)) (right_defects : Finset (Fin m)),
    left_defects ≃o right_defects) := {
    invFun := fun ⟨left_defects, right_defects, bijection⟩ =>
      Diagram.of_bijection left_defects right_defects bijection,
    toFun := fun d => ⟨d.left_defects, d.right_defects, d.bijection⟩
    right_inv := fun d => by
      simp only [of_bijection]
      apply congr_arg
      apply congr_arg
      exact bijection_of_of_bijection d.fst d.2.fst d.2.snd
  }

/- Diagrams act on Fin n by sending left defects to their
corresponding right defect, and undefined elsewhere.
-/
def act {n m : ℕ} (d : Diagram n m) (i : Fin n) :
  Option (Fin m) :=
  if h : i ∈ d.left_defects then
    some (d.bijection ⟨i, h⟩)
  else
    none

/- The action of the identity diagram is the identity function
-/
def act_of_id {n : ℕ} (i : Fin n) : act (id n) i = some i := by
  simp [act, bijection_of_id_is_id]
  simp [id]

/- The action of the empty diagram is nowhere defined
-/
def act_of_empty {n m : ℕ} (i : Fin n) : act (empty n m) i = none := rfl

/-! ## Multiplication of diagrams
-/

def mul {n m k : ℕ} (d₁ : Diagram n m) (d₂ : Diagram m k) :
  Diagram n k := {
    left_defects :=
      { x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.bijection ⟨x, h⟩) ∈ d₂.left_defects},
    right_defects :=
      { y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.bijection.symm ⟨y, h⟩) ∈ d₁.right_defects},
    consistant := by
      let f : ({x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.bijection ⟨x, h⟩) ∈ d₂.left_defects}
        : Finset (Fin n)) →
          { y | ∃ (h : y ∈ d₂.right_defects),
                ↑(d₂.bijection.symm ⟨y, h⟩) ∈ d₁.right_defects } := fun ⟨x, hx⟩ =>
              ⟨↑(d₂.bijection ⟨d₁.bijection ⟨x, (Finset.mem_filter.mp hx).2.choose⟩,
                        (Finset.mem_filter.mp hx).2.choose_spec⟩ ) , by simp⟩
      let g : ({ y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.bijection.symm ⟨y, h⟩) ∈ d₁.right_defects}
          : Finset (Fin k)) →
          {x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.bijection ⟨x, h⟩) ∈ d₂.left_defects} :=
          fun ⟨y, hy⟩ =>
              ⟨↑(d₁.bijection.symm ⟨↑(d₂.bijection.symm ⟨y, (Finset.mem_filter.mp hy).2.choose⟩),
              (Finset.mem_filter.mp hy).2.choose_spec⟩ ), by simp⟩
      apply Finset.card_bij'
        (s := ({x | ∃ (h : x ∈ d₁.left_defects), ↑(d₁.bijection ⟨x, h⟩) ∈ d₂.left_defects}
                 : Finset (Fin n)))
        (t := ({y | ∃ (h : y ∈ d₂.right_defects), ↑(d₂.bijection.symm ⟨y, h⟩) ∈ d₁.right_defects}
                 : Finset (Fin k)))
        (i := fun x hx => f ⟨x, hx⟩)
        (j := fun y hy => g ⟨y, hy⟩)
        (left_inv := fun a ha => by simp[f, g])
        (right_inv := fun a ha => by simp[f, g])
      · simp [f]
      · simp [g]
  }

instance has_hmul : HMul (Diagram n m) (Diagram m k) (Diagram n k) := ⟨mul⟩

@[simp]
def hmul_left_defects (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).left_defects = ({ x | ∃ (h : x ∈ d₁.left_defects),
           ↑(d₁.bijection ⟨x, h⟩) ∈ d₂.left_defects } : Finset (Fin n)) := rfl

@[simp]
def hmul_right_defects (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).right_defects = ({ y | ∃ (h : y ∈ d₂.right_defects),
           ↑(d₂.bijection.symm ⟨y, h⟩) ∈ d₁.right_defects } : Finset (Fin k)) := rfl

@[simp]
def mul_id (d : Diagram n m) : d * (id m) = d := by
    apply Diagram.ext
    · simp [id]
    · simp
      simp [id]

@[simp]
def id_mul (d : Diagram n m) : (id n) * d = d := by
    apply Diagram.ext
    · simp
      simp [id]
    · simp [id]

/-! ### Simple results about multiplication
-/

/-- The left defects of a product do not change if you only change the right defects of the
right factor. -/
def mul_left_of_right_arbitrary {d₁ : Diagram n m} (d₂ d₃ : Diagram m k)
  (h : d₂.left_defects = d₃.left_defects) : (d₁ * d₂).left_defects = (d₁ * d₃).left_defects := by
    simp [h]

def mul_right_subset (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).right_defects ⊆ d₂.right_defects := by
    intro x hx
    simp only [hmul_right_defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.choose

def mul_left_subset (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).left_defects ⊆ d₁.left_defects := by
    intro x hx
    simp only [hmul_left_defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.choose

/-! ## Through degree of multiplication
-/

theorem through_degree_of_mul (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).through_index = Finset.card (d₁.right_defects ∩ d₂.left_defects) := by
    unfold through_index
    apply Finset.card_bij'
      (s := (d₁ * d₂).left_defects)
      (i := fun a ha => by simp at ha; exact ↑(d₁.bijection ⟨a, ha.choose⟩))
      (j := fun a ha => d₁.bijection.symm ⟨a, Finset.mem_of_mem_inter_left ha⟩)
    · intro a ha
      simp
    · intro a ha
      simp
    · intro a ha
      simp at ha
      simp [ha.choose_spec]
    · intro a ha
      simp[Finset.mem_of_mem_inter_right ha]

/-- Multiplication does not increase the through degree of either diagram. -/
theorem mul_not_increase_through_degree (d₁ : Diagram n m) (d₂ : Diagram m k) :
  (d₁ * d₂).through_index ≤ min d₁.through_index d₂.through_index := by
    unfold Diagram.through_index
    simp only [le_inf_iff]
    constructor
    · apply Finset.card_le_card
      exact Diagram.mul_left_subset _ _
    · rw[PlanarRook.Diagram.consistant]
      rw[PlanarRook.Diagram.consistant]
      apply Finset.card_le_card
      exact Diagram.mul_right_subset _ _

def through_index_of_mul_independent_of_right (d₁ : Diagram n m) (d₂ d₃ : Diagram m k)
  (h : d₂.left_defects = d₃.left_defects) : (d₁ * d₂).through_index = (d₁ * d₃).through_index := by
    rw [through_index, through_index, mul_left_of_right_arbitrary d₂ d₃ h]

/-! ### Lemmata for proving associativity of multiplication
-/

def restate_mul₃ (d₁ : Diagram n m) (d₂ : Diagram m k) (x : d₁.left_defects)
  (hxx : ↑(d₁.bijection x) ∈ d₂.left_defects) :
    ((d₁ * d₂).bijection ⟨x, by simp [hxx]⟩) = (d₂.bijection ⟨_, hxx⟩ : Fin k) := by
       have xd₁d₂ : ↑x ∈ (d₁ * d₂).left_defects := by simp [hxx, x.prop]
       let f := (d₁ * d₂).bijection
       let g : ↥(d₁ * d₂).left_defects ≃o ↥(d₁ * d₂).right_defects := {
          toFun := fun ⟨x, hx⟩ => ⟨d₂.bijection ⟨d₁.bijection
            ⟨x, Finset.mem_of_subset (mul_left_subset _ _) hx⟩, by
            simp at hx
            exact hx.choose_spec
          ⟩, by simp⟩
          invFun := fun ⟨y, hy⟩ => ⟨d₁.bijection.symm
            ⟨d₂.bijection.symm ⟨y, Finset.mem_of_subset (mul_right_subset _ _) hy⟩, by
            simp at hy
            exact hy.choose_spec
          ⟩, by simp⟩
          map_rel_iff' := by simp
          left_inv := fun h => by simp
          right_inv := fun h => by simp
       }
       have kk : ↑((d₁ * d₂).bijection ⟨x, xd₁d₂⟩) = f ⟨x, xd₁d₂⟩ := rfl
       rw [kk]
       have kk : d₂.bijection ⟨↑(d₁.bijection x), hxx⟩ = ⟨g ⟨x, xd₁d₂⟩, by
         apply Finset.mem_of_subset (mul_right_subset d₁ d₂)
         simp
         ⟩ := rfl
       simp only [hmul_right_defects, hmul_left_defects]
       rw [kk]
       have kk : f = g := by rw [Subsingleton.elim f]
       rw [kk]
       simp

def restate_mul₅ (d₁ : Diagram n m) (d₂ : Diagram m k) (x : d₂.right_defects)
  (hx : ↑(d₂.bijection.symm x) ∈ d₁.right_defects) :
    ((d₁ * d₂).bijection.symm ⟨x, by simp[hx]⟩)
     = (⟨d₁.bijection.symm ⟨_, hx⟩, by simp⟩ : (d₁ * d₂).left_defects) := by
         have xd₁d₂ : ↑x ∈ (d₁ * d₂).right_defects := by simp [hx, x.prop]
         let f := (d₁ * d₂).bijection.symm
         let g : ↥(d₁ * d₂).right_defects ≃o ↥(d₁ * d₂).left_defects := {
            toFun := fun ⟨y, hy⟩ => ⟨d₁.bijection.symm
              ⟨d₂.bijection.symm ⟨y, Finset.mem_of_subset (mul_right_subset _ _) hy⟩, by
              simp at hy
              exact hy.choose_spec
            ⟩, by simp⟩
            invFun := fun ⟨x, hx⟩ => ⟨d₂.bijection.toFun ⟨d₁.bijection.toFun
              ⟨x, Finset.mem_of_subset (mul_left_subset _ _) hx⟩, by
              simp at hx
              exact hx.choose_spec
            ⟩, by simp⟩
            map_rel_iff' := by simp
            left_inv := fun h => by simp
            right_inv := fun h => by simp
         }
         have kk : ↑((d₁ * d₂).bijection.symm ⟨x, xd₁d₂⟩) = f ⟨x, xd₁d₂⟩ := rfl
         rw [kk]
         have kk : ⟨↑(d₁.bijection.symm ⟨↑(d₂.bijection.symm x), by simp [hx]⟩), by simp⟩
            = g ⟨x, xd₁d₂⟩ := rfl
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
       simp only [hmul_right_defects, hmul_left_defects, Finset.mem_filter, Finset.mem_univ,
         true_and]
       constructor
       · simp only [forall_exists_index]
         intro ha hb hc
         use ha
         use hb
         have kk:= Diagram.restate_mul₃ d₁ d₂ ⟨x, ha⟩ hb
         simp only [hmul_right_defects, hmul_left_defects] at kk
         rw [kk] at hc
         exact hc
       · simp only [forall_exists_index]
         intro ha hb hc
         constructor
         · have kk := Diagram.restate_mul₃ d₁ d₂ ⟨x, ha⟩ hb
           simp only [hmul_right_defects, hmul_left_defects] at kk
           rw [kk]
           exact hc
         · use ha
     · rw[hmul_right_defects]
       ext x
       simp only [hmul_right_defects, hmul_left_defects, Finset.mem_filter, Finset.mem_univ,
         true_and]
       constructor
       · simp only [forall_exists_index]
         intro h ha hb
         use ⟨h, ha⟩
         have kk := Diagram.restate_mul₅ d₂ d₃ ⟨x, h⟩ ha
         have kk₂ := SetCoe.ext_iff.mpr kk
         simp only [hmul_left_defects, hmul_right_defects] at kk₂
         rw [←kk₂] at hb
         exact hb
       · intro h
         simp only at h
         rcases h with ⟨ha, hb⟩
         rcases ha with ⟨hc, hd⟩
         use hc
         use hd
         have kk := Diagram.restate_mul₅ d₂ d₃ ⟨x, hc⟩ hd
         have kk₂ := SetCoe.ext_iff.mpr kk
         simp only [hmul_left_defects, hmul_right_defects] at kk₂
         rw [kk₂] at hb
         exact hb

#eval ((example_1) * (id 5)).act 4

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

/-! ## The twist factor in the monoid

There is a natural number that arises when multiplying two diagrams,
`PlanarRook.Monoid.mul_exponent`, which counts the number of disconnected components in the
resulting diagram. This can be used when defining `PlanarRook.Algebra` to determine the
"twist": the power of `δ` that appears. Here we collate some results about this number.
-/

def mul_exponent (d₁ : Diagram n m) (d₂ : Diagram m k) : ℕ :=
  Finset.card (d₁.right_defects ∪ d₂.left_defects)ᶜ

theorem mul_exponent' (d₁ : Diagram n m) (d₂ : Diagram m k) :
  ((mul_exponent d₁ d₂) : ℤ) = m - d₁.through_index - d₂.through_index + (d₁ * d₂).through_index
  := by
  unfold mul_exponent
  simp only [Finset.compl_eq_univ_sdiff, Finset.subset_univ, Finset.cast_card_sdiff,
    Finset.card_univ, Fintype.card_fin, Finset.cast_card_union, Diagram.through_degree_of_mul]
  rw [Diagram.through_index_eq_right d₁, Diagram.through_index_eq_left]
  ring_nf

/-- The identity diagram invokes zero twist when multiplied on the right. -/
def mul_exponent_eq_zero_of_id (d : Diagram n m) :
  Monoid.mul_exponent d (Diagram.id m) = 0 := by simp [Monoid.mul_exponent, Diagram.id]

/-- The identity diagram invokes zero twist when multiplied on the left. -/
def mul_exponent_eq_zero_of_id' (d : Diagram n m) :
  PlanarRook.Monoid.mul_exponent (Diagram.id n) d = 0 := by simp [Monoid.mul_exponent, Diagram.id]

/-- The twist is additive over associated multipliation as an integer. -/
def mul_exponent_assoc' (d₁ : Diagram n m) (d₂ : Diagram m k) (d₃ : Diagram k l) :
  ((PlanarRook.Monoid.mul_exponent d₁ d₂) : ℤ) +
  ((PlanarRook.Monoid.mul_exponent (d₁ * d₂) d₃) : ℤ) =
  ((PlanarRook.Monoid.mul_exponent d₁ (d₂ * d₃)) : ℤ) +
  ((PlanarRook.Monoid.mul_exponent d₂ d₃) : ℤ) := by
    rw [mul_exponent', mul_exponent', mul_exponent', mul_exponent']
    ring_nf
    rw[Diagram.mul_assoc]

/-- The twist is non-negative. -/
def mul_exponent_ge_zero (d₁ : Diagram n m) (d₂ : Diagram m k) :
  0 ≤ mul_exponent d₁ d₂ := by unfold mul_exponent; simp

/-- The twist is additive over associated multiplication as a natural number. -/
def mul_exponent_assoc (d₁ : Diagram n m) (d₂ : Diagram m k) (d₃ : Diagram k l) :
  Monoid.mul_exponent d₁ d₂ +
  Monoid.mul_exponent (d₁ * d₂) d₃ =
  PlanarRook.Monoid.mul_exponent d₁ (d₂ * d₃) +
  PlanarRook.Monoid.mul_exponent d₂ d₃ := by
    apply (Nat.cast_inj (R:=ℤ)).mp
    simp [PlanarRook.Monoid.mul_exponent_assoc']

def mul_exponent_of_right_arbitrary (d₁ : Diagram n m) (d₂ d₃ : Diagram m k)
  (h₁ : d₂.left_defects = d₃.left_defects) :
  Monoid.mul_exponent d₁ d₂ = Monoid.mul_exponent d₁ d₃ := by
    unfold mul_exponent
    rw [h₁]

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

def Diagram.ι_Involutive : Function.Involutive (α := Diagram n n) Diagram.ι := Diagram.ι_involutive

def Diagram.ι_bijection (d : Diagram n m) : d.ι.bijection = d.bijection.symm :=
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
        rw [←Diagram.ι_bijection] at hb
        exact hb
      · intro h
        rcases h with ⟨ha, hb⟩
        use ha
        rw [←Diagram.ι_bijection]
        exact hb
    constructor

/-- The involution preserves the through index. -/
theorem Monoid.ι_through_index (d : Diagram n m) :
  (Diagram.ι d).through_index = d.through_index := by
    simp [Diagram.ι, Diagram.through_index, d.consistant]

/-- The involution preserves the multiplication exponent. -/
@[simp]
theorem Monoid.mul_exponent_of_ι (d₁ : Diagram n m) (d₂ : Diagram m k) :
  Monoid.mul_exponent d₂.ι d₁.ι = Monoid.mul_exponent d₁ d₂ := by
    simp [Monoid.mul_exponent,Diagram.ι,Finset.inter_comm]

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
