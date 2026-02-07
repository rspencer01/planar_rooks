/-
Copyright (c) 2026 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer
-/

/-!
# Order Isomorphisms between Finsets

This module provides some utilities for working with order isomorphisms between finite sets.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

section

open OrderIso

variable {α β : Type}[LinearOrder α] [LinearOrder β]

/-- There is a unique order isomorphism between finsets of equal cardinality
when the source type has a well-founded linear order.
-/
instance unique_finite_orderiso [WellFoundedLT α]
  {a : Finset α} {b : Finset β}
  (equal_size : a.card = b.card) :
  Unique (a ≃o b) := {
    default := (a.orderIsoOfFin rfl).symm.trans (b.orderIsoOfFin equal_size.symm),
    uniq := fun f => OrderIso.subsingleton_of_wellFoundedLT.allEq f _
  }

/-- If there exists an order isomorphism between two finsets, they must have
equal cardinality.
-/
theorem equal_size_of_orderiso {a : Finset α} {b : Finset β} (f : a ≃o b) :
  a.card = b.card := by
      have k := Finset.card_bij'
        (s := a)
        (t := b)
        (i :=  fun a ha => f.toFun ⟨a, ha⟩)
        (j := fun b hb => f.invFun ⟨b, hb⟩)
      apply k
      · exact fun a ha => by simp
      · exact fun b hb => by simp
      · exact fun a ha => by simp
      · exact fun b hb => by simp
end
