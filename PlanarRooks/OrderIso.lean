import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

section

open OrderIso

variable {α β : Type}[LinearOrder α] [LinearOrder β]

instance unique_finite_orderiso [WellFoundedLT α]
  {a : Finset α} {b : Finset β}
  (equal_size : a.card = b.card) :
  Unique (a ≃o b) := {
    default := (a.orderIsoOfFin rfl).symm.trans (b.orderIsoOfFin equal_size.symm),
    uniq := fun f => OrderIso.subsingleton_of_wellFoundedLT.allEq f _
  }

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
