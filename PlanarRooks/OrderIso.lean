import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

section

open OrderIso

variable {α β : Type} [LinearOrder α] [WellFoundedLT α] [LinearOrder β]

instance unique_finite_orderiso {a : Finset α} {b : Finset β} (equal_size : a.card = b.card) :
  Unique (a ≃o b) := {
    default := (a.orderIsoOfFin rfl).symm.trans (b.orderIsoOfFin equal_size.symm),
    uniq := fun f => OrderIso.subsingleton_of_wellFoundedLT.allEq f _
  }

end
