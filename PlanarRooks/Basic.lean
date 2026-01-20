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

-- A planar rook diagram is encoded as a pair of subsets of {1, ..., n} and
-- {1, ..., m } of equal size where the first gives the positions of the through strings on the left
-- side, and the second gives the positions of the through strings on the right side.
structure PlanarRookDiagram (n m : ℕ) where
  (through_strings : (Fin n) ≃. (Fin m))
  (is_planar : ∀ (a b : Fin n), a ≤ b → through_strings a ≤ through_strings b ∨ through_strings b = none)

instance : Finite (Fin n ≃. Fin m) :=
  Finite.of_injective PEquiv.toFun DFunLike.coe_injective

@[ext]
theorem PlanarRookDiagram.ext {n m : ℕ}
  {d₁ d₂ : PlanarRookDiagram n m}
  (h : d₁.through_strings = d₂.through_strings) :
  d₁ = d₂ :=
by
  cases d₁
  cases d₂
  cases h
  rfl

instance : Finite (PlanarRookDiagram n m) := by
  apply Finite.of_injective (β := (Fin n) ≃. (Fin m)) PlanarRookDiagram.through_strings
  intro a1 a2 h
  exact PlanarRookDiagram.ext h

instance : DecidableEq (PlanarRookDiagram n m) := by
  classical
  intro a b
  refine decidable_of_iff (a.through_strings = b.through_strings) ?_
  constructor
  · exact PlanarRookDiagram.ext
  · intro h
    rw [h]


noncomputable instance {n m : ℕ} : Fintype (PlanarRookDiagram n m) := by
  apply Fintype.ofFinite


-- The left through strings of a diagram are the positions of the through strings on the left side
def PlanarRookDiagram.left_through {n m : ℕ} (d : PlanarRookDiagram n m) : Finset (Fin n) :=
  Finset.filter (fun i => d.through_strings.toFun i ≠ none) Finset.univ
-- The right through strings of a diagram are the positions of the through strings on the right side
def PlanarRookDiagram.right_through {n m : ℕ} (d : PlanarRookDiagram n m) : Finset (Fin m) :=
  Finset.filter (fun i => d.through_strings.invFun i ≠ none) Finset.univ

#check Fin.find?

def PEquiv.ofList {a b : Nat} (l : List (Fin a × Fin b))
    (h_inj' : ∀ i x y, (x, i) ∈ l → (y, i) ∈ l → x = y)
    :
    Fin a ≃. Fin b :=
    let toFun' := fun i =>
      Fin.find? (fun p => (i, p) ∈ l)
    let toFun'Inj : ∀ x y, toFun' x = some y → (x, y) ∈ l := by
      intro x y h
      have k := Fin.find?_eq_some_iff.mp h
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at k
      exact k.1
{
  toFun := toFun',
  invFun := fun j => Fin.find? (fun i => (toFun' i) = some j),
  inv := by
    intros x y
    constructor
    · intro h
      have k := (Fin.find?_eq_some_iff.mp h).1
      simp only [decide_eq_true_eq] at k
      exact k
    · intro h
      have j := toFun'Inj _ _ h
      apply Fin.find?_eq_some_iff.mpr
      constructor
      · simp only [decide_eq_true_eq]
        exact h
      · intro jk hjk
        have hjj := ne_of_lt hjk
        simp only [decide_eq_false_iff_not, ne_eq]
        intro r
        have jr := toFun'Inj _ _ r
        have kk := h_inj' _ _ _ jr j
        exact hjj kk
}

def R {i j : ℕ}:= (fun (a b : Fin i × Fin j) => (a.2 ≠ b.2 ∨ a = b) ∧ ((a.1 ≥ b.1 ∨ a.2 < b.2 ) ∨ (b.1 ≥ a.1 ∨ b.2 < a.2 )))
instance {i j : ℕ}: DecidableRel (R (i:=i) (j:=j)) := sorry
def symmR {i j : ℕ}: Symmetric (R (i:=i) (j:=j))  := by
        intro a b h
        unfold R at h
        unfold R
        constructor
        · have j := h.1
          cases j with
          | inl ha => exact Or.inl ha.symm
          | inr ha => exact Or.inr ha.symm
        · have j := h.2
          cases j with
          |inl ha => exact Or.inr ha
          |inr ha => exact Or.inl ha
def mkme {i j : ℕ} (ddlist : List (Fin i × Fin j)) : List.Pairwise R ddlist -> Fin i ≃. Fin j := fun k =>
  PEquiv.ofList ddlist ( fun i x y h₁ h₂ => by
      have reflR : ∀ a ∈ ddlist, R a a := by
        intro a h
        unfold R
        constructor
        · exact Or.inr rfl
        · exact Or.inl (Or.inl (le_refl _))
      have kk := List.Pairwise.forall_of_forall (R := R) (l := ddlist) symmR reflR k h₁ h₂
      unfold R at kk
      simp at kk
      exact kk.left
    )

def ll := (List.pwFilter R ([(0, 2), (2, 3), (8, 8)] : List (Fin 4 × Fin 10)))
def foob := mkme (i := 4) (j := 10) ll (List.pairwise_pwFilter _)
#check foob

def mktwo {i j : ℕ} (ddlist : List (Fin i × Fin j)) : List.Pairwise R ddlist -> PlanarRookDiagram i j := fun h => {
  through_strings := mkme ddlist h,
  is_planar := by
    intro a b h
    unfold mkme
    unfold PEquiv.ofList
    simp



}


#eval PEquiv.ofList (a := 3) (b := 7) [(1, 2), (0, 1)] (fun i x y h₁ h₂ => by
  cases h₁
  · cases h₂
    · rfl
    · contradiction
  · cases h₂
    · contradiction
    ·
)

-- When two diagrams are composed, they form a number of dangling strings
def danglingStringsCount {n m p : ℕ}
  (d1 : PlanarRookDiagram n m) (d2 : PlanarRookDiagram m p) : ℕ :=
  let left_stubs : Finset (Fin m) := d1.right_throughᶜ
  let right_stubs : Finset (Fin m) := d2.left_throughᶜ
  let barbells : Finset (Fin m) := left_stubs ∩ right_stubs
  barbells.card

-- Lets have an example. This is the diagram from 5 strings to 4 strings with 3 through strings
def exampleDiagram1 : PlanarRookDiagram 5 4 :=
  { through_strings := {(1, 0), (3, 2), (4, 3)} }
def exampleDiagram2 : PlanarRookDiagram 4 6 :=
  { through_strings := {(0, 1), (2, 4)} }

#eval danglingStringsCount exampleDiagram1 exampleDiagram2 = 1

-- Given a number in {0, ..., n-1}, the diagram acts on this number, taking it either to
-- nothing (if it is not in the left through set) or to the corresponding number in the right
-- through set.
def PlanarRookDiagram.act {n m : ℕ} (d : PlanarRookDiagram n m) : Fin n → Option (Fin m) :=
  fun i =>
    (d.through_strings.filter (fun p => p.1 = i)).image Prod.snd |> Finset.min

#eval exampleDiagram1.act 2

def g : Finset (Fin 5) := Finset.univ

#eval g

-- Multiplication is now simple - its the composition of action
def PlanarRookDiagram.mul {n m p : ℕ}
  (d1 : PlanarRookDiagram n m) (d2 : PlanarRookDiagram m p) : PlanarRookDiagram n p :=
  { through_strings :=
      (Finset.univ.filterMap (fun i : Fin n =>
      ((d1.act i).bind (fun j => (d2.act j).map (fun k => (i, k))))
      )
      (by
        intro a a' v b c
        have h1 : v.fst = a := by
          simp only [Option.mem_def] at b
          have hh := Option.bind_eq_some_iff.mp b
          obtain ⟨j, ha, hb⟩ := hh
          have hi := Option.map_eq_some_iff.mp hb
          obtain ⟨k, hc, hd⟩ := hi
          rw [← hd]
        have h2 : v.fst = a' := by
          simp only [Option.mem_def] at c
          have hh := Option.bind_eq_some_iff.mp c
          obtain ⟨j, ha, hb⟩ := hh
          have hi := Option.map_eq_some_iff.mp hb
          obtain ⟨k, hc, hd⟩ := hi
          rw [← hd]
        rw [← h1, ← h2]
        )
      )
  }

def PlanarRookDiagram.identity (n : ℕ) : PlanarRookDiagram n n :=
  { through_strings := Finset.univ.image (fun i : Fin n => (i, i)) }

noncomputable def HomSpaceBasis (n m : ℕ) (k : Type) [Field k] :
  Module.Basis (PlanarRookDiagram n m) k ((PlanarRookDiagram n m) → k) :=
  Pi.basisFun k (PlanarRookDiagram n m)

variable (k : Type) [Field k] (δ : k) {x y z : ℕ}

noncomputable def compBasis :
      PlanarRookDiagram x y →
      PlanarRookDiagram y z →
      ((PlanarRookDiagram x z) → k) :=
      fun dxy dyz => (δ ^ danglingStringsCount dxy dyz) • (Pi.basisFun k _ (dxy.mul dyz))

#check compBasis k

noncomputable def compLinear :
    ((PlanarRookDiagram x y) → k) →
    ((PlanarRookDiagram y z) → k) →
    ((PlanarRookDiagram x z) → k) := by
    classical
    refine ((Module.Basis.constr (HomSpaceBasis x y k) k ) ?_).toFun
    intro bxy
    refine ((Module.Basis.constr (HomSpaceBasis y z k) k) ?_).toFun
    intro byz
    exact compBasis k δ bxy byz

#check compLinear k δ

-- Now we construct a category.  The objects are natural numbers, and the morphisms
-- from n to m are linear spans of planar rook diagrams from n to m. We need to specify
-- a field and a fugicity parameter δ.

noncomputable def PlanarRookCategory (k : Type) [Field k] (δ : k) : CategoryTheory.Category ℕ where
  Hom := fun n m => (PlanarRookDiagram n m) → k
  id := fun n => fun d => if d = (PlanarRookDiagram.identity n) then 1 else 0
  comp := compLinear k δ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

def PlanarRookAlgebra (k : Type) [Field k] (δ : k) (n : ℕ) :=
  (PlanarRookCategory k δ).Hom n n
deriving Module k, AddCommMonoid

-- We can now prove that the dimension of the planar rook algebra is the sum of binom(n, k)^2
-- for k = 0 to n.

theorem PlanarRookDiagramCard (n : ℕ) :
  Fintype.card (PlanarRookDiagram n n) = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 := by
  sorry


theorem PlanarRookAlgebraDim (k : Type) [Field k] (δ : k) (n : ℕ) :
  Module.rank k (PlanarRookAlgebra k δ n) =
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 := by
  -- The planar rook algebra is just the space of functions from PlanarRookDiagram n n to k
  -- Since PlanarRookDiagram n n is finite, this has dimension equal to its cardinality
  have h1 : Module.rank k (PlanarRookAlgebra k δ n) = Fintype.card (PlanarRookDiagram n n) := by
    -- PlanarRookAlgebra k δ n = (PlanarRookDiagram n n) → k
    simp only [PlanarRookAlgebra]
    -- The rank of functions from a finite type to a field equals the cardinality
    rw [rank_pi]
    simp only [Cardinal.sum_const, Cardinal.mk_fintype]
  -- Apply the previous theorem
  rw [h1, PlanarRookDiagramCard n]
