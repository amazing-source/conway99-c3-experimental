import C3formal.FixLemma
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement

/-!
# Proofs of the statements of `Challenge.lean`

Same names and same statements as `Challenge.lean`; `lake comparator` checks that the statements
are identical. Everything follows from `C3.no_order3` (`C3formal/FixLemma.lean`):

* the group forms: `σ ^ 3 = 1` is `σ (σ (σ v)) = v` for every `v`, then Cauchy's theorem;
* the elementary form: a symmetric Boolean matrix with zero diagonal is a `SimpleGraph`, the
  counting hypotheses are `IsSRGWith`, and a map with `σ ∘ σ ∘ σ = id` preserving adjacency is an
  automorphism;
* the sanity checks: the 3 × 3 rook's graph and the shift of its rows, facts checked by `decide`.
-/

namespace Conway99

theorem srg99_aut_cube {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h3 : ∀ v, σ (σ (σ v)) = v) :
    ∀ v, σ v = v := by
  classical
  exact C3.no_order3 G hG σ h3

/-- For an automorphism, `σ ^ 3` is `σ ∘ σ ∘ σ`. -/
theorem pow_three_apply {V : Type*} {G : SimpleGraph V} (σ : G ≃g G) (v : V) :
    (σ ^ 3) v = σ (σ (σ v)) := by
  rw [pow_three, RelIso.mul_apply, RelIso.mul_apply]

theorem srg99_no_orderOf_three {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) : orderOf σ ≠ 3 := by
  intro h
  have h3 : σ ^ 3 = 1 := h ▸ pow_orderOf_eq_one σ
  have hid : σ = 1 := RelIso.ext fun v => by
    rw [RelIso.one_apply]
    exact srg99_aut_cube G hG σ (fun w => by rw [← pow_three_apply, h3, RelIso.one_apply]) v
  rw [hid, orderOf_one] at h
  omega

/-- The automorphisms of a finite graph form a finite type. -/
theorem finite_aut {V : Type*} [Finite V] (G : SimpleGraph V) : Finite (G ≃g G) :=
  Finite.of_injective _ RelIso.toEquiv_injective

theorem srg99_three_not_dvd_card_aut {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) : ¬ 3 ∣ Nat.card (G ≃g G) := by
  intro hdvd
  have := finite_aut G
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact srg99_no_orderOf_three G hG σ hσ

/-! ### From a Boolean adjacency matrix to Mathlib's graphs -/

/-- The simple graph whose adjacency matrix is `adj`. -/
def graphOf {n : ℕ} (adj : Fin n → Fin n → Bool) (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false) : SimpleGraph (Fin n) where
  Adj i j := adj i j = true
  symm := ⟨fun i j h => (h_symm j i).trans h⟩
  loopless := ⟨fun i h => by rw [h_loop i] at h; exact Bool.false_ne_true h⟩

instance {n : ℕ} (adj : Fin n → Fin n → Bool) (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false) : DecidableRel (graphOf adj h_symm h_loop).Adj :=
  fun i j => inferInstanceAs (Decidable (adj i j = true))

/-- Counting with `List.countP` over `[0, …, n - 1]` is the cardinality of a `Finset` filter. -/
theorem card_filter_eq_countP {n : ℕ} (p : Fin n → Bool) :
    (Finset.univ.filter (fun i => p i = true)).card = (List.finRange n).countP p := by
  rw [Fin.univ_def, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter]

/-- The counting hypotheses of `srg99_elementary` say that `graphOf adj` is strongly regular. -/
theorem graphOf_isSRGWith {n k l m : ℕ} (adj : Fin n → Fin n → Bool)
    (h_symm : ∀ i j, adj i j = adj j i) (h_loop : ∀ i, adj i i = false)
    (h_deg : ∀ i, (List.finRange n).countP (fun j => adj i j) = k)
    (h_adj : ∀ i j, adj i j = true →
      (List.finRange n).countP (fun x => adj i x && adj j x) = l)
    (h_nonadj : ∀ i j, i ≠ j → adj i j = false →
      (List.finRange n).countP (fun x => adj i x && adj j x) = m) :
    (graphOf adj h_symm h_loop).IsSRGWith n k l m where
  card := Fintype.card_fin n
  regular i := by
    rw [← h_deg i, ← card_filter_eq_countP, SimpleGraph.degree,
      SimpleGraph.neighborFinset_eq_filter]
    rfl
  of_adj i j h := by
    rw [← h_adj i j h, ← card_filter_eq_countP, ← Set.toFinset_card]
    congr 1
    ext x
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true]
    exact Iff.rfl
  of_not_adj := by
    intro i j hne h
    have h' : adj i j = false := by simpa [graphOf] using h
    rw [← h_nonadj i j hne h', ← card_filter_eq_countP, ← Set.toFinset_card]
    congr 1
    ext x
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true]
    exact Iff.rfl

/-- A map with `σ ∘ σ ∘ σ = id` that preserves `adj` is an automorphism of `graphOf adj`. -/
def autOf {n : ℕ} {adj : Fin n → Fin n → Bool} {h_symm : ∀ i j, adj i j = adj j i}
    {h_loop : ∀ i, adj i i = false} (σ : Fin n → Fin n)
    (h_aut : ∀ i j, adj (σ i) (σ j) = adj i j) (h_cube : ∀ i, σ (σ (σ i)) = i) :
    graphOf adj h_symm h_loop ≃g graphOf adj h_symm h_loop where
  toFun := σ
  invFun i := σ (σ i)
  left_inv := h_cube
  right_inv := h_cube
  map_rel_iff' := by
    intro a b
    simp only [graphOf, Equiv.coe_fn_mk, h_aut]

theorem srg99_elementary (adj : Fin 99 → Fin 99 → Bool)
    (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false)
    (h_deg : ∀ i, (List.finRange 99).countP (fun j => adj i j) = 14)
    (h_adj : ∀ i j, adj i j = true →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 1)
    (h_nonadj : ∀ i j, i ≠ j → adj i j = false →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 2)
    (σ : Fin 99 → Fin 99)
    (h_aut : ∀ i j, adj (σ i) (σ j) = adj i j)
    (h_cube : ∀ i, σ (σ (σ i)) = i) :
    ∀ i, σ i = i :=
  srg99_aut_cube (graphOf adj h_symm h_loop)
    (graphOf_isSRGWith adj h_symm h_loop h_deg h_adj h_nonadj) (autOf σ h_aut h_cube) h_cube

/-! ### Sanity checks: the 3 × 3 rook's graph -/

/-- The 3 × 3 rook's graph: cells `0, …, 8` of a 3 × 3 board, adjacent when they share a row or a
column. It is an srg(9, 4, 1, 2). -/
def rook3 (i j : Fin 9) : Bool :=
  i != j && (i.val / 3 == j.val / 3 || i.val % 3 == j.val % 3)

/-- Moves every cell one row down (cyclically): an automorphism of order 3 of the rook's graph. -/
def shift3 (i : Fin 9) : Fin 9 :=
  ⟨(i.val + 3) % 9, Nat.mod_lt _ (by decide)⟩

theorem rook3_symm : ∀ i j, rook3 i j = rook3 j i := by decide
theorem rook3_loop : ∀ i, rook3 i i = false := by decide
theorem rook3_deg : ∀ i, (List.finRange 9).countP (fun j => rook3 i j) = 4 := by decide
theorem rook3_adj : ∀ i j, rook3 i j = true →
    (List.finRange 9).countP (fun k => rook3 i k && rook3 j k) = 1 := by decide
theorem rook3_nonadj : ∀ i j, i ≠ j → rook3 i j = false →
    (List.finRange 9).countP (fun k => rook3 i k && rook3 j k) = 2 := by decide
theorem shift3_aut : ∀ i j, rook3 (shift3 i) (shift3 j) = rook3 i j := by decide
theorem shift3_cube : ∀ i, shift3 (shift3 (shift3 i)) = i := by decide
theorem shift3_ne : shift3 0 ≠ 0 := by decide

/-- The rook's graph as a `SimpleGraph`. -/
def rookGraph : SimpleGraph (Fin 9) := graphOf rook3 rook3_symm rook3_loop

instance : DecidableRel rookGraph.Adj :=
  inferInstanceAs (DecidableRel (graphOf rook3 rook3_symm rook3_loop).Adj)

theorem rookGraph_srg : rookGraph.IsSRGWith 9 4 1 2 :=
  graphOf_isSRGWith rook3 rook3_symm rook3_loop rook3_deg rook3_adj rook3_nonadj

/-- The row shift as an automorphism of the rook's graph. -/
def shiftAut : rookGraph ≃g rookGraph := autOf shift3 shift3_aut shift3_cube

theorem srg9_aut_cube_false :
    ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith 9 4 1 2 → ∀ σ : G ≃g G, (∀ v, σ (σ (σ v)) = v) → ∀ v, σ v = v :=
  fun h => shift3_ne (h rookGraph rookGraph_srg shiftAut shift3_cube 0)

theorem srg9_group_forms_false :
    ∃ (G : SimpleGraph (Fin 9)) (_ : DecidableRel G.Adj), G.IsSRGWith 9 4 1 2 ∧
      (∃ σ : G ≃g G, orderOf σ = 3) ∧ 3 ∣ Nat.card (G ≃g G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf shiftAut = 3 := by
    apply orderOf_eq_prime
    · exact RelIso.ext fun i => by rw [pow_three_apply, RelIso.one_apply]; exact shift3_cube i
    · intro h
      apply shift3_ne
      exact congrArg (fun τ : rookGraph ≃g rookGraph => τ 0) h
  have := finite_aut rookGraph
  exact ⟨rookGraph, inferInstance, rookGraph_srg, ⟨shiftAut, hσ⟩, hσ ▸ orderOf_dvd_natCard shiftAut⟩

theorem srg9_elementary_false :
    ¬ ∀ (adj : Fin 9 → Fin 9 → Bool),
      (∀ i j, adj i j = adj j i) →
      (∀ i, adj i i = false) →
      (∀ i, (List.finRange 9).countP (fun j => adj i j) = 4) →
      (∀ i j, adj i j = true → (List.finRange 9).countP (fun k => adj i k && adj j k) = 1) →
      (∀ i j, i ≠ j → adj i j = false →
        (List.finRange 9).countP (fun k => adj i k && adj j k) = 2) →
      ∀ σ : Fin 9 → Fin 9, (∀ i j, adj (σ i) (σ j) = adj i j) → (∀ i, σ (σ (σ i)) = i) →
        ∀ i, σ i = i :=
  fun h => shift3_ne (h rook3 rook3_symm rook3_loop rook3_deg rook3_adj rook3_nonadj shift3
    shift3_aut shift3_cube 0)

end Conway99
