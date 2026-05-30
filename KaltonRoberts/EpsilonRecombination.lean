/-
# Epsilon-loss recombination theorems

Bridge from arbitrary real-weighted `WeightedCollection` to the finite
uniform recombination theorem (`one_sided_recombination_uniform_core`),
with an epsilon loss in the recombination inequality.

The key idea: approximate the source weighted collection by a finite
uniform family using floor-based integer rounding. The floor construction
preserves the exact item-frequency bound (≤ α) while introducing at most
an additive `|J| · M / N` error in the average deficit, which can be made
≤ ε by choosing N large enough.

**Reference**: Lemma 3.2 in Section 3 of the companion paper.
-/
import Mathlib
import KaltonRoberts.Defs
import KaltonRoberts.Collections
import KaltonRoberts.UniformRecombination

open Finset BigOperators

set_option maxHeartbeats 1600000

noncomputable section

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Auxiliary: M is nonneg, deficit helpers -/

omit [Fintype U] in
lemma M_nonneg_of_bound (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M) : 0 ≤ M := by
  have := hM ∅; simp [hf.1] at this; exact this

omit [Fintype U] in
lemma deficit_nonneg_of_bound (f : Finset U → ℝ) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M) (S : Finset U) : 0 ≤ deficit f M S := by
  simp [deficit]; linarith [abs_le.mp (hM S)]

omit [Fintype U] in
lemma deficit_empty_eq (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ) :
    deficit f M ∅ = M := by
  simp [deficit, hf.1]

/-! ## Floor-based approximation of weighted collections -/

namespace WeightedCollection

variable (C : WeightedCollection U)

/-- Floor count for index j when building a uniform family with N total indices. -/
def floorCount (N : ℕ) (j : C.J) : ℕ :=
  ⌊(N : ℝ) * C.weight j / C.totalWeight⌋₊

omit [Fintype U] in
/-- Each floor count is at most the continuous fractional value. -/
lemma floorCount_le_frac (N : ℕ) (j : C.J) :
    (C.floorCount N j : ℝ) ≤ (N : ℝ) * C.weight j / C.totalWeight :=
  Nat.floor_le (div_nonneg (mul_nonneg (Nat.cast_nonneg N) (C.weight_nonneg j))
    (le_of_lt C.totalWeight_pos))

omit [Fintype U] in
/-
Sum of floor counts is at most N.
-/
lemma floorCount_sum_le (N : ℕ) :
    ∑ j : C.J, C.floorCount N j ≤ N := by
  -- By definition of floor count �,� we know that j, C.floorCount N j ≤ N.
  have h_floor_count_le_N : ∑ j, (C.floorCount N j : ℝ) ≤ N := by
    refine' le_trans ( Finset.sum_le_sum fun j _ => C.floorCount_le_frac N j ) _;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_div ];
    rw [ div_le_iff₀ ( C.totalWeight_pos ) ];
    rfl;
  exact_mod_cast h_floor_count_le_N

/-- The number of empty-set copies to pad up to N. -/
def emptyCount (N : ℕ) : ℕ := N - ∑ j : C.J, C.floorCount N j

omit [Fintype U] in
/-
Empty count is at most card J.
-/
lemma emptyCount_le_card (N : ℕ) :
    C.emptyCount N ≤ Fintype.card C.J := by
  -- By definition, we have $\ �sum�_{j \in J} \lfloor N \cdot w_j / W \rfloor \leq \sum_{j \in J} (N \cdot w_j / W) = N$.
  have h_sum_floor_le_N : ∑ j : C.J, C.floorCount N j ≤ N := by
    exact C.floorCount_sum_le N
  unfold WeightedCollection.emptyCount;
  -- Since $N \cdot w_j/W - \lfloor N \cdot w_j/W \rfloor < 1$, $\sum_j (N \cdot w_j/W - \lfloor N \cdot w_j/W \rfloor) < \sum_j 1 = \text{card } J$.
  have h_sum_lt_card : ∑ j : C.J, ((N : ℝ) * C.weight j / C.totalWeight - (C.floorCount N j : ℝ)) < Fintype.card C.J := by
    convert Finset.sum_lt_sum_of_nonempty _ fun j _ => show ( N : ℝ ) * C.weight j / C.totalWeight - ↑ ( C.floorCount N j ) < 1 from ?_ using 1;
    · simp +decide;
    · cases isEmpty_or_nonempty C.J <;> simp_all +decide;
      exact absurd ( C.total_pos ) ( by simp +decide [ Finset.sum_eq_zero ] );
    · exact sub_lt_iff_lt_add'.mpr ( Nat.lt_floor_add_one _ );
  rw [ ← @Nat.cast_le ℝ ];
  convert h_sum_lt_card.le using 1 ; rw [ Nat.cast_sub h_sum_floor_le_N ] ; simp +decide ; ring_nf;
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc ];
  simp +decide [ WeightedCollection.totalWeight, ne_of_gt C.total_pos ]

/-- Approximate index type: sigma type for set copies plus empty copies. -/
abbrev ApproxIdx (N : ℕ) : Type _ :=
  (Σ j : C.J, Fin (C.floorCount N j)) ⊕ Fin (C.emptyCount N)

/-- The approximation family: sigma part maps to sets, empty part maps to ∅. -/
def approxFam (N : ℕ) : C.ApproxIdx N → Finset U
  | .inl ⟨j, _⟩ => C.sets j
  | .inr _ => ∅

/-
Cardinality of ApproxIdx equals N when floor sum ≤ N.
-/
omit [Fintype U] in
lemma approxIdx_card (N : ℕ) (h : ∑ j : C.J, C.floorCount N j ≤ N) :
    Fintype.card (C.ApproxIdx N) = N := by
  simp +decide [ WeightedCollection.ApproxIdx ];
  exact Nat.add_sub_of_le h

/-
Count of i-containing indices in the approximation family.
-/
omit [Fintype U] in
lemma approx_count (N : ℕ) (i : U) :
    (Finset.univ.filter (fun idx : C.ApproxIdx N => i ∈ C.approxFam N idx)).card =
      ∑ j ∈ Finset.univ.filter (fun j : C.J => i ∈ C.sets j), C.floorCount N j := by
  rw [ Finset.card_filter, Finset.sum_ite ];
  rw [ show ( Finset.univ.filter fun x : C.ApproxIdx N => i ∈ C.approxFam N x ) = Finset.biUnion ( Finset.univ.filter fun j : C.J => i ∈ C.sets j ) fun j => Finset.image ( fun k : Fin ( C.floorCount N j ) => Sum.inl ⟨ j, k ⟩ ) ( Finset.univ : Finset ( Fin ( C.floorCount N j ) ) ) from ?_, Finset.sum_biUnion ];
  · simp +decide [ Finset.card_image_of_injective, Function.Injective ];
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
  · ext x; cases x <;> simp +decide [ WeightedCollection.approxFam ] ;
    grind

omit [Fintype U] in
/-
Frequency in the approximation is at most the weighted item frequency.
-/
lemma approx_freq_le (N : ℕ) (i : U)
    (hle : ∑ j : C.J, C.floorCount N j ≤ N) (hN : 0 < N) :
    ((Finset.univ.filter (fun idx : C.ApproxIdx N => i ∈ C.approxFam N idx)).card : ℝ) /
      (Fintype.card (C.ApproxIdx N) : ℝ) ≤ C.itemFreq i := by
  -- Using the lemma that bounds the sum of floor counts, we can show that the sum of floor counts is at most the weighted item frequency.
  have h_sum_floorCount_le_weighted_itemFreq : ∑ j ∈ Finset.univ.filter (fun j => i ∈ C.sets j), C.floorCount N j ≤ (N : ℝ) * (∑ j ∈ Finset.univ.filter (fun j => i ∈ C.sets j), C.weight j) / C.totalWeight := by
    push_cast [ Finset.mul_sum _ _ _, Finset.sum_div ];
    exact Finset.sum_le_sum fun j hj => C.floorCount_le_frac N j;
  convert div_le_div_of_nonneg_right h_sum_floorCount_le_weighted_itemFreq ( Nat.cast_nonneg N ) using 1;
  · rw [ ← approx_count, approxIdx_card ];
    exact hle;
  · rw [ eq_div_iff ( by positivity ), mul_comm ] ; unfold WeightedCollection.itemFreq ; simp +decide [ Finset.sum_ite ] ; ring;

/-
Sum of deficits over the approximation family decomposes into set and empty parts.
-/
omit [Fintype U] in
lemma approx_deficit_sum (N : ℕ) (f : Finset U → ℝ) (M : ℝ) :
    ∑ idx : C.ApproxIdx N, deficit f M (C.approxFam N idx) =
      (∑ j : C.J, (C.floorCount N j : ℝ) * deficit f M (C.sets j)) +
      (C.emptyCount N : ℝ) * deficit f M ∅ := by
  unfold WeightedCollection.approxFam;
  simp +decide [ Fintype.sum_sigma ]

omit [Fintype U] in
/-
Average deficit of the approximation is at most D + card(J) · M / N.
-/
lemma approx_avgDeficit_le (N : ℕ) (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (D : ℝ) (hdeficit : C.avgDeficit f M ≤ D)
    (hle : ∑ j : C.J, C.floorCount N j ≤ N) (hN : 0 < N) :
    (∑ idx : C.ApproxIdx N, deficit f M (C.approxFam N idx)) /
      (Fintype.card (C.ApproxIdx N) : ℝ) ≤
      D + (Fintype.card C.J : ℝ) * M / (N : ℝ) := by
  rw [ add_div', div_le_div_iff₀ ] <;> try positivity;
  · rw [ WeightedCollection.approx_deficit_sum ];
    -- Applying the definition of `avgDeficit` and the hypothesis `hdeficit`.
    have h_avg_deficit : (∑ j : C.J, (C.floorCount N j : ℝ) * deficit f M (C.sets j)) ≤ (D * N) := by
      refine' le_trans _ ( mul_le_mul_of_nonneg_right hdeficit ( Nat.cast_nonneg _ ) );
      rw [ WeightedCollection.avgDeficit, div_mul_eq_mul_div, le_div_iff₀ ];
      · have h_floorCount_le_frac : ∀ j : C.J, (C.floorCount N j : ℝ) * C.totalWeight ≤ (N : ℝ) * C.weight j := by
          intro j
          have h_floorCount_le_frac : (C.floorCount N j : ℝ) ≤ (N : ℝ) * C.weight j / C.totalWeight := by
            exact Nat.floor_le ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( C.weight_nonneg j ) ) ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) );
          rwa [ le_div_iff₀ ( C.totalWeight_pos ) ] at h_floorCount_le_frac;
        simpa only [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ] using Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ( h_floorCount_le_frac j ) ( deficit_nonneg_of_bound f M hM ( C.sets j ) );
      · exact C.total_pos;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( add_le_add h_avg_deficit ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( C.emptyCount_le_card N ) ) ( deficit_nonneg_of_bound f M hM ∅ ) ) ) ( Nat.cast_nonneg _ ) ) _;
    rw [ deficit_empty_eq f hf M ] ; rw [ C.approxIdx_card N hle ] ;
  · exact Nat.cast_pos.mpr ( by rw [ C.approxIdx_card N hle ] ; positivity )

end WeightedCollection

/-! ## Epsilon one-sided recombination -/

omit [Fintype U] in
/-- **Lemma 3.2 (ε-version)** One-sided recombination with epsilon loss.
Bridges arbitrary real-weighted collections to the finite uniform theorem. -/
theorem one_sided_recombination_core_eps
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (α_val : ℚ) (r_val : ℕ) (θ_val : ℚ)
    (hθ : 0 < (θ_val : ℝ)) (hθ1 : (θ_val : ℝ) < 1)
    (hexp : StrongExpandersExist α_val r_val θ_val)
    (hr : 0 < r_val)
    (_hα : 0 < (α_val : ℝ))
    (C : WeightedCollection U)
    (hfreq : ∀ i : U, C.itemFreq i ≤ (α_val : ℝ))
    (D : ℝ) (hD : 0 ≤ D)
    (hdeficit : C.avgDeficit f M ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (C' : WeightedCollection U) (D' : ℝ), 0 ≤ D' ∧
      (∀ i : U, C'.itemFreq i ≤ (α_val : ℝ) / (θ_val : ℝ)) ∧
      C'.avgDeficit f M ≤ D' ∧
      (1 - (θ_val : ℝ)) * M ≤ D + ε - (θ_val : ℝ) * D' +
        2 * (r_val : ℝ) - 1 - (θ_val : ℝ) := by
  -- Choose N large enough so card(J) * M / N ≤ ε
  set N := max 1 (⌈(Fintype.card C.J : ℝ) * M / ε⌉₊ + 1) with hN_def
  have hle := C.floorCount_sum_le N
  have hN : (0 : ℕ) < N := by omega
  have hI : 0 < Fintype.card (C.ApproxIdx N) := by
    rw [C.approxIdx_card N hle]; exact hN
  -- Frequency bound: approx frequency ≤ itemFreq ≤ α_val
  have hfreq_approx : ∀ i : U,
      ((Finset.univ.filter (fun idx => i ∈ C.approxFam N idx)).card : ℝ) /
        (Fintype.card (C.ApproxIdx N) : ℝ) ≤ (α_val : ℝ) :=
    fun i => le_trans (C.approx_freq_le N i hle hN) (hfreq i)
  -- N large enough: card(J) * M / N ≤ ε
  have hM_nn : (0 : ℝ) ≤ M := M_nonneg_of_bound f hf M hM
  have hN_large : (Fintype.card C.J : ℝ) * M / (N : ℝ) ≤ ε := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
    have h1 : (Fintype.card C.J : ℝ) * M ≤ (⌈(Fintype.card C.J : ℝ) * M / ε⌉₊ : ℝ) * ε := by
      rw [← div_le_iff₀ hε]; exact Nat.le_ceil _
    have h2 : (⌈(Fintype.card C.J : ℝ) * M / ε⌉₊ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast show ⌈(Fintype.card C.J : ℝ) * M / ε⌉₊ ≤ N from by omega
    linarith [mul_le_mul_of_nonneg_right h2 (le_of_lt hε)]
  -- Average deficit bound
  have havg : (∑ idx : C.ApproxIdx N, deficit f M (C.approxFam N idx)) /
      (Fintype.card (C.ApproxIdx N) : ℝ) ≤ D + ε :=
    le_trans (C.approx_avgDeficit_le N f hf M hM D hdeficit hle hN) (by linarith)
  -- Apply the finite-uniform recombination theorem
  obtain ⟨C', D', hD'nn, hC'freq, hC'def, hineq⟩ :=
    one_sided_recombination_uniform_core f hf M hM α_val r_val θ_val hθ hθ1 hexp hr hI
      (C.approxFam N) hfreq_approx (D + ε) (by linarith) havg
  exact ⟨C', D', hD'nn, hC'freq, hC'def, by linarith⟩

/-! ## Epsilon two-sided recombination -/

omit [Fintype U] in
private lemma IsApproxAdditive_neg (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) :
    IsApproxAdditive (fun S => -f S) 1 := by
  constructor
  · simp [hf.1]
  · intro A B hAB
    rw [show -f A + -f B - -f (A ∪ B) = -(f A + f B - f (A ∪ B)) by ring, abs_neg]
    exact hf.2 A B hAB

omit [Fintype U] in
/-- **Lemma 3.3 (ε-version)** Two-sided recombination with epsilon loss.
Applies epsilon one-sided to deficit side and surplus side, then averages. -/
theorem two_sided_recombination_core_eps
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (α_val : ℚ) (r_val : ℕ) (θ_val : ℚ)
    (hθ : 0 < (θ_val : ℝ)) (hθ1 : (θ_val : ℝ) < 1)
    (hexp : StrongExpandersExist α_val r_val θ_val)
    (hr : 0 < r_val)
    (hα : 0 < (α_val : ℝ))
    (C_def : WeightedCollection U) (C_sur : WeightedCollection U)
    (hfreq_def : ∀ i : U, C_def.itemFreq i ≤ (α_val : ℝ))
    (hfreq_sur : ∀ i : U, C_sur.itemFreq i ≤ (α_val : ℝ))
    (D S_val : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S_val)
    (hdeficit : C_def.avgDeficit f M ≤ D)
    (hsurplus : C_sur.avgSurplus f M ≤ S_val)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (C'_def C'_sur : WeightedCollection U) (D' S' : ℝ), 0 ≤ D' ∧ 0 ≤ S' ∧
      (∀ i : U, C'_def.itemFreq i ≤ (α_val : ℝ) / (θ_val : ℝ)) ∧
      (∀ i : U, C'_sur.itemFreq i ≤ (α_val : ℝ) / (θ_val : ℝ)) ∧
      C'_def.avgDeficit f M ≤ D' ∧
      C'_sur.avgSurplus f M ≤ S' ∧
      (1 - (θ_val : ℝ)) * M ≤ (D + S_val) / 2 + ε -
        (θ_val : ℝ) * ((D' + S') / 2) +
        2 * (r_val : ℝ) - 1 - (θ_val : ℝ) := by
  -- Apply epsilon one-sided to deficit
  obtain ⟨C'_def, D', hD'nn, hC'def_freq, hC'def_avg, hineq_def⟩ :=
    one_sided_recombination_core_eps f hf M hM α_val r_val θ_val hθ hθ1 hexp hr hα
      C_def hfreq_def D hD hdeficit ε hε
  -- Apply epsilon one-sided to surplus (= deficit of -f)
  have hf_neg := IsApproxAdditive_neg f hf
  have hM_neg : ∀ S : Finset U, |(fun S => -f S) S| ≤ M :=
    fun S => by simp [abs_neg]; exact hM S
  have hsur_as_def : C_sur.avgDeficit (fun S => -f S) M ≤ S_val := by
    simp [WeightedCollection.avgDeficit, WeightedCollection.avgSurplus, deficit, surplus] at *
    exact hsurplus
  obtain ⟨C'_sur, S', hS'nn, hC'sur_freq, hC'sur_avg_neg, hineq_sur⟩ :=
    one_sided_recombination_core_eps (fun S => -f S) hf_neg M hM_neg α_val r_val θ_val
      hθ hθ1 hexp hr hα C_sur hfreq_sur S_val hS hsur_as_def ε hε
  -- Convert avgDeficit(-f) to avgSurplus(f)
  have h_convert : C'_sur.avgDeficit (fun S => -f S) M = C'_sur.avgSurplus f M := by
    simp [WeightedCollection.avgDeficit, WeightedCollection.avgSurplus, deficit, surplus]
  refine ⟨C'_def, C'_sur, D', S', hD'nn, hS'nn, hC'def_freq, hC'sur_freq,
    hC'def_avg, h_convert ▸ hC'sur_avg_neg, ?_⟩
  -- Average the two one-sided inequalities
  linarith

end
