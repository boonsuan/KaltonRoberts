/-
# Product and mixed intersection collections

This file constructs product intersection collections and mixed intersection
collections, proving the frequency and deficit bounds needed for Corollary 3.1.

**Reference**: Corollary 3.1 in Section 3 of the companion paper.
-/
import Mathlib
import KaltonRoberts.Defs
import KaltonRoberts.Collections
import KaltonRoberts.Lemmas

open Finset BigOperators

set_option maxHeartbeats 800000

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Helper: sum of products = (sum)^ℓ -/

private lemma sum_prod_eq_pow {J : Type*} [DecidableEq J] [Fintype J]
    (w : J → ℝ) (ℓ : ℕ) :
    ∑ x : Fin ℓ → J, ∏ k : Fin ℓ, w (x k) = (∑ j : J, w j) ^ ℓ := by
  have h := @Finset.prod_univ_sum (Fin ℓ) ℝ _ _ (fun _ => J) _ (fun _ => Finset.univ) (fun _ j => w j)
  simp [Fintype.piFinset_univ] at h
  linarith

/-! ## Two-set deficit intersection inequality -/

omit [Fintype U] in
/-- Deficit of an intersection is at most the sum of deficits plus 2. -/
theorem deficit_inter_le (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (A B : Finset U) :
    deficit f M (A ∩ B) ≤ deficit f M A + deficit f M B + 2 := by
  unfold deficit;
  have h_mod : |f A + f B - f (A ∪ B) - f (A ∩ B)| ≤ 2 := by
    convert approx_modularity f hf A B using 1;
  grind

/-! ## Finite intersection deficit bound -/

/-- The intersection of a family indexed by `Fin ℓ`. -/
noncomputable def finsetInter (A : Fin ℓ → Finset U) : Finset U :=
  Finset.univ.inf A

/-- Deficit of ℓ-fold intersection is at most sum of deficits + 2*(ℓ-1). -/
theorem deficit_finsetInter_le (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : Fin ℓ → Finset U) :
    deficit f M (finsetInter A) ≤
      ∑ k : Fin ℓ, deficit f M (A k) + 2 * ((ℓ : ℝ) - 1) := by
  induction' hℓ with ℓ hℓ ih;
  · simp +decide [ finsetInter ];
  · simp +decide [ Fin.sum_univ_castSucc, finsetInter ] at *;
    rw [ show ( Finset.univ.inf A : Finset U ) = ( Finset.univ.inf ( fun k : Fin ℓ => A ( Fin.castSucc k ) ) ) ∩ A ( Fin.last ℓ ) from ?_ ];
    · linarith [ deficit_inter_le f hf M hM ( Finset.univ.inf fun k : Fin ℓ => A ( Fin.castSucc k ) ) ( A ( Fin.last ℓ ) ), ih fun k => A ( Fin.castSucc k ) ];
    · ext x; simp +decide [ Finset.mem_inf, Finset.mem_inter ] ;
      exact ⟨ fun h => ⟨ fun i => h _, h _ ⟩, fun h i => by cases i using Fin.lastCases <;> simp +decide [ * ] ⟩

/-! ## Product intersection collection -/

/-- The ℓ-fold product intersection collection. -/
noncomputable def WeightedCollection.productInter
    (C : WeightedCollection U) (ℓ : ℕ) (_ : 1 ≤ ℓ) :
    WeightedCollection U where
  J := Fin ℓ → C.J
  sets := fun x => finsetInter (fun k => C.sets (x k))
  weight := fun x => ∏ k : Fin ℓ, C.weight (x k)
  weight_nonneg := fun x => Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
  total_pos := by
    rw [sum_prod_eq_pow]
    exact pow_pos C.totalWeight_pos ℓ

/-- Total weight of the product collection equals C.totalWeight^ℓ. -/
lemma WeightedCollection.productInter_totalWeight
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (C.productInter ℓ hℓ).totalWeight = C.totalWeight ^ ℓ := by
  exact sum_prod_eq_pow C.weight ℓ

/-- Item frequency of the product collection is at most (itemFreq C i)^ℓ. -/
lemma WeightedCollection.productInter_itemFreq
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : U) :
    (C.productInter ℓ hℓ).itemFreq i ≤ (C.itemFreq i) ^ ℓ := by
  unfold WeightedCollection.itemFreq;
  rw [ div_pow, WeightedCollection.productInter_totalWeight ];
  rw [ ← sum_prod_eq_pow ];
  simp +decide [ WeightedCollection.productInter ];
  gcongr;
  · exact pow_nonneg ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _;
  · split_ifs <;> simp_all +decide [ Finset.prod_ite ];
    · simp_all +decide [ Finset.mem_inf, finsetInter ];
    · exact mul_nonneg ( Finset.prod_nonneg fun _ _ => C.weight_nonneg _ ) ( pow_nonneg ( by norm_num ) _ )

/-- Average deficit of the product collection. -/
lemma WeightedCollection.productInter_avgDeficit
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (D : ℝ) (_hD : 0 ≤ D) (hdeficit : C.avgDeficit f M ≤ D) :
    (C.productInter ℓ hℓ).avgDeficit f M ≤
      ℓ * D + 2 * ((ℓ : ℝ) - 1) := by
  refine' le_trans _ ( add_le_add ( mul_le_mul_of_nonneg_left hdeficit ( Nat.cast_nonneg _ ) ) le_rfl );
  unfold WeightedCollection.avgDeficit; norm_num [ WeightedCollection.productInter_totalWeight, WeightedCollection.productInter ] ;
  have h_prod : (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * deficit f M (finsetInter (fun k => C.sets (x k)))) ≤
    (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * (∑ k, deficit f M (C.sets (x k)) + 2 * (ℓ - 1))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left (deficit_finsetInter_le f hf M hM ℓ hℓ (fun k => C.sets (x k))) (Finset.prod_nonneg (fun k _ => C.weight_nonneg (x k)));
  have h_prod : (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * (∑ k, deficit f M (C.sets (x k)))) = ℓ * C.totalWeight ^ (ℓ - 1) * (∑ j : C.J, C.weight j * deficit f M (C.sets j)) := by
    have h_prod : ∀ k : Fin ℓ, (∑ x : Fin ℓ → C.J, (∏ j, C.weight (x j)) * deficit f M (C.sets (x k))) = C.totalWeight ^ (ℓ - 1) * (∑ j : C.J, C.weight j * deficit f M (C.sets j)) := by
      intro k
      have h_prod : (∑ x : Fin ℓ → C.J, (∏ j, C.weight (x j)) * deficit f M (C.sets (x k))) = (∏ j : Fin ℓ, (∑ x : C.J, C.weight x * (if j = k then deficit f M (C.sets x) else 1))) := by
        simp +decide only [prod_sum];
        refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide;
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), funext fun i => funext fun _ => rfl ⟩;
        · simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
          exact fun x => by rw [ mul_right_comm, ← Finset.mul_prod_erase _ _ ( Finset.mem_univ k ) ] ;
      simp_all +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
      exact mul_comm _ _;
    convert Finset.sum_congr rfl fun k ( hk : k ∈ Finset.univ ) => h_prod k using 1;
    · rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
    · simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ];
  have h_prod : (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * (2 * (ℓ - 1))) = 2 * (ℓ - 1) * C.totalWeight ^ ℓ := by
    rw [ ← Finset.sum_mul _ _ _, sum_prod_eq_pow ] ; ring_nf;
    rw [ show C.totalWeight = ∑ j : C.J, C.weight j from rfl ] ; ring;
  have h_prod : (∑ x : Fin ℓ → C.J, (∏ k, C.weight (x k)) * (∑ k, deficit f M (C.sets (x k)) + 2 * (ℓ - 1))) = ℓ * C.totalWeight ^ (ℓ - 1) * (∑ j : C.J, C.weight j * deficit f M (C.sets j)) + 2 * (ℓ - 1) * C.totalWeight ^ ℓ := by
    simp_all +decide [ mul_add, Finset.sum_add_distrib ];
  convert div_le_div_of_nonneg_right ( le_trans ‹_› h_prod.le ) ( pow_nonneg ( le_of_lt C.totalWeight_pos ) ℓ ) using 1;
  · congr! 1;
    convert WeightedCollection.productInter_totalWeight C ℓ hℓ using 1;
  · field_simp;
    rw [ div_add', div_eq_div_iff ] <;> norm_num [ pow_succ, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < C.totalWeight from C.totalWeight_pos ) ];
    cases ℓ <;> simp +decide [ pow_succ' ] ; ring;
    ring

/-! ## Mixed intersection collection

The key insight for the mixed collection: to make the convex combination
work with unnormalized collections, we multiply the ℓ-branch by TW^(ℓ+1)
and the (ℓ+1)-branch by TW^ℓ, equalizing the denominators.
The total weight becomes TW^(2ℓ+1).
-/

/-- The mixed intersection collection: weighted mixture of ℓ-fold and (ℓ+1)-fold
product intersections, with balanced weights so that frequency bounds work
correctly for unnormalized collections. -/
noncomputable def WeightedCollection.mixedInter
    (C : WeightedCollection U) (ℓ : ℕ) (_hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    WeightedCollection U where
  J := (Fin ℓ → C.J) ⊕ (Fin (ℓ + 1) → C.J)
  sets := fun j => match j with
    | Sum.inl x => finsetInter (fun k => C.sets (x k))
    | Sum.inr x => finsetInter (fun k => C.sets (x k))
  weight := fun j => match j with
    | Sum.inl x => (1 - τ) * C.totalWeight ^ (ℓ + 1) * (∏ k : Fin ℓ, C.weight (x k))
    | Sum.inr x => τ * C.totalWeight ^ ℓ * (∏ k : Fin (ℓ + 1), C.weight (x k))
  weight_nonneg := fun j => by
    cases j with
    | inl x =>
      apply mul_nonneg (mul_nonneg (by linarith) (pow_nonneg C.totalWeight_pos.le _))
      exact Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
    | inr x =>
      apply mul_nonneg (mul_nonneg hτ (pow_nonneg C.totalWeight_pos.le _))
      exact Finset.prod_nonneg fun k _ => C.weight_nonneg (x k)
  total_pos := by
    simp only [Fintype.sum_sum_type]
    rw [← Finset.mul_sum, ← Finset.mul_sum,
        sum_prod_eq_pow C.weight ℓ, sum_prod_eq_pow C.weight (ℓ + 1)]
    have hpos : (0 : ℝ) < ∑ j : C.J, C.weight j := C.totalWeight_pos
    have h1 := pow_pos hpos ℓ
    have h2 := pow_pos hpos (ℓ + 1)
    have htw : C.totalWeight = ∑ j : C.J, C.weight j := rfl
    rw [htw]
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) (mul_nonneg h2.le h1.le),
              mul_nonneg hτ (mul_nonneg h1.le h2.le)]

/-- Total weight of the mixed collection. -/
lemma WeightedCollection.mixedInter_totalWeight
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (C.mixedInter ℓ hℓ τ hτ hτ1).totalWeight =
      C.totalWeight ^ (2 * ℓ + 1) := by
  simp only [totalWeight, mixedInter, Fintype.sum_sum_type]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
      sum_prod_eq_pow C.weight ℓ, sum_prod_eq_pow C.weight (ℓ + 1)]
  set S := ∑ j : C.J, C.weight j
  ring

/-
Item frequency of the mixed collection.
-/
lemma WeightedCollection.mixedInter_itemFreq_le
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (t : ℝ) (_ht : 0 ≤ t) (_ht1 : t ≤ 1)
    (hfreq : ∀ i : U, C.itemFreq i ≤ t) (i : U) :
    (C.mixedInter ℓ hℓ τ hτ hτ1).itemFreq i ≤
      (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1) := by
  rw [ WeightedCollection.itemFreq ];
  rw [ div_le_iff₀ ( by exact ( by { exact ( WeightedCollection.mixedInter_totalWeight C ℓ hℓ τ hτ hτ1 ▸ pow_pos C.totalWeight_pos _ ) } ) ) ];
  have h_mixed_freq : (∑ x : Fin ℓ → C.J, (∏ k : Fin ℓ, C.weight (x k)) * (if i ∈ finsetInter (fun k => C.sets (x k)) then 1 else 0)) ≤ t ^ ℓ * (∑ j : C.J, C.weight j) ^ ℓ ∧ (∑ x : Fin (ℓ + 1) → C.J, (∏ k : Fin (ℓ + 1), C.weight (x k)) * (if i ∈ finsetInter (fun k => C.sets (x k)) then 1 else 0)) ≤ t ^ (ℓ + 1) * (∑ j : C.J, C.weight j) ^ (ℓ + 1) := by
    have h_mixed_freq : ∀ k : ℕ, 1 ≤ k → (∑ x : Fin k → C.J, (∏ j : Fin k, C.weight (x j)) * (if i ∈ finsetInter (fun j => C.sets (x j)) then 1 else 0)) ≤ t ^ k * (∑ j : C.J, C.weight j) ^ k := by
      intro k hk
      have h_mixed_freq : (∑ x : Fin k → C.J, (∏ j : Fin k, C.weight (x j)) * (if i ∈ finsetInter (fun j => C.sets (x j)) then 1 else 0)) ≤ (∑ j : C.J, C.weight j * (if i ∈ C.sets j then 1 else 0)) ^ k := by
        rw [ ← sum_prod_eq_pow ];
        refine' Finset.sum_le_sum fun x _ => _;
        split_ifs <;> simp_all +decide [ Finset.prod_ite ];
        · simp_all +decide [ Finset.mem_inf, finsetInter ];
        · exact mul_nonneg ( Finset.prod_nonneg fun _ _ => C.weight_nonneg _ ) ( by positivity );
      have h_mixed_freq : (∑ j : C.J, C.weight j * (if i ∈ C.sets j then 1 else 0)) ≤ t * (∑ j : C.J, C.weight j) := by
        have := hfreq i;
        rwa [ WeightedCollection.itemFreq, div_le_iff₀ ( C.totalWeight_pos ) ] at this;
      exact le_trans ‹_› ( by rw [ ← mul_pow ] ; exact pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => mul_nonneg ( C.weight_nonneg _ ) ( by split_ifs <;> norm_num ) ) h_mixed_freq _ );
    exact ⟨ h_mixed_freq ℓ hℓ, h_mixed_freq ( ℓ + 1 ) ( Nat.le_succ_of_le hℓ ) ⟩;
  convert add_le_add ( mul_le_mul_of_nonneg_left h_mixed_freq.1 ( show 0 ≤ ( 1 - τ ) * ( ∑ j : C.J, C.weight j ) ^ ( ℓ + 1 ) by exact mul_nonneg ( sub_nonneg.2 hτ1 ) ( pow_nonneg ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _ ) ) ) ( mul_le_mul_of_nonneg_left h_mixed_freq.2 ( show 0 ≤ τ * ( ∑ j : C.J, C.weight j ) ^ ℓ by exact mul_nonneg hτ ( pow_nonneg ( Finset.sum_nonneg fun _ _ => C.weight_nonneg _ ) _ ) ) ) using 1;
  · convert Fintype.sum_sum_type ( fun x => ( C.mixedInter ℓ hℓ τ hτ hτ1 ).weight x * if i ∈ ( C.mixedInter ℓ hℓ τ hτ hτ1 ).sets x then 1 else 0 ) using 1;
    simp +decide [ WeightedCollection.mixedInter ];
    simp +decide [ Finset.sum_ite, mul_assoc, mul_comm, Finset.mul_sum _ _ _, WeightedCollection.totalWeight ];
  · rw [ WeightedCollection.mixedInter_totalWeight ] ; ring_nf;
    rfl

/-
Average deficit of the mixed collection.
-/
lemma WeightedCollection.mixedInter_avgDeficit_le
    (C : WeightedCollection U) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (M : ℝ) (hM : ∀ S : Finset U, |f S| ≤ M)
    (D : ℝ) (hD : 0 ≤ D) (hdeficit : C.avgDeficit f M ≤ D) :
    (C.mixedInter ℓ hℓ τ hτ hτ1).avgDeficit f M ≤
      ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2) := by
  unfold WeightedCollection.avgDeficit WeightedCollection.mixedInter;
  rw [ Fintype.sum_sum_type, div_le_iff₀ ];
  · have h_left : (∑ x : Fin ℓ → C.J, (∏ k : Fin ℓ, C.weight (x k)) * deficit f M (finsetInter (fun k => C.sets (x k)))) ≤ C.totalWeight ^ ℓ * (ℓ * D + 2 * (ℓ - 1)) := by
      convert mul_le_mul_of_nonneg_left ( WeightedCollection.productInter_avgDeficit C ℓ hℓ f hf M hM D hD hdeficit ) ( show 0 ≤ C.totalWeight ^ ℓ by exact pow_nonneg C.totalWeight_pos.le _ ) using 1;
      unfold WeightedCollection.avgDeficit; simp +decide [ mul_comm, WeightedCollection.productInter_totalWeight ] ;
      rw [ mul_div_cancel₀ _ ( pow_ne_zero _ C.totalWeight_pos.ne' ) ] ; rfl;
    have h_right : (∑ x : Fin (ℓ + 1) → C.J, (∏ k : Fin (ℓ + 1), C.weight (x k)) * deficit f M (finsetInter (fun k => C.sets (x k)))) ≤ C.totalWeight ^ (ℓ + 1) * ((ℓ + 1) * D + 2 * ℓ) := by
      have := WeightedCollection.productInter_avgDeficit C ( ℓ + 1 ) ( by linarith ) f hf M hM D hD hdeficit;
      unfold WeightedCollection.avgDeficit at this;
      rw [ div_le_iff₀ ] at this <;> norm_num [ WeightedCollection.productInter_totalWeight ] at *;
      · convert this using 1 ; ring!;
      · exact pow_pos C.totalWeight_pos _;
    convert add_le_add ( mul_le_mul_of_nonneg_left h_left ( show 0 ≤ ( 1 - τ ) * C.totalWeight ^ ( ℓ + 1 ) by exact mul_nonneg ( sub_nonneg.2 hτ1 ) ( pow_nonneg C.totalWeight_pos.le _ ) ) ) ( mul_le_mul_of_nonneg_left h_right ( show 0 ≤ τ * C.totalWeight ^ ℓ by exact mul_nonneg hτ ( pow_nonneg C.totalWeight_pos.le _ ) ) ) using 1;
    · simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
    · erw [ WeightedCollection.mixedInter_totalWeight ] ; ring;
      · linarith;
      · exact hτ;
      · linarith;
  · apply_rules [ mul_pos, pow_pos, WeightedCollection.totalWeight_pos ]
