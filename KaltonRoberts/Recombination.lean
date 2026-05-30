/-
# One-sided recombination: witness-level theorem

This file proves the witness-level version of Lemma 3.2 (one-sided recombination)
from the companion paper.

**Reference**: Lemma 3.2 in Section 3 of the companion paper.
-/
import Mathlib
import KaltonRoberts.Defs

open Finset BigOperators Classical

set_option maxHeartbeats 1600000

noncomputable section

variable {U : Type*} [DecidableEq U]

/-! ## Approximate-additivity partition lemmas -/

/-- If `f` is `1`-additive and `pieces : Fin n → Finset U` are pairwise disjoint
with union `A`, then `f(A) ≥ ∑ f(pieces) - (n - 1)`. -/
theorem approx_additive_finset_partition_lower
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (n : ℕ) (hn : 1 ≤ n) (pieces : Fin n → Finset U)
    (hpw : ∀ i j : Fin n, i ≠ j → Disjoint (pieces i) (pieces j))
    (A : Finset U)
    (hunion : A = Finset.univ.biUnion pieces) :
    f A ≥ ∑ i : Fin n, f (pieces i) - ((n : ℝ) - 1) := by
  induction' n with n ih generalizing A <;> simp_all +decide [ Fin.sum_univ_castSucc ];
  rcases n with ( _ | n ) <;> simp_all +decide [ Fin.sum_univ_castSucc ];
  have h_union : f (Finset.biUnion Finset.univ pieces) ≥ f (Finset.biUnion Finset.univ (pieces ∘ Fin.castSucc)) + f (pieces (Fin.last (n + 1))) - 1 := by
    have h_union : f (Finset.biUnion Finset.univ pieces) = f (Finset.biUnion Finset.univ (pieces ∘ Fin.castSucc) ∪ pieces (Fin.last (n + 1))) := by
      congr with x ; simp +decide [ Fin.exists_iff ];
      exact ⟨ fun ⟨ i, hi, hx ⟩ => if hi' : i = n + 1 then Or.inr ( by simpa [ hi' ] using hx ) else Or.inl ⟨ i, Nat.le_of_lt_succ ( lt_of_le_of_ne hi hi' ), hx ⟩, fun hx => hx.elim ( fun ⟨ i, hi, hx ⟩ => ⟨ i, Nat.le_succ_of_le hi, hx ⟩ ) fun hx => ⟨ n + 1, le_rfl, hx ⟩ ⟩;
    have := hf.2 ( Finset.biUnion Finset.univ ( pieces ∘ Fin.castSucc ) ) ( pieces ( Fin.last ( n + 1 ) ) ) ?_ <;> simp_all +decide [ Finset.disjoint_left ];
    · linarith [ abs_le.mp this ];
    · exact fun a i hi => hpw _ _ ( ne_of_lt ( Fin.castSucc_lt_last i ) ) hi;
  linarith! [ ih ( fun i => pieces i.castSucc ) fun i j hij => hpw _ _ ( by simpa [ Fin.ext_iff ] using hij ) ]

/-- If `f` is `1`-additive and `pieces : Fin n → Finset U` are pairwise disjoint
with union `A`, then `∑ f(pieces) ≤ f(A) + (n - 1)`. -/
theorem approx_additive_finset_partition_upper
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (n : ℕ) (hn : 1 ≤ n) (pieces : Fin n → Finset U)
    (hpw : ∀ i j : Fin n, i ≠ j → Disjoint (pieces i) (pieces j))
    (A : Finset U)
    (hunion : A = Finset.univ.biUnion pieces) :
    ∑ i : Fin n, f (pieces i) ≤ f A + ((n : ℝ) - 1) := by
  induction' n with n ih generalizing A;
  · contradiction;
  · rcases n with ( _ | n ) <;> simp_all +decide [ Fin.sum_univ_succ ];
    have := hf.2 ( pieces 0 ) ( Finset.biUnion Finset.univ fun i : Fin ( n + 1 ) => pieces ( Fin.succ i ) ) ?_ <;> simp_all +decide [ Finset.disjoint_left ];
    · rw [ show ( Finset.univ.biUnion pieces : Finset U ) = pieces 0 ∪ Finset.biUnion Finset.univ fun i : Fin ( n + 1 ) => pieces ( Fin.succ i ) from ?_ ];
      · linarith! [ abs_le.mp this, ih ( fun i => pieces i.succ ) fun i j hij a ha hb => hpw _ _ ( by simpa [ Fin.ext_iff ] using hij ) ha hb ];
      · ext x; simp +decide [ Fin.exists_fin_succ ] ;
    · exact fun x hx i => hpw _ _ ( ne_of_lt ( Fin.succ_pos i ) ) hx

/-
Reverse direction: `∑ f(pieces) ≥ f(A) - (n - 1)`. Used for the source-side
bound in recombination.
-/
theorem approx_additive_finset_partition_sum_lower
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (n : ℕ) (hn : 1 ≤ n) (pieces : Fin n → Finset U)
    (hpw : ∀ i j : Fin n, i ≠ j → Disjoint (pieces i) (pieces j))
    (A : Finset U)
    (hunion : A = Finset.univ.biUnion pieces) :
    ∑ i : Fin n, f (pieces i) ≥ f A - ((n : ℝ) - 1) := by
  -- Apply the approximation lemma to -f.
  have := approx_additive_finset_partition_upper (-f) (by
  constructor <;> simp +decide [ hf.1 ];
  exact fun A B hAB => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hf.2 A B hAB ) ], by linarith [ abs_le.mp ( hf.2 A B hAB ) ] ⟩) n hn pieces hpw A hunion
  simp at this
  linarith [hf.1, hf.2]

/-! ## Hall matching from expansion -/

/-- From an expander's expansion property, derive Hall's matching for any
subset of left vertices of size at most the expansion threshold. -/
theorem hall_matching_from_expansion
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {r : ℕ} (edge : V → Fin r → W)
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (A : Finset V) (hA : A.card ≤ threshold) :
    ∃ (match_fn : A → W),
      Function.Injective match_fn ∧
      ∀ x : A, match_fn x ∈ edgeNeighbors edge x.val := by
  have hall_cond : ∀ s : Finset A, s.card ≤ (s.biUnion (fun x => edgeNeighbors edge x.val)).card := by
    intro s
    set S := s.image (Subtype.val : A → V) with hS_def
    have hS_card : S.card = s.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hS_le : S.card ≤ threshold := by
      rw [hS_card]
      exact le_trans (Finset.card_le_univ s |>.trans (by rw [Fintype.card_coe])) hA
    have hexp_S := hexp S hS_le
    calc s.card = S.card := hS_card.symm
      _ ≤ (S.biUnion (fun v => edgeNeighbors edge v)).card := hexp_S
      _ = (s.biUnion (fun x => edgeNeighbors edge x.val)).card := by
          congr 1; ext w; simp only [Finset.mem_biUnion, Finset.mem_image, hS_def]
          exact ⟨fun ⟨_, ⟨a, ha, rfl⟩, hw⟩ => ⟨a, ha, hw⟩,
                 fun ⟨a, ha, hw⟩ => ⟨_, ⟨a, ha, rfl⟩, hw⟩⟩
  rw [Finset.all_card_le_biUnion_card_iff_exists_injective] at hall_cond
  exact hall_cond

/-! ## Recombination construction -/

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {r : ℕ} (edge : V → Fin r → W)
variable (C : V → Finset U)

/-- For each item `i`, the set of source vertices containing it. -/
def sourceVertices (i : U) : Finset V :=
  Finset.univ.filter (fun v => i ∈ C v)

/-- Per-item Hall matching: for each item `i`, an injective map from
source vertices containing `i` into `W`, landing in the edge-neighbor set. -/
def perItemMatch
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (i : U) : ↥(sourceVertices C i) → W :=
  (hall_matching_from_expansion edge threshold hexp (sourceVertices C i) (hfreq i)).choose

lemma perItemMatch_injective
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (i : U) : Function.Injective (perItemMatch edge C threshold hexp hfreq i) :=
  (hall_matching_from_expansion edge threshold hexp (sourceVertices C i) (hfreq i)).choose_spec.1

lemma perItemMatch_mem_neighbors
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (i : U) (x : ↥(sourceVertices C i)) :
    perItemMatch edge C threshold hexp hfreq i x ∈ edgeNeighbors edge x.val := by
  exact (hall_matching_from_expansion edge threshold hexp (sourceVertices C i) (hfreq i)).choose_spec.2 x

/-- For each source vertex `v` and item `i ∈ C v`, choose an edge label `e : Fin r`
such that `edge v e` equals the matched target of `(v, i)`. -/
def assignLabel
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (v : V) (i : U) (hi : i ∈ C v) : Fin r :=
  let _w := perItemMatch edge C threshold hexp hfreq i
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hi⟩⟩
  -- w ∈ edgeNeighbors edge v = univ.image (edge v), so ∃ e, edge v e = w
  (Finset.mem_image.mp (perItemMatch_mem_neighbors edge C threshold hexp hfreq i
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hi⟩⟩)).choose

lemma assignLabel_spec
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (v : V) (i : U) (hi : i ∈ C v) :
    edge v (assignLabel edge C threshold hexp hfreq v i hi) =
      perItemMatch edge C threshold hexp hfreq i
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hi⟩⟩ :=
  (Finset.mem_image.mp (perItemMatch_mem_neighbors edge C threshold hexp hfreq i
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hi⟩⟩)).choose_spec.2

/-- Edge piece: for each `v : V` and `e : Fin r`, the subset of `C v` whose
assigned edge label is `e`. -/
def edgePiece
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (v : V) (e : Fin r) : Finset U :=
  (C v).filter (fun i => ∃ hi : i ∈ C v, assignLabel edge C threshold hexp hfreq v i hi = e)

/-- Target set: for each `w : W`, the union of all edge pieces arriving at `w`. -/
def targetSet
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (w : W) : Finset U :=
  (Finset.univ.product Finset.univ).biUnion
    (fun ve : V × Fin r =>
      if edge ve.1 ve.2 = w then edgePiece edge C threshold hexp hfreq ve.1 ve.2 else ∅)

/-! ## Properties of the construction -/

/-
Edge pieces partition `C v`: their union is `C v`.
-/
lemma edgePiece_union
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (v : V) :
    C v = Finset.univ.biUnion (fun e => edgePiece edge C threshold hexp hfreq v e) := by
  ext i
  simp [edgePiece]

/-
Edge pieces are pairwise disjoint.
-/
lemma edgePiece_pairwise_disjoint
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (v : V) (e₁ e₂ : Fin r) (he : e₁ ≠ e₂) :
    Disjoint (edgePiece edge C threshold hexp hfreq v e₁)
             (edgePiece edge C threshold hexp hfreq v e₂) := by
  refine Finset.disjoint_left.mpr ?_;
  simp +decide [ edgePiece ];
  grind

/-
Each item appears in at most as many target sets as source sets containing it.
This is the key strengthening: the per-item matching injects source occurrences
into target vertices, so target count ≤ source count.
-/
lemma targetSet_freq_source_count_bound
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (i : U) :
    (Finset.univ.filter (fun w => i ∈ targetSet edge C threshold hexp hfreq w)).card ≤
      (sourceVertices C i).card := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun v : sourceVertices C i => perItemMatch edge C threshold hexp hfreq i v ) Finset.univ;
  · intro w hw; simp_all +decide [ targetSet ] ;
    obtain ⟨ a, b, hw ⟩ := hw; split_ifs at hw <;> simp_all +decide [ edgePiece ] ;
    grind +suggestions;
  · exact Finset.card_image_le.trans ( by simp +decide )

/-
Corollary: each item appears in at most `threshold` target sets.
-/
lemma targetSet_freq_bound
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold)
    (i : U) :
    (Finset.univ.filter (fun w => i ∈ targetSet edge C threshold hexp hfreq w)).card ≤ threshold :=
  le_trans (targetSet_freq_source_count_bound edge C threshold hexp hfreq i) (hfreq i)

/-
**Key inequality**: `∑_v f(C v) ≤ ∑_w f(T w) + 2rN - N - L`.

Derived from:
- Source partition: `∑_{v,e} f(P v e) ≥ ∑_v f(C v) - N(r-1)` (partition_sum_lower)
- Target partition: `∑_{v,e} f(P v e) ≤ ∑_w f(T w) + (rN - L)` (partition_upper + right coverage)
- Sum rearrangement: `∑_v ∑_e f(P v e) = ∑_w ∑_{(v,e): edge v e = w} f(P v e)`
-/
lemma recombination_source_target_ineq
    (edge : V → Fin r → W)
    (hcov : ∀ w : W, ∃ v : V, ∃ e : Fin r, edge v e = w)
    (hr : 0 < r)
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (C : V → Finset U)
    (hfreq : ∀ i : U, (sourceVertices C i).card ≤ threshold) :
    ∑ v : V, f (C v) ≤
      ∑ w : W, f (targetSet edge C threshold hexp hfreq w) +
      2 * (r : ℝ) * (Fintype.card V : ℝ) - (Fintype.card V : ℝ) - (Fintype.card W : ℝ) := by
  -- By the properties of the target set, we have $\sum_{v \in V} \sum_{e \in \text{Fin } r} f(\text{edgePiece } v e) \geq \sum_{v \in V} f(C v) - (r - 1) * \text{card } V$.
  have h_target_sum : ∑ v, ∑ e, f (edgePiece edge C threshold hexp hfreq v e) ≥ ∑ v, f (C v) - (r - 1) * (Fintype.card V : ℝ) := by
    have h_source_partition : ∀ v : V, f (C v) ≤ ∑ e : Fin r, f (edgePiece edge C threshold hexp hfreq v e) + (r - 1) := by
      intro v;
      have := approx_additive_finset_partition_sum_lower f hf r hr ( fun e => edgePiece edge C threshold hexp hfreq v e ) ( fun e₁ e₂ he => edgePiece_pairwise_disjoint edge C threshold hexp hfreq v e₁ e₂ he ) ( C v ) ( by rw [ edgePiece_union edge C threshold hexp hfreq v ] ) ; linarith;
    have := Finset.sum_le_sum fun v ( hv : v ∈ Finset.univ ) => h_source_partition v; simp_all +decide [ mul_comm, Finset.sum_add_distrib ] ;
    linarith;
  -- By the properties of the target set, we have $\sum_{w \in W} \sum_{(v, e) \text{ with } \text{edge } v e = w} f(\text{edgePiece } v e) \leq \sum_{w \in W} f(\text{targetSet } w) + (r * \text{card } V - \text{card } W)$.
  have h_target_sum_upper : ∑ w, ∑ v ∈ Finset.univ, ∑ e ∈ Finset.univ, (if edge v e = w then f (edgePiece edge C threshold hexp hfreq v e) else 0) ≤ ∑ w, f (targetSet edge C threshold hexp hfreq w) + (r * (Fintype.card V : ℝ) - (Fintype.card W : ℝ)) := by
    have h_target_sum_upper : ∀ w, ∑ v ∈ Finset.univ, ∑ e ∈ Finset.univ, (if edge v e = w then f (edgePiece edge C threshold hexp hfreq v e) else 0) ≤ f (targetSet edge C threshold hexp hfreq w) + ((Finset.univ.filter (fun ve : V × Fin r => edge ve.1 ve.2 = w)).card - 1) := by
      intro w
      have h_target_sum_upper_step : ∀ S : Finset (V × Fin r), S.Nonempty → (∀ ve₁ ve₂, ve₁ ∈ S → ve₂ ∈ S → ve₁ ≠ ve₂ → Disjoint (edgePiece edge C threshold hexp hfreq ve₁.1 ve₁.2) (edgePiece edge C threshold hexp hfreq ve₂.1 ve₂.2)) → ∑ ve ∈ S, f (edgePiece edge C threshold hexp hfreq ve.1 ve.2) ≤ f (Finset.biUnion S (fun ve => edgePiece edge C threshold hexp hfreq ve.1 ve.2)) + (S.card - 1) := by
        intro S hS_nonempty hS_disjoint
        have h_target_sum_upper_step : ∑ ve ∈ S, f (edgePiece edge C threshold hexp hfreq ve.1 ve.2) ≤ f (Finset.biUnion S (fun ve => edgePiece edge C threshold hexp hfreq ve.1 ve.2)) + (S.card - 1) := by
          have h_partition : ∀ (pieces : Fin S.card → Finset U), (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) → (∑ i, f (pieces i)) ≤ f (Finset.univ.biUnion pieces) + (S.card - 1) := by
            intro pieces hpw_disjoint
            apply approx_additive_finset_partition_upper f hf S.card (by
            exact Finset.card_pos.mpr hS_nonempty) pieces hpw_disjoint (Finset.univ.biUnion pieces) (by
            rfl)
          obtain ⟨g, hg⟩ : ∃ g : Fin S.card ≃ S, True := by
            exact ⟨ Fintype.equivOfCardEq ( by simp +decide ), trivial ⟩;
          convert h_partition ( fun i => edgePiece edge C threshold hexp hfreq ( g i |>.1.1 ) ( g i |>.1.2 ) ) _ using 1;
          · rw [ ← Finset.sum_coe_sort ];
            conv_lhs => rw [ ← Equiv.sum_comp g ] ;
          · congr! 2;
            ext; simp [Finset.mem_biUnion];
            exact ⟨ fun ⟨ a, b, h₁, h₂ ⟩ => ⟨ g.symm ⟨ ( a, b ), h₁ ⟩, by simpa using h₂ ⟩, fun ⟨ a, h₂ ⟩ => ⟨ _, _, g a |>.2, by simpa using h₂ ⟩ ⟩;
          · exact fun i j hij => hS_disjoint _ _ ( g i |>.2 ) ( g j |>.2 ) ( by simpa [ Fin.ext_iff ] using fun h => hij <| g.injective <| Subtype.ext h );
        exact h_target_sum_upper_step;
      convert h_target_sum_upper_step ( Finset.filter ( fun ve => edge ve.1 ve.2 = w ) ( Finset.univ.product Finset.univ ) ) _ _ using 1;
      · erw [ Finset.sum_filter, Finset.sum_product ];
      · congr! 2;
        ext; simp [targetSet];
        exact ⟨ fun ⟨ a, b, h ⟩ => ⟨ a, b, by split_ifs at h <;> tauto ⟩, fun ⟨ a, b, h₁, h₂ ⟩ => ⟨ a, b, by rw [ if_pos h₁ ] ; exact h₂ ⟩ ⟩;
      · obtain ⟨ v, e, rfl ⟩ := hcov w; exact ⟨ ⟨ v, e ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_univ _, Finset.mem_univ _ ⟩, rfl ⟩ ⟩ ;
      · intro ve₁ ve₂ h₁ h₂ hne
        simp [edgePiece] at *;
        rw [ Finset.disjoint_left ];
        intro i hi₁ hi₂
        obtain ⟨hi₁', hi₁''⟩ := Finset.mem_filter.mp hi₁
        obtain ⟨hi₂', hi₂''⟩ := Finset.mem_filter.mp hi₂
        have h_eq : perItemMatch edge C threshold hexp hfreq i ⟨ve₁.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁'⟩⟩ = perItemMatch edge C threshold hexp hfreq i ⟨ve₂.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₂'⟩⟩ := by
          grind +locals;
        have := perItemMatch_injective edge C threshold hexp hfreq i h_eq; simp_all +decide [ Finset.mem_filter ] ;
        grind +revert;
    refine' le_trans ( Finset.sum_le_sum fun w _ => h_target_sum_upper w ) _;
    simp +decide [ Finset.sum_add_distrib ];
    rw_mod_cast [ ← Finset.card_biUnion ];
    · exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ mul_comm ] );
    · exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z => by aesop;
  have h_sum_eq : ∑ w, ∑ v ∈ Finset.univ, ∑ e ∈ Finset.univ, (if edge v e = w then f (edgePiece edge C threshold hexp hfreq v e) else 0) = ∑ v, ∑ e, f (edgePiece edge C threshold hexp hfreq v e) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro v hv; rw [ Finset.sum_comm ] ; simp +decide ;
  linarith

/-! ## One-sided recombination: witness-level core -/

/-
**Lemma 3.2** (One-sided recombination, witness-level).

Given a concrete finite expander witness and source sets `C : V → Finset U`
with bounded item frequency and average deficit, constructs target sets
`T : W → Finset U` and proves the recombination inequality.

**Reference**: Lemma 3.2 in Section 3 of the companion paper.
-/
theorem one_sided_recombination_witness_core
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {r : ℕ} (hr : 0 < r)
    (edge : V → Fin r → W)
    (hcov : ∀ w : W, ∃ v : V, ∃ e : Fin r, edge v e = w)
    (threshold : ℕ)
    (hexp : ∀ S : Finset V, S.card ≤ threshold →
      (S.biUnion (fun v => edgeNeighbors edge v)).card ≥ S.card)
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (C : V → Finset U)
    (hfreq : ∀ i : U, (Finset.univ.filter (fun v => i ∈ C v)).card ≤ threshold)
    (D : ℝ) (_hD : 0 ≤ D)
    (havg_def : (∑ v : V, deficit f M (C v)) / (Fintype.card V : ℝ) ≤ D)
    (hN : 0 < (Fintype.card V : ℝ))
    (hL : 0 < (Fintype.card W : ℝ)) :
    ∃ (T : W → Finset U) (D' : ℝ),
      0 ≤ D' ∧
      (∀ i : U, (Finset.univ.filter (fun w => i ∈ T w)).card ≤
        (Finset.univ.filter (fun v => i ∈ C v)).card) ∧
      (∀ i : U, (Finset.univ.filter (fun w => i ∈ T w)).card ≤ threshold) ∧
      (∑ w : W, deficit f M (T w)) / (Fintype.card W : ℝ) ≤ D' ∧
      (1 - (Fintype.card W : ℝ) / (Fintype.card V : ℝ)) * M ≤
        D - ((Fintype.card W : ℝ) / (Fintype.card V : ℝ)) * D' +
        2 * (r : ℝ) - 1 - (Fintype.card W : ℝ) / (Fintype.card V : ℝ) := by
  -- Unfold sourceVertices to match hfreq
  have hfreq' : ∀ i : U, (sourceVertices C i).card ≤ threshold := by
    intro i; exact hfreq i
  -- Construct target sets
  set T := targetSet edge C threshold hexp hfreq' with hT_def
  set D' := (∑ w : W, deficit f M (T w)) / (Fintype.card W : ℝ) with hD'_def
  refine ⟨T, D', ?_, ?_, ?_, le_refl _, ?_⟩
  · -- D' ≥ 0: each deficit is ≥ 0 since |f(T w)| ≤ M
    apply div_nonneg
    · apply Finset.sum_nonneg; intro w _
      simp only [deficit]; linarith [abs_le.mp (hM (T w))]
    · exact le_of_lt hL
  · -- Source count bound (stronger): target count ≤ source count
    intro i; exact targetSet_freq_source_count_bound edge C threshold hexp hfreq' i
  · -- Frequency bound (corollary): target count ≤ threshold
    intro i; exact targetSet_freq_bound edge C threshold hexp hfreq' i
  · -- Deficit inequality
    -- Apply the recombination_source_target_ineq lemma to get the inequality.
    have h_ineq : ∑ v : V, deficit f M (C v) - ∑ w : W, deficit f M (T w) ≥ (Fintype.card V - Fintype.card W) * M - 2 * r * Fintype.card V + Fintype.card V + Fintype.card W := by
      have := recombination_source_target_ineq edge hcov hr threshold hexp f hf M C hfreq';
      unfold deficit at *; norm_num at *; linarith;
    field_simp;
    rw [ div_le_iff₀ ] at havg_def <;> nlinarith [ mul_div_cancel₀ ( ∑ w : W, deficit f M ( T w ) ) ( ne_of_gt hL ) ]

/-!
`one_sided_recombination_witness_core` is the concrete finite-expander
version of Lemma 3.2. The lifted uniform and epsilon-weighted versions used
by the main theorem live in `UniformRecombination.lean` and
`EpsilonRecombination.lean`.
-/

end
