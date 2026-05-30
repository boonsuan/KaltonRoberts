/-
# Derivative computations for the Phi function
-/
import Mathlib
import KaltonRoberts.Defs

open Real

set_option maxHeartbeats 6400000

/-! ## First derivatives of h_entropy components -/

theorem hasDerivAt_binEntropy (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => -x * Real.log x - (1 - x) * Real.log (1 - x))
      (Real.log (1 - x) - Real.log x) x := by
  convert HasDerivAt.sub ( HasDerivAt.mul ( hasDerivAt_neg x ) ( Real.hasDerivAt_log hx.ne' ) ) ( HasDerivAt.mul ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith : ( 1 - x ) ≠ 0 ) ) ) using 1 ; ring;
  grind

theorem hasDerivAt_h_entropy_second (θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) :
    HasDerivAt (fun x => θ * Real.log θ - x * Real.log x - (θ - x) * Real.log (θ - x))
      (Real.log (θ - x) - Real.log x) x := by
  convert HasDerivAt.sub ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id x ) ( Real.hasDerivAt_log _ ) ) ) ( HasDerivAt.mul ( hasDerivAt_id x |> HasDerivAt.const_sub _ ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub _ ) _ ) ) using 1 <;> norm_num [ hx.ne', hxθ.ne' ] ; ring;
  · grind;
  · linarith

theorem hasDerivAt_neg_entropy_scaled (r x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => r * x * Real.log x + r * (1 - x) * Real.log (1 - x))
      (r * (Real.log x - Real.log (1 - x))) x := by
  convert HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id x ) ) ( Real.hasDerivAt_log hx.ne' ) ) ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id x |> HasDerivAt.const_sub _ ) ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub _ ) ( by linarith : ( 1 - x ) ≠ 0 ) ) ) using 1 ; ring;
  norm_num [ hx.ne', sub_ne_zero.mpr hx1.ne' ]

/-! ## Second derivatives -/

theorem hasDerivAt_binEntropy_deriv (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => Real.log (1 - x) - Real.log x) (-1/(1-x) - 1/x) x := by
  convert HasDerivAt.sub ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith : ( 1 - x ) ≠ 0 ) ) ( Real.hasDerivAt_log hx.ne' ) using 1 ; ring_nf!;

theorem hasDerivAt_h_entropy_second_deriv (θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) :
    HasDerivAt (fun x => Real.log (θ - x) - Real.log x) (-1/(θ-x) - 1/x) x := by
  convert HasDerivAt.sub ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub θ ) ( by linarith : ( θ - x ) ≠ 0 ) ) ( Real.hasDerivAt_log hx.ne' ) using 1 ; ring_nf!;

theorem hasDerivAt_neg_entropy_scaled_deriv (r x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => r * (Real.log x - Real.log (1 - x))) (r * (1/x + 1/(1-x))) x := by
  convert HasDerivAt.const_mul r ( HasDerivAt.sub ( Real.hasDerivAt_log hx.ne' ) ( HasDerivAt.log ( hasDerivAt_id' x |> HasDerivAt.const_sub 1 ) ( by linarith ) ) ) using 1 ; ring

/-! ## Derivative of Phi -/

/-
The first derivative of Phi at a point `x` in `(0, θ)` with `θ < 1`.
-/
theorem hasDerivAt_Phi (r θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) (hx1 : x < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r) :
    HasDerivAt (fun x => Phi r θ x)
      ((Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x)
       + (r / θ * Real.log (r / θ) - r * Real.log r - (r / θ - r) * Real.log (r / θ - r))
       + r * (Real.log x - Real.log (1 - x))) x := by
  unfold Phi;
  have h_def : ∀ᶠ y in nhds x, h_entropy (r * y / θ) (r * y) = y * (h_entropy (r / θ) r) := by
    filter_upwards [ lt_mem_nhds hx ] with y hy;
    unfold h_entropy;
    field_simp;
    rw [ Real.log_div, Real.log_div, Real.log_div, Real.log_mul, Real.log_mul ] <;> try nlinarith;
    · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> ring <;> nlinarith;
    · exact mul_ne_zero ( mul_ne_zero hr.ne' hy.ne' ) ( by linarith );
  have h_def2 : ∀ᶠ y in nhds x, -h_entropy r (r * y) = r * y * Real.log y + r * (1 - y) * Real.log (1 - y) := by
    filter_upwards [ Ioo_mem_nhds hx hx1 ] with y hy;
    unfold h_entropy; ring;
    rw [ show r - r * y = r * ( 1 - y ) by ring, Real.log_mul ( by linarith ) ( by linarith [ hy.1, hy.2 ] ), Real.log_mul ( by linarith ) ( by linarith [ hy.1, hy.2 ] ) ] ; ring;
  have h_def3 : ∀ᶠ y in nhds x, h_entropy 1 y = -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    filter_upwards [ Ioo_mem_nhds hx hx1 ] with y hy using by unfold h_entropy; norm_num;
  have h_def4 : ∀ᶠ y in nhds x, h_entropy θ y = θ * Real.log θ - y * Real.log y - (θ - y) * Real.log (θ - y) := by
    exact Filter.Eventually.of_forall fun y => rfl;
  have h_def5 : ∀ᶠ y in nhds x, h_entropy (r * y / θ) (r * y) - h_entropy r (r * y) = y * h_entropy (r / θ) r + r * y * Real.log y + r * (1 - y) * Real.log (1 - y) := by
    filter_upwards [ h_def, h_def2 ] with y hy₁ hy₂ using by linarith;
  have h_def6 : HasDerivAt (fun y => -y * Real.log y - (1 - y) * Real.log (1 - y) + θ * Real.log θ - y * Real.log y - (θ - y) * Real.log (θ - y) + y * h_entropy (r / θ) r + r * y * Real.log y + r * (1 - y) * Real.log (1 - y)) (log (1 - x) - log x + (log (θ - x) - log x) + (r / θ * log (r / θ) - r * log r - (r / θ - r) * log (r / θ - r)) + r * (log x - log (1 - x))) x := by
    convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_binEntropy x hx hx1 ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_h_entropy_second θ x hx hxθ ) ) ( hasDerivAt_id' x |> HasDerivAt.mul_const <| h_entropy ( r / θ ) r ) ) ( hasDerivAt_neg_entropy_scaled r x hx hx1 ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) using 1 ; ring;
    rotate_left;
    rotate_left;
    exact 0;
    exact 0;
    exact 0;
    exact 0;
    · ext; norm_num; ring;
    · unfold h_entropy; ring;
  refine' h_def6.congr_of_eventuallyEq _;
  filter_upwards [ h_def, h_def2, h_def3, h_def4, h_def5 ] with y hy1 hy2 hy3 hy4 hy5 using by linarith;

/-- The second derivative of Phi equals `Phi'' r θ x`. -/
theorem hasDerivAt_Phi_second (r θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) (hx1 : x < 1)
    (hθ0 : 0 < θ) (hr : 2 < r) :
    HasDerivAt (fun x =>
      (Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x)
      + (r / θ * Real.log (r / θ) - r * Real.log r - (r / θ - r) * Real.log (r / θ - r))
      + r * (Real.log x - Real.log (1 - x)))
      (Phi'' r θ x) x := by
  convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_binEntropy_deriv x hx hx1 ) ( hasDerivAt_h_entropy_second_deriv θ x hx hxθ ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_neg_entropy_scaled_deriv r x hx hx1 ) using 1;
  unfold Phi''; ring;

/-! ## Generic ConvexOn for Phi -/

/-
ConvexOn for Phi on an interval [δ, α], given an explicit hypothesis
that the second-derivative formula `Phi'' r θ x` is nonneg on `[δ, α]`.
-/
theorem convexOn_Phi_of_Phi''_nonneg {r θ δ α : ℝ}
    (hδ : 0 < δ) (hαθ : α < θ) (hθ1 : θ < 1) (hr : 2 < r) (hθ0 : 0 < θ) (hδα : δ ≤ α)
    (hPhi'' : ∀ x : ℝ, δ ≤ x → x ≤ α → 0 ≤ Phi'' r θ x) :
    ConvexOn ℝ (Set.Icc δ α) (fun x => Phi r θ x) := by
  apply_rules [ convexOn_of_deriv2_nonneg ] <;> try exact convex_Icc δ α;
  · refine' ContinuousOn.sub ( ContinuousOn.add ( ContinuousOn.add _ _ ) _ ) _;
    · refine' ContinuousOn.sub _ _;
      · exact ContinuousOn.sub continuousOn_const ( ContinuousOn.mul continuousOn_id ( Real.continuousOn_log.mono ( by intro x hx; exact ne_of_gt ( by linarith [ hx.1 ] ) ) ) );
      · exact ContinuousOn.mul ( continuousOn_const.sub continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] );
    · refine' ContinuousOn.sub _ _;
      · exact ContinuousOn.sub continuousOn_const ( ContinuousOn.mul continuousOn_id ( Real.continuousOn_log.mono ( by intro x hx; exact ne_of_gt ( by linarith [ hx.1 ] ) ) ) );
      · exact ContinuousOn.mul ( continuousOn_const.sub continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] );
    · refine' ContinuousOn.sub _ _;
      · exact ContinuousOn.sub ( ContinuousOn.mul ( ContinuousOn.div_const ( continuousOn_const.mul continuousOn_id ) _ ) ( ContinuousOn.log ( ContinuousOn.div_const ( continuousOn_const.mul continuousOn_id ) _ ) fun x hx => by nlinarith [ hx.1, hx.2, mul_div_cancel₀ ( r * x ) hθ0.ne' ] ) ) ( ContinuousOn.mul ( continuousOn_const.mul continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.mul continuousOn_id ) fun x hx => by nlinarith [ hx.1, hx.2 ] ) );
      · refine' ContinuousOn.mul _ ( ContinuousOn.log _ _ );
        · exact ContinuousOn.sub ( ContinuousOn.div_const ( continuousOn_const.mul continuousOn_id ) _ ) ( continuousOn_const.mul continuousOn_id );
        · exact ContinuousOn.sub ( ContinuousOn.div_const ( continuousOn_const.mul continuousOn_id ) _ ) ( continuousOn_const.mul continuousOn_id );
        · exact fun x hx => by nlinarith [ hx.1, hx.2, mul_div_cancel₀ ( r * x ) hθ0.ne', mul_pos ( by linarith : 0 < r ) ( by linarith [ hx.1 ] : 0 < x ) ] ;
    · refine' ContinuousOn.sub _ _;
      · exact ContinuousOn.sub continuousOn_const <| ContinuousOn.mul ( continuousOn_const.mul continuousOn_id ) <| ContinuousOn.log ( continuousOn_const.mul continuousOn_id ) fun x hx => by nlinarith [ hx.1 ] ;
      · exact ContinuousOn.mul ( continuousOn_const.sub ( continuousOn_const.mul continuousOn_id ) ) ( ContinuousOn.log ( continuousOn_const.sub ( continuousOn_const.mul continuousOn_id ) ) fun x hx => by nlinarith [ hx.1, hx.2 ] );
  · norm_num +zetaDelta at *;
    intro x hx; exact ( hasDerivAt_Phi r θ x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.1, hx.2 ] ) ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt;
  · simp +zetaDelta at *;
    -- By definition of $Phi$, we know that its derivative is given by the expression in `hasDerivAt_Phi`.
    have h_deriv : ∀ x ∈ Set.Ioo δ α, deriv (fun x => Phi r θ x) x = (Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x) + (r / θ * Real.log (r / θ) - r * Real.log r - (r / θ - r) * Real.log (r / θ - r)) + r * (Real.log x - Real.log (1 - x)) := by
      intro x hx; exact HasDerivAt.deriv ( hasDerivAt_Phi r θ x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ( by linarith [ hx.1, hx.2 ] ) ) ;
    exact DifferentiableOn.congr ( fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.add ( DifferentiableAt.add ( DifferentiableAt.add ( DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) <| by linarith [ hx.1, hx.2 ] ) <| DifferentiableAt.log ( differentiableAt_id ) <| by linarith [ hx.1, hx.2 ] ) <| DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) <| by linarith [ hx.1, hx.2 ] ) <| DifferentiableAt.log ( differentiableAt_id ) <| by linarith [ hx.1, hx.2 ] ) <| differentiableAt_const _ ) <| DifferentiableAt.mul ( differentiableAt_const _ ) <| DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id ) <| by linarith [ hx.1, hx.2 ] ) <| DifferentiableAt.log ( differentiableAt_id.const_sub _ ) <| by linarith [ hx.1, hx.2 ] ) h_deriv;
  · simp +zetaDelta at *;
    intro x hx₁ hx₂;
    convert hPhi'' x hx₁.le hx₂.le using 1;
    convert HasDerivAt.deriv ( hasDerivAt_Phi_second r θ x ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ) using 1;
    exact Filter.EventuallyEq.deriv_eq ( by filter_upwards [ Ioo_mem_nhds hx₁ hx₂ ] with y hy using HasDerivAt.deriv ( hasDerivAt_Phi r θ y ( by linarith [ hy.1 ] ) ( by linarith [ hy.2 ] ) ( by linarith [ hy.2 ] ) ( by linarith [ hy.1 ] ) ( by linarith [ hy.2 ] ) ( by linarith [ hy.1 ] ) ) )