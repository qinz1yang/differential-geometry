import DifferentialGeometry.Geometry.Metric.Approximation.CalibratedCoordinates

/-!
# Original radial coordinates from two calibrated prefixes

Fixed-length positive and negative prefixes calibrate the original centered distance.
The errors tend to zero after the length is fixed; no endpoint distance coordinate replaces it.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w

variable {A : ℕ → Type u} [∀ i, MetricSpace (A i)]
variable {Y : Type v} {Z : Type w} [MetricSpace Y] [MetricSpace Z]
variable {o : ∀ i, A i} {γ : ℝ → Y} {z : Z} {R ε : ℕ → ℝ}

theorem eventually_original_radial_error_lt
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z))
    (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, z))
    (f : ∀ i, PointedBallApprox (o i) (γ 0) (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (p : ∀ i, A i)
    (hcal : ∀ T : ℝ, 0 < T → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∃ aPlus aMinus : BallCarrier (o i) (R i),
        T - η ≤ dist (p i) aPlus.val - dist (p i) (o i) ∧
        dist (p i) aMinus.val - dist (p i) (o i) ≤ -T + η ∧
        dist ((f i).toFun aPlus) (γ T) ≤ η ∧
        dist ((f i).toFun aMinus) (γ (-T)) ≤ η) :
    ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ x : BallCarrier (o i) (R i), dist x.val (o i) ≤ S →
        |dist (p i) x.val - dist (p i) (o i) - (e ((f i).toFun x)).fst| < η := by
  have hLip (i : ℕ) : LipschitzWith 1
      (fun x : A i => dist (p i) x - dist (p i) (o i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right] using
      (LipschitzWith.dist_right (p i)).dist_le_mul x y
  intro S hS η hη
  let B := S + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hsub : Tendsto (fun T : ℝ => T - B) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-B) tendsto_id
  have hden : Tendsto (fun T : ℝ => 2 * (T - B)) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have hbound : Tendsto (fun T : ℝ => B ^ 2 / (2 * (T - B))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (B ^ 2)
  obtain ⟨T, hTB, hTη⟩ := ((eventually_gt_atTop B).and
    (hbound.eventually (eventually_lt_nhds (by positivity : 0 < η / 4)))).exists
  have hT : 0 < T := hB.trans hTB
  have heighth : 0 < η / 8 := by positivity
  filter_upwards [hR.eventually (eventually_ge_atTop S),
    hε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hε.eventually (eventually_lt_nhds heighth), hcal T hT (η / 8) heighth]
    with i hiR hiεone hiε hi
  refine ⟨hiR, ?_⟩
  intro x hx
  obtain ⟨aPlus, aMinus, hp, hm, hfp, hfm⟩ := hi
  have hxB : dist ((f i).toFun x) (γ 0) ≤ B := by
    dsimp only [B]
    linarith [(f i).radial_upper x]
  have hh := abs_coordinate_error_le_of_opposite_calibration e halign (f i)
    (fun x => dist (p i) x - dist (p i) (o i)) (hLip i)
    aPlus aMinus x (E := 0) (by norm_num) hp (by simpa only [add_zero] using hm)
    hfp hfm hxB hTB
  linarith

end GC.MetricGeometry
