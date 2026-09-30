import DifferentialGeometry.Geometry.Metric.ProductBusemann
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Topology.MetricSpace.Lipschitz

open Filter
open scoped Topology

namespace GC.MetricGeometry

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {γ : ℝ → Y} {z : Z} {R ε E η ζ B T : ℝ}

theorem abs_coordinate_error_le_of_opposite_calibration
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, z))
    (f : PointedBallApprox p (γ 0) R ε) (h : X → ℝ) (hLip : LipschitzWith 1 h)
    (aPlus aMinus x : BallCarrier p R) (hE : 0 ≤ E)
    (hplus : T - η ≤ h aPlus.val) (hminus : h aMinus.val ≤ -T + E + η)
    (hfplus : dist (f.toFun aPlus) (γ T) ≤ ζ) (hfminus : dist (f.toFun aMinus) (γ (-T)) ≤ ζ)
    (hB : dist (f.toFun x) (γ 0) ≤ B) (hTB : B < T) :
    |h x.val - (e (f.toFun x)).fst| ≤ E + η + ε + ζ + B ^ 2 / (2 * (T - B)) := by
  have hp : |h x.val - h aPlus.val| ≤ dist x.val aPlus.val := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip.dist_le_mul x.val aPlus.val
  have hm : |h x.val - h aMinus.val| ≤ dist x.val aMinus.val := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip.dist_le_mul x.val aMinus.val
  have hdp := (abs_lt.mp (f.distortion x aPlus)).1
  have hdm := (abs_lt.mp (f.distortion x aMinus)).1
  have htp := dist_triangle (f.toFun x) (γ T) (f.toFun aPlus)
  have htm := dist_triangle (f.toFun x) (γ (-T)) (f.toFun aMinus)
  rw [dist_comm (γ T) (f.toFun aPlus)] at htp
  rw [dist_comm (γ (-T)) (f.toFun aMinus)] at htm
  obtain ⟨hbp, hbm⟩ := e.dist_aligned_line_sub_bounds halign (f.toFun x) hB hTB
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hp).1, hbp.2],
    by linarith [(abs_le.mp hm).2, hbm.2]⟩

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {o : ∀ i, A i} {r εseq Eseq ηseq : ℕ → ℝ}

theorem eventually_abs_coordinate_error_lt_of_opposite_calibration
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, z))
    (f : ∀ i, PointedBallApprox (o i) (γ 0) (r i) (εseq i))
    (hr : Tendsto r atTop atTop) (hε : Tendsto εseq atTop (𝓝 0))
    (h : ∀ i, A i → ℝ) (hLip : ∀ i, LipschitzWith 1 (h i))
    (hE : ∀ i, 0 ≤ Eseq i) (hEzero : Tendsto Eseq atTop (𝓝 0))
    (hηzero : Tendsto ηseq atTop (𝓝 0))
    (hcalibration : ∀ T : ℝ, 0 < T → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      ∃ aPlus aMinus : BallCarrier (o i) (r i),
        T - ηseq i ≤ h i aPlus.val ∧ h i aMinus.val ≤ -T + Eseq i + ηseq i ∧
        dist ((f i).toFun aPlus) (γ T) ≤ ζ ∧ dist ((f i).toFun aMinus) (γ (-T)) ≤ ζ) :
    ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      S ≤ r i ∧ ∀ x : BallCarrier (o i) (r i), dist x.val (o i) ≤ S →
        |h i x.val - (e ((f i).toFun x)).fst| < η := by
  intro S hS η hη
  let B := S + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hsub : Tendsto (fun T : ℝ => T - B) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-B) tendsto_id
  have hden : Tendsto (fun T : ℝ => 2 * (T - B)) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have hbound : Tendsto (fun T : ℝ => B ^ 2 / (2 * (T - B))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (B ^ 2)
  obtain ⟨T, hTB, hTη⟩ := ((eventually_gt_atTop B).and
    (hbound.eventually (eventually_lt_nhds (by positivity : 0 < η / 4)))).exists
  have hT : 0 < T := hB.trans hTB
  have heighth : 0 < η / 8 := by positivity
  filter_upwards [hr.eventually (eventually_ge_atTop S),
    hε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hε.eventually (eventually_lt_nhds heighth), hEzero.eventually (eventually_lt_nhds heighth),
    hηzero.eventually (eventually_lt_nhds heighth), hcalibration T hT (η / 8) heighth]
    with i hiR hiεone hiε hiE hiη hi
  refine ⟨hiR, ?_⟩
  intro x hx
  obtain ⟨aPlus, aMinus, hp, hm, hfp, hfm⟩ := hi
  have hxB : dist ((f i).toFun x) (γ 0) ≤ B := by
    dsimp only [B]
    linarith [(f i).radial_upper x]
  have hh := abs_coordinate_error_le_of_opposite_calibration e halign (f i) (h i) (hLip i)
    aPlus aMinus x (hE i) hp hm hfp hfm hxB hTB
  linarith

theorem eventually_abs_distance_coordinate_error_lt_of_opposite_calibration
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, z))
    (f : ∀ i, PointedBallApprox (o i) (γ 0) (r i) (εseq i))
    (hr : Tendsto r atTop atTop) (hε : Tendsto εseq atTop (𝓝 0))
    (a : ∀ i, A i)
    (hE : ∀ i, 0 ≤ Eseq i) (hEzero : Tendsto Eseq atTop (𝓝 0))
    (hηzero : Tendsto ηseq atTop (𝓝 0))
    (hcalibration : ∀ T : ℝ, 0 < T → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      ∃ aPlus aMinus : BallCarrier (o i) (r i),
        T - ηseq i ≤ dist (o i) (a i) - dist aPlus.val (a i) ∧ dist (o i) (a i) - dist aMinus.val (a i) ≤ -T + Eseq i + ηseq i ∧
        dist ((f i).toFun aPlus) (γ T) ≤ ζ ∧ dist ((f i).toFun aMinus) (γ (-T)) ≤ ζ) :
    ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      S ≤ r i ∧ ∀ x : BallCarrier (o i) (r i), dist x.val (o i) ≤ S →
        |dist (o i) (a i) - dist x.val (a i) - (e ((f i).toFun x)).fst| < η := by
  have hLip (i : ℕ) : LipschitzWith 1 (fun x : A i => dist (o i) (a i) - dist x (a i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show dist (o i) (a i) - dist x (a i) - (dist (o i) (a i) - dist y (a i)) =
      -(dist x (a i) - dist y (a i)) by ring, abs_neg]
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (LipschitzWith.dist_left (a i)).dist_le_mul x y
  exact eventually_abs_coordinate_error_lt_of_opposite_calibration e halign f hr hε
    (fun i x => dist (o i) (a i) - dist x (a i)) hLip hE hEzero hηzero hcalibration

end GC.MetricGeometry
