import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_mid_eq_sqrt_mul_sqrt
    (i : TensorEigenIdx (I := I) (M := M) g r s) (a : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  have hsqrt_u : Real.sqrt (x ^ (a + 2)) = x ^ ((a + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  have hsqrt_l : Real.sqrt (x ^ (a : ℝ)) = x ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_summable
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)) := by
  have hv := v.weighted_summable
  have hw := w.weighted_summable
  have h_dom : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (v.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i a * (w.coeff i) ^ 2)) :=
    (hv.mul_left _).add (hw.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
  set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
  have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt wu * Real.sqrt wl :=
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
  have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
  nlinarith [sq_nonneg (Real.sqrt wu * |v.coeff i| - Real.sqrt wl * |w.coeff i|),
    Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg (v.coeff i),
    abs_nonneg (w.coeff i), sq_abs (v.coeff i), sq_abs (w.coeff i), hsqu, hsql]

def crossPairing
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) : ℝ :=
  ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_add_left
    (v v' : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (v + v') w =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v' w := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v' w)]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.add_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_add_right
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w w' : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (w + w') =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v w' := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v w')]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.add_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_smul_left (c : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (c • v) w =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.smul_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_smul_right (c : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (c • w) =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.smul_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_eq_inner_rescale
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v w =
      (inner ℝ (TensorHs.rescaleToL2 (I := I) (M := M) v)
        (TensorHs.rescaleToL2 (I := I) (M := M) w) : ℝ) := by
  rw [lp.inner_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [show (inner ℝ ((TensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i)
          ((TensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i) : ℝ) =
        (TensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i *
          (TensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i by
      simp [RCLike.inner_apply, mul_comm]]
  rw [TensorHs.rescaleToL2_apply, TensorHs.rescaleToL2_apply,
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem abs_crossPairing_le
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    |crossPairing (I := I) (M := M) v w| ≤ ‖v‖ * ‖w‖ := by
  rw [crossPairing_eq_inner_rescale]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have hv : ‖TensorHs.rescaleToL2 (I := I) (M := M) v‖ = ‖v‖ :=
    (TensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map v
  have hw : ‖TensorHs.rescaleToL2 (I := I) (M := M) w‖ = ‖w‖ :=
    (TensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map w
  rw [hv, hw]

omit [NeZero (Module.finrank ℝ E)] in
theorem crossPairing_self_eq_normSq
    (v : TensorHs (I := I) (M := M) g r s (a + 2)) :
    crossPairing (I := I) (M := M) v
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v) =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 := by
  rw [TensorHs.norm_sq_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [tensorHsInclusion_coeff_apply, tensorHsInclusion_coeff_apply, sq]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_norm_sq_le
    (v : TensorHs (I := I) (M := M) g r s (a + 2)) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 ≤
      ‖v‖ *
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v‖ := by
  rw [← crossPairing_self_eq_normSq (I := I) (M := M) v]
  refine le_trans (le_abs_self _) ?_
  exact abs_crossPairing_le (I := I) (M := M) v
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) v)

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

end
