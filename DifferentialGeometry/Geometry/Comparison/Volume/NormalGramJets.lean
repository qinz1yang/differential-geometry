import DifferentialGeometry.Analysis.Calculus.IteratedDeriv.Power
import DifferentialGeometry.Geometry.Comparison.Volume.RadialGramJets
import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartSmoothness

noncomputable section

open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open NormalCoordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

theorem normalGram_zero
    (g : SmoothRiemannianMetric I M) (p : M) (i j : Fin (Module.finrank ℝ E)) :
    normalGramMatrix g p 0 i j = g.inner p (chartModelBasis E i) (chartModelBasis E j) := by
  rw [normalGram_apply, expMapDiffeo_zero]
  exact normalChartAt_metric_pullback_at_origin g p (chartModelBasis E i) (chartModelBasis E j)

theorem radialJacobi_inner_eventually_eq_normalGram
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    (fun t => g.inner (radialCurve g p x t)
      (radialJacobiField g p x (chartModelBasis E i) t)
      (radialJacobiField g p x (chartModelBasis E j) t)) =ᶠ[𝓝 0]
      fun t => t ^ 2 * normalGramMatrix g p (t • x) i j := by
  have htx : ∀ᶠ t : ℝ in 𝓝 0, ‖t • x‖ < expMapC2Radius g p :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by
      simpa using expMapC2Radius_pos g p)
  filter_upwards [htx] with t ht
  rw [normalGram_radial g p (mem_expMapDiffeo_source_of_norm_lt_radius g p ht) ht,
    radialJacobi_scale g p x (chartModelBasis E i) t,
    radialJacobi_scale g p x (chartModelBasis E j) t,
    radialJacobi_one_smul g p (t • x) (chartModelBasis E i) t ht,
    radialJacobi_one_smul g p (t • x) (chartModelBasis E j) t ht]
  let β : E →L[ℝ] E →L[ℝ] ℝ := g.inner (Exponential.expMap g p (t • x))
  let v : E := radialJacobiField g p (t • x) (chartModelBasis E i) 1
  let w : E := radialJacobiField g p (t • x) (chartModelBasis E j) 1
  change β (t • v) (t • w) = t ^ 2 * β v w
  rw [β.map_smul, smul_apply, (β v).map_smul]
  simp only [smul_eq_mul, pow_two, mul_assoc]

private theorem contDiffAt_normalGram_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun t : ℝ => normalGramMatrix g p (t • x) i j) 0 := by
  have hG := contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_normalGramMatrix_zero g p) i) j
  have hline : ContDiffAt ℝ ∞ (fun t : ℝ => t • x) 0 :=
    contDiffAt_id.smul contDiffAt_const
  have hG' : ContDiffAt ℝ ∞ (fun y : E => normalGramMatrix g p y i j) ((0 : ℝ) • x) := by
    simpa only [zero_smul] using hG
  exact hG'.comp 0 hline

variable [T2Space M]

theorem deriv_normalGram_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    deriv (fun t : ℝ => normalGramMatrix g p (t • x) i j) 0 = 0 := by
  have hG := (contDiffAt_normalGram_radial_zero g p x i j).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hprod := iteratedDeriv_pow_mul_zero hG 2
  norm_num only [Nat.choose, Nat.factorial, Nat.cast_ofNat, iteratedDeriv_one, Nat.reduceSub] at hprod
  have hzero := (radialJacobi_inner_eventually_eq_normalGram g p x i j).iteratedDeriv_eq 3
  rw [radialJacobi_inner_third_derivative] at hzero
  have h := hzero.trans hprod
  linarith

theorem second_derivative_normalGram_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x) i j) 0 =
      -(2 / 3 : ℝ) * g.inner p
        (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x)
        (chartModelBasis E j) := by
  have hG := (contDiffAt_normalGram_radial_zero g p x i j).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hprod := iteratedDeriv_pow_mul_zero hG 2
  norm_num only [Nat.choose, Nat.factorial, Nat.cast_ofNat, iteratedDeriv_one, Nat.reduceSub] at hprod
  have hzero := (radialJacobi_inner_eventually_eq_normalGram g p x i j).iteratedDeriv_eq 4
  rw [radialJacobi_inner_fourth_derivative] at hzero
  have h := hzero.trans hprod
  linarith

theorem fderiv_normalGram_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    fderiv ℝ (normalGramMatrix g p) 0 = 0 := by
  ext x i j
  have hG := (contDiffAt_normalGramMatrix_zero g p).differentiableAt (by simp)
  have hline := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const x) (by simp)
  have hentry := hasDerivAt_pi.mp (hasDerivAt_pi.mp hline i) j
  change (fderiv ℝ (normalGramMatrix g p) 0) x i j = (0 : ℝ)
  exact (congrArg (fun v : E => (fderiv ℝ (normalGramMatrix g p) 0) v i j)
    (one_smul ℝ x)).symm.trans
      (hentry.deriv.symm.trans (deriv_normalGram_radial_zero g p x i j))

private theorem iteratedFDeriv_two_normalGram_entry_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    iteratedFDeriv ℝ 2 (fun y => normalGramMatrix g p y i j) 0 (fun _ => x) =
      -(2 / 3 : ℝ) * g.inner p
        (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x)
        (chartModelBasis E j) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  let U := Metric.ball (0 : E) (expMapC2Radius g p)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzero : L 0 ∈ U := by simpa [L, U] using expMapC2Radius_pos g p
  have hG := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_normalGramMatrix g p) i) j
  have hcomp := L.iteratedFDerivWithin_comp_right hG hU.uniqueDiffOn
    (hU.preimage L.continuous).uniqueDiffOn hzero (i := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [iteratedFDerivWithin_of_isOpen 2 (hU.preimage L.continuous) hzero,
    iteratedFDerivWithin_of_isOpen 2 hU hzero] at hcomp
  have h := congrArg (fun B => B (fun _ : Fin 2 => (1 : ℝ))) hcomp
  have heq : iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x) i j) 0 =
      iteratedFDeriv ℝ 2 (fun y => normalGramMatrix g p y i j) 0 (fun _ => x) := by
    simpa only [iteratedDeriv_eq_iteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, zero_smul, one_smul,
      Function.comp_def, L] using h
  exact heq.symm.trans (second_derivative_normalGram_radial_zero g p x i j)

theorem iteratedFDeriv_two_normalGram_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    iteratedFDeriv ℝ 2 (normalGramMatrix g p) 0 (fun _ => x) i j =
      -(2 / 3 : ℝ) * g.inner p
        (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x)
        (chartModelBasis E j) := by
  let P : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →L[ℝ]
      (Fin (Module.finrank ℝ E) → ℝ) := ContinuousLinearMap.proj i
  let Q : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let A := Q.comp P
  have hA := A.iteratedFDeriv_comp_left (contDiffAt_normalGramMatrix_zero g p) (i := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h := congrArg (fun B => B (fun _ : Fin 2 => x)) hA
  have heq : iteratedFDeriv ℝ 2 (fun y => normalGramMatrix g p y i j) 0 (fun _ => x) =
      iteratedFDeriv ℝ 2 (normalGramMatrix g p) 0 (fun _ => x) i j := by
    exact h
  exact heq.symm.trans (iteratedFDeriv_two_normalGram_entry_zero g p x i j)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
