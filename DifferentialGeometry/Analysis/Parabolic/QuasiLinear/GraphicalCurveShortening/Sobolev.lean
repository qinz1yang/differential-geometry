import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.LocalComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.External.DeGiorgi.MoserIteration.CutoffPrep.Basics

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

private def centeredGraphDiffusionCoefficient (t : ℝ) : ℝ :=
  graphDiffusionCoefficient t - 1

private theorem centeredGraphDiffusionCoefficient_smooth :
    ContDiff ℝ (⊤ : ℕ∞) centeredGraphDiffusionCoefficient := by
  exact (contDiff_graphDiffusionCoefficient (E := ℝ)).sub contDiff_const

private theorem centeredGraphDiffusionCoefficient_zero :
    centeredGraphDiffusionCoefficient 0 = 0 := by
  simp [centeredGraphDiffusionCoefficient, graphDiffusionCoefficient]

private theorem centeredGraphDiffusionCoefficient_deriv_bound :
    ∃ M : ℝ, ∀ t, |deriv centeredGraphDiffusionCoefficient t| ≤ M := by
  refine ⟨1, ?_⟩
  intro t
  have h := norm_deriv_le_of_lipschitz (x₀ := t)
    (graphDiffusionCoefficient_lipschitz (E := ℝ))
  change |deriv (fun s : ℝ => graphDiffusionCoefficient s - 1) t| ≤ 1
  simpa only [deriv_sub_const, Real.norm_eq_abs, NNReal.coe_one] using h

private theorem deriv_centeredGraphDiffusionCoefficient (t : ℝ) :
    deriv centeredGraphDiffusionCoefficient t =
      -2 * graphDiffusionCoefficient t ^ 2 * t := by
  have h := ((hasDerivAt_graphDiffusionCoefficient (hasDerivAt_id t)).sub_const 1).deriv
  change deriv (fun s : ℝ => graphDiffusionCoefficient s - 1) t = _
  simpa using h

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def _root_.DeGiorgi.MemW1pWitness.graphDiffusionCoefficientSubOne
    {Ω : Set E} {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hΩ : IsOpen Ω) :
    DeGiorgi.MemW1pWitness 2 (fun x => graphDiffusionCoefficient (u x) - 1) Ω :=
  DeGiorgi.MemW1pWitness.compSmoothBounded (d := d) hΩ hu
    centeredGraphDiffusionCoefficient
    centeredGraphDiffusionCoefficient_smooth
    centeredGraphDiffusionCoefficient_zero
    centeredGraphDiffusionCoefficient_deriv_bound

theorem _root_.DeGiorgi.MemW1pWitness.graphDiffusionCoefficientSubOne_weakGrad
    {Ω : Set E} {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hΩ : IsOpen Ω) (x : E) :
    (hu.graphDiffusionCoefficientSubOne hΩ).weakGrad x =
      (-2 * graphDiffusionCoefficient (u x) ^ 2 * u x) • hu.weakGrad x := by
  ext i
  change deriv centeredGraphDiffusionCoefficient (u x) * hu.weakGrad x i = _
  rw [deriv_centeredGraphDiffusionCoefficient]
  rfl

theorem graphDiffusionCoefficient_sub_one_memW1p
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) :
    DeGiorgi.MemW1p 2 (fun x => graphDiffusionCoefficient (u x) - 1) Ω :=
  (hu.someWitness.graphDiffusionCoefficientSubOne hΩ).memW1p


theorem hasWeakPartialDeriv_graphDiffusionCoefficient_sub_one
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (-2 * graphDiffusionCoefficient (u x) ^ 2 * u x) * hu.weakGrad x i)
      (fun x => graphDiffusionCoefficient (u x) - 1) Ω := by
  have h := (hu.graphDiffusionCoefficientSubOne hΩ).isWeakGrad i
  simpa only [DeGiorgi.MemW1pWitness.graphDiffusionCoefficientSubOne_weakGrad,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h

theorem graphDiffusionCoefficient_memW1p
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)] (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) :
    DeGiorgi.MemW1p 2 (fun x => graphDiffusionCoefficient (u x)) Ω := by
  have h := ((hu.someWitness.graphDiffusionCoefficientSubOne hΩ).subConst
    hΩ (-1)).memW1p
  simpa only [sub_neg_eq_add, sub_add_cancel] using h

end DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem exists_graphDiffusionCoefficient_h1_on_closedBall
    {ι : Type*} [Fintype ι] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ alpha : Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
          TensorHs g 0 0 1,
        LipschitzWith C alpha ∧
        ∀ v x, scalarH1ToContinuous g (alpha v) x =
          graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι =>
            scalarH1ToContinuous g
              (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
                (AddCircle.parameterDerivativeHsPi g 1 (f₀ + v.val) i)) x)) := by
  let D : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 1) :=
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1))).comp
        (AddCircle.parameterDerivativeHsPi g 1)
  let F : (ι → ℝ) → ℝ := fun p => graphDiffusionCoefficient (WithLp.toLp 2 p)
  have hF : ContDiff ℝ ∞ F := contDiff_graphDiffusionCoefficient.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff
  obtain ⟨r, hr, C, N, hN, _, hNe, _⟩ := exists_scalarH1_composition_on_ball
    g F hF.contDiffOn isOpen_univ (D f₀) (subset_univ _)
  let R := r / (2 * (‖D‖ + 1))
  have hR : 0 < R := div_pos hr (by positivity)
  let S := Metric.closedBall
    (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R
  have hmap (v : S) : D (f₀ + v.val) ∈ Metric.ball (D f₀) r := by
    have hv : ‖v.val‖ ≤ R := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right] using v.property
    have hmul : ‖D‖ * R < r := by
      have hden : 0 < 2 * (‖D‖ + 1) := by positivity
      dsimp only [R]
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith only [hr, norm_nonneg D, mul_pos hr (show 0 < ‖D‖ + 2 by positivity)]
    rw [Metric.mem_ball, dist_eq_norm, map_add, add_sub_cancel_left]
    exact (D.le_opNorm v.val).trans_lt
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg D)).trans_lt hmul)
  let A : S → Metric.ball (D f₀) r := fun v => ⟨D (f₀ + v.val), hmap v⟩
  have hA : LipschitzWith ‖D‖₊ A := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change dist (D (f₀ + v.val)) (D (f₀ + w.val)) ≤ ‖D‖ * dist v.val w.val
    exact (D.dist_le_opNorm _ _).trans_eq (by rw [dist_add_left])
  refine ⟨R, hR, C * ‖D‖₊, fun v => N (A v), hN.comp hA, ?_⟩
  intro v x
  exact hNe (A v) x

end DifferentialGeometry.Analysis.Parabolic
