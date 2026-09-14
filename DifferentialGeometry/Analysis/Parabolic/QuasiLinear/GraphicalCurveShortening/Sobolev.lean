import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients
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
