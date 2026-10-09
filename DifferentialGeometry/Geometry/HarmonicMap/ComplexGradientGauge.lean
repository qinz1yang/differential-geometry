import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientEquation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.SmallBallGauge

set_option autoImplicit false
noncomputable section

open Set Metric Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual coefficient matrix of the chart complex-gradient equation,
acting on the ordinary finite product of complex coordinate spaces. -/
def chartComplexGradientOperator
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (p : M) (U : ℂ → M) (z : ℂ) :
    (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
      (Fin (Module.finrank ℝ E) → ℂ) :=
  ∑ k : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      chartComplexGradientCoefficient g p U k j z •
        ((ContinuousLinearMap.single ℂ
            (fun _ : Fin (Module.finrank ℝ E) => ℂ) k).comp
          (ContinuousLinearMap.proj j :
            (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ] ℂ))

/-- The operator uses the original coefficient indices without a transpose. -/
theorem chartComplexGradientOperator_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (p : M) (U : ℂ → M) (z : ℂ)
    (v : Fin (Module.finrank ℝ E) → ℂ)
    (k : Fin (Module.finrank ℝ E)) :
    chartComplexGradientOperator g p U z v k =
      ∑ j, chartComplexGradientCoefficient g p U k j z * v j := by
  simp [chartComplexGradientOperator, ContinuousLinearMap.comp_apply,
    Pi.single_apply, smul_eq_mul]

/-- Smoothness of the same scalar chart coefficients gives smoothness of their
finite complex-linear operator assembly. -/
theorem contDiffOn_chartComplexGradientOperator
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (p : M) (hsrc : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (chartComplexGradientOperator g p U) s := by
  unfold chartComplexGradientOperator
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.sum
  intro j _
  exact (contDiffOn_chartComplexGradientCoefficient g hs hU p hsrc k j).smul_const _

/-- The original Morrey disk has a continuous unit-valued integral gauge for its
actual chart coefficient on a buffered interior disk. The same gauge supplies
the Hölder integrand for the separate interior regularity theorem. -/
theorem IsMorreyDisk.exists_small_ball_complex_gradient_gauge
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ (R : ℝ) (hR : 0 < R),
      closedBall a (2 * R) ⊆ ball (0 : ℂ) 1 ∧
      (∀ z ∈ closedBall a (2 * R),
        diskExtension u z ∈ (chartAt E (diskExtension u a)).source) ∧
      ∃ A_R : C(closedBall a R,
          (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
            (Fin (Module.finrank ℝ E) → ℂ)),
        (∀ z : closedBall a R,
          A_R z = chartComplexGradientOperator g
            (diskExtension u a) (diskExtension u) (z : ℂ)) ∧
        4 * R * ‖A_R‖ < (1 / 4 : ℝ) ∧
        ∃ P : C(closedBall a R,
            (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
              (Fin (Module.finrank ℝ E) → ℂ)),
          P = 1 + DifferentialGeometry.Analysis.diskCauchyTransform
            a R hR (A_R * P) ∧
          ‖P - 1‖ ≤ (4 * R * ‖A_R‖) / (1 - 4 * R * ‖A_R‖) ∧
          ‖P‖ ≤ 2 ∧
          (∀ z : closedBall a R, IsUnit (P z)) ∧
          (∀ z w : closedBall a R,
            ‖P z - P w‖ ≤
              16 * Real.sqrt R * ‖A_R * P‖ *
                Real.sqrt ‖(z : ℂ) - (w : ℂ)‖) ∧
          (∃ H : ℝ≥0,
            HolderWith H (1 / 2 : ℝ≥0)
              (fun z : closedBall a R => A_R z * P z)) ∧
          (let P₀ : ℂ →
              ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                (Fin (Module.finrank ℝ E) → ℂ)) := fun z =>
            1 + (Real.pi : ℂ)⁻¹ •
              ∫ w : closedBall a R,
                (z - (w : ℂ))⁻¹ • (A_R w * P w)
                ∂(volume.comap ((↑) : closedBall a R → ℂ))
           (∀ z : closedBall a R, P₀ (z : ℂ) = P z) ∧
             ∀ z ∈ closedBall a R, IsUnit (P₀ z)) := by
  let U := diskExtension u
  let p := U a
  let s := ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (ball (0 : ℂ) 1) :=
    hu.smoothInterior
  have hs : IsOpen s := hU.continuousOn.isOpen_inter_preimage isOpen_ball
    (chartAt E p).open_source
  have has : a ∈ s := ⟨ha, mem_chart_source E (U a)⟩
  have hsub : s ⊆ ball (0 : ℂ) 1 := inter_subset_left
  have hsrc : ∀ z ∈ s, U z ∈ (chartAt E p).source := fun _ hz => hz.2
  have hA : ContDiffOn ℝ 1 (chartComplexGradientOperator g p U) s :=
    (contDiffOn_chartComplexGradientOperator g hs (hU.mono hsub) p hsrc).of_le
      (by norm_num)
  obtain ⟨R, hR, hbuffer, A_R, hA_R, hsmall, hP⟩ :=
    DifferentialGeometry.Analysis.exists_small_ball_unit_integral_gauge hs has
      (chartComplexGradientOperator g p U) hA
  refine ⟨R, hR, ?_, ?_, A_R, hA_R, hsmall, hP⟩
  · exact fun z hz => (hbuffer hz).1
  · exact fun z hz => (hbuffer hz).2

end DifferentialGeometry.Geometry
