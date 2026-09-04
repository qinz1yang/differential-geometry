import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.GalerkinSobolevFourBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.GalerkinSobolevThreeBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (finiteEigenComboHs smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem galerkin_background_action_sobolev_three_four_pairing_bounds_of_low_view_norm_le
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η3 η4 : ℝ}, 0 < η3 → 0 < η4 →
      ∃ δ R0 : ℝ, 0 < δ ∧ δ ≤ 1 / 3 ∧ 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G3 G4 : ℝ, 0 ≤ G3 ∧ 0 ≤ G4 ∧
            (∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hδ_lt : δ < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) δ),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galerkinLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hδ_lt hreal F c).coeff i)| ≤
                  η3 * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                  G3 * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2)) ∧
            (∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hδ_lt : δ < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) δ),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galerkinLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hδ_lt hreal F c).coeff i)| ≤
                  η4 * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
                  G4 * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) *
                      (∑ i ∈ F,
                        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                          (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2)) := by
  intro η3 η4 hη3 hη4
  obtain ⟨δ3, hδ3, hδ3third, hpair3⟩ :=
    galerkin_background_action_sobolev_three_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ hη3
  obtain ⟨δ4, hδ4, hδ4third, hpair4⟩ :=
    galerkin_background_action_sobolev_four_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ hη4
  let δ : ℝ := min δ3 δ4
  have hδ : 0 < δ := lt_min hδ3 hδ4
  have hδthird : δ ≤ 1 / 3 := (min_le_left δ3 δ4).trans hδ3third
  obtain ⟨R3, hR3, hR3one, hpair3δ⟩ := hpair3 hδ (min_le_left δ3 δ4)
  obtain ⟨R4, hR4, hR4one, hpair4δ⟩ := hpair4 hδ (min_le_right δ3 δ4)
  let R0 : ℝ := min R3 R4
  have hR0 : 0 < R0 := lt_min hR3 hR4
  have hR0one : R0 ≤ 1 := (min_le_left R3 R4).trans hR3one
  refine ⟨δ, R0, hδ, hδthird, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨G3, hG3, hpair3G⟩ := hpair3δ g hEq hjet
  obtain ⟨G4, hG4, hpair4G⟩ := hpair4δ g hEq hjet
  refine ⟨G3, G4, hG3, hG4, ?_, ?_⟩
  · intro R hR hRR0 hδ_lt hreal F c hmem
    exact hpair3G hR (hRR0.trans (min_le_left R3 R4)) hδ_lt hreal F c hmem
  · intro R hR hRR0 hδ_lt hreal F c hmem
    exact hpair4G hR (hRR0.trans (min_le_right R3 R4)) hδ_lt hreal F c hmem

theorem galerkin_background_action_sobolev_three_four_pairing_bounds_of_low_view_norm_le_with_caps
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ δcap Rcap : ℝ} (hΛ : 1 ≤ Λ)
    (hδcap : 0 < δcap) (hRcap : 0 < Rcap) :
    ∃ δ R0 : ℝ, 0 < δ ∧ δ ≤ 1 / 3 ∧ δ ≤ δcap ∧
      0 < R0 ∧ R0 ≤ 1 ∧ R0 ≤ Rcap ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G3 G4 : ℝ, 0 ≤ G3 ∧ 0 ≤ G4 ∧
            (∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hδ_lt : δ < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) δ),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galerkinLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hδ_lt hreal F c).coeff i)| ≤
                  (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                  G3 * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2)) ∧
            (∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hδ_lt : δ < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) δ),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galerkinLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hδ_lt hreal F c).coeff i)| ≤
                  (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
                  G4 * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) *
                      (∑ i ∈ F,
                        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                          (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2)) := by
  obtain ⟨δ3, hδ3, hδ3third, hpair3⟩ :=
    galerkin_background_action_sobolev_three_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ one_pos
  obtain ⟨δ4, hδ4, _hδ4third, hpair4⟩ :=
    galerkin_background_action_sobolev_four_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ one_pos
  let δ : ℝ := min (min δ3 δ4) δcap
  have hδ : 0 < δ := lt_min (lt_min hδ3 hδ4) hδcap
  have hδ3le : δ ≤ δ3 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ4le : δ ≤ δ4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδthird : δ ≤ 1 / 3 := hδ3le.trans hδ3third
  have hδcaple : δ ≤ δcap := min_le_right _ _
  obtain ⟨R3, hR3, hR3one, hpair3δ⟩ := hpair3 hδ hδ3le
  obtain ⟨R4, hR4, _hR4one, hpair4δ⟩ := hpair4 hδ hδ4le
  let R0 : ℝ := min (min R3 R4) Rcap
  have hR0 : 0 < R0 := lt_min (lt_min hR3 hR4) hRcap
  have hR0one : R0 ≤ 1 :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans hR3one
  have hR0cap : R0 ≤ Rcap := min_le_right _ _
  refine ⟨δ, R0, hδ, hδthird, hδcaple, hR0, hR0one, hR0cap, ?_⟩
  intro g hEq hjet
  obtain ⟨G3, hG3, hpair3G⟩ := hpair3δ g hEq hjet
  obtain ⟨G4, hG4, hpair4G⟩ := hpair4δ g hEq hjet
  refine ⟨G3, G4, hG3, hG4, ?_, ?_⟩
  · intro R hR hRR0 hδ_lt hreal F c hmem
    simpa only [one_mul] using hpair3G hR
      (hRR0.trans ((min_le_left _ _).trans (min_le_left _ _)))
      hδ_lt hreal F c hmem
  · intro R hR hRR0 hδ_lt hreal F c hmem
    simpa only [one_mul] using hpair4G hR
      (hRR0.trans ((min_le_left _ _).trans (min_le_right _ _)))
      hδ_lt hreal F c hmem

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
