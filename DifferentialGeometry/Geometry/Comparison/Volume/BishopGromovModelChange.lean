import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Curvature.RicciPullback
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace

/-!
# Bishop–Gromov across a linear change of model

The abstract local Bishop–Gromov comparison (`localBishopGromov_cross`,
`localBishopGromov_absolute_upper`) is stated for a model vector space carrying an inner product.
Product models such as `(𝓡 1).prod (𝓡 1)` (vector space `E₁ × E₁` with the sup norm) carry none.
This module transfers the comparison to any boundaryless model `I` on a finite-dimensional `E` that
admits a continuous linear equivalence `e : E ≃L[ℝ] F` to an inner-product space `F`.

Method: `I' = I.transContinuousLinearEquiv e` has the same charts; the identity map is a
diffeomorphism `Φ : (M, I') ≃ (M, I)` (Mathlib's `toTransContinuousLinearEquiv`), and the pulled
back metric `g' = Φ^* g` has the same length distance (`riemannianEDistOf_pullbackMetricCross`),
the same volume measure (`riemannianVolumeMeasure_pullback_cross`) and the same Ricci tensor up to
`dΦ` (`ricciTensor_pullbackMetricCross`). The manifold carries only its topology in the
statements; the metric-space structure needed by the abstract kernel is the induced one
(`inducedEMetricSpace g'`), installed inside the proof, so no competing (pseudo-)emetric instance
of the carrier (for instance the product one of `Circle × Circle`) is ever used.
The balls are those of `g`'s own length distance (`Collapse.ballVolume`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [FiniteDimensional ℝ F] in
/-- The transported model `I.transContinuousLinearEquiv e` of a boundaryless model is boundaryless. -/
theorem boundaryless_transContinuousLinearEquiv (e : E ≃L[ℝ] F) :
    (I.transContinuousLinearEquiv e).Boundaryless := by
  refine ⟨?_⟩
  rw [ModelWithCorners.transContinuousLinearEquiv_range, ModelWithCorners.range_eq_univ,
    image_univ, e.surjective.range_eq]

/-- Bishop–Gromov (cross form and absolute upper bound) for a boundaryless model whose vector
space is only linearly equivalent to an inner-product space. Balls and volumes are those of `g`
itself; `n = finrank E`. -/
theorem bishopGromov_of_continuousLinearEquiv [ConnectedSpace M] (e : E ≃L[ℝ] F)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hRic : BonnetMyers.RicciBoundedBelow g (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K)) (p : M) :
    (∀ {s R : ℝ}, 0 < s → s ≤ R → ENNReal.ofReal R ≤ bishopGromovRadius K ⊤ →
      Collapse.ballVolume g p R * ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s) ≤
        ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R) * Collapse.ballVolume g p s) ∧
    (∀ {R : ℝ}, 0 < R → ENNReal.ofReal R ≤ bishopGromovRadius K ⊤ →
      Collapse.ballVolume g p R ≤ ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R)) := by
  let I' : ModelWithCorners ℝ F H := I.transContinuousLinearEquiv e
  let : I'.Boundaryless := boundaryless_transContinuousLinearEquiv e
  let Φ : M ≃ₘ⟮I', I⟯ M := (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm
  let g' : SmoothRiemannianMetric I' M := Diffeomorph.pullbackMetricCross g Φ
  have hdist (x y : M) : riemannianEDistOf (I := I') g' x y = riemannianEDistOf (I := I) g x y :=
    riemannianEDistOf_pullbackMetricCross g Φ x y
  have hvol : riemannianVolumeMeasure I' M g' = riemannianVolumeMeasure I M g := by
    rw [riemannianVolumeMeasure_pullback_cross]
    exact Measure.map_id
  have hball (r : ℝ) : Collapse.ballVolume g' p r = Collapse.ballVolume g p r := by
    simp only [Collapse.ballVolume, riemannianBallOf, hdist, hvol]
  have hfin : Module.finrank ℝ F = Module.finrank ℝ E := e.finrank_eq.symm
  let : NeZero (Module.finrank ℝ F) := ⟨by rw [hfin]; exact NeZero.ne _⟩
  have hRic' : BonnetMyers.RicciBoundedBelow g' (((Module.finrank ℝ F - 1 : ℕ) : ℝ) * K) := by
    intro x v
    rw [ricciTensor_pullbackMetricCross, Diffeomorph.pullbackMetricCross_inner, hfin]
    exact hRic (Φ x) _
  let : EMetricSpace M := inducedEMetricSpace g'
  let : RiemannianBundle (fun x : M => TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  let : IsRiemannianManifold I' M := inducedEMetricSpace_isRiemannianManifold g'
  let : IsContinuousRiemannianBundle F (fun x : M => TangentSpace I' x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g'
  have hEnorm : IsMetricNorm (I := I') (M := M) g' := isMetricNorm_of_smoothRiemannianMetric g'
  let : CompleteSpace M := inducedEMetricSpace_completeSpace g'
  let R₀ : Set.Ioi (0 : ℝ≥0∞) := ⟨⊤, ENNReal.zero_lt_top⟩
  have hRicOn := ricciBoundedBelowOn_of_global
    (s := {y : M | riemannianEDist I' p y < R₀.1}) hRic'
  refine ⟨fun {s R} hs hsR hR => ?_, fun {R} hRpos hR => ?_⟩
  · have h := localBishopGromov_cross g' hEnorm p K R₀ hRicOn hs hsR hR
    rw [← collapseBallVolume_eq_comparison g' hEnorm, ← collapseBallVolume_eq_comparison g' hEnorm,
      hball, hball, hfin] at h
    exact h
  · have h := localBishopGromov_absolute_upper g' hEnorm p K R₀ hRicOn hRpos hR
    rw [← collapseBallVolume_eq_comparison g' hEnorm, hball, hfin] at h
    exact h

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
