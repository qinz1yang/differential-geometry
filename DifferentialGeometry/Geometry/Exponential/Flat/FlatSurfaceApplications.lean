import DifferentialGeometry.Geometry.Exponential.Flat.SegmentShift
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.TranslationExclusion

/-!
# Consumers of SF4(a)–(b)

* `flat_false_of_endpoint_interval_model`: LFR23's torus exclusion for a SMOOTH complete flat
  orientable surface — SF-B's segment-shift producer feeds W4-F7c's `false_of_translation_of_lt`.
  (LFR23's own binding needs the same producer for the `C^m` metric `k`: lane SF-FT.)
* `isZLattice_intSpan_euclidean`: the plane-lattice lemma on the standard lattice `ℤ²` of the
  Euclidean plane (cocompactness via `ZSpan.fract`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- LFR23's torus exclusion, smooth flat form: a complete flat orientable smooth surface with a
segment of length `5` from `z₀` carries no based interval model of distortion `δ < 5/3`. -/
theorem flat_false_of_endpoint_interval_model (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hq0 : q z₀ = 0) (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hδ : δ < 5 / 3) {γ : ℝ → M} (hγ0 : γ 0 = z₀)
    (hγ : ∀ t ∈ Icc 0 5, ∀ t' ∈ Icc 0 5, dist (γ t) (γ t') = |t - t'|) : False := by
  have h5 : (2 : ℝ) * (5 / 2) = 5 := by norm_num
  obtain ⟨τ, hτ0, hτs⟩ := flat_exists_isometryEquiv_shift_segment_dist (I := I) hdim o g hEnorm hR
    (s := 5 / 2) (by norm_num) (by rw [h5]; exact hγ)
  rw [h5] at hτs
  exact DifferentialGeometry.Geometry.Collapse.false_of_translation_of_lt hq0 hqnn hdist hδ hγ0 hγ
    τ (by rw [← hγ0]; exact hτ0) hτs

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.FlatSurface

/-- Concrete consumer of the lattice lemma: the standard `ℤ²` in the Euclidean plane. -/
theorem isZLattice_intSpan_euclidean :
    IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)) := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  refine isZLattice_of_cocompact _ (R := ∑ i, ‖b i‖) fun y => ?_
  refine ⟨ZSpan.floor b y, (ZSpan.floor b y).2, ?_⟩
  rw [← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b y

/-- Concrete consumer of the planar translation lemma: a nonzero translation of the plane. -/
theorem translation_apply_eq_add_example (c : EuclideanSpace ℝ (Fin 2)) (hc : c ≠ 0)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) c) y =
      y + (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) c) 0 := by
  refine apply_eq_add_of_fixedPoint_free (by simp) _ ?_ ?_ y
  · have hL : (((AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) c).linearIsometryEquiv :
        EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = LinearMap.id := by
      ext v : 1
      simp [AffineIsometryEquiv.linearIsometryEquiv, AffineIsometryEquiv.constVAdd]
    rw [hL, LinearMap.det_id]
    exact one_pos
  · intro z hz
    apply hc
    simpa using hz

end DifferentialGeometry.Geometry.FlatSurface
