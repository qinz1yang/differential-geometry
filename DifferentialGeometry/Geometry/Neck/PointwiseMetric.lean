import DifferentialGeometry.Geometry.Neck.PointwiseChart
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance (O : Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

def pointwiseMetric (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (H : SmoothRiemannianMetric IC (openCylinder L)) :
    SmoothRiemannianMetric IC (bufferedCylinder d) :=
  Diffeomorph.pullbackMetric
    (H.restrictOpenOfSubset (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL))
    (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d))

theorem pointwiseMetric_inner (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (H : SmoothRiemannianMetric IC (openCylinder L))
    (x : bufferedCylinder d) (v w : TangentSpace IC x) :
    (pointwiseMetric e z₀ hfit hBL H).inner x v w =
      H.inner (pointwiseCylinderMap e z₀ hfit hBL x)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x v)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x w) := by
  rw [pointwiseMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictSubset_inner]
  rw [roundCylinderRestrict_mfderiv, roundCylinderRestrict_mfderiv,
    pointwiseCylinderMap_mfderiv, pointwiseCylinderMap_mfderiv]
  rfl

theorem pointwiseMetric_reference (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    pointwiseMetric e z₀ hfit hBL
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)) =
      referenceMetric d := by
  rw [pointwiseMetric, SmoothRiemannianMetric.restrictOpen_flat]
  exact pullback_roundCylinderMetric_roundCylinderRestrict e z₀ (bufferedCylinder d)

theorem metricDerivNorm_pointwiseMetric (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (H HInf : SmoothRiemannianMetric IC (openCylinder L)) (j : ℕ)
    (x : bufferedCylinder d) :
    metricDerivNorm j (pointwiseMetric e z₀ hfit hBL H)
      (pointwiseMetric e z₀ hfit hBL HInf) (referenceMetric d) x =
    metricDerivNorm j H HInf
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
      (pointwiseCylinderMap e z₀ hfit hBL x) := by
  have h := metricDerivNorm_pullback
    (H.restrictOpenOfSubset (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL))
    (HInf.restrictOpenOfSubset (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL))
    (((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)).restrictOpenOfSubset
      (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL))
    (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)) j x
  rw [metricDerivNorm_flat] at h
  change metricDerivNorm j (pointwiseMetric e z₀ hfit hBL H)
    (pointwiseMetric e z₀ hfit hBL HInf)
    (pointwiseMetric e z₀ hfit hBL
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))) x = _ at h
  rw [pointwiseMetric_reference] at h
  exact h

theorem metricDerivENormSupOn_pointwiseMetric (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (H HInf : SmoothRiemannianMetric IC (openCylinder L))
    (K : Set (bufferedCylinder d)) (p : ℕ) :
    metricDerivENormSupOn K p (pointwiseMetric e z₀ hfit hBL H)
      (pointwiseMetric e z₀ hfit hBL HInf) (referenceMetric d) =
    metricDerivENormSupOn (pointwiseCylinderMap e z₀ hfit hBL '' K) p H HInf
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pointwiseMetric, iSup_image]

theorem pointwiseMetric_error_lt (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (H : SmoothRiemannianMetric IC (openCylinder L)) (k : ℕ) {η : ℝ}
    (hsmall : metricDerivENormSupOn {q : openCylinder L | q.val.2 ∈ Icc (-B) B} k H
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)) < ENNReal.ofReal η) :
    metricDerivENormSupOn (controlledCylinder d) k (pointwiseMetric e z₀ hfit hBL H)
      (referenceMetric d) (referenceMetric d) < ENNReal.ofReal η := by
  have h := metricDerivENormSupOn_pointwiseMetric e z₀ hfit hBL H
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
    (controlledCylinder d) k
  rw [pointwiseMetric_reference] at h
  rw [h]
  exact (metricDerivENormSupOn_mono
    (image_pointwiseCylinderMap_controlledCylinder_subset e z₀ hfit hBL) le_rfl H
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))).trans_lt hsmall

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem original_local {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hm : ∀ x, Injective (mfderiv IC I Φ x)) :
    IsLocalDiffeomorph IC I ∞ Φ :=
  isLocalDiffeomorph_of_injective_mfderiv Φ hΦ hm (by
    rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp)

omit [T2Space M] in
private theorem pointwise_local {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hm : ∀ x, Injective (mfderiv IC I Φ x))
    (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    IsLocalDiffeomorph IC I ∞ (pointwiseChart Φ e z₀ hfit hBL) :=
  isLocalDiffeomorph_of_injective_mfderiv _ (contMDiff_pointwiseChart Φ hΦ e z₀ hfit hBL)
    (immersion_pointwiseChart Φ hΦ hm e z₀ hfit hBL) (by
      rw [show Module.finrank ℝ E = 3 from Fact.out]
      simp)

theorem scale_pointwiseMetric_eq_pullback {L : ℝ}
    (g : SmoothRiemannianMetric I M) (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hinj : Injective Φ)
    (hm : ∀ x, Injective (mfderiv IC I Φ x)) (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (q : ℝ) (hq : 0 < q) (qNew : ℝ) (hqNew : 0 < qNew) :
    scaleMetric (qNew / q) (div_pos hqNew hq)
      (pointwiseMetric e z₀ hfit hBL
        (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ
          (original_local Φ hΦ hm) hinj)) =
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric qNew hqNew g)
      (pointwiseChart Φ e z₀ hfit hBL) (pointwise_local Φ hΦ hm e z₀ hfit hBL)
      (injective_pointwiseChart Φ hinj e z₀ hfit hBL) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, pointwiseMetric_inner,
    pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner,
    pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
  have hd := hΦ.mdifferentiable (by simp)
  have hc := (contMDiff_pointwiseCylinderMap e z₀ hfit hBL).mdifferentiable (by simp)
  rw [pointwiseChart, mfderiv_comp x (hd _) (hc _)]
  change qNew / q * (q * g.inner (Φ (pointwiseCylinderMap e z₀ hfit hBL x))
      (mfderiv IC I Φ (pointwiseCylinderMap e z₀ hfit hBL x)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x v))
      (mfderiv IC I Φ (pointwiseCylinderMap e z₀ hfit hBL x)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x w))) =
    qNew * g.inner (Φ (pointwiseCylinderMap e z₀ hfit hBL x))
      (mfderiv IC I Φ (pointwiseCylinderMap e z₀ hfit hBL x)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x v))
      (mfderiv IC I Φ (pointwiseCylinderMap e z₀ hfit hBL x)
        (mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) x w))
  field_simp [ne_of_gt hq]

end DifferentialGeometry.Geometry.Neck
