import DifferentialGeometry.Geometry.Neck.RecenteringChart
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
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

def recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H : SmoothRiemannianMetric IC (bufferedCylinder δ)) :
    SmoothRiemannianMetric IC (bufferedCylinder ε) :=
  Diffeomorph.pullbackMetric
    (H.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε))

theorem recenteringMetric_inner {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (H : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (x : bufferedCylinder ε) (v w : TangentSpace IC x) :
    (recenteringMetric hσ hfit H).inner x v w =
      H.inner (recenteringCylinderMap hσ hfit x)
        (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v)
        (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w) := by
  rw [recenteringMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictSubset_inner]
  rw [cylinderAxialRestrict_mfderiv, cylinderAxialRestrict_mfderiv,
    recenteringCylinderMap_mfderiv, recenteringCylinderMap_mfderiv]
  rfl

theorem recenteringMetric_reference {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    recenteringMetric hσ hfit (referenceMetric δ) = referenceMetric ε := by
  rw [recenteringMetric, referenceMetric, SmoothRiemannianMetric.restrictOpen_flat]
  exact pullback_cylinderMetric_cylinderAxialRestrict
    (scaleMetric 2 (by norm_num) (roundMetric (E := E3) (n := 2))) σ σ hσ
      (bufferedCylinder ε)

theorem metricDerivNorm_recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (j : ℕ) (x : bufferedCylinder ε) :
    metricDerivNorm j (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
      (referenceMetric ε) x =
    metricDerivNorm j H HInf (referenceMetric δ) (recenteringCylinderMap hσ hfit x) := by
  have h := metricDerivNorm_pullback
    (H.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (HInf.restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    ((referenceMetric δ).restrictOpenOfSubset (cylinderAxialImage_bufferedCylinder_le hσ hfit))
    (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)) j x
  rw [metricDerivNorm_flat] at h
  change metricDerivNorm j (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
    (recenteringMetric hσ hfit (referenceMetric δ)) x = _ at h
  rw [recenteringMetric_reference] at h
  exact h

theorem metricDerivENormSupOn_recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ))
    (K : Set (bufferedCylinder ε)) (p : ℕ) :
    metricDerivENormSupOn K p (recenteringMetric hσ hfit H) (recenteringMetric hσ hfit HInf)
      (referenceMetric ε) =
    metricDerivENormSupOn (recenteringCylinderMap hσ hfit '' K) p H HInf
      (referenceMetric δ) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_recenteringMetric, iSup_image]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem recenteringMetric_error_lt (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    metricDerivENormSupOn (controlledCylinder ε) k
      (recenteringMetric hσ hfit d.normalizedMetric) (referenceMetric ε) (referenceMetric ε) <
      ENNReal.ofReal δ := by
  have h := metricDerivENormSupOn_recenteringMetric hσ hfit d.normalizedMetric
    (referenceMetric δ) (controlledCylinder ε) k
  rw [recenteringMetric_reference] at h
  rw [h]
  exact (metricDerivENormSupOn_mono
    (image_recenteringCylinderMap_controlledCylinder_subset hσ hfit) le_rfl
      d.normalizedMetric (referenceMetric δ) (referenceMetric δ)).trans_lt
    d.normalizedMetric_error_lt

private theorem recenteringMap_local (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    IsLocalDiffeomorph IC I ∞ (d.recenteringMap hσ hfit) :=
  isLocalDiffeomorph_of_injective_mfderiv _ (d.contMDiff_recenteringMap hσ hfit)
    (d.immersion_recenteringMap hσ hfit) (by
      rw [show Module.finrank ℝ E = 3 from Fact.out]
      simp)

theorem scale_recenteringMetric_eq_pullback (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (qNew : ℝ) (hqNew : 0 < qNew) :
    scaleMetric (qNew / metricScalarAt g x₀) (div_pos hqNew d.scalar_pos)
      (recenteringMetric hσ hfit d.normalizedMetric) =
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric qNew hqNew g)
      (d.recenteringMap hσ hfit) (d.recenteringMap_local hσ hfit)
      (d.injective_recenteringMap hσ hfit) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, recenteringMetric_inner, d.normalizedMetric_inner,
    pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
  have hd := d.smooth.mdifferentiable (by simp)
  have hc := (contMDiff_recenteringCylinderMap hσ hfit).mdifferentiable (by simp)
  rw [recenteringMap, mfderiv_comp x (hd _) (hc _)]
  change qNew / metricScalarAt g x₀ *
      (metricScalarAt g x₀ * g.inner (d.map (recenteringCylinderMap hσ hfit x))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w))) =
    qNew * g.inner (d.map (recenteringCylinderMap hσ hfit x))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x v))
        (mfderiv IC I d.map (recenteringCylinderMap hσ hfit x)
          (mfderiv IC IC (recenteringCylinderMap hσ hfit) x w))
  field_simp [ne_of_gt d.scalar_pos]

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
