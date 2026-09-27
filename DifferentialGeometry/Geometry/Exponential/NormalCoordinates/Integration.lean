import DifferentialGeometry.Geometry.Exponential.VolumeDensity

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential NormalCoordinates Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : MeasurableSet K) (hKdom : K ⊆ expDomain (I := I) g p) :
    (∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) v)
      ∂(modelHaar (E := E))) =
    ∫⁻ w in (euclideanNormalFrame (I := I) g p) ⁻¹' K,
      ENNReal.ofReal (curveDensity (I := I) g
        (radialCurve (I := I) g p (euclideanNormalFrame (I := I) g p w))
        (fun i => radialJacobiField (I := I) g p (euclideanNormalFrame (I := I) g p w)
          (normalBasis (I := I) g p i)) 1)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := normalBasis (I := I) g p
  let L : F ≃L[ℝ] E := euclideanNormalFrame (I := I) g p
  let D : E → ℝ := fun v => curveDensity (I := I) g (radialCurve (I := I) g p v)
    (fun i => radialJacobiField (I := I) g p v (b i)) 1
  have hbmap :
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map L.toLinearEquiv = b := by
    ext i
    change euclideanNormalFrame (I := I) g p
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i) = normalBasis (I := I) g p i
    simpa only [EuclideanSpace.basisFun_apply] using euclideanNormalFrame_single g p i
  have hmap : Measure.map L (volume : Measure F) = b.addHaar := by
    calc
      _ = Measure.map L (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.addHaar := by
        rw [(EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume]
      _ = ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
          L.toLinearEquiv).addHaar := Module.Basis.map_addHaar _ _
      _ = b.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure F) b.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [lintegral_paramDensity_expMap_eq_lintegral_curveDensity_addHaar (I := I) g p b hK hKdom]
  exact (hmp.setLIntegral_comp_preimage_emb L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => ENNReal.ofReal (D v)) K).symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
