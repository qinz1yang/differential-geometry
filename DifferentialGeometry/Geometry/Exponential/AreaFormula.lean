import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Multiplicity
import DifferentialGeometry.Geometry.Exponential.VolumeDensity

noncomputable section

open Set Function Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential NormalCoordinates Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_encard_fiber_framedExpMap_eq_lintegral_curveDensity
    (g : SmoothRiemannianMetric I M) (p : M)
    {U : Set E} (hU : MeasurableSet U)
    (hdom : ∀ w ∈ U,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p)
    (hloc : IsLocallyInjective
      (U.domRestrict (framedExpMap (I := I) (E := E) g p))) :
    ∫⁻ y, {w : E | w ∈ U ∧
        framedExpMap (I := I) (E := E) g p w = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ w in U, ENNReal.ofReal
        (curveDensity (I := I) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p w))
          (fun i => radialJacobiField (I := I) g p
            (normalFrame (I := I) (E := E) g p w)
            (normalBasis (I := I) g p i)) 1) ∂(volume : Measure E) := by
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let K : Set E := L '' U
  let F : E → M := fun v =>
    expMap (I := I) g p (show TangentSpace I p from v)
  have hK : MeasurableSet K :=
    L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hU
  have hKdom : K ⊆ expDomain (I := I) g p := by
    rintro v ⟨w, hw, rfl⟩
    exact hdom w hw
  let e : U ≃ₜ K := L.toHomeomorph.image U
  have hFloc : IsLocallyInjective (K.domRestrict F) := by
    have hc := hloc.comp_right e.symm.continuous e.symm.injective
    have heq : (U.domRestrict (framedExpMap (I := I) (E := E) g p)) ∘ e.symm =
        K.domRestrict F := by
      funext v
      change F (L (e.symm v)) = F v
      exact congrArg F (congrArg Subtype.val (e.apply_symm_apply v))
    rw [heq] at hc
    exact hc
  have hcard (y : M) :
      {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y}.encard =
        {v : E | v ∈ K ∧ F v = y}.encard := by
    have hset : {v : E | v ∈ K ∧ F v = y} =
        L '' {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y} := by
      ext v
      constructor
      · rintro ⟨⟨w, hw, rfl⟩, hwy⟩
        exact ⟨w, ⟨hw, hwy⟩, rfl⟩
      · rintro ⟨w, ⟨hw, hwy⟩, rfl⟩
        exact ⟨⟨w, hw, rfl⟩, hwy⟩
    rw [hset, L.injective.encard_image]
  have hpre : (normalFrame (I := I) (E := E) g p) ⁻¹' K = U :=
    Set.preimage_image_eq U L.injective
  calc
    _ = ∫⁻ y, {v : E | v ∈ K ∧ F v = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      apply lintegral_congr
      intro y
      exact congrArg ENat.toENNReal (hcard y)
    _ = ∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g F v)
        ∂(modelHaar (E := E)) :=
      lintegral_encard_fiber_eq_lintegral_paramDensity (I := I) g
        (isOpen_expDomain (I := I) g p) hK hKdom
        ((contMDiffOn_expMap (I := I) g p).of_le (by norm_num)) hFloc
    _ = _ := by
      have h := lintegral_paramDensity_expMap_eq_lintegral_curveDensity
        (I := I) g p hK hKdom
      rw [hpre] at h
      exact h

theorem mul_riemannianVolumeMeasure_le_lintegral_curveDensity_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M)
    {U : Set E} (hU : MeasurableSet U)
    (hdom : ∀ w ∈ U,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p)
    (hloc : IsLocallyInjective
      (U.domRestrict (framedExpMap (I := I) (E := E) g p)))
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hcount : ∀ y ∈ S, m ≤
      {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y}.encard) :
    m.toENNReal * riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∫⁻ w in U, ENNReal.ofReal
        (curveDensity (I := I) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p w))
          (fun i => radialJacobiField (I := I) g p
            (normalFrame (I := I) (E := E) g p w)
            (normalBasis (I := I) g p i)) 1) ∂(volume : Measure E) := by
  calc
    _ = ∫⁻ _ in S, m.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      (setLIntegral_const S m.toENNReal).symm
    _ ≤ ∫⁻ y in S,
        {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_mono' hS (fun y hy => ENat.toENNReal_mono (hcount y hy))
    _ ≤ ∫⁻ y,
        {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_le_lintegral S _
    _ = _ :=
      lintegral_encard_fiber_framedExpMap_eq_lintegral_curveDensity (I := I) g p
        hU hdom hloc

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
