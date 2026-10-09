import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Measure

open Integral.Measure (riemannianVolumeMeasure)

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem riemannianVolumeMeasure_image_le_of_partialDiffeomorph_metric_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {A : Set M} (hA : MeasurableSet A)
    (hAS : A ⊆ Φ.source) {Q : ℝ} (hQ : 0 < Q)
    (hquad : ∀ x ∈ A, ∀ v : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure J N h (Φ '' A) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) * riemannianVolumeMeasure I M g A := by
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let V : TopologicalSpace.Opens N := ⟨Φ '' (U : Set M), image_opens_isOpen Φ Set.Subset.rfl⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_of_isOpen J V.isOpen)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace V := borel V
  let _ : BorelSpace V := ⟨rfl⟩
  let e : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Φ Set.Subset.rfl
  let q := Diffeomorph.pullbackMetricCross (h.restrictOpen V) e
  let S : Set U := Subtype.val ⁻¹' A
  have hS : MeasurableSet S := continuous_subtype_val.measurable hA
  have hm := Integral.Measure.volumeMeasure_restrict_le (g.restrictOpen U) q hQ hS
    (fun x hx v => by
      dsimp only [q]
      rw [Diffeomorph.pullbackMetricCross_inner]
      change h.inner (Φ (x : M)) (mfderiv I J e x v) (mfderiv I J e x v) ≤
        Q * g.inner (x : M) v v
      rw [PartialDiffeomorph.mfderiv_toOpensDiffeo]
      exact hquad x hx v)
  have hbound := hm Set.univ
  simp only [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    MeasureTheory.Measure.smul_apply, smul_eq_mul] at hbound
  have hmap := Integral.Measure.riemannianVolumeMeasure_pullback_cross (h.restrictOpen V) e
  have hq : riemannianVolumeMeasure I U q S = riemannianVolumeMeasure J N h (Φ '' A) := by
    rw [show q = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e from rfl, hmap,
      MeasureTheory.Measure.map_apply (show Measurable (e.symm : V → U) from e.symm.contMDiff.continuous.measurable) hS]
    have heq : (e.symm : V → U) ⁻¹' S = (Subtype.val : V → N) ⁻¹' (Φ '' A) := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, congrArg Subtype.val (e.apply_symm_apply y)⟩
      · rintro ⟨x, hx, hxy⟩
        have he : e (⟨x, hAS hx⟩ : U) = y := Subtype.ext hxy
        change (e.symm y : M) ∈ A
        rw [← he, e.symm_apply_apply]
        exact hx
    rw [heq]
    apply riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    · have hv : MeasurableEmbedding (Subtype.val : V → N) :=
        V.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel V)
      have he : MeasurableEmbedding (e : U → V) := e.toHomeomorph.measurableEmbedding
      have hm := hv.measurableSet_image.mpr (he.measurableSet_image.mpr hS)
      have hset : (Subtype.val : V → N) '' (e '' S) = Φ '' A := by
        ext y
        constructor
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨e ⟨x, hAS hx⟩, ⟨⟨x, hAS hx⟩, hx, rfl⟩, rfl⟩
      rwa [hset] at hm
    · exact Set.image_mono hAS
  rw [hq, riemannianVolumeMeasure_restrictOpen_preimage_of_subset g U hA hAS] at hbound
  exact hbound

theorem riemannianVolumeMeasure_le_image_of_partialDiffeomorph_metric_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {A : Set M} (hA : MeasurableSet A)
    (hAS : A ⊆ Φ.source) {Q : ℝ} (hQ : 0 < Q)
    (hquad : ∀ x ∈ A, ∀ v : TangentSpace I x,
      g.inner x v v ≤ Q * h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v)) :
    riemannianVolumeMeasure I M g A ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) * riemannianVolumeMeasure J N h (Φ '' A) := by
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let V : TopologicalSpace.Opens N := ⟨Φ '' (U : Set M), image_opens_isOpen Φ Set.Subset.rfl⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_of_isOpen J V.isOpen)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace V := borel V
  let _ : BorelSpace V := ⟨rfl⟩
  let e : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Φ Set.Subset.rfl
  let q := Diffeomorph.pullbackMetricCross (h.restrictOpen V) e
  let S : Set U := Subtype.val ⁻¹' A
  have hS : MeasurableSet S := continuous_subtype_val.measurable hA
  have hm := Integral.Measure.volumeMeasure_restrict_le q (g.restrictOpen U) hQ hS
    (fun x hx v => by
      dsimp only [q]
      rw [Diffeomorph.pullbackMetricCross_inner]
      change g.inner (x : M) v v ≤
        Q * h.inner (Φ (x : M)) (mfderiv I J e x v) (mfderiv I J e x v)
      rw [PartialDiffeomorph.mfderiv_toOpensDiffeo]
      exact hquad x hx v)
  have hbound := hm Set.univ
  simp only [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    MeasureTheory.Measure.smul_apply, smul_eq_mul] at hbound
  have hmap := Integral.Measure.riemannianVolumeMeasure_pullback_cross (h.restrictOpen V) e
  have hq : riemannianVolumeMeasure I U q S = riemannianVolumeMeasure J N h (Φ '' A) := by
    rw [show q = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e from rfl, hmap,
      MeasureTheory.Measure.map_apply (show Measurable (e.symm : V → U) from e.symm.contMDiff.continuous.measurable) hS]
    have heq : (e.symm : V → U) ⁻¹' S = (Subtype.val : V → N) ⁻¹' (Φ '' A) := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, congrArg Subtype.val (e.apply_symm_apply y)⟩
      · rintro ⟨x, hx, hxy⟩
        have he : e (⟨x, hAS hx⟩ : U) = y := Subtype.ext hxy
        change (e.symm y : M) ∈ A
        rw [← he, e.symm_apply_apply]
        exact hx
    rw [heq]
    apply riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    · have hv : MeasurableEmbedding (Subtype.val : V → N) :=
        V.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel V)
      have he : MeasurableEmbedding (e : U → V) := e.toHomeomorph.measurableEmbedding
      have hm := hv.measurableSet_image.mpr (he.measurableSet_image.mpr hS)
      have hset : (Subtype.val : V → N) '' (e '' S) = Φ '' A := by
        ext y
        constructor
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨e ⟨x, hAS hx⟩, ⟨⟨x, hAS hx⟩, hx, rfl⟩, rfl⟩
      rwa [hset] at hm
    · exact Set.image_mono hAS
  rw [hq, riemannianVolumeMeasure_restrictOpen_preimage_of_subset g U hA hAS] at hbound
  exact hbound

end DifferentialGeometry.Geometry.Measure
