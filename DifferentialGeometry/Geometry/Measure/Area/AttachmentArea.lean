import DifferentialGeometry.Geometry.Measure.Area.AttachmentInnerArea
import DifferentialGeometry.Geometry.Measure.Area.AttachmentSectorArea
import DifferentialGeometry.Topology.LoopSpace.AnnulusDecomposition



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Metric
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem attachDiskAnnulus_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {H : ℝ × loopCircle → M} {Ku Kh : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (Kh : ℝ≥0∞) * edist p q)
    (hglue : ∀ θ : loopCircle, u (AddCircle.toCircle θ : ℂ) = H (0, θ)) :
    ∃ K : ℝ≥0, ∀ z w,
      riemannianEDistOf g (attachDiskAnnulus u H z) (attachDiskAnnulus u H w) ≤
        (K : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hu' : LipschitzWith Ku u := hu
  have hH' : LipschitzWith Kh H := hH
  exact ⟨_, attachDiskAnnulus_lipschitz hu' hH' hglue⟩




theorem attachDiskAnnulus_area (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {H : ℝ × loopCircle → M} {Ku Kh : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (Kh : ℝ≥0∞) * edist p q)
    (hglue : ∀ θ : loopCircle, u (AddCircle.toCircle θ : ℂ) = H (0, θ)) :
    riemannianArea g (attachDiskAnnulus u H) (closedBall (0 : ℂ) 1) =
      riemannianArea g u (closedBall (0 : ℂ) 1) + cylinderArea g H := by
  obtain ⟨Ka, hKa⟩ := attachDiskAnnulus_riemannian_lipschitz g hu hH hglue
  obtain ⟨Kl, hKl⟩ := cylinderLift_riemannian_lipschitz g hH
  let A := attachDiskAnnulus u H
  have hAi : IntegrableOn (riemannianAreaDensity g A) (closedBall (0 : ℂ) 1) := by
    let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
    exact integrableOn_riemannianAreaDensity_of_lipschitz g hKa _
  have hLi : IntegrableOn (riemannianAreaDensity g (cylinderLift H)) unitSquare := by
    let : IsFiniteMeasure (volume.restrict unitSquare) :=
      isFiniteMeasure_restrict.mpr isCompact_unitSquare.measure_lt_top.ne
    exact integrableOn_riemannianAreaDensity_of_lipschitz g hKl _
  have hsub (a : ℝ) : annulusPolarMap '' annulusSector a ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using (annulusSector_image_norm hz).2.le
  have hA₀ := hAi.mono_set (hsub 0)
  have hA₁ := hAi.mono_set (hsub (1 / 2))
  have hAin := hAi.mono_set (closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hL₀ := hLi.mono_set (annulusSector_subset_square (a := 0) le_rfl (by norm_num))
  have hL₁ := hLi.mono_set (annulusSector_subset_square (a := 1 / 2) (by norm_num) (by norm_num))
  have hcyl : cylinderArea g H =
      riemannianArea g (cylinderLift H) (annulusSector 0) +
        riemannianArea g (cylinderLift H) (annulusSector (1 / 2)) := by
    calc
      _ = riemannianArea g (cylinderLift H) (annulusSector 0 ∪ annulusSector (1 / 2)) :=
        setIntegral_congr_set unitSquare_ae_eq_sectors
      _ = _ := riemannianArea_union g _ hL₀ hL₁ disjoint_annulusSectors.aedisjoint
        (isOpen_annulusSector (1 / 2)).measurableSet
  calc
    _ = riemannianArea g A (closedBall (0 : ℂ) (1 / 2) ∪
        (annulusPolarMap '' annulusSector 0 ∪ annulusPolarMap '' annulusSector (1 / 2))) :=
      setIntegral_congr_set closedDisk_ae_eq_annulusPieces
    _ = riemannianArea g A (closedBall (0 : ℂ) (1 / 2)) +
        (riemannianArea g A (annulusPolarMap '' annulusSector 0) +
          riemannianArea g A (annulusPolarMap '' annulusSector (1 / 2))) := by
      rw [riemannianArea_union g A hAin (hA₀.union hA₁)
        ((disjoint_union_right.mpr ⟨disjoint_halfDisk_annulusSector 0,
          disjoint_halfDisk_annulusSector (1 / 2)⟩).aedisjoint)
        ((measurableSet_annulusSector_image 0).union (measurableSet_annulusSector_image (1 / 2))),
        riemannianArea_union g A hA₀ hA₁ disjoint_annulusSector_images.aedisjoint
          (measurableSet_annulusSector_image (1 / 2))]
    _ = _ := by
      rw [attachDiskAnnulus_inner_area g hu H,
        attachDiskAnnulus_sector_area g u H hKa (a := 0) le_rfl (by norm_num),
        attachDiskAnnulus_sector_area g u H hKa (a := 1 / 2) (by norm_num) (by norm_num),
        ← hcyl]

end DifferentialGeometry.Geometry
