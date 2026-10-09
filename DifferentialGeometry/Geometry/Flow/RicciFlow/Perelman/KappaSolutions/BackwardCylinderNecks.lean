import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CenteredCylinderMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticCylinderNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckModel

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backwardCylinderLimit_eventually_strongNeck_with_map
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} I3} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (h : ℝ → SmoothRiemannianMetric I3 L.M) (hzero : h 0 = L.metric)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn (fun theta => h (1 - theta))
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i))) (Phi.map i) K
        (Icc (1 : ℝ) 3) order eta))
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0, DifferentialGeometry.Diffeomorph.pullbackMetricCross (h t) d =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) :
    let z := d.symm L.basepoint
    let e := (cylinderLineTranslation z.2).trans d
    e (z.1, 0) = L.basepoint ∧
      (∀ y : SpatialNeckCylinder, e y = d (y.1, y.2 + z.2)) ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 11 → ∀ᶠ i in atTop,
        ∃ nk : StrongNeck F.S eps (q (phi i)) (-tau (phi i)),
          nk.map.source = spatialNeckBuffer eps ∧
          nk.map.target = (Phi.map i ∘ e) '' (spatialNeckBuffer eps : Set SpatialNeckCylinder) ∧
          nk.center = z.1 ∧
          (∀ y : spatialNeckBuffer eps, nk.map y.val = Phi.map i (e (y : SpatialNeckCylinder))) ∧
          nk.map '' (univ ×ˢ ({0} : Set ℝ)) =
            (Phi.map i ∘ e) '' (univ ×ˢ ({0} : Set ℝ)) := by
  let z := d.symm L.basepoint
  let e := (cylinderLineTranslation z.2).trans d
  obtain ⟨hmarked, hmap, hemetric⟩ := cylinderLineTranslation_centered_pullback h d hmetric L.basepoint
  have hterminal : DifferentialGeometry.Diffeomorph.pullbackMetricCross L.metric e =
      doubleSphereCylinderMetric := by
    simpa only [hzero, scalarOneShrinkingCylinderMetric_zero] using hemetric 0 le_rfl
  have hscalar : metricScalarAt L.metric L.basepoint = 1 := by
    have hh := metricScalar_cross L.metric e (z.1, 0)
    rw [hterminal, hmarked, doubleSphereCylinderMetric_scalar_native] at hh
    exact hh.symm
  refine ⟨hmarked, hmap, ?_⟩
  intro eps heps hsmall
  have hepsone : eps < 1 := hsmall.trans (by norm_num)
  have htmetric : ∀ theta : ℝ, ∀ ht : theta ∈ Icc (1 : ℝ) 3,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (h (1 - theta)) e =
        scalarOneShrinkingCylinderMetric (1 - theta)
          (sub_lt_self 1 (lt_of_lt_of_le zero_lt_one ht.1)) :=
    fun theta ht => hemetric _ (sub_nonpos.mpr ht.1)
  filter_upwards [backwardCylinderLimit_eventually_strongNeckWitness F tau htau q Phi C
    hcanonical hscalar (fun theta => h (1 - theta)) hconvergence e z.1 hmarked htmetric
    eps heps hepsone] with i hi
  obtain ⟨W, hW⟩ := hi
  obtain ⟨nk, hsource, htarget, hcenter, hnk, hcentral⟩ := W.exists_strongNeck hsmall
  refine ⟨nk, hsource, ?_, hcenter, fun y => (hnk y).trans (hW y), ?_⟩
  · rw [htarget]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, (hW y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, hW ⟨y, hy⟩⟩
  · rw [hcentral]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.val, ⟨mem_univ _, hy⟩, (hW y).symm⟩
    · rintro ⟨⟨y, s⟩, ⟨_, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      let y0 := spatialNeckCentralPoint eps heps y
      refine ⟨y0, ?_, ?_⟩
      · change (y0 : SpatialNeckCylinder).2 = 0
        rfl
      · rw [hW y0]
        change Phi.map i (e (y, 0)) = Phi.map i (e (y, s))
        rw [hs0]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
