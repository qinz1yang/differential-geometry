import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open CheegerGromovCompactness Geometry.Curvature Surgery.Topology

theorem SpatialNeck.exists_restrict_target
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {p : M} {eps : ℝ}
    (nk : SpatialNeck g eps p) (U : TopologicalSpace.Opens M)
    (hcapture : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    ∃ (hp : p ∈ U) (out : SpatialNeck (g.restrictOpen U) eps ⟨p, hp⟩),
      out.center = nk.center ∧
      (∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (out.map z : M) = nk.map z) ∧
      (∀ x : U, out.map.symm x = nk.map.symm (x : M)) ∧
      out.map.target = {x : U | (x : M) ∈ nk.map.target} ∧
      ∀ x : U, metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) := by
  have hcenter : (nk.center, (0 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩
  have hp : p ∈ U := nk.center_eq ▸ hcapture (mem_image_of_mem nk.map hcenter)
  have hne : Nonempty U := ⟨⟨p, hp⟩⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 U hne
  let F := partialDiffeomorphTransMixed nk.map iU.symm
  have hsource : univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ ⊆ F.source := by
    intro z hz
    refine ⟨nk.domain hz, ?_⟩
    change nk.map z ∈ iU.target
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hcapture (mem_image_of_mem nk.map hz)
  have hmap (z : Cylinder) (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
      (F z : M) = nk.map z := by
    change (iU.symm (nk.map z) : M) = nk.map z
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I3 U hne
      (hcapture (mem_image_of_mem nk.map hz))]
  have hder (z : Cylinder) (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
      mfderiv IC I3 F z = mfderiv IC I3 nk.map z := by
    have heq : (fun y => (F y : M)) =ᶠ[𝓝 z] (nk.map : Cylinder → M) :=
      Filter.eventuallyEq_of_mem ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz) hmap
    exact (mfderiv_subtypeVal_comp F z).symm.trans heq.mfderiv_eq
  have hscalar : ∀ x : U, metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) := by
    intro x
    exact metricScalarAt_restrictOpen g U x
  have hQ : 0 < metricScalarAt (g.restrictOpen U) ⟨p, hp⟩ := by rw [hscalar]; exact nk.Q_pos
  let cmp : MetricComparisonOn (fun _ => nk.cylinder.metric 0)
      (fun _ => scaleMetric (metricScalarAt (g.restrictOpen U) ⟨p, hp⟩) hQ (g.restrictOpen U))
      F (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) {0} ⌈eps⁻¹⌉₊ eps := {
    pullback := nk.comparison.pullback
    pullback_eq := by
      intro s z hz v
      rw [nk.comparison.pullback_eq s z hz v]
      simp only [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner, hscalar, hder z hz]
      rw [hmap z hz]
      rfl
    jet := nk.comparison.jet
    jet_zero := nk.comparison.jet_zero
    jet_succ := nk.comparison.jet_succ
    equivalence := nk.comparison.equivalence
    close := nk.comparison.close }
  refine ⟨hp, {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hQ
    cylinder := nk.cylinder
    map := F
    center := nk.center
    center_eq := ?_
    domain := hsource
    comparison := cmp }, rfl, hmap, fun _ => rfl, ?_, hscalar⟩
  · apply Subtype.ext
    exact (hmap _ hcenter).trans nk.center_eq
  · ext x
    change (x ∈ (univ : Set U) ∧ (x : M) ∈ nk.map.target) ↔ (x : M) ∈ nk.map.target
    simp only [mem_univ, true_and]

theorem SpatialNeck.controlled_range_subset_connectedComponent
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eps : ℝ} (nk : SpatialNeck g eps p) :
    nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ connectedComponent p := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hpre : IsPreconnected (nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono nk.domain)
  apply hpre.subset_connectedComponent
  exact ⟨(nk.center,0), ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos),
    inv_pos.mpr nk.eps_pos⟩, nk.center_eq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
