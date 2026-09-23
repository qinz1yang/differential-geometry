import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Neck.SpatialFrontierOrientation

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {p : M} {eps alpha a : ℝ}

theorem SpatialNeck.exists_outward_at_coordinate_of_tolerance
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) (u : Sphere 2) (ha : |a| ≤ 4)
    {W S : Set M} (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = range (fun q => nk.map (q, a)) ∪ S)
    (hdisjoint : Disjoint (range (fun q => nk.map (q, a))) S) :
    ∃ out : SpatialNeck g alpha (nk.map (u, a)), out.center = u ∧
      (∀ q, out.map (q, 0) = nk.map (q, a)) ∧
      ((∀ q t, out.map (q, t) = nk.map (q, a + t)) ∨
        (∀ q t, out.map (q, t) = nk.map (q, a - t))) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → out.map (out.center, t) ∉ W := by
  obtain ⟨seed, hcenter, hmap⟩ := nk.exists_at_coordinate hsmall hreserve u ha
  have htranslate := nk.translated_map_apply u seed hmap
  have hzero (q : Sphere 2) : seed.map (q, 0) = nk.map (q, a) := by
    simpa only [add_zero] using nk.translated_map_apply u seed hmap q 0
  have hrange : range (fun q => seed.map (q, 0)) = range (fun q => nk.map (q, a)) :=
    congrArg range (funext hzero)
  have hfront' : frontier W = range (fun q => seed.map (q, 0)) ∪ S := by
    rw [hrange]
    exact hfront
  have hdisjoint' : Disjoint (range (fun q => seed.map (q, 0))) S := by
    rw [hrange]
    exact hdisjoint
  obtain ⟨out, _, horient, _, _, _, _, hout⟩ :=
    seed.exists_outward_graph_orientation (fun _ => 0) contMDiff_const
      (fun _ => by norm_num) rfl hregular hS hfront' hdisjoint'
  refine ⟨out, ?_, ?_, ?_, hout⟩
  · rcases horient with rfl | rfl
    · exact hcenter
    · exact hcenter
  · intro q
    rcases horient with rfl | rfl
    · exact hzero q
    · simpa only [SpatialNeck.axialReflection_apply, neg_zero] using hzero q
  · rcases horient with rfl | rfl
    · exact Or.inl htranslate
    · right
      intro q t
      rw [SpatialNeck.axialReflection_apply, htranslate]
      rfl

theorem SpatialNeck.exists_outward_at_coordinate_mul
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 156000)
    (u : Sphere 2) (ha : |a| ≤ 4)
    {W S : Set M} (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = range (fun q => nk.map (q, a)) ∪ S)
    (hdisjoint : Disjoint (range (fun q => nk.map (q, a))) S) :
    ∃ out : SpatialNeck g (13000 * eps) (nk.map (u, a)), out.center = u ∧
      (∀ q, out.map (q, 0) = nk.map (q, a)) ∧
      ((∀ q t, out.map (q, t) = nk.map (q, a + t)) ∨
        (∀ q t, out.map (q, t) = nk.map (q, a - t))) ∧
      ∃ r > 0, ∀ t, 0 < t → t < r → out.map (out.center, t) ∉ W := by
  exact nk.exists_outward_at_coordinate_of_tolerance (by linarith) le_rfl u ha
    hregular hS hfront hdisjoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
