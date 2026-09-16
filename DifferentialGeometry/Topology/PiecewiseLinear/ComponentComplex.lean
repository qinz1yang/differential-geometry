import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_connectedComponentIn_space (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    (restrict K (connectedComponentIn K.space p)).space = connectedComponentIn K.space p := by
  apply Subset.antisymm (restrict_space_subset K _)
  intro z hz
  obtain ⟨s, hs, hzs⟩ := K.mem_space_iff.mp (connectedComponentIn_subset K.space p hz)
  have hsub := (convex_convexHull ℝ (s : Set E)).isPreconnected.subset_connectedComponentIn
    hzs (K.convexHull_subset_space hs)
  rw [← connectedComponentIn_eq hz] at hsub
  exact (restrict K (connectedComponentIn K.space p)).convexHull_subset_space ⟨hs, hsub⟩ hzs

open Classical in
theorem geometricLink_restrict_connectedComponentIn (K : Geometry.SimplicialComplex ℝ E)
    {p v : E} (hv : v ∈ connectedComponentIn K.space p) :
    SimplicialComplex.geometricLink (restrict K (connectedComponentIn K.space p)) {v} =
      SimplicialComplex.geometricLink K {v} := by
  classical
  ext s
  simp only [SimplicialComplex.mem_geometricLink_singleton, mem_restrict_faces_iff]
  constructor
  · rintro ⟨hne, hvs, hs, -⟩
    exact ⟨hne, hvs, hs⟩
  · rintro ⟨hne, hvs, hs⟩
    refine ⟨hne, hvs, hs, ?_⟩
    have hsub := (convex_convexHull ℝ ((insert v s : Finset E) : Set E)).isPreconnected
      |>.subset_connectedComponentIn (subset_convexHull ℝ _ (Finset.mem_insert_self v s))
        (K.convexHull_subset_space hs)
    rwa [← connectedComponentIn_eq hv] at hsub

theorem IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) (p : E) :
    IsCombinatorialManifoldWithBoundary n (restrict K (connectedComponentIn K.space p)) := by
  classical
  cases n with
  | zero =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1
  | succ n =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1

theorem IsCombinatorialManifold.restrict_connectedComponentIn
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    (hK : IsCombinatorialManifold n K) (p : E) :
    IsCombinatorialManifold n (restrict K (connectedComponentIn K.space p)) := by
  classical
  cases n with
  | zero =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1
  | succ n =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1

end DifferentialGeometry.Topology.PiecewiseLinear
