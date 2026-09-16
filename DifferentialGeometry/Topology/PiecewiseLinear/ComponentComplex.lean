import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness

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

def connectedComponentComplex (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) : Geometry.SimplicialComplex ℝ E :=
  restrict K (((↑) : K.space → E) '' (ConnectedComponents.mk ⁻¹' {c}))

theorem connectedComponentComplex_mk (K : Geometry.SimplicialComplex ℝ E) (p : K.space) :
    connectedComponentComplex K (ConnectedComponents.mk p) =
      restrict K (connectedComponentIn K.space (p : E)) := by
  simp only [connectedComponentComplex, connectedComponents_preimage_singleton,
    ← connectedComponentIn_eq_image p.property]

theorem connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) :
    (connectedComponentComplex K c).space =
      ((↑) : K.space → E) '' (ConnectedComponents.mk ⁻¹' {c}) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space,
    connectedComponents_preimage_singleton, connectedComponentIn_eq_image p.property]

theorem connectedComponentComplex_faces_finite (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (c : ConnectedComponents K.space) :
    (connectedComponentComplex K c).faces.Finite := restrict_faces_finite K _

theorem isConnected_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) : IsConnected (connectedComponentComplex K c).space := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
  exact isConnected_connectedComponentIn_iff.mpr p.property

theorem iUnion_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E) :
    ⋃ c, (connectedComponentComplex K c).space = K.space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [connectedComponentComplex_space] at hc
    obtain ⟨p, -, rfl⟩ := hc
    exact p.property
  · intro x hx
    apply mem_iUnion.mpr
    refine ⟨ConnectedComponents.mk (⟨x, hx⟩ : K.space), ?_⟩
    rw [connectedComponentComplex_space]
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

theorem pairwise_disjoint_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E) :
    Pairwise fun c d => Disjoint (connectedComponentComplex K c).space
      (connectedComponentComplex K d).space := by
  intro c d hcd
  apply disjoint_left.mpr
  intro x hxC hxD
  rw [connectedComponentComplex_space] at hxC hxD
  obtain ⟨p, hp, hpx⟩ := hxC
  obtain ⟨q, hq, hqx⟩ := hxD
  have hpq : p = q := Subtype.val_injective (hpx.trans hqx.symm)
  subst q
  exact hcd (hp.symm.trans hq)

theorem IsCombinatorialManifold.connectedComponentComplex {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsCombinatorialManifold n K)
    (c : ConnectedComponents K.space) : IsCombinatorialManifold n (connectedComponentComplex K c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [PiecewiseLinear.connectedComponentComplex_mk]
  exact hK.restrict_connectedComponentIn p

theorem IsCombinatorialManifoldWithBoundary.connectedComponentComplex {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsCombinatorialManifoldWithBoundary n K)
    (c : ConnectedComponents K.space) :
    IsCombinatorialManifoldWithBoundary n (connectedComponentComplex K c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [PiecewiseLinear.connectedComponentComplex_mk]
  exact hK.restrict_connectedComponentIn p

theorem finite_connectedComponents_space [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : Finite (ConnectedComponents K.space) := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  infer_instance
end DifferentialGeometry.Topology.PiecewiseLinear
