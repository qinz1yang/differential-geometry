import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimKeyJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFaceRemovalJN74

/-!
# Draft 74, the zero faces of the face facts at `D_R`: points of `∂Z` and zero model faces

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). For the zero exit of `D_R`:

* `exists_zeroFace_of_frontier_JN74`: a point of `∂Z` (chain) maps to a point of a model boundary
  component `Fm` of some zero piece `i`;
* `frontier_of_zeroFace_JN74`: conversely a point of a zero model face is the image of a point
  of `∂Z`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)

/-- **`∂Z = ⋃_k ∂Z_k`** (the zero domains are closed and pairwise disjoint). -/
theorem frontier_zeroUnion_eq_JN74 (hεr : εr < 1 / 2) :
    frontier S.chain.zeroUnion_ZSP35 = ⋃ k : S.ZeroIdx74, frontier (S.zeroDom74 k) := by
  have hcl : ∀ k : S.ZeroIdx74, IsClosed (S.zeroDom74 k) := fun k =>
    (S.chain.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  exact (frontier_disjoint_iUnion_ZSP35 (fun k : S.ZeroIdx74 => S.zeroDom74 k) hcl
    (fun k k' hkk => S.chain.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)).2

/-- **A point of `∂Z` lies in a zero model face**: for the zero exit `zero` there are a zero piece
`i` and a model boundary component `Fm` of it with `ψ x ∈ (piece i).map '' Fm`. -/
theorem exists_zeroFace_of_frontier_JN74 (hεr : εr < 1 / 2) (zero : ZSP02SmoothExit74 S)
    {x : M.X}
    (hx : x ∈ frontier S.chain.zeroUnion_ZSP35) :
    ∃ (i : Fin zero.rows.count) (Fm : ModelBoundaryFace (zero.rows.piece i)),
      M.ψ x ∈ (zero.rows.piece i).map '' Fm.1 := by
  obtain ⟨σ, hσ⟩ := zero.link
  rw [S.frontier_zeroUnion_eq_JN74 hεr] at hx
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  have hbd : pieceBoundary (zero.rows.piece (σ.symm k)) = M.ψ '' frontier (S.zeroDom74 k) := by
    have h := (hσ (σ.symm k)).2.1
    rw [σ.apply_symm_apply] at h
    exact h
  have hxb : M.ψ x ∈ pieceBoundary (zero.rows.piece (σ.symm k)) := by
    rw [hbd]
    exact ⟨x, hk, rfl⟩
  obtain ⟨p, hp, hpx⟩ := hxb
  exact ⟨σ.symm k, ActualComponent.of hp, p, mem_connectedComponentIn hp, hpx⟩

/-- **A point of a zero model face is the image of a point of `∂Z`**. -/
theorem frontier_of_zeroFace_JN74 (hεr : εr < 1 / 2) (zero : ZSP02SmoothExit74 S)
    (i : Fin zero.rows.count) (Fm : ModelBoundaryFace (zero.rows.piece i)) {x : M.X}
    (hx : M.ψ x ∈ (zero.rows.piece i).map '' Fm.1) :
    x ∈ frontier S.chain.zeroUnion_ZSP35 := by
  obtain ⟨σ, hσ⟩ := zero.link
  rw [S.frontier_zeroUnion_eq_JN74 hεr]
  obtain ⟨p, hp, hpx⟩ := hx
  have hpb : (zero.rows.piece i).map p ∈ pieceBoundary (zero.rows.piece i) :=
    ⟨p, Fm.subset hp, rfl⟩
  rw [(hσ i).2.1] at hpb
  obtain ⟨y, hy, hyp⟩ := hpb
  rw [hpx] at hyp
  rw [← M.ψ.injective hyp]
  exact mem_iUnion.2 ⟨σ i, hy⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
