import DifferentialGeometry.Topology.Connected.BoundaryCollarComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Geometry.Neck.Spatial
import Mathlib.Topology.OpenPartialHomeomorph.Composition

section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [T2Space M] (T : TubeSystem M)

theorem connectedComponent_eq_preimage_of_capCore_outward_collar
    {K : Set M} (cap : CapCore K) (hcore : K ⊆ T.core)
    (b : T.Boundary) (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    (hfront : frontier K = range (T.boundarySphere b))
    (hzero : ∀ z : Sphere 2, e (z, 0) = T.boundarySphere b z)
    (hpos : ∀ z : Sphere 2, ∀ t ∈ Ioo (0 : ℝ) r, e (z, t) ∈ T.removedBand b.1)
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : T.core → M) ⁻¹' K := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
  have hfront' : frontier K = range (fun z : Sphere 2 => e (z, 0)) := by
    simpa only [hzero] using hfront
  apply DifferentialGeometry.Topology.connectedComponent_eq_preimage_of_outward_collar
    cap.closure_interior_carrier cap.isConnected_carrier.isPreconnected hcore e hr hsource
    hfront' _ x hx
  intro z t ht hmem
  exact hmem (mem_iUnion.mpr ⟨b.1, hpos z t ht⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] (T : TubeSystem M)

theorem connectedComponent_eq_preimage_of_capCore_of_spatialNeck
    {K : Set M} (cap : CapCore K) (hcore : K ⊆ T.core)
    (b : T.Boundary) (hfront : frontier K = range (T.boundarySphere b))
    {g : SmoothRiemannianMetric ThreeModel M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube b.1 q = nk.map (q.1, q.2.val))
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : T.core → M) ⁻¹' K := by
  let H : (Sphere 2 × ℝ) ≃ₜ (Sphere 2 × ℝ) :=
    { toFun := fun q => (q.1, if b.2 then 1 - q.2 else -1 + q.2)
      invFun := fun q => (q.1, if b.2 then 1 - q.2 else 1 + q.2)
      left_inv := by intro q; cases b.2 <;> simp
      right_inv := by intro q; cases b.2 <;> simp
      continuous_toFun := by
        cases hb : b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd)
      continuous_invFun := by
        cases hb : b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd) }
  let e := H.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph
  have happ (z : Sphere 2) (t : ℝ) :
      e (z, t) = nk.map (z, if b.2 then 1 - t else -1 + t) := rfl
  have hrange : (2 : ℝ) < eps⁻¹ := by
    have heps : eps < (2 : ℝ)⁻¹ := nk.eps_small.trans (by norm_num)
    exact lt_inv_of_lt_inv₀ nk.eps_pos heps
  apply T.connectedComponent_eq_preimage_of_capCore_outward_collar cap hcore b e
    (r := 1) zero_lt_one _ hfront _ _ x hx
  · rintro ⟨z, t⟩ ⟨_, ht⟩
    change H (z, t) ∈ nk.map.source
    apply nk.domain
    change (z, if b.2 then 1 - t else -1 + t) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
    refine ⟨mem_univ _, ?_, ?_⟩ <;> cases b.2 <;>
      simp only [Bool.false_eq_true, if_false, if_true] <;> linarith [ht.1, ht.2]
  · intro z
    rw [happ]
    change _ = T.tube b.1 (z, boundaryLevel b.2)
    rw [hmap _ (by cases hb : b.2 <;> norm_num [boundaryLevel, hb])]
    cases b.2 <;> simp [boundaryLevel]
  · intro z t ht
    let v : ℝ := if b.2 then 1 - t else -1 + t
    have hv : v ∈ Ioo (-1 : ℝ) 1 := by
      cases hb : b.2 <;> simp only [v, hb, Bool.false_eq_true, if_false, if_true] <;>
        constructor <;> linarith [ht.1, ht.2]
    let q : TubeDomain := (z, ⟨v, by constructor <;> linarith [hv.1, hv.2]⟩)
    refine ⟨q, hv, ?_⟩
    rw [hmap q ⟨hv.1.le, hv.2.le⟩]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end
