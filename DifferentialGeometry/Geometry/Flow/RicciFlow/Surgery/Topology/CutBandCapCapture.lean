import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Topology.Connected.CoverBySides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] (T : TubeSystem M)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem isPreconnected_closedBand (a : T.Index) :
    IsPreconnected (T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) := by
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let : PreconnectedSpace (Icc (-1 : ℝ) 1) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let j : Sphere 2 × Icc (-1 : ℝ) 1 → TubeDomain :=
    fun q => (q.1,⟨q.2.val,by constructor <;> linarith [q.2.property.1,q.2.property.2]⟩)
  have hj : Continuous j := continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hr : range (T.tube a ∘ j) = T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨j q,q.2.property,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨(q.1,⟨q.2.val,hq⟩),rfl⟩
  exact hr ▸ isPreconnected_range ((T.tube a).continuous.comp hj)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem central_and_boundary_spheres_subset_of_closedBand_subset
    (a : T.Index) {K : Set M}
    (h : T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K) :
    range (fun z : Sphere 2 => T.tube a (z,⟨0,by norm_num⟩)) ⊆ K ∧
      ∀ side : Bool, range (T.boundarySphere (a,side)) ⊆ K := by
  constructor
  · rintro _ ⟨z,rfl⟩
    exact h (mem_image_of_mem (T.tube a) (by norm_num))
  · intro side
    rintro _ ⟨z,rfl⟩
    apply h
    refine ⟨(z,boundaryLevel side),?_,rfl⟩
    cases side <;> norm_num [boundaryLevel]

omit [T2Space M] in
theorem closedBand_subset_cap_core_interior_or_meets_inner_boundary
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps t : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x t U)
    (a : T.Index) (q : TubeDomain) (hq : q.2.val ∈ Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tubeMap (z,0) := by
  rcases Set.disjoint_or_nonempty_inter
      (T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) (frontier cap.core.carrier) with hd | h
  · exact Or.inl (DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      (T.isPreconnected_closedBand a) ⟨T.tube a q,mem_image_of_mem (T.tube a) hq,hcontact⟩ hd)
  · obtain ⟨w,⟨r,hr,hrw⟩,hw⟩ := h
    obtain ⟨⟨z,s⟩,hs,heq⟩ := cap.inner_boundary.symm ▸ hw
    obtain rfl : s = 0 := hs.2
    exact Or.inr ⟨r,z,hr,hrw.trans heq.symm⟩

omit [T2Space M] in
theorem closedBand_subset_cap_core_interior_or_far_inner_boundary
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps t : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (a : T.Index) (q : TubeDomain) (hq : q.2.val ∈ Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tubeMap (z,0) ∧
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x (T.tube a r) := by
  obtain h | ⟨r,z,hr,he⟩ := T.closedBand_subset_cap_core_interior_or_meets_inner_boundary cap a q hq hcontact
  · exact Or.inl h
  · refine Or.inr ⟨r,z,hr,he,?_⟩
    apply hdepth
    rw [he,← cap.tube_eq]
    exact mem_image_of_mem cap.tubeMap ⟨mem_univ _,le_rfl,zero_le_one⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

theorem closedBand_subset_closedBall_of_spatialNeck
    {g : SmoothRiemannianMetric ThreeModel M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val)) :
    T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ riemannianClosedBallOf g p
      (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt g p)) := by
  have hsmall : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  rintro _ ⟨q,hq,rfl⟩
  rw [hmap q hq]
  have h := nk.image_slab_subset_closedBall zero_le_one hsmall
    (show nk.map (q.1,q.2.val) ∈ nk.map '' (univ ×ˢ Icc (-(1 : ℝ)) 1) from
      ⟨(q.1,q.2.val),⟨mem_univ _,hq⟩,rfl⟩)
  simpa only [show (1 : ℝ)+6=7 by norm_num] using h

theorem closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p)
    (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val))
    (q : TubeDomain) (hq : q.2.val ∈ Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tubeMap (z,0) ∧
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)) ≤
          riemannianEDistOf (S.base.metric t) x p +
            ENNReal.ofReal (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) := by
  obtain h | ⟨r,z,hr,he,hfar⟩ := T.closedBand_subset_cap_core_interior_or_far_inner_boundary
    cap hdepth a q hq hcontact
  · exact Or.inl h
  · refine Or.inr ⟨r,z,hr,he,?_⟩
    have hbound := T.closedBand_subset_closedBall_of_spatialNeck nk a hmap
      (mem_image_of_mem (T.tube a) hr)
    have hdist : ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)) ≤
        riemannianEDistOf (S.base.metric t) x (T.tube a r) :=
      (ENNReal.ofReal_le_ofReal hfar).trans ENNReal.ofReal_toReal_le
    exact hdist.trans ((riemannianEDistOf_triangle (S.base.metric t) x p (T.tube a r)).trans
      (add_le_add_right hbound _))

theorem closedBand_subset_cap_core_interior_of_spatialNeck_center_close
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p)
    (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x))) :
    T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier := by
  have hcapture := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (S.base.metric t) cap.center_inside (r := ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (fun y hy => (ENNReal.ofReal_le_ofReal (hdepth y ((cap.overlap_eq.symm ▸ hy).2))).trans
      ENNReal.ofReal_toReal_le)
  intro y hy
  apply hcapture
  exact ((riemannianEDistOf_triangle (S.base.metric t) x p y).trans
    (add_le_add_right (T.closedBand_subset_closedBall_of_spatialNeck nk a hmap hy) _)).trans_lt hclose

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem boundarySphere_mem_closure_removedBand (b : T.Boundary) (q : Sphere 2) :
    T.boundarySphere b q ∈ closure (T.removedBand b.1) := by
  let f : ℝ → M := fun t => T.tube b.1 (q, Set.projIcc (-2 : ℝ) 2 (by norm_num) t)
  have hf : Continuous f := (T.tube b.1).continuous.comp
    (continuous_const.prodMk continuous_projIcc)
  have hlevel : (boundaryLevel b.2).val ∈ closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    cases b with
    | mk a side => cases side <;> norm_num [boundaryLevel]
  have himage : f '' Ioo (-1 : ℝ) 1 ⊆ T.removedBand b.1 := by
    rintro y ⟨t, ht, rfl⟩
    have ht2 : t ∈ Icc (-2 : ℝ) 2 := by constructor <;> linarith [ht.1, ht.2]
    refine ⟨(q, Set.projIcc (-2 : ℝ) 2 (by norm_num) t), ?_, rfl⟩
    change -1 < (Set.projIcc (-2 : ℝ) 2 (by norm_num) t).val ∧
      (Set.projIcc (-2 : ℝ) 2 (by norm_num) t).val < 1
    rw [Set.projIcc_of_mem (by norm_num : (-2 : ℝ) ≤ 2) ht2]
    exact ht
  have hh := closure_mono himage (mem_closure_image hf.continuousAt hlevel)
  have heq : f (boundaryLevel b.2).val = T.boundarySphere b q := by
    dsimp [f]
    rw [Set.projIcc_of_mem (by norm_num : (-2 : ℝ) ≤ 2) (boundaryLevel b.2).property]
    rfl
  exact heq ▸ hh

theorem eq_of_boundarySphere_mem_of_frontier_eq
    {K : Set M} (hcore : K ⊆ T.core) (b : T.Boundary)
    (hfront : frontier K = range (T.boundarySphere b))
    {b' : T.Boundary} {q : Sphere 2} (hq : T.boundarySphere b' q ∈ K) : b' = b := by
  have hnot : T.boundarySphere b' q ∉ interior K := by
    intro hint
    have hh := T.boundarySphere_mem_closure_removedBand b' q
    have hn := (mem_closure_iff_nhds.mp hh) (interior K)
      (isOpen_interior.mem_nhds hint)
    obtain ⟨y, hyint, hyband⟩ := hn
    exact hcore (interior_subset hyint) (mem_iUnion.mpr ⟨b'.1, hyband⟩)
  have hf : T.boundarySphere b' q ∈ frontier K := (mem_frontier_iff_notMem_interior hq).mpr hnot
  obtain ⟨z, hz⟩ := hfront ▸ hf
  have hidx : b'.1 = b.1 := by
    by_contra hne
    exact (disjoint_left.mp (T.disjoint hne))
      (mem_range_self (q, boundaryLevel b'.2)) ⟨(z, boundaryLevel b.2), hz⟩
  apply Prod.ext hidx
  have he : T.tube b.1 (q, boundaryLevel b'.2) = T.tube b.1 (z, boundaryLevel b.2) := by
    have hh : T.tube b.1 (z, boundaryLevel b.2) = T.tube b'.1 (q, boundaryLevel b'.2) := hz
    rw [hidx] at hh
    exact hh.symm
  have hcoord := congrArg (fun p : TubeDomain => p.2.val) ((T.embedding b.1).injective he)
  revert hcoord
  cases hb' : b'.2 <;> cases hb : b.2
  · intro _; rfl
  · norm_num [boundaryLevel]
  · norm_num [boundaryLevel]
  · intro _; rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem closedBand_subset_connectedComponent_of_cylinder
    (b : T.Boundary) (R : Sphere 2 × ℝ → M)
    (hR : ContinuousOn R (univ ×ˢ Icc (0 : ℝ) 1))
    (hRzero : ∀ q : Sphere 2, R (q,0) = T.boundarySphere b q)
    (q : Sphere 2) :
    T.tube b.1 '' {p : TubeDomain | p.2.val ∈ Icc (-1 : ℝ) 1} ⊆
      connectedComponent (R (q,1)) := by
  let _ : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  have hconn : IsPreconnected (R '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    (isPreconnected_univ.prod isPreconnected_Icc).image R hR
  have hR0 : R (q,0) ∈ R '' (univ ×ˢ Icc (0 : ℝ) 1) :=
    ⟨(q,0),⟨mem_univ _,by norm_num⟩,rfl⟩
  have hR1 : R (q,1) ∈ R '' (univ ×ˢ Icc (0 : ℝ) 1) :=
    ⟨(q,1),⟨mem_univ _,by norm_num⟩,rfl⟩
  have h01 : T.boundarySphere b q ∈ connectedComponent (R (q,1)) :=
    hRzero q ▸ hconn.subset_connectedComponent hR1 hR0
  have hqband : T.boundarySphere b q ∈
      T.tube b.1 '' {p : TubeDomain | p.2.val ∈ Icc (-1 : ℝ) 1} := by
    refine ⟨(q,boundaryLevel b.2),?_,rfl⟩
    cases b.2 <;> norm_num [boundaryLevel]
  intro y hy
  have hy0 := (T.isPreconnected_closedBand b.1).subset_connectedComponent hqband hy
  rwa [← connectedComponent_eq h01] at hy0

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end
