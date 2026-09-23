import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarDepth
import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Neck.SphericalBarrier

open private exists_compactDomain_of_cylinder_slab from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
open private slab_boundary_chart from DifferentialGeometry.Topology.Manifold.CylinderSlabBoundary

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M} {U : Set M}

omit [T2Space M] in
theorem LocalCap.mem_truncated_core_on_tube
    (cap : LocalCap S eps x t U) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (q : Sphere 2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    cap.tube_map (q,s) ∈ cap.core.carrier ∪ cap.tube_map '' (univ ×ˢ Icc (0 : ℝ) c) ↔ s ≤ c := by
  constructor
  · rintro (hcore | ⟨z,hz,hzeq⟩)
    · have hzero := (cap.tube_map_mem_core_iff hs).mp hcore
      exact hzero ▸ hc.1.le
    · have heq := cap.tube_map.injOn
        (cap.tube_domain ⟨hz.1,hz.2.1,hz.2.2.trans hc.2.le⟩)
        (cap.tube_domain ⟨mem_univ _,hs⟩) hzeq
      have hh : z.2 = s := congrArg Prod.snd heq
      exact hh ▸ (show z.2 ≤ c from hz.2.2)
  · intro hsc
    exact Or.inr ⟨(q,s),⟨mem_univ _,hs.1,hsc⟩,rfl⟩

theorem LocalCap.exists_truncated_compactDomain
    (cap : LocalCap S eps x t U) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ K : CompactDomain M,
      K.carrier = cap.core.carrier ∪ cap.tube_map '' (univ ×ˢ Icc (0 : ℝ) c) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ U ∧
      frontier K.carrier = range (fun q : Sphere 2 => cap.tube_map (q,c)) := by
  have hcpos : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  let V := cap.core.carrier ∪ cap.tube_map '' (univ ×ˢ Icc (0 : ℝ) c)
  have hsrc : (univ ×ˢ Icc (0 : ℝ) c : Set Cylinder) ⊆ cap.tube_map.source :=
    fun z hz => cap.tube_domain ⟨hz.1,hz.2.1,hz.2.2.trans hc.2.le⟩
  obtain ⟨T,hT⟩ := exists_compactDomain_of_cylinder_slab cap.tube_map hc.1 hsrc
  have hVc : IsCompact V := cap.core.compact.union (hT ▸ T.compact)
  have hVU : V ⊆ U := by
    rintro y (hy | ⟨z,hz,rfl⟩)
    · exact cap.union_eq.ge (Or.inl hy)
    · exact cap.union_eq.ge (Or.inr (cap.tube_eq ▸
        ⟨z,⟨hz.1,hz.2.1,hz.2.2.trans hc.2.le⟩,rfl⟩))
  have hcoreInt : cap.core.carrier ⊆ interior V := by
    intro y hy
    by_cases hyint : y ∈ interior cap.core.carrier
    · exact interior_mono subset_union_left hyint
    · have hyfront : y ∈ frontier cap.core.carrier :=
        ⟨cap.core.compact.isClosed.closure_eq.symm ▸ hy,hyint⟩
      have hbaseNeighborhood : y ∈ interior U := cap.core_inside hy
      have hVnear : V ∈ 𝓝 y := by
        have hremove : y ∉ cap.tube_map '' (univ ×ˢ Icc (c/2) 1) := by
          rintro ⟨q,hq,hqy⟩
          have hqcore : cap.tube_map q ∈ cap.core.carrier := hqy.symm ▸ hy
          have heq := (cap.tube_map_mem_core_iff ⟨hq.2.1.trans' (half_pos hc.1).le,hq.2.2⟩).mp hqcore
          linarith [hq.2.1]
        have hclosed : IsClosed (cap.tube_map '' (univ ×ˢ Icc (c/2) 1)) :=
          ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
            (cap.tube_map.contMDiffOn_toFun.continuousOn.mono (fun q hq =>
              cap.tube_domain ⟨hq.1,(half_pos hc.1).le.trans hq.2.1,hq.2.2⟩))).isClosed
        apply Filter.mem_of_superset ((isOpen_interior.inter hclosed.isOpen_compl).mem_nhds ⟨hbaseNeighborhood,hremove⟩)
        intro q hq
        rcases cap.union_eq.le (interior_subset hq.1) with hqcore | hqtube
        · exact Or.inl hqcore
        · obtain ⟨z,hz,rfl⟩ := cap.tube_eq.symm ▸ hqtube
          have hzhalf : z.2 < c/2 := by
            by_contra hn
            exact hq.2 ⟨z,⟨hz.1,le_of_not_gt hn,hz.2.2⟩,rfl⟩
          exact Or.inr ⟨z,⟨hz.1,hz.2.1,by linarith⟩,rfl⟩
      exact mem_interior_iff_mem_nhds.mpr hVnear
  have hfront : frontier V = range (fun q : Sphere 2 => cap.tube_map (q,c)) := by
    apply Subset.antisymm
    · intro y hy
      have hyV := hVc.isClosed.frontier_subset hy
      rcases hyV with hycore | ⟨z,hz,rfl⟩
      · exact False.elim (hy.2 (hcoreInt hycore))
      · by_cases heq : z.2 = c
        · exact ⟨z.1,by rw [← heq]⟩
        have hzlt : z.2 < c := lt_of_le_of_ne hz.2.2 heq
        by_cases hz0 : z.2 = 0
        · have hzcore := (cap.tube_map_mem_core_iff (z := z.1) ⟨hz.2.1,hz.2.2.trans hc.2.le⟩).mpr hz0
          exact False.elim (hy.2 (hcoreInt hzcore))
        have hzpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hz0)
        have hopen : IsOpen (cap.tube_map '' (univ ×ˢ Ioo (0 : ℝ) c)) :=
          cap.tube_map.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
            (fun q hq => hsrc ⟨hq.1,hq.2.1.le,hq.2.2.le⟩)
        have hsub : cap.tube_map '' (univ ×ˢ Ioo (0 : ℝ) c) ⊆ V :=
          fun q hq => Or.inr (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hq)
        exact False.elim (hy.2 (hopen.subset_interior_iff.mpr hsub ⟨z,⟨hz.1,hzpos,hzlt⟩,rfl⟩))
    · rintro y ⟨q,rfl⟩
      have hpoint : cap.tube_map (q,c) ∈ V := Or.inr ⟨(q,c),⟨mem_univ _,hc.1.le,le_rfl⟩,rfl⟩
      refine ⟨subset_closure hpoint,?_⟩
      intro hInt
      have htend : ContinuousAt (fun s : ℝ => cap.tube_map (q,s)) c :=
        (cap.tube_map.contMDiffOn_toFun.continuousOn.continuousAt
          (cap.tube_map.open_source.mem_nhds (hsrc ⟨mem_univ _,hc.1.le,le_rfl⟩))).comp
          (continuous_const.continuousAt.prodMk continuous_id.continuousAt)
      have hmem := htend.preimage_mem_nhds (isOpen_interior.mem_nhds hInt)
      have hR : Ioo c 1 ∈ 𝓝[>] c := Ioo_mem_nhdsGT hc.2
      have hsmall : ∀ᶠ s in 𝓝[>] c, cap.tube_map (q,s) ∈ interior V := Filter.mem_of_superset
        (nhdsWithin_le_nhds hmem) (fun _ h => h)
      obtain ⟨s,hs,hsv⟩ := ((show ∀ᶠ s in 𝓝[>] c, s ∈ Ioo c 1 from hR).and hsmall).exists
      have hsc := (cap.mem_truncated_core_on_tube hc q ⟨hc.1.le.trans hs.1.le,hs.2.le⟩).mp (interior_subset hsv)
      exact (not_lt_of_ge hsc) hs.1
  have hmeet : (cap.core.carrier ∩ T.carrier).Nonempty := by
    let q := DifferentialGeometry.Topology.sphereTwoNorth
    have hm : cap.tube_map (q,0) ∈ cap.core.carrier := (cap.tube_map_mem_core_iff ⟨le_rfl,zero_le_one⟩).mpr rfl
    exact ⟨_,hm,hT.symm ▸ ⟨(q,0),⟨mem_univ _,le_rfl,hc.1.le⟩,rfl⟩⟩
  refine ⟨{ carrier := V
            compact := hVc
            connected := by change IsConnected (cap.core.carrier ∪ _); rw [← hT]; exact cap.core.connected.union hmeet T.connected
            regular_closed := ?_
            boundary_chart := ?_ },rfl,interior_mono subset_union_left cap.center_inside,hVU,hfront⟩
  · apply Subset.antisymm (closure_minimal interior_subset hVc.isClosed)
    rintro y (hy | hy)
    · exact (closure_mono (interior_mono subset_union_left)) (cap.core.regular_closed.symm ▸ hy)
    · have hsub : T.carrier ⊆ V := fun y hy => Or.inr (hT ▸ hy)
      exact closure_mono (interior_mono hsub) (T.regular_closed.symm ▸ (hT.symm ▸ hy))
  · intro y hy
    obtain ⟨q,rfl⟩ := hfront ▸ hy
    obtain ⟨F,hF,hzero,hside⟩ := slab_boundary_chart cap.tube_map hc.1 hsrc q
    have hnot : cap.tube_map (q,c) ∉ cap.core.carrier := by
      rw [cap.tube_map_mem_core_iff ⟨hc.1.le,hc.2.le⟩]
      exact hc.1.ne'
    let F' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict F cap.core.carrierᶜ cap.core.compact.isClosed.isOpen_compl
    refine ⟨F',⟨hF,hnot⟩,hzero,?_⟩
    intro z hz
    change z ∈ V ↔ F z 0 ≤ 0
    constructor
    · rintro (hzcore | hzslab)
      · exact (hz.2 hzcore).elim
      · exact (hside z hz.1).mp hzslab
    · intro hh
      exact Or.inr ((hside z hz.1).mpr hh)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

open private SpatialNeck.slice_isSmoothEmbedding SpatialNeck.exists_slice_collar from DifferentialGeometry.Geometry.Neck.SphericalBarrier

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {epsc t : ℝ} {x : M} {U : Set M}

set_option backward.isDefEq.respectTransparency false in
theorem LocalCap.exists_midpoint_spherical_barrier
    (cap : LocalCap S epsc x t U)
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (heps : eps < 1 / 8646)
    (hmap : ∀ z : Cylinder, cap.tube_map z = nk.map z)
    (A C2 : ℝ) (hA : 0 < A)
    (hscalar : ∀ y ∈ U, 4*A ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ 4*C2^2*A) :
    ∃ K : CompactDomain M,
      K.carrier = cap.core.carrier ∪ nk.map '' (univ ×ˢ Icc (0 : ℝ) (1/2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ U ∧
      frontier K.carrier = range (fun y : Sphere 2 => nk.map (y,1/2)) ∧
      IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y,1/2)) ∧
      (∀ y ∈ K.carrier, 2*A < metricScalarAt g y ∧ metricScalarAt g y ≤ 8*C2^2*A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2*A < metricScalarAt g (nk.map z) ∧ metricScalarAt g (nk.map z) ≤ 8*C2^2*A) ∧
      nk.cylindricalChart.metricCloseOn g eps
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ y z, z ∈ Icc (-101 : ℝ) 101 → (y,z) ∈ nk.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y,1/2)),
        c.radius < 1/4 ∧ ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
          c.toFun q = nk.map (q.1,1/2+(q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have hfun : (cap.tube_map : Cylinder → M) = nk.map := funext hmap
  have hlen : (101 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith)
  obtain ⟨K,hK,hx,hKU,hfront⟩ := cap.exists_truncated_compactDomain (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1)
  have hpU : p ∈ U := by
    have htube : cap.tube_map (nk.center,0) ∈ cap.tube := cap.tube_eq ▸
      ⟨(nk.center,0),⟨mem_univ _,by norm_num⟩,rfl⟩
    rw [hmap,nk.center_eq] at htube
    exact cap.union_eq.ge (Or.inr htube)
  have hQ := hscalar p hpU
  have hwide : ∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
      2*A < metricScalarAt g (nk.map z) ∧ metricScalarAt g (nk.map z) ≤ 8*C2^2*A := by
    intro z hz
    have hs := nk.scalar_bounds_on_image_window ⟨z,⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩
    have hl : metricScalarAt g p/2 < (1-4323*eps)*metricScalarAt g p := by nlinarith [nk.Q_pos]
    have hu : (1+4323*eps)*metricScalarAt g p ≤ 2*metricScalarAt g p := by nlinarith [nk.Q_pos]
    constructor
    · exact (by linarith [hQ.1] : 2*A ≤ metricScalarAt g p/2).trans_lt (hl.trans_le hs.1)
    · nlinarith [hs.2,hQ.2]
  have hmid : (1/2 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ := by constructor <;> linarith
  have hm : ∀ y : Sphere 2, (y,(1/2 : ℝ)) ∈ nk.cylindricalChart.domain := fun y => ⟨mem_univ _,hmid⟩
  obtain ⟨c,hc,_,hcoord⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    nk.cylindricalChart.domain nk.cylindricalChart.target nk.cylindricalChart.chart
    (fun _ => (1/2 : ℝ)) contMDiff_const hm (by norm_num : (0 : ℝ)<1/4)
  refine ⟨K,by simpa only [hfun] using hK,hx,hKU,by simpa only [hmap] using hfront,
    SpatialNeck.slice_isSmoothEmbedding nk hmid,?_,hwide,?_,?_,c,hc,?_⟩
  · intro y hy
    have h := hscalar y (hKU hy)
    have hn := mul_nonneg (sq_nonneg C2) hA.le
    constructor <;> nlinarith
  · intro z _ j hj
    exact nk.cylindricalChart_metricCloseOn z (mem_univ _) j hj
  · intro y z hz
    exact ⟨mem_univ _,by linarith [hz.1],by linarith [hz.2]⟩
  · intro q
    have heq : c.toFun q = nk.map (q.1,1/2+(q.2 : ℝ)) := (hcoord q).choose_spec
    refine ⟨heq,?_⟩
    rw [heq,hK]
    have hpoint := hmap (q.1,1/2+(q.2 : ℝ))
    rw [← hpoint]
    have hs : 1/2+(q.2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [q.2.property.1,q.2.property.2]
    rw [cap.mem_truncated_core_on_tube (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1) q.1 hs]
    constructor <;> intro h <;> linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
