import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCoreGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalRegionBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreCylinderAbsorption
import DifferentialGeometry.Geometry.Neck.StaticSlabCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover

open private CanonicalWitness.exists_cap_core_with_spatial_neck_frontier from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover

noncomputable section
open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M] (T : TubeSystem M)

omit [ChartedSpace ThreeSpace M] [T2Space M] in
private theorem removedBand_disjoint_boundarySphere (b : T.Boundary) :
    Disjoint (T.removedBand b.1) (range (T.boundarySphere b)) := by
  rw [disjoint_left]
  rintro x hx ⟨q, rfl⟩
  exact T.boundarySphere_mem_core b q (mem_iUnion.mpr ⟨b.1, hx⟩)

theorem closedBand_subset_or_capCore_union_cylinder_cutting_side
    {K : Set M} (cap : CapCore K) (b : T.Boundary)
    (R : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hR : univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source)
    (hRzero : ∀ q : Sphere 2, R (q, 0) = T.boundarySphere b q)
    (hinter : R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      (⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
        range (T.boundarySphere b))
    (hfront : frontier K = range (fun q : Sphere 2 => R (q, 1))) :
    (R '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ K ∧
      T.tube b.1 '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior K) ∨
      (Nonempty (CapCore (K ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
        frontier (K ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) = range (T.boundarySphere b) ∧
        Disjoint (K ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) (T.removedBand b.1)) := by
  have hupper : Disjoint (range (fun q : Sphere 2 => R (q, 1)))
      (⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) := by
    rw [disjoint_left]
    rintro x ⟨q, rfl⟩ hx
    have hlow : R (q, 1) ∈ range (T.boundarySphere b) :=
      hinter ▸ ⟨mem_image_of_mem R ⟨mem_univ _, by norm_num⟩, hx⟩
    obtain ⟨z, hz⟩ := hlow
    have he := congrArg Prod.snd (R.injOn
      (hR ⟨mem_univ _, by norm_num⟩) (hR ⟨mem_univ _, by norm_num⟩)
      ((hRzero z).trans hz))
    norm_num at he
  let V := T.tube b.1 '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}
  let L := R '' (univ ×ˢ Icc (0 : ℝ) 1)
  let q₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hVsub : V ⊆ ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} :=
    subset_iUnion (fun i => T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) b.1
  have hboundaryV : T.boundarySphere b q₀ ∈ V :=
    ⟨(q₀, boundaryLevel b.2), by cases b.2 <;> norm_num [boundaryLevel], rfl⟩
  have hboundaryL : T.boundarySphere b q₀ ∈ L :=
    ⟨(q₀, 0), ⟨mem_univ _, by norm_num⟩, hRzero q₀⟩
  have hVfront : Disjoint V (frontier K) := by
    rw [hfront]
    exact (hupper.mono_right hVsub).symm
  rcases cap.subset_or_nonempty_union_cylinder_of_frontier R hR hfront with hsub | ⟨hcap, hmeet, hboundary⟩
  · exact Or.inl ⟨hsub, isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      (T.isPreconnected_closedBand b.1) ⟨_, hboundaryV, hsub hboundaryL⟩ hVfront⟩
  · right
    have hnot : T.boundarySphere b q₀ ∉ K := by
      intro hK
      have hu : T.boundarySphere b q₀ ∈ range (fun q : Sphere 2 => R (q, 1)) :=
        hmeet ▸ ⟨hK, hboundaryL⟩
      exact disjoint_left.mp hupper hu (hVsub hboundaryV)
    have hVout : V ⊆ interior Kᶜ :=
      isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        (T.isPreconnected_closedBand b.1) ⟨_, hboundaryV, hnot⟩
        (by rwa [frontier_compl])
    refine ⟨hcap, ?_, ?_⟩
    · simpa only [hRzero] using hboundary
    · rw [disjoint_left]
      intro x hx hxband
      rcases hx with hxK | hxL
      · exact interior_subset (hVout (by
          obtain ⟨q, hq, rfl⟩ := hxband
          exact ⟨q, ⟨hq.1.le, hq.2.le⟩, rfl⟩)) hxK
      · have hxW : x ∈ ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} := by
          apply hVsub
          obtain ⟨q, hq, rfl⟩ := hxband
          exact ⟨q, ⟨hq.1.le, hq.2.le⟩, rfl⟩
        exact disjoint_left.mp (T.removedBand_disjoint_boundarySphere b) hxband
          (hinter ▸ ⟨hxL, hxW⟩)

section

variable [IsManifold I3 ∞ M] [SigmaCompactSpace M] [PreconnectedSpace M]

private theorem spatial_cap_or_whole_with_domain_of_not_spatial_neck
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps C1 C2 t : ℝ} {x : M}
    (W : CanonicalWitness S eps C1 C2 x t)
    (hchart : W.capTubeHasNeckChart eps)
    (hx : ¬ Nonempty (SpatialNeck (S.base.metric t) eps x)) :
    Nonempty (PositiveComponent (M := M) univ) ∨
      (∃ z : M, Nonempty (RoundComponent S eps z t univ)) ∨
      ∃ K : Set M, Nonempty (CapCore K) ∧ K ⊆ W.domain.carrier ∧
        riemannianBallOf (S.base.metric t) x
          (1000 / Real.sqrt (metricScalarAt (S.base.metric t) x)) ⊆ interior K := by
  cases htag : W.alternative with
  | neck data => exact (hx ⟨data.strong.toSpatialNeck⟩).elim
  | positive whole data sec =>
    have heq : W.domain.carrier = univ := whole.trans
      (PreconnectedSpace.connectedComponent_eq_univ x)
    exact Or.inl ⟨heq ▸ data⟩
  | round whole data =>
    have heq : W.domain.carrier = univ := whole.trans
      (PreconnectedSpace.connectedComponent_eq_univ x)
    exact Or.inr (Or.inl ⟨x, ⟨heq ▸ data⟩⟩)
  | cap data depth =>
    obtain ⟨K, v, nk, hmodel, hK, _, hKW, _, _, _⟩ :=
      CanonicalWitness.exists_cap_core_with_spatial_neck_frontier W hchart data depth htag
    refine Or.inr (Or.inr ⟨K.carrier, hmodel, hKW, ?_⟩)
    have hcore : data.core.carrier ⊆ K.carrier := by rw [hK]; exact subset_union_left
    have hball := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
      (S.base.metric t) data.center_inside
      (r := ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x))) (by
        intro z hz
        have hztube : z ∈ data.tube := (data.overlap_eq.symm ▸ hz).2
        exact (ENNReal.ofReal_le_ofReal (depth z hztube)).trans ENNReal.ofReal_toReal_le)
    intro z hz
    apply interior_mono hcore (hball ?_)
    exact hz.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)))

theorem capCore_cutting_side_or_captured_band_or_whole_of_stopped_cylinder
    {J : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) J)
    {eps C1 C2 t : ℝ} (heps : eps ≤ 1 / 8646)
    (b : T.Boundary) (R : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hR : univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source)
    (hRzero : ∀ q : Sphere 2, R (q, 0) = T.boundarySphere b q)
    (hinter : R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      (⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
        range (T.boundarySphere b))
    {p : M} (nk : SpatialNeck (S.base.metric t) eps p) (a : ℝ) (ha : |a| ≤ 4)
    (κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hRone : ∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a))
    (W : CanonicalWitness S eps C1 C2 (nk.map (nk.center, a)) t)
    (hchart : W.capTubeHasNeckChart eps)
    (hstopped : ¬ Nonempty (SpatialNeck (S.base.metric t) eps (nk.map (nk.center, a)))) :
    Nonempty (PositiveComponent (M := M) univ) ∨
      (∃ z : M, Nonempty (RoundComponent S eps z t univ)) ∨
      (∃ K : Set M, Nonempty (CapCore K) ∧ K ⊆ W.domain.carrier ∧
        frontier K = range (fun q : Sphere 2 => nk.map (q, a)) ∧
        R '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ K ∧
        T.tube b.1 '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior K) ∨
      ∃ K : Set M, Nonempty (CapCore K) ∧
        frontier K = range (T.boundarySphere b) ∧ Disjoint K (T.removedBand b.1) := by
  rcases spatial_cap_or_whole_with_domain_of_not_spatial_neck W hchart hstopped with
    hpos | hround | ⟨U, hcap, hUW, hball⟩
  · exact Or.inl hpos
  · exact Or.inr (Or.inl hround)
  have hslab := nk.image_slab_subset_of_ball_subset heps nk.center ha rfl hball
  have hlevel : |a| < eps⁻¹ := ha.trans_lt
    ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small]))
  obtain ⟨K, hK, _, _, hKfront, hKU⟩ :=
    hcap.some.exists_capCore_side_of_sphere_embedding (fun q : Sphere 2 => nk.map (q, a))
      (nk.isSmoothEmbedding_level hlevel)
      (by
        rintro z ⟨q, rfl⟩
        exact hslab ⟨(q, a), ⟨mem_univ _, abs_le.mp ha⟩, rfl⟩)
  have hupperRange : range (fun q : Sphere 2 => R (q, 1)) =
      range (fun q : Sphere 2 => nk.map (q, a)) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨κ q, (hRone q).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨κ.symm q, ?_⟩
      change R (κ.symm q, 1) = nk.map (q, a)
      rw [hRone, κ.apply_symm_apply]
  rcases T.closedBand_subset_or_capCore_union_cylinder_cutting_side hK.some b R hR hRzero
      hinter (hKfront.trans hupperRange.symm) with hcaptured | hside
  · exact Or.inr (Or.inr (Or.inl ⟨K, hK, hKU.trans (interior_subset.trans hUW),
      hKfront, hcaptured.1, hcaptured.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, hside⟩))

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] [ChartedSpace ThreeSpace M]
  (E : CutCapTopology M Q D N)

theorem cylinder_subset_image_compl_retainedCore
    (b : E.tubes.Boundary) (q₀ : Sphere 2)
    (hb : E.tubes.coreBoundarySphere b q₀ ∉ E.retainedCore)
    (R : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hR : univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source)
    (hRzero : ∀ q : Sphere 2, R (q, 0) = E.tubes.boundarySphere b q)
    (hinter : R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      (⋃ j, E.tubes.tube j '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
        range (E.tubes.boundarySphere b)) :
    R '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ Subtype.val '' E.retainedCoreᶜ := by
  let L := R '' (univ ×ˢ Icc (0 : ℝ) 1)
  have hcore : L ⊆ E.tubes.core := by
    intro z hz hnot
    obtain ⟨j, q, hq, hqz⟩ := mem_iUnion.mp hnot
    have hclosed : z ∈ ⋃ j, E.tubes.tube j ''
        {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} :=
      mem_iUnion.mpr ⟨j, q, ⟨hq.1.le, hq.2.le⟩, hqz⟩
    have hboundary : z ∈ range (E.tubes.boundarySphere b) := hinter ▸ ⟨hz, hclosed⟩
    obtain ⟨r, hr⟩ := hboundary
    exact E.tubes.boundarySphere_mem_core b r (hr ▸ hnot)
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hpre : IsPreconnected L :=
    (isPreconnected_univ.prod isPreconnected_Icc).image _
      (R.contMDiffOn_toFun.continuousOn.mono hR)
  have hprecore : IsPreconnected ((Subtype.val : E.tubes.core → M) ⁻¹' L) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hcore]
    exact hpre
  have hstart : E.tubes.coreBoundarySphere b q₀ ∈
      (Subtype.val : E.tubes.core → M) ⁻¹' L :=
    ⟨(q₀, 0), ⟨mem_univ _, by norm_num⟩, hRzero q₀⟩
  have hdiscard := hprecore.subset_isClopen E.isClopen_retainedCore.compl
    ⟨E.tubes.coreBoundarySphere b q₀, hstart, hb⟩
  intro z hz
  exact ⟨⟨z, hcore hz⟩, hdiscard hz, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
private theorem exists_retained_coreComponent_subset_interior_of_closedBand_subset
    (b : (H.event i).transition.trace.tubes.Index)
    {K : Set (H.stage i.castSucc).Carrier}
    (hband : (H.event i).transition.trace.tubes.tube b ''
      {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K)
    (hfront : frontier K ⊆ Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ) :
    ∃ z ∈ (H.event i).transition.trace.retainedCore,
      Subtype.val '' connectedComponent z ⊆ interior K := by
  classical
  let T := (H.event i).transition.trace.tubes
  let E := (H.event i).transition.trace
  obtain ⟨side, hside⟩ : ∃ side : Bool, (H.event i).RetainedBoundary (b, side) := by
    by_cases h : (H.event i).RetainedBoundary (b, false)
    · exact ⟨false, h⟩
    · exact ⟨true, (G.one_retained_side b).mpr h⟩
  let q : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let z : T.core := T.coreBoundarySphere (b, side) q
  have hzret : z ∈ E.retainedCore := hside q
  have hzK : z.val ∈ K := hband ⟨(q, TubeSystem.boundaryLevel side),
    by cases side <;> norm_num [TubeSystem.boundaryLevel], rfl⟩
  have hcomp : connectedComponent z ⊆ E.retainedCore :=
    E.isClopen_retainedCore.connectedComponent_subset hzret
  have hdis : Disjoint (Subtype.val '' connectedComponent z) (frontier K) := by
    rw [disjoint_left]
    rintro w ⟨v, hv, rfl⟩ hw
    obtain ⟨v', hv', he⟩ := hfront hw
    have he' : v' = v := Subtype.ext he
    exact hv' (he' ▸ hcomp hv)
  have hinside : Subtype.val '' connectedComponent z ⊆ interior K :=
    DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      (isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn)
      ⟨z.val, ⟨z, mem_connectedComponent, rfl⟩, hzK⟩ hdis
  exact ⟨z, hzret, hinside⟩

include G in
theorem exists_late_not_closedBand_subset_canonical_of_discarded_frontier
    {η : ℝ} (hη : 0 < η) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ (eps C1 C2 : ℝ) (x : (H.stage i.castSucc).Carrier),
        ∀ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t,
          C2 * (((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η) <
            (H.event i).incoming.flow.scalar t x →
          ∀ K ⊆ W.domain.carrier,
            frontier K ⊆ Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ →
            ∀ j : (H.event i).transition.trace.tubes.Index,
              ¬ (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K := by
  obtain ⟨d, hd, hgap⟩ := G.exists_late_retained_component_scalar_gap hη
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 x W hhigh K hKW hfront j hband
  obtain ⟨z, hz, hinside⟩ :=
    G.exists_retained_coreComponent_subset_interior_of_closedBand_subset j hband hfront
  obtain ⟨y, hymk, hyscalar⟩ := hgap t ht C2
    (zero_le_one.trans W.one_le_comparison_constant) x hhigh z hz
  have hyK : y.val ∈ K := interior_subset
    (hinside ⟨y, ConnectedComponents.coe_eq_coe'.mp hymk, rfl⟩)
  have hbound := (W.scalar_bounds y.val (hKW hyK)).1
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hbound' : (H.event i).incoming.flow.scalar t x ≤
      C2 * (H.event i).incoming.flow.scalar t y.val := by
    have hh := mul_le_mul_of_nonneg_left hbound hC2.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hh
  exact (not_lt_of_ge hbound') hyscalar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters) [PreconnectedSpace (H.stage i.castSucc).Carrier]

include G in
theorem exists_late_capCore_cutting_side_or_whole_of_stopped_cylinder
    {η : ℝ} (hη : 0 < η) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ eps C1 C2 : ℝ, eps ≤ 1 / 8646 →
        ∀ b : (H.event i).transition.trace.tubes.Boundary,
          ¬ (H.event i).RetainedBoundary b →
          ∀ R : PartialDiffeomorph IC I3 Cylinder (H.stage i.castSucc).Carrier ∞,
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source →
            (∀ q : Sphere 2, R (q, 0) = (H.event i).transition.trace.tubes.boundarySphere b q) →
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
              (⋃ j, (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
              range ((H.event i).transition.trace.tubes.boundarySphere b) →
            ∀ (p : (H.stage i.castSucc).Carrier)
              (nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps p)
              (a : ℝ), |a| ≤ 4 →
              ∀ κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                (∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a)) →
                ∀ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2
                    (nk.map (nk.center, a)) t,
                  W.capTubeHasNeckChart eps →
                  ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps
                    (nk.map (nk.center, a))) →
                  C2 * (((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η) <
                    (H.event i).incoming.flow.scalar t (nk.map (nk.center, a)) →
                  Nonempty (PositiveComponent (M := (H.stage i.castSucc).Carrier) univ) ∨
                    (∃ z : (H.stage i.castSucc).Carrier,
                      Nonempty (RoundComponent (H.event i).incoming.flow eps z t univ)) ∨
                    ∃ K : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore K) ∧
                      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
                      Disjoint K ((H.event i).transition.trace.tubes.removedBand b.1) := by
  obtain ⟨d, hd, hexclude⟩ :=
    G.exists_late_not_closedBand_subset_canonical_of_discarded_frontier hη
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 heps b hb R hR hRzero hinter p nk a ha κ hRone W hchart hstop hhigh
  obtain ⟨q₀, hq₀⟩ := not_forall.mp hb
  have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
    b q₀ hq₀ R hR hRzero hinter
  rcases (H.event i).transition.trace.tubes.capCore_cutting_side_or_captured_band_or_whole_of_stopped_cylinder
      (H.event i).incoming.flow heps b R hR hRzero hinter nk a ha κ hRone W hchart hstop with
    hpos | hround | ⟨K, _, hKW, hfront, _, hband⟩ | hside
  · exact Or.inl hpos
  · exact Or.inr (Or.inl hround)
  · exfalso
    apply hexclude t ht eps C1 C2 _ W hhigh K hKW _ b.1 (hband.trans interior_subset)
    rw [hfront]
    rintro z ⟨q, rfl⟩
    apply hdiscard
    refine ⟨(κ.symm q, 1), ⟨mem_univ _, by norm_num⟩, ?_⟩
    rw [hRone, κ.apply_symm_apply]
  · exact Or.inr (Or.inr hside)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

open Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_late_not_closedBand_subset_of_scalar_comparison
    {C : ℝ} (hC : 0 ≤ C)
    (hscale : ∀ j, C * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ K : Set (H.stage i.castSucc).Carrier,
        (∀ x ∈ K, ∀ y ∈ K,
          (H.event i).incoming.flow.scalar t x ≤ C * (H.event i).incoming.flow.scalar t y) →
        frontier K ⊆ Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ →
        ∀ j : (H.event i).transition.trace.tubes.Index,
          ¬ (H.event i).transition.trace.tubes.tube j ''
            {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K := by
  classical
  let A := ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  have hmarg (j : (H.event i).transition.trace.tubes.Index) :
      ∀ᶠ η : ℝ in 𝓝 (0 : ℝ), C * (A + η) < (G.neck j).scale := by
    have ht : Tendsto (fun η : ℝ => C * (A + η)) (𝓝 0) (𝓝 (C * A)) := by
      have ht₀ := (tendsto_const_nhds (x := A)).add (tendsto_id (x := (𝓝 (0 : ℝ))))
      have ht₁ := ht₀.const_mul C
      simpa only [id_eq, add_zero] using ht₁
    exact ht.eventually_lt_const (hscale j)
  have hall : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, C * (A + η) < (G.neck j).scale :=
    (eventually_all.mpr hmarg).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, hηscale, hη⟩ := (hall.and self_mem_nhdsWithin).exists
  have hηpos : 0 < η := hη
  obtain ⟨d₀, hd₀, hanchors⟩ := G.exists_late_retained_component_scalar_anchors hηpos
  have hseed (j : (H.event i).transition.trace.tubes.Index) :
      ∀ᶠ t in 𝓝[<] H.time i.succ,
        C * (A + η) < (H.event i).incoming.flow.scalar t (G.neck j).center.val := by
    have hh : Tendsto (fun t => metricScalarAt ((H.event i).incoming.flow.base.metric t) (G.neck j).center.val)
        (𝓝[<] H.time i.succ) (𝓝 (G.neck j).scale) := by
      simpa only [(G.neck j).scale_scalar] using
        (H.event i).terminal.tendsto_metricScalarAt (G.neck j).center
    exact hh.eventually_const_lt (hηscale j)
  obtain ⟨d₁, hd₁, hseeds⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (H.event i).incoming.lt).mp (eventually_all.mpr hseed)
  refine ⟨max d₀ d₁, ⟨hd₀.1.trans (le_max_left _ _), max_lt hd₀.2 hd₁.2⟩, ?_⟩
  intro t ht K hcomparison hfront j hband
  obtain ⟨z, hz, hinside⟩ :=
    G.exists_retained_coreComponent_subset_interior_of_closedBand_subset j hband hfront
  obtain ⟨y, hycore, hymk, _, hyscalar⟩ := hanchors z hz
  have hyK : y.val ∈ K := interior_subset
    (hinside ⟨⟨y.val, hycore⟩, ConnectedComponents.coe_eq_coe'.mp hymk, rfl⟩)
  have hcut : (G.neck j).center.val ∈ K := by
    apply hband
    let q : TubeDomain := ((G.neck j).sphereMark, ⟨0, by norm_num⟩)
    refine ⟨q, by norm_num [q], ?_⟩
    rw [G.tube_eq j q (G.tube_in_buffer j q)]
    exact congrArg Subtype.val (G.neck j).marked
  have htwice := hcomparison (G.neck j).center.val hcut y.val hyK
  have hylt := hyscalar t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
  have hh := htwice.trans (mul_le_mul_of_nonneg_left hylt.le hC)
  exact (not_lt_of_ge hh) (hseeds ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩ j)

include G in
theorem exists_late_not_closedBand_subset_canonical_of_cutting_scale
    {C : ℝ} (hC : 1 ≤ C)
    (hscale : ∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ (eps C1 C2 : ℝ), C2 ≤ C →
        ∀ (x : (H.stage i.castSucc).Carrier)
          (W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t),
          ∀ K ⊆ W.domain.carrier,
            frontier K ⊆ Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ →
            ∀ j : (H.event i).transition.trace.tubes.Index,
              ¬ (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ K := by
  obtain ⟨d, hd, hexclude⟩ :=
    G.exists_late_not_closedBand_subset_of_scalar_comparison (sq_nonneg C) hscale
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 hC2 x W K hKW hfront j
  apply hexclude t ht K ?_ hfront j
  intro y hy z hz
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hC2pos : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hzpos : 0 < (H.event i).incoming.flow.scalar t z :=
    (mul_pos (inv_pos.mpr hC2pos) W.Q_pos).trans_le (W.scalar_bounds z (hKW hz)).1
  have hC2square : C2 ^ 2 ≤ C ^ 2 := sq_le_sq₀ hC2pos.le hCpos.le |>.mpr hC2
  exact (W.scalar_le_sq_mul_at_mem_domain (hKW hz) y (hKW hy)).trans
    (mul_le_mul_of_nonneg_right hC2square hzpos.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters) [PreconnectedSpace (H.stage i.castSucc).Carrier]

include G in
theorem exists_late_capCore_cutting_side_or_whole_of_stopped_cylinder_of_cutting_scale
    {C : ℝ} (hC : 1 ≤ C)
    (hscale : ∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ eps C1 C2 : ℝ, eps ≤ 1 / 8646 → C2 ≤ C →
        ∀ b : (H.event i).transition.trace.tubes.Boundary,
          ¬ (H.event i).RetainedBoundary b →
          ∀ R : PartialDiffeomorph IC I3 Cylinder (H.stage i.castSucc).Carrier ∞,
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source →
            (∀ q : Sphere 2, R (q, 0) = (H.event i).transition.trace.tubes.boundarySphere b q) →
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
              (⋃ j, (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
              range ((H.event i).transition.trace.tubes.boundarySphere b) →
            ∀ (p : (H.stage i.castSucc).Carrier)
              (nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps p)
              (a : ℝ), |a| ≤ 4 →
              ∀ κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                (∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a)) →
                ∀ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2
                    (nk.map (nk.center, a)) t,
                  W.capTubeHasNeckChart eps →
                  ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps
                    (nk.map (nk.center, a))) →
                  Nonempty (PositiveComponent (M := (H.stage i.castSucc).Carrier) univ) ∨
                    (∃ z : (H.stage i.castSucc).Carrier,
                      Nonempty (RoundComponent (H.event i).incoming.flow eps z t univ)) ∨
                    ∃ K : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore K) ∧
                      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
                      Disjoint K ((H.event i).transition.trace.tubes.removedBand b.1) := by
  obtain ⟨d, hd, hexclude⟩ :=
    G.exists_late_not_closedBand_subset_canonical_of_cutting_scale hC hscale
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 heps hC2 b hb R hR hRzero hinter p nk a ha κ hRone W hchart hstop
  obtain ⟨q₀, hq₀⟩ := not_forall.mp hb
  have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
    b q₀ hq₀ R hR hRzero hinter
  rcases (H.event i).transition.trace.tubes.capCore_cutting_side_or_captured_band_or_whole_of_stopped_cylinder
      (H.event i).incoming.flow heps b R hR hRzero hinter nk a ha κ hRone W hchart hstop with
    hpos | hround | ⟨K, _, hKW, hfront, _, hband⟩ | hside
  · exact Or.inl hpos
  · exact Or.inr (Or.inl hround)
  · exfalso
    apply hexclude t ht eps C1 C2 hC2 _ W K hKW _ b.1 (hband.trans interior_subset)
    rw [hfront]
    rintro z ⟨q, rfl⟩
    apply hdiscard
    refine ⟨(κ.symm q, 1), ⟨mem_univ _, by norm_num⟩, ?_⟩
    rw [hRone, κ.apply_symm_apply]
  · exact Or.inr (Or.inr hside)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_late_capCore_cutting_side_of_spatial_cap_of_cutting_scale
    {C : ℝ} (hC : 0 ≤ C)
    (hscale : ∀ j, C * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ eps : ℝ, eps ≤ 1 / 8646 →
        ∀ b : (H.event i).transition.trace.tubes.Boundary,
          ¬ (H.event i).RetainedBoundary b →
          ∀ R : PartialDiffeomorph IC I3 Cylinder (H.stage i.castSucc).Carrier ∞,
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source →
            (∀ q : Sphere 2, R (q, 0) = (H.event i).transition.trace.tubes.boundarySphere b q) →
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
              (⋃ j, (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
              range ((H.event i).transition.trace.tubes.boundarySphere b) →
            ∀ (p : (H.stage i.castSucc).Carrier)
              (nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps p)
              (a : ℝ), |a| ≤ 4 →
              ∀ κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                (∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a)) →
                ∀ U : Set (H.stage i.castSucc).Carrier,
                  (∀ x ∈ U, ∀ y ∈ U,
                    (H.event i).incoming.flow.scalar t x ≤ C * (H.event i).incoming.flow.scalar t y) →
                  (U = connectedComponent (nk.map (nk.center, a)) ∨
                    ∃ V : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore V) ∧ V ⊆ U ∧
                      riemannianBallOf ((H.event i).incoming.flow.base.metric t) (nk.map (nk.center, a))
                        (1000 / Real.sqrt (metricScalarAt ((H.event i).incoming.flow.base.metric t)
                          (nk.map (nk.center, a)))) ⊆ interior V) →
                  ∃ K : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore K) ∧
                      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
                      Disjoint K ((H.event i).transition.trace.tubes.removedBand b.1) := by
  obtain ⟨d, hd, hexclude⟩ := G.exists_late_not_closedBand_subset_of_scalar_comparison hC hscale
  refine ⟨d, hd, ?_⟩
  intro t ht eps heps b hb R hR hRzero hinter p nk a ha κ hRone U hcomparison hmodels
  obtain ⟨q₀, hq₀⟩ := not_forall.mp hb
  have hdiscard := (H.event i).transition.trace.cylinder_subset_image_compl_retainedCore
    b q₀ hq₀ R hR hRzero hinter
  let _ : LocallyConnectedSpace (H.stage i.castSucc).Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace (H.stage i.castSucc).Carrier
  have hwhole : U ≠ connectedComponent (nk.map (nk.center, a)) := by
    intro heq
    apply hexclude t ht U hcomparison _ b.1
    · rw [heq]
      have hpoint : R (κ.symm nk.center, 1) = nk.map (nk.center, a) := by
        rw [hRone, κ.apply_symm_apply]
      rw [← hpoint]
      exact (H.event i).transition.trace.tubes.closedBand_subset_connectedComponent_of_cylinder
        b R (R.contMDiffOn_toFun.continuousOn.mono hR) hRzero (κ.symm nk.center)
    · rw [heq, isClopen_connectedComponent.frontier_eq]
      exact empty_subset _
  obtain ⟨V, hV, hVU, hball⟩ := hmodels.resolve_left hwhole
  have hslab := nk.image_slab_subset_of_ball_subset heps nk.center ha rfl hball
  have hlevel : |a| < eps⁻¹ := ha.trans_lt
    ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small]))
  obtain ⟨K, hK, _, _, hKfront, hKV⟩ :=
    hV.some.exists_capCore_side_of_sphere_embedding (fun q : Sphere 2 => nk.map (q, a))
      (nk.isSmoothEmbedding_level hlevel)
      (by
        rintro z ⟨q, rfl⟩
        exact hslab ⟨(q, a), ⟨mem_univ _, abs_le.mp ha⟩, rfl⟩)
  have hupperRange : range (fun q : Sphere 2 => R (q, 1)) =
      range (fun q : Sphere 2 => nk.map (q, a)) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨κ q, (hRone q).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨κ.symm q, ?_⟩
      change R (κ.symm q, 1) = nk.map (q, a)
      rw [hRone, κ.apply_symm_apply]
  rcases (H.event i).transition.trace.tubes.closedBand_subset_or_capCore_union_cylinder_cutting_side
      hK.some b R hR hRzero hinter (hKfront.trans hupperRange.symm) with hcaptured | hside
  · exfalso
    apply hexclude t ht K (fun x hx y hy =>
      hcomparison x (hVU (interior_subset (hKV hx))) y (hVU (interior_subset (hKV hy)))) _
      b.1 (hcaptured.2.trans interior_subset)
    rw [hKfront, ← hupperRange]
    rintro z ⟨q, rfl⟩
    exact hdiscard ⟨(q, 1), ⟨mem_univ _, by norm_num⟩, rfl⟩
  · exact ⟨_, hside⟩

include G in
theorem exists_late_capCore_cutting_side_of_stopped_cylinder_of_cutting_scale
    {C : ℝ} (hC : 1 ≤ C)
    (hscale : ∀ j, C ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      (G.neck j).scale) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ eps C1 C2 : ℝ, eps ≤ 1 / 8646 → C2 ≤ C →
        ∀ b : (H.event i).transition.trace.tubes.Boundary,
          ¬ (H.event i).RetainedBoundary b →
          ∀ R : PartialDiffeomorph IC I3 Cylinder (H.stage i.castSucc).Carrier ∞,
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source →
            (∀ q : Sphere 2, R (q, 0) = (H.event i).transition.trace.tubes.boundarySphere b q) →
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
              (⋃ j, (H.event i).transition.trace.tubes.tube j ''
                {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
              range ((H.event i).transition.trace.tubes.boundarySphere b) →
            ∀ (p : (H.stage i.castSucc).Carrier)
              (nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps p)
              (a : ℝ), |a| ≤ 4 →
              ∀ κ : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                (∀ q : Sphere 2, R (q, 1) = nk.map (κ q, a)) →
                ∀ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2
                    (nk.map (nk.center, a)) t,
                  W.capTubeHasNeckChart eps →
                  ¬ Nonempty (SpatialNeck ((H.event i).incoming.flow.base.metric t) eps
                    (nk.map (nk.center, a))) →
                  ∃ K : Set (H.stage i.castSucc).Carrier, Nonempty (CapCore K) ∧
                      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
                      Disjoint K ((H.event i).transition.trace.tubes.removedBand b.1) := by
  obtain ⟨d, hd, hside⟩ :=
    G.exists_late_capCore_cutting_side_of_spatial_cap_of_cutting_scale (sq_nonneg C) hscale
  refine ⟨d, hd, ?_⟩
  intro t ht eps C1 C2 heps hC2 b hb R hR hRzero hinter p nk a ha κ hRone W hchart hstop
  apply hside t ht eps heps b hb R hR hRzero hinter p nk a ha κ hRone W.domain.carrier
  · intro x hx y hy
    have hC2pos : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hypos : 0 < (H.event i).incoming.flow.scalar t y :=
      (mul_pos (inv_pos.mpr hC2pos) W.Q_pos).trans_le (W.scalar_bounds y hy).1
    exact (W.scalar_le_sq_mul_at_mem_domain hy x hx).trans
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hC2pos.le hCpos.le).mpr hC2) hypos.le)
  · by_cases hwhole : W.domain.carrier = connectedComponent (nk.map (nk.center, a))
    · exact Or.inl hwhole
    · right
      cases htag : W.alternative with
      | neck data => exact (hstop ⟨data.strong.toSpatialNeck⟩).elim
      | positive whole data sec => exact (hwhole whole).elim
      | round whole data => exact (hwhole whole).elim
      | cap data depth =>
        obtain ⟨U, _, _, hU, hUeq, _, hUW, _, _, _⟩ :=
          CanonicalWitness.exists_cap_core_with_spatial_neck_frontier W hchart data depth htag
        refine ⟨U.carrier, hU, hUW, ?_⟩
        have hcore : data.core.carrier ⊆ U.carrier := by rw [hUeq]; exact subset_union_left
        have hball := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
          ((H.event i).incoming.flow.base.metric t) data.center_inside
          (r := ENNReal.ofReal (10000 / Real.sqrt ((H.event i).incoming.flow.scalar t (nk.map (nk.center, a))))) (by
            intro z hz
            have hztube : z ∈ data.tube := (data.overlap_eq.symm ▸ hz).2
            exact (ENNReal.ofReal_le_ofReal (depth z hztube)).trans ENNReal.ofReal_toReal_le)
        intro z hz
        apply interior_mono hcore (hball ?_)
        exact hz.trans_le (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
