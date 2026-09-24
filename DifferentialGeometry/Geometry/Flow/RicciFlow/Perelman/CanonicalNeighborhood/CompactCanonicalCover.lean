import DifferentialGeometry.Geometry.Neck.CompactCapGrowth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreSphereFilling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapReset
import DifferentialGeometry.Geometry.Neck.SpatialFrontierRecentering
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 t : ℝ}


variable {epsc : ℝ} {x : M}

private theorem CanonicalWitness.exists_cap_core_with_spatial_neck_frontier
    (witness : CanonicalWitness S epsc C1 C2 x t)
    (hchart : witness.capTubeHasNeckChart eps)
    (cap : LocalCap S epsc x t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z)
    (htag : witness.alternative = CanonicalAlternative.cap cap hdepth) :
    ∃ (V : CompactDomain M) (v : M) (neck : SpatialNeck (S.base.metric t) eps v),
      Nonempty (CapCore V.carrier) ∧
      V.carrier = cap.core.carrier ∪ cap.tube_map '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tube_map z) ∧
      (∀ q : Sphere 2, ∀ a, 0 < a → a < 1 / 2 → neck.map (q, 1 / 2 + a) ∉ V.carrier) := by
  obtain ⟨v, nk, hmap⟩ := hchart cap hdepth htag
  obtain ⟨V, hV, hxV, hVU, hVfront⟩ :=
    cap.exists_truncated_compactDomain (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  have hmodel : Nonempty (CapCore V.carrier) := by
    rw [hV]
    exact cap.nonempty_capCore_truncated_core (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  refine ⟨V, v, nk.toSpatialNeck, hmodel, hV, hxV, hVU, ?_, ?_, ?_⟩
  · rw [hVfront]
    congr 1
    funext q
    exact hmap _
  · intro z
    exact (hmap z).symm
  · intro q a ha ha1
    change nk.map (q, 1 / 2 + a) ∉ V.carrier
    rw [← hmap, hV]
    intro h
    have hm := (cap.mem_truncated_core_on_tube (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
      q (by constructor <;> linarith : 1 / 2 + a ∈ Icc (0 : ℝ) 1)).mp h
    linarith


private structure StoppedCap (g : SmoothRiemannianMetric I3 M) (eps : ℝ) where
  region : Set M
  cap : CapCore region
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  bound : |level| ≤ 4
  frontier_eq : frontier region = range (fun q : Sphere 2 => neck.map (q, level))
  stopped : ¬ Nonempty (SpatialNeck g eps (neck.map (neck.center, level)))

private def StoppedCap.center {g : SmoothRiemannianMetric I3 M} (T : StoppedCap g eps) : M :=
  T.neck.map (T.neck.center, T.level)

private theorem exists_canonical_cap_of_not_whole
    [PreconnectedSpace M] (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t)
    (hpos : ¬ Nonempty (PositiveComponent (M := M) univ))
    (hround : ¬ ∃ x : M, Nonempty (RoundComponent S eps x t univ))
    (x : M) (hx : ¬ Nonempty (SpatialNeck (S.base.metric t) eps x)) :
    ∃ cap : LocalCap S eps x t (W x).domain.carrier,
      ∃ depth : ∀ z ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z,
        (W x).alternative = CanonicalAlternative.cap cap depth := by
  cases htag : (W x).alternative with
  | neck data => exact (hx ⟨data.strong.toSpatialNeck⟩).elim
  | cap data depth => exact ⟨data, depth, rfl⟩
  | positive whole data sec =>
    have heq : (W x).domain.carrier = univ := whole.trans
      (PreconnectedSpace.connectedComponent_eq_univ x)
    exact (hpos ⟨heq ▸ data⟩).elim
  | round whole data =>
    have heq : (W x).domain.carrier = univ := whole.trans
      (PreconnectedSpace.connectedComponent_eq_univ x)
    exact (hround ⟨x, ⟨heq ▸ data⟩⟩).elim


private theorem exists_stopped_cap_reset
    (hsmall : eps ≤ 1 / 2028000000)
    (hgrowth : ∀ (W : Set M), CapCore W →
      ∀ (x : M) (initial : SpatialNeck (S.base.metric t) eps x) (a : ℝ), |a| ≤ 4 →
      frontier W = range (fun q : Sphere 2 => initial.map (q, a)) →
      ∃ K : Set M, ∃ p : M, ∃ neck : SpatialNeck (S.base.metric t) eps p, ∃ level : ℝ,
        Nonempty (CapCore K) ∧ W ⊆ K ∧ closure (interior K) = K ∧
        |level| ≤ 4 ∧ frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
        ¬ Nonempty (SpatialNeck (S.base.metric t) eps (neck.map (neck.center, level))))
    (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t)
    (hchart : ∀ x, (W x).capTubeHasNeckChart eps)
    (T : StoppedCap (S.base.metric t) eps)
    (cap : LocalCap S eps T.center t (W T.center).domain.carrier)
    (depth : ∀ z ∈ cap.tube, 10000 / Real.sqrt (S.scalar t T.center) ≤
      metricDistance (S.base.metric t) T.center z)
    (htag : (W T.center).alternative = CanonicalAlternative.cap cap depth)
    (hnested : T.region ⊆ cap.core.carrier) :
    ∃ (T' : StoppedCap (S.base.metric t) eps)
      (out : SpatialNeck (S.base.metric t) (13000 * eps) T.center),
      T.region ⊆ T'.region ∧ cap.core.carrier ⊆ T'.region ∧
      frontier T.region = range (fun q : Sphere 2 => out.map (q, 0)) ∧
      ∃ r > 0, ∀ z, 0 < z → z < r → out.map (out.center, z) ∉ T.region := by
  have hrec : eps ≤ 1 / 156000 := hsmall.trans (by norm_num)
  obtain ⟨out, houtcenter, houtzero, houtmap, hout⟩ :=
    T.neck.exists_outward_at_coordinate_mul hrec T.neck.center T.bound
      T.cap.closure_interior_carrier isClosed_empty
      (by simpa only [union_empty] using T.frontier_eq) (disjoint_empty _)
  have hfront : frontier T.region = range (fun q : Sphere 2 => out.map (q, 0)) := by
    rw [T.frontier_eq]
    exact congrArg range (funext houtzero).symm
  obtain ⟨V, v, newneck, hmodel, hV, hTV, hcapV, hVU, hfrontV, hmapV, houtV, hfresh⟩ :=
    (W T.center).exists_singleton_cap_reset_with_capCore (hchart T.center) cap depth htag
      out (by linarith : 13000 * eps ≤ 1 / 8646) T.cap.isCompact_carrier.isClosed
      (fun _ => 0) continuous_const (fun _ => by norm_num) rfl hfront hout hnested
  obtain ⟨K, p, neck, level, hmodelK, hVK, hregK, hbound, hfrontK, hstop⟩ :=
    hgrowth V.carrier hmodel.some v newneck (1 / 2) (by norm_num) hfrontV
  let T' : StoppedCap (S.base.metric t) eps :=
    ⟨K, hmodelK.some, p, neck, level, hbound, hfrontK, hstop⟩
  exact ⟨T', out, hTV.trans hVK, hcapV.trans hVK, hfront, hout⟩


private theorem not_forall_nested_cap_at_stopped_frontiers
    [CompactSpace M]
    (hsmall : eps ≤ 1 / 2028000000)
    (hgrowth : ∀ (W : Set M), CapCore W →
      ∀ (x : M) (initial : SpatialNeck (S.base.metric t) eps x) (a : ℝ), |a| ≤ 4 →
      frontier W = range (fun q : Sphere 2 => initial.map (q, a)) →
      ∃ K : Set M, ∃ p : M, ∃ neck : SpatialNeck (S.base.metric t) eps p, ∃ level : ℝ,
        Nonempty (CapCore K) ∧ W ⊆ K ∧ closure (interior K) = K ∧
        |level| ≤ 4 ∧ frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
        ¬ Nonempty (SpatialNeck (S.base.metric t) eps (neck.map (neck.center, level))))
    (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t)
    (hchart : ∀ x, (W x).capTubeHasNeckChart eps)
    (T₀ : StoppedCap (S.base.metric t) eps)
    (cap : (T : StoppedCap (S.base.metric t) eps) →
      LocalCap S eps T.center t (W T.center).domain.carrier)
    (depth : ∀ T, ∀ z ∈ (cap T).tube, 10000 / Real.sqrt (S.scalar t T.center) ≤
      metricDistance (S.base.metric t) T.center z)
    (htag : ∀ T, (W T.center).alternative = CanonicalAlternative.cap (cap T) (depth T))
    (hnested : ∀ T, T.region ⊆ (cap T).core.carrier) : False := by
  classical
  have hnext (T : StoppedCap (S.base.metric t) eps) :=
    exists_stopped_cap_reset hsmall hgrowth W hchart T (cap T) (depth T) (htag T) (hnested T)
  choose next out hsub habs hfront hout using hnext
  let seq : ℕ → StoppedCap (S.base.metric t) eps := fun n => next^[n] T₀
  have hseq (n : ℕ) : seq (n + 1) = next (seq n) := Function.iterate_succ_apply' _ _ _
  have hmono : Monotone (fun n => (seq n).region) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hseq]
    exact hsub (seq n)
  apply not_exists_monotone_singleton_cap_resets_in_compact
    (S := S) (epsc := eps) isCompact_univ
    (by linarith : 13000 * eps ≤ 1 / 156000)
    (fun n => (seq n).center) (fun n => out (seq n))
    (fun n => (W (seq n).center).domain.carrier) (fun n => cap (seq n))
    (fun n => depth (seq n)) (fun n => (seq n).region) hmono
    (fun n => (seq n).cap.isCompact_carrier.isClosed)
    (fun _ _ => 0) (fun _ => continuous_const) (fun _ _ => by norm_num)
    (fun _ => rfl)
    (fun n => hfront (seq n)) (fun n => hout (seq n))
  · intro n
    rw [hseq]
    exact habs (seq n)
  · exact fun _ => mem_univ _


omit [SigmaCompactSpace M] in
private theorem cap_frontier_nested_or_cover
    [PreconnectedSpace M]
    {g : SmoothRiemannianMetric I3 M} {W U : Set M}
    (old : CapCore W) {p : M}
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| ≤ 4)
    (hfront : frontier W = range (fun q : Sphere 2 => nk.map (q, level)))
    (hmake : ∃ K : Set M, Nonempty (CapCore K) ∧ IsCompact K ∧
      closure (interior K) = K ∧ frontier K = range (fun q : Sphere 2 => nk.map (q, level)) ∧
      K ⊆ interior U) :
    W ⊆ interior U ∨
      ∃ K : Set M, Nonempty (CapCore K) ∧ K ∩ W = frontier W ∧
        frontier K = frontier W ∧ W ∪ K = univ := by
  obtain ⟨K, hKcap, hKcompact, hKreg, hKfront, hKU⟩ := hmake
  have hW := old.closure_interior_carrier
  have hconn : IsPreconnected (interior W) :=
    (isConnected_interior_of_compact_regular_neck_boundary nk hlevel
      old.isCompact_carrier hW hfront).isPreconnected
  let trans : Cylinder ≃ₜ Cylinder :=
    { toFun := fun z => (z.1, level + z.2)
      invFun := fun z => (z.1, z.2 - level)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := trans.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph
  have hzero (q : Sphere 2) : T (q, 0) = nk.map (q, level) := by
    change nk.map (q, level + 0) = _
    rw [add_zero]
  have hsrc (q : Sphere 2) : (q, 0) ∈ T.source := by
    change (q, level + 0) ∈ nk.map.source
    rw [add_zero]
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    exact nk.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hc := DifferentialGeometry.Topology.subset_or_fill_of_shared_cylinder_boundary
    T hsrc hW hKreg hconn isClosed_empty
    (by simpa only [hzero, union_empty] using hfront)
    (by simpa only [hzero] using hKfront)
    (disjoint_empty _)
  simp only [hzero] at hc
  rcases hc with hWK | ⟨hinter, _, hfrontempty, _⟩
  · exact Or.inl (hWK.trans hKU)
  · exact Or.inr ⟨K, hKcap, hinter.trans hfront.symm, hKfront.trans hfront.symm,
      (isClopen_iff_frontier_eq_empty.mpr hfrontempty).eq_univ
        (old.nonempty_carrier.mono subset_union_left)⟩


private theorem compact_canonical_neck_cap_cover_alternatives
    [PreconnectedSpace M] [CompactSpace M]
    (hsmall : eps ≤ 1 / 2028000000)
    (hgrowth : ∀ (W : Set M), CapCore W →
      ∀ (x : M) (initial : SpatialNeck (S.base.metric t) eps x) (a : ℝ), |a| ≤ 4 →
      frontier W = range (fun q : Sphere 2 => initial.map (q, a)) →
      ∃ K : Set M, ∃ p : M, ∃ neck : SpatialNeck (S.base.metric t) eps p, ∃ level : ℝ,
        Nonempty (CapCore K) ∧ W ⊆ K ∧ closure (interior K) = K ∧
        |level| ≤ 4 ∧ frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
        ¬ Nonempty (SpatialNeck (S.base.metric t) eps (neck.map (neck.center, level))))
    (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t)
    (hchart : ∀ x, (W x).capTubeHasNeckChart eps)
    (hfill : ∀ (T : StoppedCap (S.base.metric t) eps),
      ∀ cap : LocalCap S eps T.center t (W T.center).domain.carrier,
      ∀ depth : ∀ z ∈ cap.tube, 10000 / Real.sqrt (S.scalar t T.center) ≤
        metricDistance (S.base.metric t) T.center z,
      (W T.center).alternative = CanonicalAlternative.cap cap depth →
      ∃ K : Set M, Nonempty (CapCore K) ∧ IsCompact K ∧
        closure (interior K) = K ∧ frontier K = range (fun q : Sphere 2 => T.neck.map (q,T.level)) ∧
        K ⊆ interior cap.core.carrier) :
    (∀ x : M, Nonempty (SpatialNeck (S.base.metric t) eps x)) ∨
      Nonempty (PositiveComponent (M := M) univ) ∨
      (∃ x : M, Nonempty (RoundComponent S eps x t univ)) ∨
      ∃ (K L : Set M) (p : M) (neck : SpatialNeck (S.base.metric t) eps p) (level : ℝ),
        Nonempty (CapCore K) ∧ Nonempty (CapCore L) ∧ |level| ≤ 4 ∧
        frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
        L ∩ K = frontier K ∧ frontier L = frontier K ∧ K ∪ L = univ := by
  classical
  by_cases hneck : ∀ x : M, Nonempty (SpatialNeck (S.base.metric t) eps x)
  · exact Or.inl hneck
  right
  by_cases hpositive : Nonempty (PositiveComponent (M := M) univ)
  · exact Or.inl hpositive
  right
  by_cases hround : ∃ x : M, Nonempty (RoundComponent S eps x t univ)
  · exact Or.inl hround
  right
  by_contra hncover
  push Not at hneck
  obtain ⟨x, hx⟩ := hneck
  obtain ⟨cap₀, depth₀, htag₀⟩ :=
    exists_canonical_cap_of_not_whole W hpositive hround x (fun h => h.elim hx.false)
  obtain ⟨V, v, nk, hmodel, _, _, _, hfront, _, _⟩ :=
    (W x).exists_cap_core_with_spatial_neck_frontier (hchart x) cap₀ depth₀ htag₀
  obtain ⟨K₀, p₀, neck₀, level₀, hmodel₀, _, _, hbound₀, hfront₀, hstop₀⟩ :=
    hgrowth V.carrier hmodel.some v nk (1 / 2) (by norm_num) hfront
  let T₀ : StoppedCap (S.base.metric t) eps :=
    ⟨K₀, hmodel₀.some, p₀, neck₀, level₀, hbound₀, hfront₀, hstop₀⟩
  have hcap (T : StoppedCap (S.base.metric t) eps) :=
    exists_canonical_cap_of_not_whole W hpositive hround T.center T.stopped
  choose cap depth htag using hcap
  have hnested (T : StoppedCap (S.base.metric t) eps) : T.region ⊆ (cap T).core.carrier := by
    rcases cap_frontier_nested_or_cover T.cap T.neck T.bound T.frontier_eq
      (hfill T (cap T) (depth T) (htag T)) with hin | ⟨L, hL, hmeet, hboundary, hcover⟩
    · exact hin.trans interior_subset
    · exact (hncover ⟨T.region, L, T.point, T.neck, T.level, ⟨T.cap⟩, hL, T.bound,
      T.frontier_eq, hmeet, hboundary, hcover⟩).elim
  exact not_forall_nested_cap_at_stopped_frontiers hsmall hgrowth W hchart T₀ cap depth htag hnested


theorem exists_compact_canonical_neck_cap_cover_alternatives_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (C1 C2 t : ℝ)
        (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t),
        (∀ x, (W x).capTubeHasNeckChart eps) →
        (∀ x : M, Nonempty (SpatialNeck (S.base.metric t) eps x)) ∨
          Nonempty (PositiveComponent (M := M) univ) ∨
          (∃ x : M, Nonempty (RoundComponent S eps x t univ)) ∨
          ∃ (K L : Set M) (p : M) (neck : SpatialNeck (S.base.metric t) eps p) (level : ℝ),
            Nonempty (CapCore K) ∧ Nonempty (CapCore L) ∧ |level| ≤ 4 ∧
            frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
            L ∩ K = frontier K ∧ frontier L = frontier K ∧ K ∪ L = univ := by
  obtain ⟨eta, heta, hgrowth⟩ := exists_spatial_neck_cap_frontier_non_neck_tolerance.{u}
  refine ⟨min eta (1 / 2028000000), lt_min heta (by norm_num), ?_⟩
  intro eps heps M _ _ _ _ _ _ D S C1 C2 t W hchart
  have hsmall : eps ≤ 1 / 2028000000 := heps.trans (min_le_right _ _)
  have hstep := hgrowth eps (heps.trans (min_le_left _ _)) M (S.base.metric t)
  apply compact_canonical_neck_cap_cover_alternatives hsmall hstep W hchart
  intro T cap depth htag
  have hlevel : |T.level| < eps⁻¹ := T.bound.trans_lt
    ((lt_inv_comm₀ (by norm_num) T.neck.eps_pos).mpr (by linarith [T.neck.eps_small]))
  apply cap.core_model.exists_capCore_side_of_sphere_embedding
    (fun q : Sphere 2 => T.neck.map (q, T.level)) (T.neck.isSmoothEmbedding_level hlevel)
  rintro z ⟨q, rfl⟩
  exact T.neck.image_slab_subset_cap_core_of_center_in_slab
    (hsmall.trans (by norm_num) : eps ≤ 1 / 8646) T.neck.center T.bound rfl cap depth
    ⟨(q, T.level), ⟨mem_univ _, abs_le.mp T.bound⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
