import DifferentialGeometry.Geometry.Neck.StaticQuarterBand
import DifferentialGeometry.Geometry.Neck.CompactCapGrowth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreSphereFilling
import DifferentialGeometry.Geometry.Neck.SpatialFrontierRecentering
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Geometry.Neck.QuarterBandPacking
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapConnectedInterior

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {eps : ℝ}

private structure StaticStoppedCap (g : SmoothRiemannianMetric I3 M) (eps : ℝ) where
  region : Set M
  cap : CapCore region
  point : M
  neck : SpatialNeck g eps point
  level : ℝ
  bound : |level| ≤ 4
  frontier_eq : frontier region = range (fun q : Sphere 2 => neck.map (q, level))
  stopped : ¬ Nonempty (SpatialNeck g eps (neck.map (neck.center, level)))

private def StaticStoppedCap.center {g : SmoothRiemannianMetric I3 M} (T : StaticStoppedCap g eps) : M :=
  T.neck.map (T.neck.center, T.level)

private theorem static_cap_frontier_nested_or_cover
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


theorem exists_compact_spatial_neck_cap_cover_alternatives_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
        (g : SmoothRiemannianMetric I3 M),
        (∀ x : M, ¬ Nonempty (SpatialNeck g eps x) →
          ∃ (K : CompactDomain M) (v : M) (nk : SpatialNeck g eps v) (a : ℝ),
            0 < metricScalarAt g x ∧ Nonempty (CapCore K.carrier) ∧ |a| ≤ 4 ∧
            frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
            riemannianBallOf g x (1000 / Real.sqrt (metricScalarAt g x)) ⊆ interior K.carrier) →
        (∀ x : M, Nonempty (SpatialNeck g eps x)) ∨
          ∃ (K L : Set M) (p : M) (neck : SpatialNeck g eps p) (level : ℝ),
            Nonempty (CapCore K) ∧ Nonempty (CapCore L) ∧ |level| ≤ 4 ∧
            frontier K = range (fun q : Sphere 2 => neck.map (q, level)) ∧
            L ∩ K = frontier K ∧ frontier L = frontier K ∧ K ∪ L = univ := by
  classical
  obtain ⟨eta, heta, hgrowth⟩ := exists_spatial_neck_cap_frontier_non_neck_tolerance.{u}
  refine ⟨min eta (1 / 2028000000), lt_min heta (by norm_num), ?_⟩
  intro eps heps M _ _ _ _ _ _ g hcap
  have hsmall : eps ≤ 1 / 2028000000 := heps.trans (min_le_right _ _)
  have hstep := hgrowth eps (heps.trans (min_le_left _ _)) M g
  by_cases hall : ∀ x : M, Nonempty (SpatialNeck g eps x)
  · exact Or.inl hall
  right
  by_contra hcover
  push Not at hall
  obtain ⟨x, hx⟩ := hall
  obtain ⟨U₀, v₀, nk₀, a₀, _, hcap₀, ha₀, hf₀, hball₀⟩ :=
    hcap x (fun h => h.elim hx.false)
  obtain ⟨K₀, p₀, neck₀, level₀, hmodel₀, _, _, hbound₀, hfront₀, hstop₀⟩ :=
    hstep U₀.carrier hcap₀.some v₀ nk₀ a₀ ha₀ hf₀
  let T₀ : StaticStoppedCap g eps := ⟨K₀, hmodel₀.some, p₀, neck₀, level₀, hbound₀, hfront₀, hstop₀⟩
  have hnext (T : StaticStoppedCap g eps) :
      ∃ (T' : StaticStoppedCap g eps) (out : SpatialNeck g (13000 * eps) T.center),
        T.region ⊆ T'.region ∧
        out.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ T'.region ∧
        out.map (out.center, 1 / 4) ∉ T.region := by
    obtain ⟨U, v, nk, a, _, hcU, ha, hfrontU, hball⟩ := hcap T.center T.stopped
    have hslab := T.neck.image_slab_subset_of_ball_subset
      (hsmall.trans (by norm_num) : eps ≤ 1 / 8646) T.neck.center T.bound rfl hball
    have hlevel : |T.level| < eps⁻¹ := T.bound.trans_lt
      ((lt_inv_comm₀ (by norm_num) T.neck.eps_pos).mpr (by linarith [T.neck.eps_small]))
    have hfill := hcU.some.exists_capCore_side_of_sphere_embedding
      (fun q : Sphere 2 => T.neck.map (q, T.level)) (T.neck.isSmoothEmbedding_level hlevel)
      (by
        rintro z ⟨q, rfl⟩
        exact hslab ⟨(q, T.level), ⟨mem_univ _, abs_le.mp T.bound⟩, rfl⟩)
    have hsub : T.region ⊆ U.carrier := by
      rcases static_cap_frontier_nested_or_cover T.cap T.neck T.bound T.frontier_eq hfill with h | h
      · exact h.trans interior_subset
      · obtain ⟨L, hL, hmeet, hboundary, hfill⟩ := h
        exact False.elim (hcover ⟨T.region, L, T.point, T.neck, T.level,
          ⟨T.cap⟩, hL, T.bound, T.frontier_eq, hmeet, hboundary, hfill⟩)
    obtain ⟨out, _, houtzero, _, hout⟩ :=
      T.neck.exists_outward_at_coordinate_mul (hsmall.trans (by norm_num)) T.neck.center T.bound
        T.cap.closure_interior_carrier isClosed_empty
        (by simpa only [union_empty] using T.frontier_eq) (disjoint_empty _)
    have hfront : frontier T.region = range (fun q : Sphere 2 => out.map (q, 0)) := by
      rw [T.frontier_eq]
      exact congrArg range (funext houtzero).symm
    have hband := out.quarter_band_subset_ball_sdiff_of_outward_graph
      (by linarith : 13000 * eps ≤ 1 / 8646) hball
      (fun _ => 0) continuous_const (fun _ => by norm_num) rfl T.cap.isCompact_carrier.isClosed
      hfront hout
    obtain ⟨K, p, neck, level, hmodel, hUK, _, hbound, hfrontK, hstop⟩ :=
      hstep U.carrier hcU.some v nk a ha hfrontU
    let T' : StaticStoppedCap g eps := ⟨K, hmodel.some, p, neck, level, hbound, hfrontK, hstop⟩
    exact ⟨T', out, hsub.trans hUK,
      fun z hz => hUK (interior_subset (hband hz).1),
      (hband ⟨(out.center, 1 / 4), ⟨mem_univ _, by norm_num⟩, rfl⟩).2⟩
  choose next out hsub hband hfresh using hnext
  let T : ℕ → StaticStoppedCap g eps := fun n => next^[n] T₀
  have hT (n : ℕ) : T (n + 1) = next (T n) := Function.iterate_succ_apply' _ _ _
  have hmono : Monotone (fun n => (T n).region) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hT]
    exact hsub (T n)
  exact not_exists_monotone_fresh_neck_quarter_bands_in_compact g isCompact_univ
    (by linarith : 13000 * eps ≤ 1 / 156000) (fun n => (T n).center)
    (fun n => out (T n)) (fun _ => mem_univ _) (fun n => (T n).region) hmono
    (fun n => by rw [hT]; exact hband (T n)) (fun n => hfresh (T n))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
