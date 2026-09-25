import DifferentialGeometry.Geometry.Neck.CompactCapCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapTruncation
import DifferentialGeometry.Geometry.Metric.Distance.Boundary

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


theorem CanonicalWitness.spatial_cap_or_whole_of_not_spatial_neck
    [PreconnectedSpace M] {x : M}
    (W : CanonicalWitness S eps C1 C2 x t)
    (hchart : W.capTubeHasNeckChart eps)
    (hx : ¬ Nonempty (SpatialNeck (S.base.metric t) eps x)) :
    Nonempty (PositiveComponent (M := M) univ) ∨
      (∃ z : M, Nonempty (RoundComponent S eps z t univ)) ∨
      ∃ (K : CompactDomain M) (v : M) (nk : SpatialNeck (S.base.metric t) eps v) (a : ℝ),
        0 < metricScalarAt (S.base.metric t) x ∧ Nonempty (CapCore K.carrier) ∧ |a| ≤ 4 ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
        riemannianBallOf (S.base.metric t) x
          (1000 / Real.sqrt (metricScalarAt (S.base.metric t) x)) ⊆ interior K.carrier := by
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
    obtain ⟨K, v, nk, hmodel, hK, _, _, hfront, _, _⟩ :=
      W.exists_cap_core_with_spatial_neck_frontier hchart data depth htag
    refine Or.inr (Or.inr ⟨K, v, nk, 1 / 2, W.Q_pos, hmodel, by norm_num, hfront, ?_⟩)
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
  obtain ⟨eta, heta, hcover⟩ := exists_compact_spatial_neck_cap_cover_alternatives_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ D S C1 C2 t W hchart
  classical
  by_cases hpositive : Nonempty (PositiveComponent (M := M) univ)
  · exact Or.inr (Or.inl hpositive)
  by_cases hround : ∃ x : M, Nonempty (RoundComponent S eps x t univ)
  · exact Or.inr (Or.inr (Or.inl hround))
  rcases hcover eps heps M (S.base.metric t) (fun x hx =>
      (((W x).spatial_cap_or_whole_of_not_spatial_neck (hchart x) hx).resolve_left hpositive).resolve_left hround)
      with hn | hc
  · exact Or.inl hn
  · exact Or.inr (Or.inr (Or.inr hc))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
