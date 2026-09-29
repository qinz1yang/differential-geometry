import DifferentialGeometry.Geometry.Neck.CompactCapCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapTruncation
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Neck.SpatialRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness
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
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tubeMap z) ∧
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


omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem positive_component_restrictOpen
    {U : TopologicalSpace.Opens M} (c : PositiveComponent (M := M) (U : Set M)) :
    Nonempty (PositiveComponent (M := U) Set.univ) := by
  have hU : Nonempty U := by
    cases c with
    | sphere F hsrc htgt =>
      obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty
        (x := (0 : EuclideanSpace ℝ (Fin 4))) (r := 1)).mpr zero_le_one
      let z : Sphere 3 := ⟨z, hz⟩
      refine ⟨⟨F z, ?_⟩⟩
      change F z ∈ (U : Set M)
      rw [← htgt]
      exact F.map_source (hsrc.symm ▸ mem_univ z)
    | projective Z pr F hsrc htgt =>
      obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty
        (x := (0 : EuclideanSpace ℝ (Fin 4))) (r := 1)).mpr zero_le_one
      let z : Sphere 3 := ⟨z, hz⟩
      refine ⟨⟨F (pr.quotient z), ?_⟩⟩
      change F (pr.quotient z) ∈ (U : Set M)
      rw [← htgt]
      exact F.map_source (hsrc.symm ▸ mem_univ _)
  let e := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U hU
  have hetarget : e.target = (U : Set M) := U.openPartialHomeomorphSubtypeCoe_target hU
  have hesource : e.source = Set.univ := rfl
  have himage : e.symm '' (U : Set M) = (Set.univ : Set U) := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨(y : M), y.property, ?_⟩
      change e.symm (e y) = y
      exact e.symm_apply_apply (hesource.symm ▸ mem_univ y)
  cases c with
  | sphere F hsrc htgt =>
    refine ⟨PositiveComponent.sphere (F.trans e.symm) ?_ ?_⟩
    · rw [PartialDiffeomorph.trans_source, hsrc, univ_inter]
      apply Set.eq_univ_of_forall
      intro z
      change F z ∈ e.target
      rw [hetarget, ← htgt]
      exact F.map_source (hsrc.symm ▸ mem_univ z)
    · change (F.toPartialEquiv.trans e.symm.toPartialEquiv).target = _
      rw [PartialEquiv.trans_target'']
      change e.symm '' (e.target ∩ F.target) = _
      rw [hetarget, htgt, inter_self, himage]
  | projective Z pr F hsrc htgt =>
    refine ⟨PositiveComponent.projective Z pr (F.trans e.symm) ?_ ?_⟩
    · rw [PartialDiffeomorph.trans_source, hsrc, univ_inter]
      apply Set.eq_univ_of_forall
      intro z
      change F z ∈ e.target
      rw [hetarget, ← htgt]
      exact F.map_source (hsrc.symm ▸ mem_univ z)
    · change (F.toPartialEquiv.trans e.symm.toPartialEquiv).target = _
      rw [PartialEquiv.trans_target'']
      change e.symm '' (e.target ∩ F.target) = _
      rw [hetarget, htgt, inter_self, himage]


private def roundComponentRestrictOpen
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] (x : U)
    (R : RoundComponent S eps (x : M) t (U : Set M)) :
    RoundComponent (solutionOnRestrictOpen S U) eps x t univ := by
  letI := R.topology
  letI := R.charted
  letI := R.smooth
  letI := R.t2
  letI := R.compact
  letI := R.connected
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩
  have hitarget : i.target = (U : Set M) := U.openPartialHomeomorphSubtypeCoe_target ⟨x⟩
  have hmap (z : R.Z) : R.map z ∈ U := by
    change (R.map z : M) ∈ (U : Set M)
    have hz : R.map z ∈ R.map.target :=
      R.map.map_source (by rw [R.source_eq]; exact mem_univ z)
    simpa only [R.target_eq] using hz
  let F := R.map.trans i.symm
  have hsource : F.source = univ := by
    ext z
    rw [show F.source = R.map.source ∩ R.map ⁻¹' i.target from rfl, R.source_eq]
    simp only [hitarget, mem_inter_iff, mem_univ, true_and, mem_preimage]
    exact iff_true_intro (hmap z)
  have htarget : F.target = univ := by
    ext z
    change (z ∈ i.source ∧ i z ∈ R.map.target) ↔ z ∈ (univ : Set U)
    rw [R.target_eq]
    exact iff_true_intro ⟨mem_univ z, z.property⟩
  have hval (z : R.Z) : (F z : M) = R.map z := by
    change (i.symm (R.map z) : M) = R.map z
    apply i.right_inv'
    rw [hitarget]
    exact hmap z
  have hdf (z : R.Z) : mfderiv I3 I3 F z = mfderiv I3 I3 R.map z := by
    have heq : (fun y => (F y : M)) = (R.map : R.Z → M) := funext hval
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp, heq]
  have hscalar : (solutionOnRestrictOpen S U).scalar t x = S.scalar t (x : M) :=
    scalar_restrictOpen S U t x
  have hQ : 0 < (solutionOnRestrictOpen S U).scalar t x := hscalar.symm ▸ R.Q_pos
  have hinner (z : R.Z) (v w : TangentSpace I3 (F z)) :
      ((solutionOnRestrictOpen S U).base.metric t).inner (F z) v w =
        (S.base.metric t).inner (R.map z) v w := by
    change ((S.base.metric t).restrictOpen U).inner (F z) v w = _
    rw [SmoothRiemannianMetric.restrictOpen_inner, hval]
  refine {
    Z := R.Z
    topology := R.topology
    charted := R.charted
    smooth := R.smooth
    t2 := R.t2
    compact := R.compact
    connected := R.connected
    metric := R.metric
    p := R.p
    scalar_one := R.scalar_one
    constant_curvature := R.constant_curvature
    map := F
    source_eq := hsource
    target_eq := htarget
    center_eq := ?_
    Q_pos := hQ
    comparison := ?_
    metric_bounds := ?_ }
  · apply Subtype.ext
    exact (hval R.p).trans R.center_eq
  · refine {
      pullback := R.comparison.pullback
      pullback_eq := ?_
      jet := R.comparison.jet
      jet_zero := R.comparison.jet_zero
      jet_succ := R.comparison.jet_succ
      equivalence := R.comparison.equivalence
      close := R.comparison.close }
    intro s z hz v
    rw [R.comparison.pullback_eq s z hz v]
    simp only [scaleMetric_inner, hscalar, hinner, hdf]
    rfl
  · intro z v
    rw [hscalar, hinner, hdf]
    exact R.metric_bounds z v


private theorem CanonicalWitness.exists_cap_core_on_connectedComponent
    (U : TopologicalSpace.Opens M) (xU : U)
    (hU : (U : Set M) = connectedComponent (xU : M))
    (W : CanonicalWitness S eps C1 C2 (xU : M) t)
    (hchart : W.capTubeHasNeckChart eps)
    (cap : LocalCap S eps (xU : M) t W.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t (xU : M)) ≤ metricDistance (S.base.metric t) (xU : M) z)
    (htag : W.alternative = CanonicalAlternative.cap cap hdepth) :
    ∃ (K : CompactDomain U) (v : U) (nk : SpatialNeck ((S.base.metric t).restrictOpen U) eps v),
      Nonempty (CapCore K.carrier) ∧
      Subtype.val '' K.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      (∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (nk.map z : M) = cap.tubeMap z) ∧
      riemannianBallOf ((S.base.metric t).restrictOpen U) xU
        (1000 / Real.sqrt (metricScalarAt ((S.base.metric t).restrictOpen U) xU)) ⊆
          interior K.carrier := by
  obtain ⟨K, v, nk, hmodel, hK, hxK, hKW, hfront, hmap, houtside⟩ :=
    W.exists_cap_core_with_spatial_neck_frontier hchart cap hdepth htag
  have hKU : K.carrier ⊆ U := by
    rw [hU]
    exact K.connected.subset_connectedComponent (interior_subset hxK)
  have hvK : v ∈ K.carrier := by
    rw [← nk.center_eq, hmap, hK]
    exact Or.inr ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hvU : v ∈ U := hKU hvK
  have hcapture : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
    rw [hU]
    have hvc : v ∈ connectedComponent (xU : M) := by
      change v ∈ (U : Set M) at hvU
      rwa [hU] at hvU
    rw [connectedComponent_eq hvc]
    exact nk.controlled_range_subset_connectedComponent
  obtain ⟨hvU', nkU, hcenterU, hmapU, hinvU, htargetU, hscalarU⟩ :=
    nk.exists_restrict_target U hcapture
  let KU := K.restrictOpen U hKU
  have hhalf (q : Sphere 2) : (q, (1 / 2 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hinv : (1 : ℝ) < eps⁻¹ := (one_lt_inv₀ W.eps_pos).mpr W.eps_lt_one
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  refine ⟨KU, ⟨v, hvU'⟩, nkU, hmodel.some.nonempty_preimage_open U hKU,
    (K.image_restrictOpen_carrier U hKU).trans hK, ?_, ?_, ?_⟩
  · rw [K.frontier_restrictOpen_carrier U hKU, hfront]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, Subtype.ext ?_⟩
      exact (hmapU (q, 1 / 2) (hhalf q)).trans hq
    · rintro ⟨q, rfl⟩
      exact ⟨q, (hmapU (q, 1 / 2) (hhalf q)).symm⟩
  · intro z hz
    exact (hmapU z hz).trans (hmap z)
  · have hcore : cap.core.carrier ⊆ K.carrier := by rw [hK]; exact subset_union_left
    have hball := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
      (S.base.metric t) cap.center_inside
      (r := ENNReal.ofReal (10000 / Real.sqrt (S.scalar t (xU : M)))) (by
        intro z hz
        have hztube : z ∈ cap.tube := (cap.overlap_eq.symm ▸ hz).2
        exact (ENNReal.ofReal_le_ofReal (hdepth z hztube)).trans ENNReal.ofReal_toReal_le)
    intro z hz
    rw [K.interior_restrictOpen_carrier U hKU]
    apply interior_mono hcore (hball ?_)
    have hscalar : metricScalarAt ((S.base.metric t).restrictOpen U) xU = S.scalar t (xU : M) :=
      hscalarU xU
    change riemannianEDistOf ((S.base.metric t).restrictOpen U) xU z <
      ENNReal.ofReal (1000 / Real.sqrt (metricScalarAt ((S.base.metric t).restrictOpen U) xU)) at hz
    rw [hscalar] at hz
    exact ((riemannianEDistOf_le_restrictOpen (S.base.metric t) U xU z).trans_lt hz).trans_le
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)))


theorem CanonicalWitness.spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] (xU : U)
    (hU : (U : Set M) = connectedComponent (xU : M))
    (W : CanonicalWitness S eps C1 C2 (xU : M) t)
    (hchart : W.capTubeHasNeckChart eps)
    (hx : ¬ Nonempty (SpatialNeck ((S.base.metric t).restrictOpen U) eps xU)) :
    Nonempty (PositiveComponent (M := U) univ) ∨
      (∃ z : U, Nonempty (RoundComponent (solutionOnRestrictOpen S U) eps z t univ)) ∨
      ∃ (K : CompactDomain U) (v : U) (nk : SpatialNeck ((S.base.metric t).restrictOpen U) eps v) (a : ℝ),
        0 < metricScalarAt ((S.base.metric t).restrictOpen U) xU ∧ Nonempty (CapCore K.carrier) ∧
        |a| ≤ 4 ∧ frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, a)) ∧
        riemannianBallOf ((S.base.metric t).restrictOpen U) xU
          (1000 / Real.sqrt (metricScalarAt ((S.base.metric t).restrictOpen U) xU)) ⊆
            interior K.carrier := by
  cases htag : W.alternative with
  | neck data =>
    have hcapture : data.strong.toSpatialNeck.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
      rw [hU]
      exact data.strong.toSpatialNeck.controlled_range_subset_connectedComponent
    exact (hx ⟨data.strong.toSpatialNeck.restrictOpen hcapture⟩).elim
  | positive whole data sec =>
    have hdom : W.domain.carrier = (U : Set M) := whole.trans hU.symm
    exact Or.inl (positive_component_restrictOpen (hdom ▸ data))
  | round whole data =>
    have hdom : W.domain.carrier = (U : Set M) := whole.trans hU.symm
    exact Or.inr (Or.inl ⟨xU, ⟨roundComponentRestrictOpen U xU (hdom ▸ data)⟩⟩)
  | cap data depth =>
    obtain ⟨K, v, nk, hmodel, hcarrier, hfront, hmap, hball⟩ :=
      W.exists_cap_core_on_connectedComponent U xU hU hchart data depth htag
    refine Or.inr (Or.inr ⟨K, v, nk, 1 / 2, ?_, hmodel, by norm_num, hfront, hball⟩)
    have hscalar := scalar_restrictOpen S U t xU
    change 0 < (solutionOnRestrictOpen S U).scalar t xU
    rw [hscalar]
    exact W.Q_pos

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
