import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Neck.SpatialSourceBounds

open private exists_compactDomain_of_cylinder_slab from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
open private slab_boundary_chart from
  DifferentialGeometry.Topology.Manifold.CylinderSlabBoundary

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
  {U : Set M}

omit [T2Space M] in
theorem SpatialLocalCap.tubeMap_mem_core_iff
    (cap : SpatialLocalCap g eps x U) {z : Sphere 2} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    cap.tubeMap (z, a) ∈ cap.core.carrier ↔ a = 0 := by
  have hsource : (z, a) ∈ cap.tubeMap.source := cap.tube_domain ⟨mem_univ z, ha⟩
  have htube : cap.tubeMap (z, a) ∈ cap.tube :=
    cap.tube_eq ▸ ⟨(z, a), ⟨mem_univ z, ha⟩, rfl⟩
  constructor
  · intro hcore
    have hboundary : cap.tubeMap (z, a) ∈ frontier cap.core.carrier :=
      cap.overlap_eq ▸ ⟨hcore, htube⟩
    rw [← cap.inner_boundary] at hboundary
    obtain ⟨⟨w, b⟩, hb, heq⟩ := hboundary
    have hb0 : b = 0 := hb.2
    have hsource' : (w, b) ∈ cap.tubeMap.source :=
      cap.tube_domain ⟨mem_univ w, by
        simpa only [hb0] using (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)⟩
    have heq' : (w, b) = (z, a) := by
      calc
        (w, b) = cap.tubeMap.symm (cap.tubeMap (w, b)) :=
          (cap.tubeMap.left_inv' hsource').symm
        _ = cap.tubeMap.symm (cap.tubeMap (z, a)) := congrArg cap.tubeMap.symm heq
        _ = (z, a) := cap.tubeMap.left_inv' hsource
    exact (congrArg Prod.snd heq').symm.trans hb0
  · rintro rfl
    have hboundary : cap.tubeMap (z, 0) ∈ frontier cap.core.carrier :=
      cap.inner_boundary ▸ ⟨(z, 0), ⟨mem_univ z, rfl⟩, rfl⟩
    rw [← cap.overlap_eq] at hboundary
    exact hboundary.1

omit [T2Space M] in
theorem SpatialLocalCap.mem_truncated_core_on_tube
    (cap : SpatialLocalCap g eps x U) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (q : Sphere 2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    cap.tubeMap (q, s) ∈ cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c) ↔
      s ≤ c := by
  constructor
  · rintro (hcore | ⟨z, hz, hzeq⟩)
    · have hzero := (cap.tubeMap_mem_core_iff hs).mp hcore
      exact hzero ▸ hc.1.le
    · have heq := cap.tubeMap.injOn
        (cap.tube_domain ⟨hz.1, hz.2.1, hz.2.2.trans hc.2.le⟩)
        (cap.tube_domain ⟨mem_univ _, hs⟩) hzeq
      have hh : z.2 = s := congrArg Prod.snd heq
      exact hh ▸ (show z.2 ≤ c from hz.2.2)
  · intro hsc
    exact Or.inr ⟨(q, s), ⟨mem_univ _, hs.1, hsc⟩, rfl⟩

theorem SpatialLocalCap.nonempty_capCore_truncated_core
    (cap : SpatialLocalCap g eps x U) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    Nonempty (CapCore
      (cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c))) := by
  by_cases hc0 : c = 0
  · have hsub : cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c) ⊆ cap.core.carrier := by
      rintro y ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
      have ha0 : a = 0 := by rw [hc0] at ha; exact le_antisymm ha.2 ha.1
      exact (cap.tubeMap_mem_core_iff (by rw [ha0]; exact ⟨le_rfl, zero_le_one⟩)).mpr ha0
    simpa only [union_eq_self_of_subset_right hsub] using ⟨cap.coreModel⟩
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
  let A : ℝ ≃ₘ[ℝ] ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc0).toContinuousLinearEquiv.toDiffeomorph
  let T := ((Diffeomorph.refl I2 (Sphere 2) ∞).prodCongr A).toPartialDiffeomorph.trans
    cap.tubeMap
  have hT (q : Sphere 2) (a : ℝ) : T (q, a) = cap.tubeMap (q, c * a) := rfl
  have hsource : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source := by
    intro z hz
    refine ⟨mem_univ _, cap.tube_domain ?_⟩
    exact ⟨mem_univ _, mul_nonneg hc.1 hz.2.1,
      (mul_le_mul_of_nonneg_left hz.2.2 hc.1).trans (by simpa using hc.2)⟩
  have hfront : frontier cap.core.carrier = range (fun q : Sphere 2 => T (q, 0)) := by
    rw [← cap.inner_boundary]
    ext y
    constructor
    · rintro ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
      have ha0 : a = 0 := ha
      exact ⟨q, by simp only [hT, mul_zero, ha0]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, by simp only [hT, mul_zero]⟩
  have hside (q : Sphere 2) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
      (hm : T (q, a) ∈ cap.core.carrier) : a = 0 := by
    rw [hT] at hm
    have hca : c * a ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hc.1 ha.1,
        (mul_le_mul_of_nonneg_left ha.2 hc.1).trans (by simpa using hc.2)⟩
    exact (mul_eq_zero.mp ((cap.tubeMap_mem_core_iff hca).mp hm)).resolve_left hc0
  have himage : T '' (univ ×ˢ Icc (0 : ℝ) 1) =
      cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c) := by
    ext y
    constructor
    · rintro ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
      exact ⟨(q, c * a), ⟨mem_univ _, mul_nonneg hc.1 ha.1,
        by simpa using mul_le_mul_of_nonneg_left ha.2 hc.1⟩, rfl⟩
    · rintro ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
      refine ⟨(q, a / c), ⟨mem_univ _, div_nonneg ha.1 hc.1,
        (div_le_one hcpos).mpr ha.2⟩, ?_⟩
      rw [hT, mul_div_cancel₀ _ hc0]
  simpa only [himage] using cap.coreModel.nonempty_union_cylinder T hsource hfront hside

theorem SpatialLocalCap.exists_truncated_compactDomain
    (cap : SpatialLocalCap g eps x U) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ K : CompactDomain M,
      K.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ U ∧
      frontier K.carrier = range (fun q : Sphere 2 => cap.tubeMap (q, c)) := by
  have hcpos : 0 < c := hc.1
  let V := cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) c)
  have hsrc : (univ ×ˢ Icc (0 : ℝ) c : Set Cylinder) ⊆ cap.tubeMap.source :=
    fun z hz => cap.tube_domain ⟨hz.1, hz.2.1, hz.2.2.trans hc.2.le⟩
  obtain ⟨T, hT⟩ := exists_compactDomain_of_cylinder_slab cap.tubeMap hc.1 hsrc
  have hVc : IsCompact V := cap.core.compact.union (hT ▸ T.compact)
  have hVU : V ⊆ U := by
    rintro y (hy | ⟨z, hz, rfl⟩)
    · exact cap.union_eq.ge (Or.inl hy)
    · exact cap.union_eq.ge (Or.inr (cap.tube_eq ▸
        ⟨z, ⟨hz.1, hz.2.1, hz.2.2.trans hc.2.le⟩, rfl⟩))
  have hcoreInt : cap.core.carrier ⊆ interior V := by
    intro y hy
    by_cases hyint : y ∈ interior cap.core.carrier
    · exact interior_mono subset_union_left hyint
    · have hbaseNeighborhood : y ∈ interior U := cap.core_inside hy
      have hVnear : V ∈ 𝓝 y := by
        have hremove : y ∉ cap.tubeMap '' (univ ×ˢ Icc (c / 2) 1) := by
          rintro ⟨q, hq, hqy⟩
          have hqcore : cap.tubeMap q ∈ cap.core.carrier := hqy.symm ▸ hy
          have heq := (cap.tubeMap_mem_core_iff
            ⟨hq.2.1.trans' (half_pos hc.1).le, hq.2.2⟩).mp hqcore
          linarith [hq.2.1]
        have hclosed : IsClosed (cap.tubeMap '' (univ ×ˢ Icc (c / 2) 1)) :=
          ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
            (cap.tubeMap.contMDiffOn_toFun.continuousOn.mono (fun q hq =>
              cap.tube_domain ⟨hq.1, (half_pos hc.1).le.trans hq.2.1, hq.2.2⟩))).isClosed
        apply Filter.mem_of_superset ((isOpen_interior.inter hclosed.isOpen_compl).mem_nhds
          ⟨hbaseNeighborhood, hremove⟩)
        intro q hq
        rcases cap.union_eq.le (interior_subset hq.1) with hqcore | hqtube
        · exact Or.inl hqcore
        · obtain ⟨z, hz, rfl⟩ := cap.tube_eq.symm ▸ hqtube
          have hzhalf : z.2 < c / 2 := by
            by_contra hn
            exact hq.2 ⟨z, ⟨hz.1, le_of_not_gt hn, hz.2.2⟩, rfl⟩
          exact Or.inr ⟨z, ⟨hz.1, hz.2.1, by linarith⟩, rfl⟩
      exact mem_interior_iff_mem_nhds.mpr hVnear
  have hfront : frontier V = range (fun q : Sphere 2 => cap.tubeMap (q, c)) := by
    apply Subset.antisymm
    · intro y hy
      have hyV := hVc.isClosed.frontier_subset hy
      rcases hyV with hycore | ⟨z, hz, rfl⟩
      · exact False.elim (hy.2 (hcoreInt hycore))
      · by_cases heq : z.2 = c
        · exact ⟨z.1, by rw [← heq]⟩
        have hzlt : z.2 < c := lt_of_le_of_ne hz.2.2 heq
        by_cases hz0 : z.2 = 0
        · have hzcore := (cap.tubeMap_mem_core_iff (z := z.1)
            ⟨hz.2.1, hz.2.2.trans hc.2.le⟩).mpr hz0
          exact False.elim (hy.2 (hcoreInt hzcore))
        have hzpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hz0)
        have hopen : IsOpen (cap.tubeMap '' (univ ×ˢ Ioo (0 : ℝ) c)) :=
          cap.tubeMap.toOpenPartialHomeomorph.isOpen_image_of_subset_source
            (isOpen_univ.prod isOpen_Ioo) (fun q hq => hsrc ⟨hq.1, hq.2.1.le, hq.2.2.le⟩)
        have hsub : cap.tubeMap '' (univ ×ˢ Ioo (0 : ℝ) c) ⊆ V :=
          fun q hq => Or.inr (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hq)
        exact False.elim (hy.2 (hopen.subset_interior_iff.mpr hsub
          ⟨z, ⟨hz.1, hzpos, hzlt⟩, rfl⟩))
    · rintro y ⟨q, rfl⟩
      have hpoint : cap.tubeMap (q, c) ∈ V := Or.inr ⟨(q, c), ⟨mem_univ _, hc.1.le, le_rfl⟩, rfl⟩
      refine ⟨subset_closure hpoint, ?_⟩
      intro hInt
      have htend : ContinuousAt (fun s : ℝ => cap.tubeMap (q, s)) c :=
        (cap.tubeMap.contMDiffOn_toFun.continuousOn.continuousAt
          (cap.tubeMap.open_source.mem_nhds (hsrc ⟨mem_univ _, hc.1.le, le_rfl⟩))).comp
          (continuous_const.continuousAt.prodMk continuous_id.continuousAt)
      have hmem := htend.preimage_mem_nhds (isOpen_interior.mem_nhds hInt)
      have hR : Ioo c 1 ∈ 𝓝[>] c := Ioo_mem_nhdsGT hc.2
      have hsmall : ∀ᶠ s in 𝓝[>] c, cap.tubeMap (q, s) ∈ interior V := Filter.mem_of_superset
        (nhdsWithin_le_nhds hmem) (fun _ h => h)
      obtain ⟨s, hs, hsv⟩ := ((show ∀ᶠ s in 𝓝[>] c, s ∈ Ioo c 1 from hR).and hsmall).exists
      have hsc := (cap.mem_truncated_core_on_tube hc q
        ⟨hc.1.le.trans hs.1.le, hs.2.le⟩).mp (interior_subset hsv)
      exact (not_lt_of_ge hsc) hs.1
  have hmeet : (cap.core.carrier ∩ T.carrier).Nonempty := by
    let q := DifferentialGeometry.Topology.sphereTwoNorth
    have hm : cap.tubeMap (q, 0) ∈ cap.core.carrier :=
      (cap.tubeMap_mem_core_iff ⟨le_rfl, zero_le_one⟩).mpr rfl
    exact ⟨_, hm, hT.symm ▸ ⟨(q, 0), ⟨mem_univ _, le_rfl, hc.1.le⟩, rfl⟩⟩
  refine ⟨{ carrier := V
            compact := hVc
            connected := by
              change IsConnected (cap.core.carrier ∪ _)
              rw [← hT]
              exact cap.core.connected.union hmeet T.connected
            regular_closed := ?_
            boundary_chart := ?_ }, rfl, interior_mono subset_union_left cap.center_inside,
    hVU, hfront⟩
  · apply Subset.antisymm (closure_minimal interior_subset hVc.isClosed)
    rintro y (hy | hy)
    · exact (closure_mono (interior_mono subset_union_left)) (cap.core.regular_closed.symm ▸ hy)
    · have hsub : T.carrier ⊆ V := fun y hy => Or.inr (hT ▸ hy)
      exact closure_mono (interior_mono hsub) (T.regular_closed.symm ▸ (hT.symm ▸ hy))
  · intro y hy
    obtain ⟨q, rfl⟩ := hfront ▸ hy
    obtain ⟨F, hF, hzero, hside⟩ := slab_boundary_chart cap.tubeMap hc.1 hsrc q
    have hnot : cap.tubeMap (q, c) ∉ cap.core.carrier := by
      rw [cap.tubeMap_mem_core_iff ⟨hc.1.le, hc.2.le⟩]
      exact hc.1.ne'
    let F' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict F cap.core.carrierᶜ
      cap.core.compact.isClosed.isOpen_compl
    refine ⟨F', ⟨hF, hnot⟩, hzero, ?_⟩
    intro z hz
    change z ∈ V ↔ F z 0 ≤ 0
    constructor
    · rintro (hzcore | hzslab)
      · exact (hz.2 hzcore).elim
      · exact (hside z hz.1).mp hzslab
    · intro hh
      exact Or.inr ((hside z hz.1).mpr hh)

variable [SigmaCompactSpace M] {C1 C2 : ℝ}

theorem SpatialCanonicalWitness.alternative_eq_neck_or_cap_of_mul_scalar_lt {y : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hy : y ∈ connectedComponent x)
    (hscalar : C2 * metricScalarAt g y < metricScalarAt g x) :
    (∃ neck : SpatialLocalNeck g eps x W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck) ∨
    ∃ cap : SpatialLocalCap g eps x W.domain.carrier,
      ∃ hdepth : ∀ z ∈ cap.tube,
        10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x z,
        W.alternative = SpatialCanonicalAlternative.cap cap hdepth := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hproper : W.domain.carrier ≠ connectedComponent x := by
    intro hwhole
    have hbound := (W.scalar_bounds y (hwhole.symm ▸ hy)).1
    have hmul := mul_le_mul_of_nonneg_left hbound hC2.le
    have hcancel : C2 * (C2⁻¹ * metricScalarAt g x) = metricScalarAt g x := by
      rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul]
    rw [hcancel] at hmul
    exact (not_le_of_gt hscalar) hmul
  cases W.alternative with
  | neck data => exact Or.inl ⟨data, rfl⟩
  | cap data deep => exact Or.inr ⟨data, deep, rfl⟩
  | positive whole data hsec => exact (hproper whole).elim
  | round whole data => exact (hproper whole).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_normalizedNeck_of_incoming_spatialNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps x.1) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center = x ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).1 = (neck n).map z.1 := by
  classical
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨_, D2, q, _, hD2, hq, hc⟩ := hm epsCan hepsCan le_rfl
  let C : NNReal := ⟨D2, zero_le_one.trans hD2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 :=
    fun y t ht hy => (hc y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  let A := (1 + 4323 * eps) * (metricScalarAt L.metric x + 1)
  obtain ⟨Kold, hKold, hKregular, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch A
  let K : Set G.terminalRegularOpen := Subtype.val ⁻¹' Kold
  have himage : Subtype.val '' K = Kold := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKregular hy⟩, hy, rfl⟩
  have hK : IsCompact K := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hKold
  have hcenter : ∀ᶠ n in atTop,
      G.flow.scalar (τ n) x.1 < metricScalarAt L.metric x + 1 :=
    ((L.tendsto_metricScalarAt x).comp hτ).eventually_lt_const (lt_add_one _)
  have hlate : ∀ᶠ n in atTop, ∀ z : neckBuffer δ, (neck n).map z.1 ∈ Kold := by
    filter_upwards [hcenter, hτ.eventually (Ioo_mem_nhdsLT hd.2)] with n hn ht
    intro z
    apply hcapture (τ n) ht
    have hb := (neck n).scalar_upper_bound_neckBuffer hfit z
    exact hb.trans (mul_le_mul_of_nonneg_left hn.le
      (by have := (neck n).eps_pos; positivity))
  have hrange : ∀ᶠ n in atTop,
      metricScalarAt L.metric x / 2 ≤ G.flow.scalar (τ n) x.val ∧
        G.flow.scalar (τ n) x.val ≤ metricScalarAt L.metric x + 1 := by
    have hscale := (L.tendsto_metricScalarAt x).comp hτ
    filter_upwards [hscale.eventually (Ioo_mem_nhds
      (half_lt_self hx) (lt_add_one (metricScalarAt L.metric x)))] with n hn
    exact ⟨hn.1.le, hn.2.le⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hlate
  have htail := L.eventually_normalizedNeck_of_moving_spatialNecks
    (hτ.comp (tendsto_add_atTop_nat n₀)) (fun _ => x) (fun _ => hx) hδ hδ1 hepsδ hfit k hk
    (fun n => neck (n + n₀))
    (fun n z => hKregular (hn₀ (n + n₀) (by omega) z)) hK
    (Eventually.of_forall fun n z _ => by
      rw [himage]
      exact hn₀ (n + n₀) (by omega) z)
    (half_pos hx) ((tendsto_add_atTop_nat n₀).eventually hrange)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp htail
  apply eventually_atTop.mpr
  refine ⟨n₀ + n₁, fun n hn => ?_⟩
  have heq : n - n₀ + n₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨N, hN, hm, hc⟩ := hn₁ (n - n₀) (by omega)
  refine ⟨N, hN, ?_, ?_⟩
  · exact hm.trans (congrArg (fun i => (neck i).center) heq)
  · intro z
    exact (hc z).trans (congrArg (fun i => (neck i).map z.1) heq)

theorem TerminalLimitMetric.eventually_spatialNeck_of_incoming_spatialNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 11) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps x.val) :
    ∀ᶠ n in atTop, ∃ nk : SpatialNeck L.metric δ x,
      nk.center = (neck n).center ∧
        ∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val := by
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ (neck 0).eps_pos hepsδ.le)
  have hevent := L.eventually_normalizedNeck_of_incoming_spatialNecks hτ x hx hδ
    (hδsmall.trans (by norm_num)) hepsδ hfit ⌈δ⁻¹⌉₊ hk neck
  filter_upwards [hevent] with n hn
  obtain ⟨N, hN, hmark, hmap⟩ := hn
  obtain ⟨nk, hnkmark, hnkmap⟩ := N.exists_spatialNeck le_rfl hδsmall le_rfl
  let nk' : SpatialNeck L.metric δ x := hN ▸ nk
  have hcenter : nk'.center = (neck n).center := by
    cases hN
    exact hnkmark.trans hmark
  have hvalues : ∀ z : neckBuffer δ, (nk'.map z.val).val = (neck n).map z.val := by
    cases hN
    intro z
    exact (congrArg Subtype.val (hnkmap z)).trans (hmap z)
  exact ⟨nk', hcenter, hvalues⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_spatial_neck_or_cap
    (L : G.TerminalLimitMetric) (x y : G.terminalRegularOpen)
    (hy : y.val ∈ connectedComponent x.val) {eps C1 C2 : ℝ}
    (hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x) :
    ∀ᶠ t in 𝓝[<] s, ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x.val,
      (∃ neck : SpatialLocalNeck (G.flow.base.metric t) eps x.val W.domain.carrier,
        W.alternative = SpatialCanonicalAlternative.neck neck) ∨
      ∃ cap : SpatialLocalCap (G.flow.base.metric t) eps x.val W.domain.carrier,
        ∃ depth, W.alternative = SpatialCanonicalAlternative.cap cap depth := by
  have hc := ((L.tendsto_metricScalarAt y).const_mul C2).eventually_lt
    (L.tendsto_metricScalarAt x) hscalar
  filter_upwards [hc] with t ht
  intro W
  exact W.alternative_eq_neck_or_cap_of_mul_scalar_lt hy ht

theorem TerminalLimitMetric.eventually_spatial_neck_or_cap_of_not_isCompact
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (eps C1 C2 : ℝ) :
    ∀ᶠ t in 𝓝[<] s, ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x.val,
      (∃ neck : SpatialLocalNeck (G.flow.base.metric t) eps x.val W.domain.carrier,
        W.alternative = SpatialCanonicalAlternative.neck neck) ∨
      ∃ cap : SpatialLocalCap (G.flow.base.metric t) eps x.val W.domain.carrier,
        ∃ depth, W.alternative = SpatialCanonicalAlternative.cap cap depth := by
  obtain ⟨y, hy, hscalar⟩ :=
    L.exists_scalar_gt_on_connectedComponent_of_not_isCompact x hnoncompact
      (C2 * metricScalarAt L.metric x)
  have hy' : y.val ∈ connectedComponent x.val :=
    continuous_subtype_val.mapsTo_connectedComponent x hy
  have hc := ((L.tendsto_metricScalarAt x).const_mul C2).eventually_lt
    (L.tendsto_metricScalarAt y) hscalar
  filter_upwards [hc] with t ht
  intro W
  have hproper : W.domain.carrier ≠ connectedComponent x.val := by
    intro hwhole
    exact (not_le_of_gt ht) (W.scalar_bounds y.val (hwhole.symm ▸ hy')).2
  cases W.alternative with
  | neck data => exact Or.inl ⟨data, rfl⟩
  | cap data deep => exact Or.inr ⟨data, deep, rfl⟩
  | positive whole data hsec => exact (hproper whole).elim
  | round whole data => exact (hproper whole).elim

theorem exists_spatial_neck_or_cap_sequence_of_eventually
    {x : P.Carrier} {eps C1 C2 q : ℝ}
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x,
        W.capTubeHasNeckChart eps)
    (hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x)
    (hbranch : ∀ᶠ t in 𝓝[<] s,
      ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x,
      (∃ neck : SpatialLocalNeck (G.flow.base.metric t) eps x W.domain.carrier,
        W.alternative = SpatialCanonicalAlternative.neck neck) ∨
      ∃ cap : SpatialLocalCap (G.flow.base.metric t) eps x W.domain.carrier,
        ∃ depth, W.alternative = SpatialCanonicalAlternative.cap cap depth) :
    ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ Ioo a s) ∧ Tendsto τ atTop (𝓝[<] s) ∧
      ∃ W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) eps C1 C2 x,
        (∀ n, (W n).capTubeHasNeckChart eps) ∧
        ((∃ neck : ∀ n, SpatialLocalNeck (G.flow.base.metric (τ n)) eps x (W n).domain.carrier,
          ∀ n, (W n).alternative = SpatialCanonicalAlternative.neck (neck n)) ∨
         ∃ cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) eps x (W n).domain.carrier,
           ∃ depth : ∀ n, ∀ z ∈ (cap n).tube,
             10000 / Real.sqrt (G.flow.scalar (τ n) x) ≤
               metricDistance (G.flow.base.metric (τ n)) x z,
             ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) := by
  classical
  obtain ⟨d, hd, hlate⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp
    (hhigh.and hbranch)
  obtain ⟨τ, hτmono, hτmem, hτlim⟩ := exists_seq_strictMono_tendsto' hd.2
  have hτ : Tendsto τ atTop (𝓝[<] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτlim, Eventually.of_forall (fun n => (hτmem n).2)⟩
  have hτdomain (n : ℕ) : τ n ∈ Ioo a s := ⟨hd.1.trans_lt (hτmem n).1, (hτmem n).2⟩
  choose W hW using fun n => hcanonical (τ n) (hτdomain n) (hlate (hτmem n)).1
  have halt (n : ℕ) := (hlate (hτmem n)).2 (W n)
  let isNeck (n : ℕ) : Prop :=
    ∃ neck : SpatialLocalNeck (G.flow.base.metric (τ n)) eps x (W n).domain.carrier,
      (W n).alternative = SpatialCanonicalAlternative.neck neck
  by_cases hfrequent : ∃ᶠ n in atTop, isNeck n
  · obtain ⟨φ, hφ, hφneck⟩ := extraction_of_frequently_atTop hfrequent
    choose neck hneck using hφneck
    exact ⟨fun n => τ (φ n), hτmono.comp hφ, fun n => hτdomain (φ n), hτ.comp hφ.tendsto_atTop,
      fun n => W (φ n), fun n => hW (φ n), Or.inl ⟨neck, hneck⟩⟩
  · have hcaps : ∀ᶠ n in atTop,
        ∃ cap : SpatialLocalCap (G.flow.base.metric (τ n)) eps x (W n).domain.carrier,
        ∃ depth, (W n).alternative = SpatialCanonicalAlternative.cap cap depth := by
      filter_upwards [not_frequently.mp hfrequent] with n hn
      exact (halt n).resolve_left hn
    obtain ⟨φ, hφ, hφcap⟩ := extraction_of_eventually_atTop hcaps
    choose cap depth hcap using hφcap
    exact ⟨fun n => τ (φ n), hτmono.comp hφ, fun n => hτdomain (φ n), hτ.comp hφ.tendsto_atTop,
      fun n => W (φ n), fun n => hW (φ n), Or.inr ⟨cap, depth, hcap⟩⟩

theorem TerminalLimitMetric.eventually_spatial_cap_neck_compact_capture
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) {epsCanonical eps C1 C2 : ℝ}
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical x.val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ (v : ℕ → P.Carrier) (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps (v n)),
        (∀ n z, (cap n).tubeMap z = (neck n).map z) ∧
        (∀ n, v n ∈ (cap n).tube) ∧
        ∀ᶠ n in atTop,
          (W n).domain.carrier ∪ (neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆
            Subtype.val '' K := by
  classical
  choose v neck hmap using fun n => hW n (cap n) (depth n) (hcap n)
  have hv (n : ℕ) : v n ∈ (cap n).tube := by
    rw [← (cap n).tube_eq]
    exact ⟨((neck n).center, 0), ⟨mem_univ _, by norm_num⟩,
      (hmap n ((neck n).center, 0)).trans (neck n).center_eq⟩
  have hvW (n : ℕ) : v n ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr (hv n)
  have heps : 0 ≤ eps := (neck 0).eps_pos.le
  have hC2 : 0 ≤ C2 := zero_le_one.trans (W 0).one_le_comparison_constant
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨_, D2, q, _, hD2, hq, hc⟩ := hm epsCan hepsCan le_rfl
  let C : NNReal := ⟨D2, zero_le_one.trans hD2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 :=
    fun y t ht hy => (hc y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  let B := (1 + 4323 * eps) * (C2 * (|metricScalarAt L.metric x| + 1))
  obtain ⟨K₀, hK₀, hKreg, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch B
  let K : Set G.terminalRegularOpen := Subtype.val ⁻¹' K₀
  have himage : Subtype.val '' K = K₀ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKreg hy⟩, hy, rfl⟩
  have hK : IsCompact K := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hK₀
  have hcenter : ∀ᶠ t in 𝓝[<] s,
      G.flow.scalar t x.val < |metricScalarAt L.metric x| + 1 :=
    (L.tendsto_metricScalarAt x).eventually_lt_const
      (by linarith [le_abs_self (metricScalarAt L.metric x)])
  obtain ⟨d', hd', hcenter'⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hcenter
  have hfac : 1 ≤ 1 + 4323 * eps := by linarith
  refine ⟨K, hK, v, neck, hmap, hv, ?_⟩
  filter_upwards [hτ.eventually (Ioo_mem_nhdsLT hd.2),
    hτ.eventually (Ioo_mem_nhdsLT hd'.2)] with n hn hn'
  have hR : G.flow.scalar (τ n) x.val ≤ |metricScalarAt L.metric x| + 1 := (hcenter' hn').le
  have hdom : ∀ y ∈ (W n).domain.carrier,
      G.flow.scalar (τ n) y ≤ C2 * (|metricScalarAt L.metric x| + 1) := fun y hy =>
    (W n).scalar_bounds y hy |>.2.trans (mul_le_mul_of_nonneg_left hR hC2)
  have hCB : C2 * (|metricScalarAt L.metric x| + 1) ≤ B :=
    le_mul_of_one_le_left (by positivity) hfac
  rw [himage]
  rintro y (hy | hy)
  · exact hcapture (τ n) hn y ((hdom y hy).trans hCB)
  · apply hcapture (τ n) hn
    have hs := ((neck n).scalar_bounds_on_image_window hy).2
    exact hs.trans (mul_le_mul_of_nonneg_left (hdom (v n) (hvW n)) (by positivity))

theorem TerminalLimitMetric.eventually_scalar_range_on_spatial_domains
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hx : 0 < metricScalarAt L.metric x) {C1 C2 eps : ℝ} :
    ∀ᶠ t in 𝓝[<] s, ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x.val,
      ∀ v ∈ W.domain.carrier,
        metricScalarAt L.metric x / (2 * C2) ≤ G.flow.scalar t v ∧
          G.flow.scalar t v ≤ C2 * (metricScalarAt L.metric x + 1) := by
  have hlow := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds (half_lt_self hx))
  have hhigh := (L.tendsto_metricScalarAt x).eventually_lt_const (lt_add_one _)
  filter_upwards [hlow, hhigh] with t htlo hthi
  intro W v hv
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hs := W.scalar_bounds v hv
  constructor
  · have hmul := mul_le_mul_of_nonneg_left htlo.le (inv_pos.mpr hC2).le
    have heq : C2⁻¹ * (metricScalarAt L.metric x / 2) =
        metricScalarAt L.metric x / (2 * C2) := by field_simp
    rw [heq] at hmul
    exact hmul.trans hs.1
  · exact hs.2.trans (mul_le_mul_of_nonneg_left hthi.le hC2.le)

theorem TerminalLimitMetric.eventually_normalizedNeck_of_spatial_caps
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical x.val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen)
      (nk : SpatialNeck (G.flow.base.metric (τ n)) eps v.val),
      (∀ z, (cap n).tubeMap z = nk.map z) ∧ v.val ∈ (cap n).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
  classical
  obtain ⟨K, hK, v, neck, hmap, hv, hcapture⟩ :=
    L.eventually_spatial_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hvW (n : ℕ) : v n ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr (hv n)
  have hC2 : 0 < C2 := zero_lt_one.trans_le (W 0).one_le_comparison_constant
  let qmin := metricScalarAt L.metric x / (2 * C2)
  let qmax := C2 * (metricScalarAt L.metric x + 1)
  have hqmin : 0 < qmin := by dsimp only [qmin]; positivity
  have hrange : ∀ᶠ n in atTop, qmin ≤ G.flow.scalar (τ n) (v n) ∧
      G.flow.scalar (τ n) (v n) ≤ qmax := by
    filter_upwards [hτ.eventually (L.eventually_scalar_range_on_spatial_domains
      x hx (C1 := C1) (C2 := C2) (eps := epsCanonical))] with n hn
    exact hn (W n) (v n) (hvW n)
  have hclose := hτ.eventually (L.eventually_scalar_close_on_compact hK (half_pos hqmin))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hcapture.and (hrange.and hclose))
  have hsub (n : ℕ) := (hn₀ (n + n₀) (by omega)).1
  have hregv (n : ℕ) : v (n + n₀) ∈ G.terminalRegularRegion := by
    obtain ⟨y, hy, he⟩ := hsub n (Or.inl (hvW (n + n₀)))
    exact he ▸ y.property
  let v' : ℕ → G.terminalRegularOpen := fun n => ⟨v (n + n₀), hregv n⟩
  have hvK (n : ℕ) : v' n ∈ K := by
    obtain ⟨y, hy, he⟩ := hsub n (Or.inl (hvW (n + n₀)))
    have he' : y = v' n := Subtype.ext he
    exact he' ▸ hy
  have hpositive (n : ℕ) : 0 < metricScalarAt L.metric (v' n) := by
    have hr := (hn₀ (n + n₀) (by omega)).2.1.1
    have he := abs_lt.mp ((hn₀ (n + n₀) (by omega)).2.2 (v' n) (hvK n))
    change qmin ≤ metricScalarAt (G.flow.base.metric (τ (n + n₀))) (v' n).val at hr
    linarith [he.2]
  have hwindow (n : ℕ) (z : neckBuffer δ) :
      (neck (n + n₀)).map z.val ∈ Subtype.val '' K := by
    apply hsub n
    right
    refine ⟨z.val, ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · have hz := z.property.1
      change -δ⁻¹ - 1 < z.val.2 at hz
      linarith
    · have hz := z.property.2
      change z.val.2 < δ⁻¹ + 1 at hz
      linarith
  have hregular (n : ℕ) (z : neckBuffer δ) :
      (neck (n + n₀)).map z.val ∈ G.terminalRegularRegion := by
    obtain ⟨y, hy, he⟩ := hwindow n z
    exact he ▸ y.property
  have hout := L.eventually_normalizedNeck_of_moving_spatialNecks
    (hτ.comp (tendsto_add_atTop_nat n₀)) v' hpositive hδ hδ1 hepsδ hfit k hk
    (fun n => neck (n + n₀)) hregular hK
    (Eventually.of_forall fun n z _ => hwindow n z) hqmin
    (Eventually.of_forall fun n => (hn₀ (n + n₀) (by omega)).2.1)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hout
  apply eventually_atTop.mpr
  refine ⟨n₀ + n₁, ?_⟩
  intro n hn
  have heq : n - n₀ + n₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨N, hNv, hNmark, hNmap⟩ := hn₁ (n - n₀) (by omega)
  have hresult : ∃ (v : G.terminalRegularOpen)
      (nk : SpatialNeck (G.flow.base.metric (τ (n - n₀ + n₀))) eps v.val),
      (∀ z, (cap (n - n₀ + n₀)).tubeMap z = nk.map z) ∧
      v.val ∈ (cap (n - n₀ + n₀)).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
    exact ⟨v' (n - n₀), neck (n - n₀ + n₀), hmap (n - n₀ + n₀),
      hv (n - n₀ + n₀), N, hNv, hNmark, hNmap⟩
  exact heq ▸ hresult

theorem TerminalLimitMetric.eventually_scalar_bounds_on_spatial_domains
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps C1 C2 : ℝ}
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) eps C1 C2 x.val)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, (W n).domain.carrier ⊆ Subtype.val '' K) :
    ∀ᶠ n in atTop, ∀ y : G.terminalRegularOpen, y.val ∈ (W n).domain.carrier →
      3 * metricScalarAt L.metric x / (4 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 3 * C2 * metricScalarAt L.metric x / 2 := by
  have hC2 : 1 ≤ C2 := (W 0).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hcenter := hτ.eventually (L.eventually_scalar_close_on_compact
    (K := {x}) isCompact_singleton (div_pos hx (by norm_num : (0 : ℝ) < 8)))
  have hclose := hτ.eventually (L.eventually_scalar_close_on_compact hK
    (div_pos hx (by positivity : 0 < 8 * C2)))
  filter_upwards [hcapture, hcenter, hclose] with n hn hc he
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hn hy
  have hyK : y ∈ K := (Subtype.ext hzy : z = y) ▸ hz
  have hxc := abs_lt.mp (hc x (mem_singleton x))
  have hyc := abs_lt.mp (he y hyK)
  change -(metricScalarAt L.metric x / 8) <
      G.flow.scalar (τ n) x.val - metricScalarAt L.metric x ∧
    G.flow.scalar (τ n) x.val - metricScalarAt L.metric x < metricScalarAt L.metric x / 8 at hxc
  change -(metricScalarAt L.metric x / (8 * C2)) <
      G.flow.scalar (τ n) y.val - metricScalarAt L.metric y ∧
    G.flow.scalar (τ n) y.val - metricScalarAt L.metric y <
      metricScalarAt L.metric x / (8 * C2) at hyc
  have hs : C2⁻¹ * G.flow.scalar (τ n) x.val ≤ G.flow.scalar (τ n) y.val ∧
      G.flow.scalar (τ n) y.val ≤ C2 * G.flow.scalar (τ n) x.val :=
    (W n).scalar_bounds y.val hy
  have hslo : G.flow.scalar (τ n) x.val ≤ C2 * G.flow.scalar (τ n) y.val := by
    have hm := mul_le_mul_of_nonneg_left hs.1 hC2pos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul] using hm
  have herr : metricScalarAt L.metric x / (8 * C2) ≤ metricScalarAt L.metric x / 8 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * C2)).mpr
    have hm := mul_lt_mul_of_pos_left hyc.2 hC2pos
    have heq : C2 * (metricScalarAt L.metric x / (8 * C2)) = metricScalarAt L.metric x / 8 := by
      field_simp
    rw [heq] at hm
    nlinarith [hxc.1]
  · have hm := mul_lt_mul_of_pos_left hxc.2 hC2pos
    nlinarith [hs.2, hyc.1, hx, hC2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap
    (L : G.TerminalLimitMetric) {g : SmoothRiemannianMetric I3 P.Carrier} {eps : ℝ}
    {x : G.terminalRegularOpen} {U : Set P.Carrier}
    (cap : SpatialLocalCap g eps x.val U) (hU : U ⊆ G.terminalRegularRegion)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hδ : δ < 1 / 102) (hk : 2 ≤ k)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).val = cap.tubeMap z.val) :
    ∃ (K : CompactDomain G.terminalRegularOpen) (e : Sphere 2 → G.terminalRegularOpen),
      Subtype.val '' K.carrier = cap.core.carrier ∪
        cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' U ∧
      frontier K.carrier = range e ∧ IsSmoothEmbedding I2 I3 ∞ e ∧
      (∀ q, (e q).val = cap.tubeMap (q, 1 / 2)) ∧
      (∀ q (hq : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ), e q = N.chart ⟨(q, 1 / 2), hq⟩) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        |metricScalarAt L.metric (N.chart z) / N.scale - 1| ≤ 4323 * δ) ∧
      N.cylindricalChart.metricCloseOn L.metric δ
        {z : N.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ N.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 e,
        c.radius < 1 / 4 ∧
        ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
          (∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
            c.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩) ∧
          (c.toFun q).val = cap.tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have hlen : (102 : ℝ) < δ⁻¹ :=
    (lt_inv_comm₀ (by norm_num) N.delta_pos).mpr (by simpa only [one_div] using hδ)
  have hmid (q : Sphere 2) : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ := by
    constructor <;> linarith
  let e : Sphere 2 → G.terminalRegularOpen := fun q =>
    (N.cylindricalChart.chart ⟨(q, 1 / 2), hmid q⟩ : G.terminalRegularOpen)
  have he (q : Sphere 2) : (e q).val = cap.tubeMap (q, 1 / 2) :=
    (congrArg Subtype.val (N.cylindricalChart_chart_apply _)).trans (hmap _)
  obtain ⟨K₀, hK₀, hx₀, hK₀U, hfront₀⟩ :=
    cap.exists_truncated_compactDomain (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  let K := K₀.restrictOpen G.terminalRegularOpen (hK₀U.trans hU)
  have hK : Subtype.val '' K.carrier = cap.core.carrier ∪
      cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) :=
    (K₀.image_restrictOpen_carrier _ _).trans hK₀
  have hxK : x ∈ interior K.carrier := by
    change x ∈ interior (K₀.restrictOpen G.terminalRegularOpen _).carrier
    rw [K₀.interior_restrictOpen_carrier]
    exact hx₀
  have hKU : K.carrier ⊆ Subtype.val ⁻¹' U := fun y hy => hK₀U hy
  have hfront : frontier K.carrier = range e := by
    change frontier (K₀.restrictOpen G.terminalRegularOpen _).carrier = range e
    rw [K₀.frontier_restrictOpen_carrier, hfront₀]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext ((he q).trans hq)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, (he q).symm⟩
  have hgraph : ∀ q : Sphere 2, (q, (1 / 2 : ℝ)) ∈ N.cylindricalChart.domain := hmid
  obtain ⟨c, hc, _, hcoord⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    N.cylindricalChart.domain N.cylindricalChart.target N.cylindricalChart.chart
    (fun _ => (1 / 2 : ℝ)) contMDiff_const hgraph (by norm_num : (0 : ℝ) < 1 / 4)
  let c' : SmoothTwoSidedCollar I2 I3 e := c
  have hcoord' (q : Sphere 2 × symmetricOpenInterval c'.radius) :
      ∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
        c'.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩ := by
    obtain ⟨hz, heq⟩ := hcoord q
    exact ⟨hz, heq.trans (N.cylindricalChart_chart_apply _)⟩
  have hEsmooth : IsSmoothEmbedding I2 I3 ∞ e := by
    let f : Sphere 2 → neckBuffer δ := fun q => ⟨(q, 1 / 2), hmid q⟩
    have hf : IsSmoothEmbedding I2 NeckCylinderModel ∞ f := by
      have hfcont : ContMDiff I2 NeckCylinderModel ∞ f :=
        (ContMDiff.subtypeVal_comp_iff (neckBuffer δ) _).mp
          (contMDiff_id.prodMk contMDiff_const)
      have hfst : ContMDiff NeckCylinderModel I2 ∞
          (fun z : neckBuffer δ => z.val.1) := contMDiff_fst.comp contMDiff_subtype_val
      exact (IsSmoothEmbedding.id : IsSmoothEmbedding I2 I2 ∞
        ((fun z : neckBuffer δ => z.val.1) ∘ f)).of_comp
          (J := NeckCylinderModel) (by simp) hfcont hfst
    have hE : e = N.chart ∘ f := funext fun q => N.cylindricalChart_chart_apply _
    rw [hE]
    exact N.chart_smooth.comp hf (by simp)
  refine ⟨K, e, hK, hxK, hKU, hfront, hEsmooth, he, ?_, ?_, ?_, ?_, c', hc, ?_⟩
  · intro q hq
    exact N.cylindricalChart_chart_apply _
  · intro z hz
    have hztest : z ∈ neckClosedTest δ := by
      change -δ⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ δ⁻¹
      constructor <;> linarith [hz.1, hz.2]
    have hy : N.chart z ∈ N.cylindricalChart.region (neckClosedTest δ) := by
      refine ⟨N.cylindricalChart.chart z, ⟨z, hztest, rfl⟩, ?_⟩
      exact N.cylindricalChart_chart_apply z
    exact N.cylindricalChart.scalar_comparison_of_metricCloseOn L.metric δ
      (by linarith) (N.cylindricalChart_metricCloseOn hk) (N.chart z) hy
  · intro z hz j hj
    apply N.cylindricalChart_metricCloseOn hk z ?_ j hj
    change -δ⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ δ⁻¹
    constructor <;> linarith [hz.1, hz.2]
  · intro q z hz
    change -δ⁻¹ - 1 < z ∧ z < δ⁻¹ + 1
    constructor <;> linarith [hz.1, hz.2]
  · intro q
    obtain ⟨hz, hq⟩ := hcoord' q
    have hpoint : (c'.toFun q).val = cap.tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) :=
      (congrArg Subtype.val hq).trans (hmap _)
    refine ⟨⟨hz, hq⟩, hpoint, ?_⟩
    change (c'.toFun q).val ∈ K₀.carrier ↔ _
    rw [hpoint, hK₀]
    have hs : 1 / 2 + (q.2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      have hc' : c'.radius < 1 / 4 := hc
      constructor <;> linarith [q.2.property.1, q.2.property.2]
    rw [cap.mem_truncated_core_on_tube (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) q.1 hs]
    constructor <;> intro h <;> linarith

theorem TerminalLimitMetric.eventually_spatial_cap_midpoint_region
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (h2k : 2 ≤ k)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical x.val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (N : NormalizedNeck L.metric δ k)
      (K : CompactDomain G.terminalRegularOpen) (e : Sphere 2 → G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier, metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric x) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric (N.chart z) ∧
          metricScalarAt L.metric (N.chart z) < 2 * C2 * metricScalarAt L.metric x) ∧
      frontier K.carrier = range e ∧ IsSmoothEmbedding I2 I3 ∞ e ∧
      (∀ q, (e q).val = (cap n).tubeMap (q, 1 / 2)) ∧
      (∀ q (hq : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ), e q = N.chart ⟨(q, 1 / 2), hq⟩) ∧
      N.cylindricalChart.metricCloseOn L.metric δ
        {z : N.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ N.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 e,
        c.radius < 1 / 4 ∧
        ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
          (∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
            c.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩) ∧
          (c.toFun q).val = (cap n).tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  obtain ⟨K₀, hK₀, v, neck, _, _, hcapture⟩ :=
    L.eventually_spatial_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hnorm := L.eventually_normalizedNeck_of_spatial_caps hτ x hx
    hδ (by linarith) hepsδ hfit k hk W hW cap depth hcap
  have hbound := L.eventually_scalar_bounds_on_spatial_domains hτ x hx W hK₀
    (hcapture.mono fun n hn => subset_union_left.trans hn)
  filter_upwards [hcapture, hnorm, hbound] with n hcn hnn hbn
  obtain ⟨vn, nk, hmap, hvn, N, hNv, _, hNmap⟩ := hnn
  have hU : (W n).domain.carrier ⊆ G.terminalRegularRegion := by
    intro y hy
    obtain ⟨z, _, he⟩ := hcn (Or.inl hy)
    exact he ▸ z.property
  have hNcap : ∀ z : neckBuffer δ, (N.chart z).val = (cap n).tubeMap z.val :=
    fun z => (hNmap z).trans (hmap z.val).symm
  obtain ⟨K, e, hK, hxK, hKU, hfront, hemb, heold, heN, hscalar, hmetric, hdomain, hc⟩ :=
    L.exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap
      (cap n) hU N (by linarith) h2k hNcap
  have hC2 : 1 ≤ C2 := (W n).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hvU : vn.val ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr hvn
  have hNscale : 3 * metricScalarAt L.metric x / (4 * C2) < N.scale ∧
      N.scale < 3 * C2 * metricScalarAt L.metric x / 2 := by
    rw [N.scale_scalar, hNv]
    exact hbn vn hvU
  have hlo : metricScalarAt L.metric x / (2 * C2) <
      3 * metricScalarAt L.metric x / (4 * C2) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * C2) (by positivity : 0 < 4 * C2)).mpr
    nlinarith
  have hhi : 3 * C2 * metricScalarAt L.metric x / 2 <
      2 * C2 * metricScalarAt L.metric x := by nlinarith [mul_pos hC2pos hx]
  refine ⟨N, K, e, hK, hxK, hKU, ?_, ?_, hfront, hemb, heold, heN, hmetric, hdomain, hc⟩
  · intro y hy
    exact ⟨hlo.trans (hbn y (hKU hy)).1, (hbn y (hKU hy)).2.trans hhi⟩
  · intro z hz
    have hs := abs_le.mp (hscalar z hz)
    have hQ := N.scale_pos
    have hsl : (1 - 4323 * δ) * N.scale ≤ metricScalarAt L.metric (N.chart z) := by
      apply (le_div_iff₀ hQ).mp
      linarith [hs.1]
    have hsu : metricScalarAt L.metric (N.chart z) ≤ (1 + 4323 * δ) * N.scale := by
      apply (div_le_iff₀ hQ).mp
      linarith [hs.2]
    have hthree : (3 / 4 : ℝ) * N.scale < metricScalarAt L.metric (N.chart z) := by
      nlinarith
    have hfive : metricScalarAt L.metric (N.chart z) < (5 / 4 : ℝ) * N.scale := by
      nlinarith
    constructor
    · have hlo' := (div_lt_iff₀ (by positivity : 0 < 4 * C2)).mp hNscale.1
      apply (div_lt_iff₀ (by positivity : 0 < 2 * C2)).mpr
      have hm := mul_lt_mul_of_pos_right hthree hC2pos
      nlinarith
    · nlinarith [hNscale.2]

theorem TerminalLimitMetric.exists_neck_spherical_barrier_of_incoming_spatialNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8646)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps x.val)
    (A C2 : ℝ) (hA : 0 < A) (hC2 : 1 ≤ C2)
    (hscale : metricScalarAt L.metric x = 4 * C2 * A) :
    ∃ (n : ℕ) (nk : SpatialNeck L.metric δ x) (K : CompactDomain G.terminalRegularOpen),
      (∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val) ∧
      K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧ x ∈ interior K.carrier ∧
      frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, -3)) ∪
        range (fun y : Sphere 2 => nk.map (y, 3)) ∧
      Disjoint (range (fun y : Sphere 2 => nk.map (y, -3)))
        (range (fun y : Sphere 2 => nk.map (y, 3))) ∧
      (∀ t ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, t))) ∧
      (∀ y ∈ K.carrier, 2 * A < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y ≤ 8 * C2 ^ 2 * A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ nk.cylindricalChart.domain) ∧
      ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, -3)))
        (cpos : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, 3))),
        cneg.radius < 1 ∧ cpos.radius < 1 ∧
        (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
          (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
        (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
          (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) := by
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  obtain ⟨n, nk, _, hmap⟩ :=
    (L.eventually_spatialNeck_of_incoming_spatialNecks hτ x hx hδ
      (hδsmall.trans (by norm_num)) hepsδ hfit neck).exists
  obtain ⟨K, hK⟩ := nk.exists_short_spherical_barrier hδsmall A C2 hA hC2 hscale
  exact ⟨n, nk, K, hmap, hK⟩

theorem TerminalLimitMetric.eventually_spatial_cap_spherical_barrier
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical x.val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v)
      (K : CompactDomain G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier, metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric x) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) < 2 * C2 * metricScalarAt L.metric x) ∧
      frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
        c.radius < 1 / 4 ∧ ∀ q,
          c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have heps : 0 < eps := by
    obtain ⟨v, nk, _⟩ := hW 0 (cap 0) (depth 0) (hcap 0)
    exact nk.eps_pos
  have hδ11 : δ < 1 / 11 := hδsmall.trans (by norm_num)
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ heps hepsδ.le)
  have hlen : (101 : ℝ) < δ⁻¹ :=
    (lt_inv_comm₀ (by norm_num) hδ).mpr (by linarith)
  have h2k : 2 ≤ ⌈δ⁻¹⌉₊ := by
    exact_mod_cast (show (2 : ℝ) ≤ δ⁻¹ by linarith).trans (Nat.le_ceil δ⁻¹)
  have hevent := L.eventually_spatial_cap_midpoint_region hτ x hx hδ hδsmall hepsδ hfit
    ⌈δ⁻¹⌉₊ hk h2k W hW cap depth hcap
  filter_upwards [hevent] with n hn
  obtain ⟨N, K, e, hK, hxK, hKU, hscalarK, hscalarN, hfront, hemb, heold, heN,
    hmetricN, hdomainN, c, hc, hcmap⟩ := hn
  obtain ⟨nk, hmark, hmap⟩ := N.exists_spatialNeck le_rfl hδ11 le_rfl
  have heq : e = (fun q : Sphere 2 => nk.map (q, 1 / 2)) := by
    funext q
    have hz : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ := by constructor <;> linarith
    exact (heN q hz).trans (hmap ⟨(q, 1 / 2), hz⟩).symm
  subst e
  refine ⟨N.center, nk, K, hK, hxK, hKU, hscalarK, ?_, hfront, hemb, ?_, ?_, c, hc, ?_⟩
  · intro z hz
    have hz' : z ∈ neckBuffer δ := by constructor <;> linarith [hz.2.1, hz.2.2]
    rw [hmap ⟨z, hz'⟩]
    exact hscalarN ⟨z, hz'⟩ hz.2
  · intro z _ j hj
    exact nk.cylindricalChart_metricCloseOn z (mem_univ _) j hj
  · intro q z hz
    exact ⟨mem_univ _, by linarith [hz.1], by linarith [hz.2]⟩
  · intro q
    obtain ⟨⟨hz, hqc⟩, _, hmem⟩ := hcmap q
    exact ⟨hqc.trans (hmap ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩).symm, hmem⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Riemannian

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_spatial_neck_slab_subset_spatial_cap_core
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {p x : G.terminalRegularOpen} {eps epsc : ℝ}
    (nk : SpatialNeck L.metric eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hx : nk.map (q, level) = x)
    {U : ℕ → Set P.Carrier}
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsc x.val (U n))
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y) :
    ∀ᶠ n in atTop, Subtype.val '' (nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) ⊆
      interior (cap n).core.carrier := by
  let Q := metricScalarAt L.metric p
  have hQ : 0 < Q := nk.Q_pos
  have hroot := Real.sqrt_pos.mpr hQ
  have hlen : (100 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith)
  let K := riemannianClosedBallOf L.metric p (30 / Real.sqrt Q)
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-100 : ℝ) 100 ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hcompactSlab : IsCompact (nk.map '' (univ ×ˢ Icc (-100 : ℝ) 100)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  have hminus : 1 / 2 < Real.sqrt (1 - eps) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - eps by linarith)
    nlinarith [Real.sqrt_nonneg (1 - eps)]
  have hK : IsCompact K := by
    apply hcompactSlab.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist L.metric p) continuous_const)
    intro y hy
    apply nk.ball_subset_image_slab (by norm_num : (0 : ℝ) < 100) hlen
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity :
      0 < 100 * Real.sqrt (1 - eps) / Real.sqrt Q)).mpr
      (div_lt_div_of_pos_right (by linarith) hroot))
  obtain ⟨d, hd, hclose⟩ := L.converges K hK 0 1 zero_lt_one
  have htime := hτ.eventually (Ioo_mem_nhdsLT hd.2)
  have hxx : x ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) :=
    ⟨(q, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hx⟩
  have hscalarx := nk.abs_scalar_ratio_sub_one_le
    (show (q, level) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ from
      ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩)
  rw [hx] at hscalarx
  have hQx : 0 < metricScalarAt L.metric x := by
    have hr : 0 < metricScalarAt L.metric x / Q := by
      change 0 < metricScalarAt L.metric x / metricScalarAt L.metric p
      linarith [(abs_le.mp hscalarx).1]
    exact (div_pos_iff.mp hr).elim (fun h => h.1) (fun h => (hQ.not_gt h.2).elim)
  have hQxle : metricScalarAt L.metric x ≤ 2 * Q := by
    apply (div_le_iff₀ hQ).mp
    change metricScalarAt L.metric x / metricScalarAt L.metric p ≤ 2
    linarith [(abs_le.mp hscalarx).2]
  have hscalar := hτ.eventually ((L.tendsto_metricScalarAt x).eventually_lt_const
    (show metricScalarAt L.metric x < 4 * Q by linarith))
  have hpositive := hτ.eventually ((L.tendsto_metricScalarAt x).eventually
    (Ioi_mem_nhds hQx))
  filter_upwards [htime, hscalar, hpositive] with n hn hsn hRn
  change G.flow.scalar (τ n) x.val < 4 * Q at hsn
  change 0 < G.flow.scalar (τ n) x.val at hRn
  let gt := (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
  have hupper : ∀ z ∈ K, ∀ v : TangentSpace I3 z,
      gt.inner z v v ≤ (2 : ℝ)^2 * L.metric.inner z v v := by
    intro z hz v
    have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      L.metric gt z (hclose (τ n) hn z hz).le v).2
    have hnn := metric_inner_self_nonneg L.metric z v
    nlinarith
  have hsmall : (4 : ℝ) < eps⁻¹ := by linarith
  have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + eps by linarith [nk.eps_pos]),
      Real.sqrt_nonneg (1 + eps)]
  have hb (y : G.terminalRegularOpen) (hy : y ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
      riemannianEDistOf L.metric p y ≤ ENNReal.ofReal (20 / Real.sqrt Q) := by
    exact (nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hsmall hy).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by nlinarith) hroot.le))
  have hcap := Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (G.flow.base.metric (τ n)) (cap n).center_inside
    (r := ENNReal.ofReal (10000 / Real.sqrt (G.flow.scalar (τ n) x.val))) (by
      intro z hz
      have hztube : z ∈ (cap n).tube := ((cap n).overlap_eq.symm ▸ hz).2
      exact (ENNReal.ofReal_le_ofReal (depth n z hztube)).trans ENNReal.ofReal_toReal_le)
  have hdist' (y : G.terminalRegularOpen)
      (hy : y ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
      riemannianEDistOf (G.flow.base.metric (τ n)) p.val y.val ≤
        ENNReal.ofReal (40 / Real.sqrt Q) := by
    have hdy : riemannianEDistOf L.metric p y < ENNReal.ofReal (30 / Real.sqrt Q) :=
      (hb y hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (div_lt_div_of_pos_right (by norm_num) hroot))
    have hdist := KappaSolutions.edistOf_map_le_of_metric_upper_on_ball L.metric gt
      (DifferentialGeometry.PartialDiffeomorph.refl G.terminalRegularOpen) p y
      (by positivity : 0 < 30 / Real.sqrt Q) (by norm_num : (0 : ℝ) < 2)
      (by intro z hz; trivial) (by
        intro z hz v
        change gt.inner z (mfderiv I3 I3 id z v) (mfderiv I3 I3 id z v) ≤ _
        simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hupper z hz v) hdy
    apply (riemannianEDistOf_le_restrictOpen (G.flow.base.metric (τ n))
      G.terminalRegularOpen p y).trans
    apply hdist.trans
    calc
      ENNReal.ofReal 2 * riemannianEDistOf L.metric p y ≤
          ENNReal.ofReal 2 * ENNReal.ofReal (20 / Real.sqrt Q) := mul_le_mul' le_rfl (hb y hy)
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
  rintro _ ⟨y, hy, rfl⟩
  apply hcap
  have hxy : riemannianEDistOf (G.flow.base.metric (τ n)) x.val y.val ≤
      ENNReal.ofReal (80 / Real.sqrt Q) := by
    have hpx := hdist' x hxx
    rw [riemannianEDistOf_comm] at hpx
    apply ((riemannianEDistOf_triangle (G.flow.base.metric (τ n)) x.val p.val y.val).trans
      (add_le_add hpx (hdist' y hy))).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hrootn : Real.sqrt (G.flow.scalar (τ n) x.val) ≤ 2 * Real.sqrt Q := by
    nlinarith [Real.sq_sqrt hRn.le, Real.sq_sqrt hQ.le,
      Real.sqrt_nonneg (G.flow.scalar (τ n) x.val)]
  apply hxy.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity :
    0 < 10000 / Real.sqrt (G.flow.scalar (τ n) x.val))).mpr
  apply (div_lt_div_iff₀ hroot (Real.sqrt_pos.mpr hRn)).mpr
  nlinarith

theorem TerminalLimitMetric.eventually_spatial_cap_core
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps C1 C2 : ℝ}
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical x.val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ K : CompactDomain G.terminalRegularOpen,
      Subtype.val '' K.carrier = (cap n).core.carrier ∧
      Nonempty (CapCore K.carrier) ∧ x ∈ interior K.carrier ∧
      (∀ y ∈ K.carrier,
        3 * metricScalarAt L.metric x / (4 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 3 * C2 * metricScalarAt L.metric x / 2) := by
  obtain ⟨K₀, hK₀, v, neck, _, _, hcapture⟩ :=
    L.eventually_spatial_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hbound := L.eventually_scalar_bounds_on_spatial_domains hτ x hx W hK₀
    (hcapture.mono fun n hn => subset_union_left.trans hn)
  filter_upwards [hcapture, hbound] with n hcn hbn
  have hcoreU : (cap n).core.carrier ⊆ (W n).domain.carrier :=
    (cap n).core_inside.trans interior_subset
  have hcore : (cap n).core.carrier ⊆ G.terminalRegularOpen := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hcn (Or.inl (hcoreU hy))
    exact hz ▸ z.property
  let K := (cap n).core.restrictOpen G.terminalRegularOpen hcore
  refine ⟨K, (cap n).core.image_restrictOpen_carrier _ _,
    (cap n).coreModel.nonempty_preimage_open _ hcore, ?_, ?_⟩
  · rw [CompactDomain.interior_restrictOpen_carrier]
    exact (cap n).center_inside
  · intro y hy
    exact hbn y (hcoreU hy)

theorem TerminalLimitMetric.spatial_neck_or_cap_core_of_spatial_sequence
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hxpos : 0 < metricScalarAt L.metric x)
    {eps δ C1 C2 : ℝ} (hδsmall : δ ≤ 1 / 8646)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) eps C1 C2 x.val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (halternatives :
      (∃ neck : ∀ n, SpatialLocalNeck (G.flow.base.metric (τ n)) eps x.val
          (W n).domain.carrier,
        ∀ n, (W n).alternative = SpatialCanonicalAlternative.neck (neck n)) ∨
      ∃ cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) eps x.val (W n).domain.carrier,
        ∃ depth : ∀ n, ∀ w ∈ (cap n).tube,
          10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
            metricDistance (G.flow.base.metric (τ n)) x.val w,
          ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n))
    {p : G.terminalRegularOpen} (nk : SpatialNeck L.metric δ p)
    (z : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hxmap : nk.map (z, level) = x) :
    Nonempty (SpatialNeck L.metric δ x) ∨
      ∃ K : CompactDomain G.terminalRegularOpen,
        Nonempty (CapCore K.carrier) ∧
        nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
        (∀ w ∈ K.carrier,
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
            metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  have hC2pos : 0 < C2 := zero_lt_one.trans_le (W 0).one_le_comparison_constant
  have hδ11 : δ < 1 / 11 := hδsmall.trans_lt (by norm_num)
  rcases halternatives with hn | hc
  · obtain ⟨neck, _⟩ := hn
    obtain ⟨n, newNeck, _, _⟩ := (L.eventually_spatialNeck_of_incoming_spatialNecks
      hτ x hxpos nk.eps_pos hδ11 hepsδ hfit (fun n => (neck n).neck)).exists
    exact Or.inl ⟨newNeck⟩
  · obtain ⟨cap, depth, hcap⟩ := hc
    have hcore := L.eventually_spatial_cap_core hτ x hxpos W hW cap depth hcap
    have hslab := L.eventually_spatial_neck_slab_subset_spatial_cap_core hτ nk hδsmall
      z hlevel hxmap cap depth
    obtain ⟨n, ⟨K, hK, hmodel, _, hscalar⟩, hinside⟩ := (hcore.and hslab).exists
    have hpre : K.carrier =
        (Subtype.val ⁻¹' (cap n).core.carrier : Set G.terminalRegularOpen) := by
      rw [← hK, preimage_image_eq _ Subtype.val_injective]
    have hlow : metricScalarAt L.metric x / (2 * C2) <
        3 * metricScalarAt L.metric x / (4 * C2) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < 2 * C2) (by positivity : 0 < 4 * C2)).mpr
      nlinarith
    have hupp : 3 * C2 * metricScalarAt L.metric x / 2 <
        (2 * C2) * metricScalarAt L.metric x := by
      nlinarith [mul_pos hC2pos hxpos]
    have hband : ∀ w ∈ K.carrier,
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
          metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x :=
      fun w hw => ⟨hlow.trans (hscalar w hw).1, (hscalar w hw).2.trans hupp⟩
    refine Or.inr ⟨K, hmodel, ?_, hband⟩
    rw [hpre, ← G.terminalRegularOpen.isOpenEmbedding'.isOpenMap
      |>.preimage_interior_eq_interior_preimage G.terminalRegularOpen.isOpenEmbedding'.continuous]
    intro w hw
    exact hinside ⟨w, hw, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
