import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSpatialCanonicalAlternatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCorePresentationExistence

open private boundary_pair_of_neck_or_cap from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrierFamily
open private ComponentEndPresentation compactComponentPresentation
  ComponentEndPresentation.toAmbient componentPresentationOfHalfCylinders
  assembleTerminalCorePresentation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCorePresentationExistence

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_spherical_barrier_at_level_of_spatiallyCanonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q A : ℝ}
    (hδsmall : δ < 1 / 20000) (hA : 0 < A)
    (hqA : q < 4 * C2 * A)
    {x y : G.terminalRegularOpen}
    (hscale : metricScalarAt L.metric x = 4 * C2 * A)
    (hy : y.val ∈ connectedComponent x.val)
    (hyA : metricScalarAt L.metric y ≤ A)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) (δ / 4) C1 C2 x.val,
        W.capTubeHasNeckChart (δ / 4)) :
    ∃ (K : CompactDomain G.terminalRegularOpen) (v : G.terminalRegularOpen)
      (nk : SpatialNeck L.metric δ v),
      x ∈ interior K.carrier ∧
      (∀ z ∈ K.carrier, 2 * A < metricScalarAt L.metric z ∧
        metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      ((K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
          range (fun q : Sphere 2 => nk.map (q, 3)) ∧
        Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
          (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
        (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞
          (fun q : Sphere 2 => nk.map (q, b))) ∧
        ∃ (cneg : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, -3)))
          (cpos : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, 3))),
          cneg.radius < 1 ∧ cpos.radius < 1 ∧
          (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
            (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
          (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
            (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
      (frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        ∃ c : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, 1 / 2)),
          c.radius < 1 / 4 ∧ ∀ q,
            c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
              (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) := by
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds (hscale.symm ▸ hqA))
  have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W₀, _⟩ := hcanonical t ht hqt
  have hδ : 0 < δ := by linarith [W₀.eps_pos]
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  let eps := δ / 4
  have hepsδ : eps < δ := by dsimp [eps]; linarith
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by
    have hδ1 : δ < 1 := hδsmall.trans (by norm_num)
    have hdiv : δ⁻¹ + 1 ≤ (δ / 4)⁻¹ := by
      rw [inv_div]
      apply (le_div_iff₀ hδ).mpr
      field_simp
      linarith
    exact hdiv
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  have hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x := by
    rw [hscale]
    have hm := mul_le_mul_of_nonneg_left hyA (zero_le_one.trans hC2)
    nlinarith
  have hbranch := L.eventually_spatial_neck_or_cap x y hy (eps := eps)
    (C1 := C1) (C2 := C2) hscalar
  obtain ⟨τ, _, _, hτ, W, hW, hcases⟩ :=
    exists_spatial_neck_or_cap_sequence_of_eventually
      (fun t ht hxq => by
        obtain ⟨w, hw⟩ := hcanonical t ht hxq
        exact ⟨w, by simpa [eps] using hw⟩)
      hhigh hbranch
  rcases hcases with ⟨neck, hneck⟩ | ⟨cap, depth, hcap⟩
  · obtain ⟨n, nk, K, _, hK, hxK, hfront, hdisj, hemb, hband, hfull, hmetric, hdom, hcollar⟩ :=
      L.exists_neck_spherical_barrier_of_incoming_spatialNecks hτ x hδ
        (hδsmall.trans (by norm_num)) hepsδ hfit
        (fun n => (neck n).neck) A C2 hA hC2 hscale
    exact ⟨K, x, nk, hxK, hband, hfull, hmetric, hdom,
      Or.inl ⟨hK, hfront, hdisj, hemb, hcollar⟩⟩
  · obtain ⟨n, v, nk, K, hK, hxK, hKU, hband, hfull, hfront, hemb, hmetric, hdom, hcollar⟩ :=
      (L.eventually_spatial_cap_spherical_barrier hτ x hx hδ hδsmall hepsδ hfit W hW cap depth
        hcap).exists
    have hlow : metricScalarAt L.metric x / (2 * C2) = 2 * A := by
      rw [hscale]
      field_simp
      ring
    have hhigh' : 2 * C2 * metricScalarAt L.metric x = 8 * C2 ^ 2 * A := by
      rw [hscale]
      ring
    refine ⟨K, v, nk, hxK, ?_, ?_, hmetric, hdom, ?_⟩
    · intro z hz
      simpa only [hlow, hhigh'] using And.intro (hband z hz).1 (hband z hz).2.le
    · intro z hz
      simpa only [hlow, hhigh'] using And.intro (hfull z hz).1 (hfull z hz).2.le
    · exact Or.inr ⟨hfront, hemb, hcollar⟩

theorem TerminalLimitMetric.spatial_neck_or_cap_core_of_spatiallyCanonical_of_not_isCompact
    (L : G.TerminalLimitMetric) {δ q C1 C2 : ℝ}
    (hδsmall : δ ≤ 1 / 8646) (hq : 0 < q)
    (p x : G.terminalRegularOpen)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) (δ / 4) C1 C2 x.val,
        W.capTubeHasNeckChart (δ / 4))
    (hqx : q < metricScalarAt L.metric x)
    (hnoncompact : ¬ IsCompact (connectedComponent x))
    (nk : SpatialNeck L.metric δ p) (z : Sphere 2) (level : ℝ)
    (hlevel : |level| ≤ 4) (hxmap : nk.map (z, level) = x) :
    Nonempty (SpatialNeck L.metric δ x) ∨
      ∃ K : CompactDomain G.terminalRegularOpen,
        Nonempty (CapCore K.carrier) ∧
        nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
        (∀ w ∈ K.carrier,
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
            metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  have hδ : 0 < δ := nk.eps_pos
  have hepsδ : δ / 4 < δ := by linarith
  have hfit : δ⁻¹ + 1 ≤ (δ / 4)⁻¹ := by
    rw [inv_div]
    apply (le_div_iff₀ hδ).mpr
    field_simp
    linarith
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hqx)
  have hbranch := L.eventually_spatial_neck_or_cap_of_not_isCompact
    x hnoncompact (δ / 4) C1 C2
  obtain ⟨τ, _, _, hτ, W, hW, halt⟩ :=
    exists_spatial_neck_or_cap_sequence_of_eventually hcanonical hhigh hbranch
  exact TerminalLimitMetric.spatial_neck_or_cap_core_of_spatial_sequence L hτ x (hq.trans hqx)
    hδsmall hepsδ hfit W hW halt nk z hlevel hxmap

theorem TerminalLimitMetric.exists_finite_spherical_barrier_cover_of_spatiallyCanonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q : ℝ}
    (hδsmall : δ < 1 / 20000)
    (hcanonical : G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s)
    (A : ℝ) (y : G.terminalRegularOpen) (hA : 0 < A) (hqA : q < 4 * C2 * A)
    (hyA : metricScalarAt L.metric y ≤ A) (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ (s : Finset {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
      (K : {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
          CompactDomain G.terminalRegularOpen),
      s.Nonempty ∧
      {z : G.terminalRegularOpen |
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p ∈ s, interior (K p).carrier ∧
      (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
        (∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
          metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
        ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v),
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      (((K p).carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
        frontier (K p).carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
          range (fun q : Sphere 2 => nk.map (q, 3)) ∧
        Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
          (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
        (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, b))) ∧
        ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, -3)))
          (cpos : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 3))),
          cneg.radius < 1 ∧ cpos.radius < 1 ∧
          (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
            (cneg.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
          (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
            (cpos.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
      (frontier (K p).carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
          c.radius < 1 / 4 ∧ ∀ q,
            c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
              (c.toFun q ∈ (K p).carrier ↔ (q.2 : ℝ) ≤ 0)))) ∧
      IsCompact (⋃ p ∈ s, frontier (K p).carrier) ∧
      Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
        (⋃ p ∈ s, frontier (K p).carrier) := by
  classical
  obtain ⟨x, _, hx⟩ :=
    L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hcont : Continuous (metricScalarAt L.metric) := (metricScalar_smooth L.metric).continuous
  have hcompact : IsCompact {z : G.terminalRegularOpen |
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z ≤ 4 * C2 * A} :=
    (L.isCompact_scalar_sublevel (4 * C2 * A)).of_isClosed_subset
      (isClosed_connectedComponent.inter (isClosed_le hcont continuous_const)) (fun z hz => hz.2)
  have hAT : A ≤ 4 * C2 * A := by nlinarith
  have hupper : ∃ z ∈ connectedComponent y, 4 * C2 * A < metricScalarAt L.metric z := by
    by_contra h
    push Not at h
    apply hnoncompact
    convert hcompact using 1
    ext z
    exact ⟨fun hz => ⟨hz, h z hz⟩, fun hz => hz.1⟩
  obtain ⟨z, hz, hzT⟩ := hupper
  have hlevelne : ({z : G.terminalRegularOpen |
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} : Set _).Nonempty := by
    obtain ⟨p, hp, hpT⟩ := isPreconnected_connectedComponent.intermediate_value
      (mem_connectedComponent (x := y)) hz hcont.continuousOn ⟨hyA.trans hAT, hzT.le⟩
    exact ⟨p, hp, hpT⟩
  have hlevel : IsCompact {z : G.terminalRegularOpen |
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} := by
    apply hcompact.of_isClosed_subset
      (isClosed_connectedComponent.inter (isClosed_eq hcont continuous_const))
    exact fun p hp => ⟨hp.1, hp.2.le⟩
  have hpacket (p : {z : G.terminalRegularOpen //
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A}) :=
    L.exists_spherical_barrier_at_level_of_spatiallyCanonical hδsmall hA hqA p.property.2
      (by
        have hycomp : y ∈ connectedComponent p.val := by
          rw [← connectedComponent_eq p.property.1]
          exact mem_connectedComponent
        exact continuous_subtype_val.image_connectedComponent_subset p.val ⟨y, hycomp, rfl⟩)
      hyA (hcanonical p.val.val)
  choose K v neck hcenter hband hfull hmetric hdomain hgeometry using hpacket
  have hcover : {z : G.terminalRegularOpen |
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p, interior (K p).carrier := fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hcenter ⟨z, hz⟩⟩
  obtain ⟨s, hs⟩ := hlevel.elim_finite_subcover (fun p => interior (K p).carrier)
    (fun _ => isOpen_interior) hcover
  have hsne : s.Nonempty := by
    obtain ⟨z, hz⟩ := hlevelne
    obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp (hs hz)
    exact ⟨p, hp⟩
  refine ⟨s, K, hsne, hs, ?_, ?_, ?_⟩
  · intro p _
    refine ⟨hcenter p, ?_, hband p, v p, neck p, hfull p, hmetric p, hdomain p, hgeometry p⟩
    rw [connectedComponent_eq p.property.1]
    exact (K p).connected.subset_connectedComponent (interior_subset (hcenter p))
  · apply s.finite_toSet.isCompact_biUnion
    intro p _
    exact (K p).compact.of_isClosed_subset isClosed_frontier (K p).compact.isClosed.frontier_subset
  · apply disjoint_left.mpr
    intro z hz hfront
    obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp hfront
    have hscalar := (hband p z ((K p).compact.isClosed.frontier_subset hp)).1
    have hlo : metricScalarAt L.metric z ≤ A := hz
    linarith

theorem TerminalLimitMetric.exists_finite_recorded_spherical_barriers_of_spatiallyCanonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q : ℝ}
    (hδsmall : δ < 1 / 20000)
    (hcanonical : G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s)
    (A : ℝ) (y : G.terminalRegularOpen) (hA : 0 < A) (hqA : q < 4 * C2 * A)
    (hyA : metricScalarAt L.metric y ≤ A) (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ (s : Finset {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
      (K : {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
          CompactDomain G.terminalRegularOpen),
      s.Nonempty ∧
      {z : G.terminalRegularOpen |
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p ∈ s, interior (K p).carrier ∧
      (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
        ∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
          metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
      ∃ (v : {p // p ∈ s} → G.terminalRegularOpen)
        (neck : ∀ p, SpatialNeck L.metric δ (v p))
        (level sign : {p // p ∈ s} × Fin 2 → ℝ)
        (collar : ∀ i, SmoothTwoSidedCollar I2 I3
          (fun z : Sphere 2 => (neck i.1).map (z, level i))),
        (∀ p, frontier (K p.val).carrier =
          ⋃ j : Fin 2, range (fun z : Sphere 2 => (neck p).map (z, level (p, j)))) ∧
        (⋃ p ∈ s, frontier (K p).carrier) =
          ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
        (∀ p, A < (1 - 4323 * δ) * metricScalarAt L.metric (v p) ∧
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric ((neck p).map z) ∧
              metricScalarAt L.metric ((neck p).map z) ≤ 8 * C2 ^ 2 * A) ∧
          (neck p).cylindricalChart.metricCloseOn L.metric δ
            {z : (neck p).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          ∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck p).cylindricalChart.domain) ∧
        (∀ i, |level i| ≤ 3 ∧ (sign i = 1 ∨ sign i = -1) ∧
          IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
          (collar i).radius < 1 ∧ ∀ z,
            (collar i).toFun z = (neck i.1).map (z.1, level i + sign i * (z.2 : ℝ)) ∧
              ((collar i).toFun z ∈ (K i.1.val).carrier ↔ (z.2 : ℝ) ≤ 0)) ∧
        IsCompact (⋃ i : {p // p ∈ s} × Fin 2,
          range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
        Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
          (⋃ i : {p // p ∈ s} × Fin 2,
            range (fun z : Sphere 2 => (neck i.1).map (z, level i))) := by
  classical
  obtain ⟨s, K, hs, hcov, hK, hcompact, hlow⟩ :=
    L.exists_finite_spherical_barrier_cover_of_spatiallyCanonical hδsmall hcanonical
      A y hA hqA hyA hnoncompact
  have hpack (p : {p // p ∈ s}) := (hK p.val p.property).2.2.2
  choose v neck hfull hmetric hdomain hgeometry using hpack
  choose level sign collar hfront hcollar using fun p =>
    boundary_pair_of_neck_or_cap (K p.val) (neck p) (hgeometry p)
  let lev : {p // p ∈ s} × Fin 2 → ℝ := fun i => level i.1 i.2
  let sgn : {p // p ∈ s} × Fin 2 → ℝ := fun i => sign i.1 i.2
  let col : ∀ i : {p // p ∈ s} × Fin 2,
      SmoothTwoSidedCollar I2 I3 (fun z : Sphere 2 => (neck i.1).map (z, lev i)) :=
    fun i => collar i.1 i.2
  have hunion : (⋃ p ∈ s, frontier (K p).carrier) =
      ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, lev i)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
      have hzp' : z ∈ ⋃ j : Fin 2,
          range (fun z : Sphere 2 => (neck ⟨p, hp⟩).map (z, level ⟨p, hp⟩ j)) :=
        (hfront ⟨p, hp⟩).subset hzp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hzp'
      exact mem_iUnion.mpr ⟨(⟨p, hp⟩, j), hj⟩
    · intro hz
      obtain ⟨⟨p, j⟩, hj⟩ := mem_iUnion.mp hz
      exact mem_iUnion₂.mpr ⟨p.val, p.property, (hfront p).symm.subset (mem_iUnion.mpr ⟨j, hj⟩)⟩
  refine ⟨s, K, hs, hcov, ?_, v, neck, lev, sgn, col, hfront, hunion, ?_,
    fun i => hcollar i.1 i.2, hunion ▸ hcompact, hunion ▸ hlow⟩
  · intro p hp
    exact ⟨(hK p hp).1, (hK p hp).2.1, (hK p hp).2.2.1⟩
  · intro p
    have hcenter := (hfull p ((neck p).center, 0) ⟨mem_univ _, by norm_num⟩).1
    rw [(neck p).center_eq] at hcenter
    refine ⟨?_, hfull p, hmetric p, hdomain p⟩
    nlinarith [(neck p).Q_pos]

theorem TerminalLimitMetric.exists_recorded_barriers_with_compact_closures_of_spatiallyCanonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q : ℝ}
    (hδsmall : δ < 1 / 20000)
    (hcanonical : G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s)
    (A : ℝ) (y : G.terminalRegularOpen) (hA : 0 < A) (hqA : q < 4 * C2 * A)
    (hyA : metricScalarAt L.metric y ≤ A) (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ (s : Finset {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
      (K : {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
          CompactDomain G.terminalRegularOpen),
      s.Nonempty ∧
      {z : G.terminalRegularOpen |
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p ∈ s, interior (K p).carrier ∧
      (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
        ∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
          metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
      ∃ (v : {p // p ∈ s} → G.terminalRegularOpen)
        (neck : ∀ p, SpatialNeck L.metric δ (v p))
        (level sign : {p // p ∈ s} × Fin 2 → ℝ)
        (collar : ∀ i, SmoothTwoSidedCollar I2 I3
          (fun z : Sphere 2 => (neck i.1).map (z, level i))),
        (∀ p, frontier (K p.val).carrier =
          ⋃ j : Fin 2, range (fun z : Sphere 2 => (neck p).map (z, level (p, j)))) ∧
        (⋃ p ∈ s, frontier (K p).carrier) =
          ⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
        (∀ p, A < (1 - 4323 * δ) * metricScalarAt L.metric (v p) ∧
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric ((neck p).map z) ∧
              metricScalarAt L.metric ((neck p).map z) ≤ 8 * C2 ^ 2 * A) ∧
          (neck p).cylindricalChart.metricCloseOn L.metric δ
            {z : (neck p).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          ∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck p).cylindricalChart.domain) ∧
        (∀ i, |level i| ≤ 3 ∧ (sign i = 1 ∨ sign i = -1) ∧
          IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i.1).map (z, level i)) ∧
          (collar i).radius < 1 ∧ ∀ z,
            (collar i).toFun z = (neck i.1).map (z.1, level i + sign i * (z.2 : ℝ)) ∧
              ((collar i).toFun z ∈ (K i.1.val).carrier ↔ (z.2 : ℝ) ≤ 0)) ∧
        IsCompact (⋃ i : {p // p ∈ s} × Fin 2,
          range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
        Disjoint {z : G.terminalRegularOpen | metricScalarAt L.metric z ≤ A}
          (⋃ i : {p // p ∈ s} × Fin 2, range (fun z : Sphere 2 => (neck i.1).map (z, level i))) ∧
        ∀ x ∈ connectedComponent y, metricScalarAt L.metric x ≤ A →
          IsCompact (closure (connectedComponentIn
            (⋃ i : {p // p ∈ s} × Fin 2,
              range (fun z : Sphere 2 => (neck i.1).map (z, level i)))ᶜ x)) ∧
          closure (connectedComponentIn
            (⋃ i : {p // p ∈ s} × Fin 2,
              range (fun z : Sphere 2 => (neck i.1).map (z, level i)))ᶜ x) ⊆
            {z : G.terminalRegularOpen |
              z ∈ connectedComponent y ∧ metricScalarAt L.metric z < 4 * C2 * A} := by
  obtain ⟨x, _, hx⟩ :=
    L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  obtain ⟨s, K, hs, hcover, hK, v, neck, level, sign, collar, hfront, hunion,
    hgeometry, hcollar, hcompact, hlow⟩ :=
    L.exists_finite_recorded_spherical_barriers_of_spatiallyCanonical hδsmall hcanonical
      A y hA hqA hyA hnoncompact
  refine ⟨s, K, hs, hcover, hK, v, neck, level, sign, collar, hfront, hunion,
    hgeometry, hcollar, hcompact, hlow, ?_⟩
  intro x hx hRx
  exact L.isCompact_closure_connectedComponentIn_of_finite_barrier_cover s K
    (by nlinarith : A ≤ 4 * C2 * A) y
    (fun i hi z hz => lt_trans (by linarith : A < 2 * A) ((hK i hi).2.2 z hz).1)
    hcover (fun i : {p // p ∈ s} × Fin 2 =>
      range (fun z : Sphere 2 => (neck i.1).map (z, level i))) hunion hx hRx

theorem exists_uniform_disjoint_spherical_region_of_spatiallyCanonical :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ,
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s →
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (K : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact K ∧ closure (interior K) = K ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
              ⊆ interior K ∧ K ⊆ connectedComponent y ∧
            (∀ x ∈ K, metricScalarAt L.metric x ≤ 8 * C2^2 * A) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier K = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier K, 2 * A < metricScalarAt L.metric x) ∧
            ∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * A < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * A) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ K ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior K ↔ t < 0 := by
  obtain ⟨eta, heta, hregion⟩ :=
    exists_compact_region_of_finite_spatial_neck_barriers_tolerance.{u, u}
  refine ⟨min eta (1 / 40000), lt_min heta (by norm_num), ?_⟩
  intro δ hδeta C1 C2 q P a s G L hcanonical A y hA hqA hyA hnoncompact
  obtain ⟨x, _, hx⟩ := L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in nhdsWithin s (Iio s), t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hδsmall : δ < 1 / 20000 := by linarith [hδeta.trans (min_le_right _ _)]
  obtain ⟨S, D, hSne, hcover, hD, v, neck, level, sign, collar, hfront, hunion, hgeometry,
    hcollar, hallcompact, hlow, hold⟩ :=
      L.exists_recorded_barriers_with_compact_closures_of_spatiallyCanonical
      hδsmall hcanonical A y hA hqA hyA hnoncompact
  let J := {p // p ∈ S} × Fin 2
  let F : J → Set G.terminalRegularOpen := fun i =>
    range (fun z : Sphere 2 => (neck i.1).map (z, level i))
  let Low := {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A}
  classical
  let _ := Fintype.ofFinite J
  have hLowcompact : IsCompact Low :=
    (L.isCompact_scalar_sublevel A).of_isClosed_subset
      (isClosed_connectedComponent.inter
        (isClosed_le (metricScalar_smooth L.metric).continuous continuous_const))
      (fun x hx => hx.2)
  have hLowold (x : G.terminalRegularOpen) (hx : x ∈ Low) :
      IsCompact (closure (connectedComponentIn
        (⋃ i ∈ (Finset.univ : Finset J), F i)ᶜ x)) := by
    simpa only [Finset.mem_univ, iUnion_true] using (hold x hx.1 hx.2).1
  obtain ⟨t, b, C, ht, hbt, htdis, hC, hCprops, hKcompact, hLowK, hKreg,
    hKsub, hKfront, hKcollar⟩ :=
    hregion δ (hδeta.trans (min_le_left _ _)) G.terminalRegularOpen L.metric
      J (fun i => v i.1) (fun i => neck i.1) level Finset.univ
      (fun i _ => (hcollar i).1) A Low hLowcompact (fun _ hx => hx.2)
      (fun i _ => (hgeometry i.1).1) hLowold
  let K := ⋃ V ∈ C, closure V
  have hKcomp : K ⊆ connectedComponent y := by
    intro z hz
    obtain ⟨V, hVC, hzV⟩ := mem_iUnion₂.mp hz
    obtain ⟨x, hx, rfl⟩ := (hC V).mp hVC
    have hsubset : connectedComponentIn (⋃ i ∈ t, F i)ᶜ x ⊆ connectedComponent y := by
      have hxout : x ∉ ⋃ i ∈ t, F i := by
        intro hxbar
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxbar
        exact disjoint_left.mp hlow hx.2 (mem_iUnion.mpr ⟨i, hxi⟩)
      have hc := isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn (show x ∈ (⋃ i ∈ t, F i)ᶜ from hxout))
      rw [← connectedComponent_eq hx.1] at hc
      exact hc
    exact closure_minimal hsubset isClosed_connectedComponent hzV
  have hKband : ∀ z ∈ K, metricScalarAt L.metric z ≤ 8 * C2^2 * A := by
    intro z hz
    rcases hKsub hz with hzold | hzchart
    · obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hzold
      have hzx' : z ∈ closure (connectedComponentIn (⋃ i : J, F i)ᶜ x) := by
        simpa only [Finset.mem_univ, iUnion_true] using hzx
      have hb := (hold x hx.1 hx.2).2 hzx'
      have hupper : 4 * C2 * A ≤ 8 * C2^2 * A :=
        mul_le_mul_of_nonneg_right (by nlinarith : 4 * C2 ≤ 8 * C2 ^ 2) hA.le
      exact hb.2.le.trans hupper
    · obtain ⟨i, _, w, hw, rfl⟩ := mem_iUnion₂.mp hzchart
      exact ((hgeometry i.1).2.1 w
        ⟨hw.1, by constructor <;> linarith [hw.2.1, hw.2.2]⟩).2
  have hfrontband : ∀ z ∈ frontier K, 2 * A < metricScalarAt L.metric z := by
    intro z hz
    obtain ⟨i, hi, w, rfl⟩ := mem_iUnion₂.mp (hKfront ▸ hz)
    exact ((hgeometry i.1).2.1 (w, level i)
      ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hcollar i).1).1, (abs_le.mp (hcollar i).1).2]⟩).1
  have hbne : b.Nonempty := by
    by_contra hn
    have hbempty : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hfrontempty : frontier K = ∅ := by
      rw [hKfront, hbempty]
      simp
    have hsub : connectedComponent y ⊆ interior K :=
      isPreconnected_subset_interior_of_meets_of_disjoint_frontier isPreconnected_connectedComponent
        ⟨y, mem_connectedComponent, interior_subset (hLowK ⟨mem_connectedComponent, hyA⟩)⟩
        (by rw [hfrontempty]; exact disjoint_empty _)
    exact hnoncompact (hKcompact.of_isClosed_subset isClosed_connectedComponent
      (hsub.trans interior_subset))
  refine ⟨J, (fun i => v i.1), (fun i => neck i.1), level, b, K, hbne, hKcompact,
    hKreg, hLowK, hKcomp,
    hKband, ?_, hKfront, hfrontband, ?_⟩
  · intro i hi j hj hij
    exact htdis (hbt hi) (hbt hj) hij
  · intro i hi
    obtain ⟨r, σ, hr, hσ, hsrc, hside, hinside⟩ := hKcollar i hi
    let r' := min r 1
    have hr' : 0 < r' := lt_min hr zero_lt_one
    have hscaled (z : ℝ) (hz : z ∈ Ioo (-r') r') : σ * z ∈ Ioo (-r) r := by
      rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hz.1, hz.2, min_le_left r 1]
    refine ⟨(hcollar i).1, (hcollar i).2.2.1, (hgeometry i.1).2.1,
      (hgeometry i.1).2.2.1, (hgeometry i.1).2.2.2, r', σ, hr', min_le_right _ _, hσ,
      (fun z t ht => hsrc z (σ * t) (hscaled t ht)), ?_, ?_⟩
    · intro z t ht
      have hh := hside z (σ * t) (hscaled t ht)
      rcases hσ with rfl | rfl <;> simpa [K] using hh
    · intro z t ht
      have hh := hinside z (σ * t) (hscaled t ht)
      rcases hσ with rfl | rfl <;> simpa [K] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

theorem exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_spatiallyCanonical :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ, 0 < q →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s →
        ∀ (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → (2 * C2) * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          ∃ (ι : Type u) (v : ι → G.terminalRegularOpen)
            (neck : ∀ i, SpatialNeck L.metric δ (v i)) (level : ι → ℝ)
            (b : Finset ι) (W : Set G.terminalRegularOpen),
            b.Nonempty ∧ IsCompact W ∧ closure (interior W) = W ∧
            {x : G.terminalRegularOpen | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ B}
              ⊆ interior W ∧ W ⊆ connectedComponent y ∧
            (∀ x ∈ W, metricScalarAt L.metric x ≤ 8 * C2^2 * B) ∧
            (b : Set ι).PairwiseDisjoint
              (fun i => range (fun z : Sphere 2 => (neck i).map (z, level i))) ∧
            frontier W = ⋃ i ∈ b, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt L.metric x) ∧
            (∀ i ∈ b, |level i| ≤ 3 ∧
              IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
                2 * B < metricScalarAt L.metric ((neck i).map z) ∧
                  metricScalarAt L.metric ((neck i).map z) ≤ 8 * C2^2 * B) ∧
              (neck i).cylindricalChart.metricCloseOn L.metric δ
                {z : (neck i).cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
              (∀ z t, t ∈ Icc (-101 : ℝ) 101 → (z, t) ∈ (neck i).cylindricalChart.domain) ∧
              ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            ∀ V : Set G.terminalRegularOpen, W ⊆ V →
              ∀ x ∈ connectedComponent y, x ∉ interior V →
                B < metricScalarAt L.metric x ∧
                ∀ (p : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck L.metric δ x) ∨
                  ∃ K : CompactDomain G.terminalRegularOpen,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt L.metric w ∧
                      metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
                        metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  obtain ⟨η, hη, hregion⟩ := exists_uniform_disjoint_spherical_region_of_spatiallyCanonical.{u}
  refine ⟨min η (1 / 8646), lt_min hη (by norm_num), ?_⟩
  intro δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact
  obtain ⟨x, _, hx⟩ := L.exists_scalar_gt_on_connectedComponent_of_not_isCompact y hnoncompact q
  have hhigh := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have htime : ∀ᶠ t in nhdsWithin s (Iio s), t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W, _⟩ := hcanonical x.val t ht hqt
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hδsmall : δ ≤ 1 / 8646 := hδη.trans (min_le_right _ _)
  let C := 2 * C2
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hB : 0 < B := hq.trans hqB
  have hqscale : q < 4 * C2 * B := by nlinarith
  obtain ⟨ι, v, neck, level, b, W, hb, hW, hreg, hlow, hcomponent,
    hscalar, hdisjoint, hfront, hfrontscalar, hnecks⟩ :=
    hregion δ (hδη.trans (min_le_left _ _)) C1 C2 q P a s G L hcanonical
      B y hB hqscale hyB hnoncompact
  refine ⟨ι, v, neck, level, b, W, hb, hW, hreg, hlow, hcomponent,
    hscalar, hdisjoint, hfront, hfrontscalar, hnecks, ?_⟩
  intro V hWV x hxcomp hxout
  have hxhigh : B < metricScalarAt L.metric x := by
    by_contra hn
    exact hxout (interior_mono hWV (hlow ⟨hxcomp, le_of_not_gt hn⟩))
  refine ⟨hxhigh, ?_⟩
  intro p nk z level hlevel hx
  have hxnoncompact : ¬ IsCompact (connectedComponent x) := by
    rw [← connectedComponent_eq hxcomp]
    exact hnoncompact
  rcases L.spatial_neck_or_cap_core_of_spatiallyCanonical_of_not_isCompact
      hδsmall hq p x (fun t ht hx => hcanonical x.val t ht hx)
      (hqB.trans hxhigh) hxnoncompact nk z level hlevel hx with hn | hc
  · exact Or.inl hn
  · obtain ⟨K, hmodel, hinside, hband⟩ := hc
    refine Or.inr ⟨K, hmodel, hinside, ?_⟩
    intro w hw
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hAx : A < metricScalarAt L.metric x / C :=
      (lt_div_iff₀ hCpos).mpr (by nlinarith)
    exact ⟨hAx.trans (hband w hw).1, hband w hw⟩

theorem exists_uniform_component_spherical_region_of_spatiallyCanonical :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η →
      ∀ C1 C2 q : ℝ, 0 < q →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (L : G.TerminalLimitMetric),
        G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s →
        ∀ (A B : ℝ) (y : G.terminalRegularOpen),
          q < B → (2 * C2) * A ≤ B → metricScalarAt L.metric y ≤ B →
          ¬ IsCompact (connectedComponent y) →
          let U := connectedComponentOpen (I := I3) y
          ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
            (v : ι → U) (neck : ∀ i, SpatialNeck (L.metric.restrictOpen U) δ (v i))
            (level : ι → ℝ) (W : Set U),
            IsCompact W ∧ closure (interior W) = W ∧
            {x : U | metricScalarAt (L.metric.restrictOpen U) x ≤ B} ⊆ interior W ∧
            (∀ x ∈ W, metricScalarAt (L.metric.restrictOpen U) x ≤ 8 * C2^2 * B) ∧
            Pairwise (fun i j => Disjoint
              (range (fun z : Sphere 2 => (neck i).map (z, level i)))
              (range (fun z : Sphere 2 => (neck j).map (z, level j)))) ∧
            frontier W = ⋃ i, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
            (∀ i, |level i| ≤ 3) ∧
            (∀ i, ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
              (∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
              ∀ z, ∀ t ∈ Ioo (-r) r,
                (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
            (∀ x ∈ frontier W, 2 * B < metricScalarAt (L.metric.restrictOpen U) x) ∧
            ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
              B < metricScalarAt (L.metric.restrictOpen U) x ∧
              ∀ (p : U) (nk : SpatialNeck (L.metric.restrictOpen U) δ p)
                (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                Nonempty (SpatialNeck (L.metric.restrictOpen U) δ x) ∨
                ∃ K : CompactDomain U,
                  Nonempty (CapCore K.carrier) ∧
                  nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                  (∀ w ∈ K.carrier, A < metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) x / (2 * C2) <
                      metricScalarAt (L.metric.restrictOpen U) w ∧
                    metricScalarAt (L.metric.restrictOpen U) w <
                      (2 * C2) * metricScalarAt (L.metric.restrictOpen U) x) := by
  obtain ⟨η, hη, hmain⟩ :=
    exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_spatiallyCanonical.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact U
  obtain ⟨ι, v, neck, level, b, W₀, hb, hW₀, hreg₀, hlow₀, hcomponent,
    hscalar₀, hdisjoint₀, hfront₀, hfrontscalar₀, hgeometry, hmodels⟩ :=
    hmain δ hδη C1 C2 q hq P a s G L hcanonical A B y hqB hAB hyB hnoncompact
  have hlevel (i : ι) (hi : i ∈ b) : |level i| < δ⁻¹ := by
    have hlen : (3 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr
        (by linarith [(neck i).eps_small])
    exact ((hgeometry i hi).1).trans_lt hlen
  obtain ⟨v', neck', hpoint, hcenter, hmap, hcompact, hregular, hinterior,
    hfront, hdisjoint⟩ := exists_spatial_neck_frontier_on_connectedComponent b v neck level
      hlevel y hW₀ hreg₀ hcomponent hfront₀ hdisjoint₀
  let W : Set U := Subtype.val ⁻¹' W₀
  let _ : Nonempty {i // i ∈ b} := by
    obtain ⟨i, hi⟩ := hb
    exact ⟨⟨i, hi⟩⟩
  refine ⟨{i // i ∈ b}, inferInstance, inferInstance, v', neck',
    (fun i => level i.val), W, hcompact, hregular, ?_, ?_, hdisjoint, hfront,
    (fun i => (hgeometry i.val i.property).1), ?_, ?_, ?_⟩
  · intro x hx
    rw [hinterior]
    apply hlow₀
    refine ⟨x.property, ?_⟩
    change metricScalarAt (L.metric.restrictOpen U) x ≤ B at hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hx
  · intro x hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
      hscalar₀ x.val hx
  · intro i
    obtain ⟨hlev, _, _, _, _, r, σ, hr, hr1, hσ, _, hside, hint⟩ :=
      hgeometry i.val i.property
    have hlen : (4 : ℝ) < δ⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i.val).eps_pos).mpr
        (by linarith [(neck i.val).eps_small])
    have hwindow (z : Sphere 2) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
        (z, level i.val + σ * t) ∈ univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ := by
      refine ⟨mem_univ _, ?_⟩
      rcases hσ with hσ | hσ
      · rw [hσ, one_mul]
        constructor <;> linarith [(abs_le.mp hlev).1, (abs_le.mp hlev).2, ht.1, ht.2]
      · rw [hσ, neg_one_mul]
        constructor <;> linarith [(abs_le.mp hlev).1, (abs_le.mp hlev).2, ht.1, ht.2]
    refine ⟨r, σ, hr, hr1, hσ, ?_, ?_, ?_⟩
    · intro z t ht
      exact (neck' i).domain (hwindow z t ht)
    · intro z t ht
      change ((neck' i).map (z, level i.val + σ * t) : G.terminalRegularOpen) ∈ W₀ ↔ t ≤ 0
      rw [hmap i _ (hwindow z t ht)]
      exact hside z t ht
    · intro z t ht
      rw [hinterior]
      change ((neck' i).map (z, level i.val + σ * t) : G.terminalRegularOpen) ∈ interior W₀ ↔ t < 0
      rw [hmap i _ (hwindow z t ht)]
      exact hint z t ht
  · intro x hx
    have hx₀ : x.val ∈ frontier W₀ := by
      have heq := U.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
        continuous_subtype_val W₀
      exact heq.superset hx
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
      hfrontscalar₀ x.val hx₀
  · intro V hWV x hxout
    let V₀ : Set G.terminalRegularOpen := Subtype.val '' V
    have hW₀V₀ : W₀ ⊆ V₀ := by
      intro w hw
      exact ⟨⟨w, hcomponent hw⟩, hWV hw, rfl⟩
    have hxout₀ : x.val ∉ interior V₀ := by
      intro hxint
      apply hxout
      have heq := U.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
        continuous_subtype_val V₀
      have hxpre : x ∈ interior ((Subtype.val : U → G.terminalRegularOpen) ⁻¹' V₀) :=
        heq ▸ hxint
      simpa only [V₀, preimage_image_eq _ Subtype.val_injective] using hxpre
    obtain ⟨hxhigh, hmodel⟩ := hmodels V₀ hW₀V₀ x.val x.property hxout₀
    refine ⟨?_, ?_⟩
    · simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
        hxhigh
    · intro p nk z height hheight hx
      obtain ⟨nk₀, _, hnkmap, _, _, _⟩ := nk.exists_of_restrictOpen
      have hx₀ : nk₀.map (z, height) = x.val := by rw [hnkmap, hx]
      rcases hmodel p.val nk₀ z height hheight hx₀ with hn | hc
      · obtain ⟨newNeck⟩ := hn
        have hcomp : connectedComponent x.val = connectedComponent y :=
          (connectedComponent_eq x.property).symm
        have hcapture : newNeck.map '' (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) ⊆ U := by
          change _ ⊆ connectedComponent y
          rw [← hcomp]
          exact newNeck.controlled_range_subset_connectedComponent
        exact Or.inl ⟨newNeck.restrictOpen hcapture⟩
      · obtain ⟨K₀, ⟨model⟩, hinside, hscalar⟩ := hc
        have hxK : x.val ∈ K₀.carrier := interior_subset (hinside
          ⟨(z, height), ⟨mem_univ _, abs_le.mp hheight⟩, hx₀⟩)
        have hKU : K₀.carrier ⊆ U := by
          change K₀.carrier ⊆ connectedComponent y
          rw [← (connectedComponent_eq x.property).symm]
          exact K₀.connected.subset_connectedComponent hxK
        let K := K₀.restrictOpen U hKU
        refine Or.inr ⟨K, model.nonempty_preimage_open U hKU, ?_, ?_⟩
        · rw [CompactDomain.interior_restrictOpen_carrier]
          rintro w ⟨v, hv, rfl⟩
          exact hinside ⟨v, hv, hnkmap v⟩
        · intro w hw
          simpa only
            [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using
              hscalar w.val hw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OneStepIncoming

open OrientedThreeStage in
theorem exists_neckRadius_spherical_region_with_scale_bound_of_spatiallyCanonical :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∀ C1 C2 q : ℝ, 1 ≤ C2 → 0 < q →
      ∀ D : OneStepIncoming.{u},
        D.slab.SpatiallyCanonicalBefore (δ / 4) C1 C2 q D.endTime →
        ∀ q' : ℝ, q ≤ q' →
        ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
          (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
          (Antitone D.parameters.neckRadius → Antitone ρ) ∧
          (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
          (HasRecenterConstants.{u} D.parameters →
            HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
          D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
          q' < (2 * C2) * ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ∧
          ((D.parameters.delta D.endTime * ρ D.endTime)^2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / (2 * C2)) ∧
          let D' := D.withNeckRadius ρ hρ
          let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
          ∀ y : D'.slab.terminalRegularOpen, metricScalarAt D'.terminal.metric y ≤ A →
            ¬ IsCompact (connectedComponent y) →
            let U := connectedComponentOpen (I := I3) y
            ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι)
              (v : ι → U) (neck : ∀ i, SpatialNeck (D'.terminal.metric.restrictOpen U) δ (v i))
              (level : ι → ℝ) (W : Set U),
              IsCompact W ∧ closure (interior W) = W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤ (2 * C2) * A} ⊆
                interior W ∧
              {x : U | metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤
                ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹} ⊆ interior W ∧
              (∀ x ∈ W, metricScalarAt (D'.terminal.metric.restrictOpen U) x ≤
                (8 * C2 ^ 2 * (2 * C2)) * A) ∧
              Pairwise (fun i j => Disjoint
                (range (fun z : Sphere 2 => (neck i).map (z, level i)))
                (range (fun z : Sphere 2 => (neck j).map (z, level j)))) ∧
              frontier W = ⋃ i, range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
              (∀ i, |level i| ≤ 3) ∧
              (∀ i, ∃ r σ : ℝ, 0 < r ∧ r ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r, (z, level i + σ * t) ∈ (neck i).map.source) ∧
                (∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ W ↔ t ≤ 0) ∧
                ∀ z, ∀ t ∈ Ioo (-r) r,
                  (neck i).map (z, level i + σ * t) ∈ interior W ↔ t < 0) ∧
              (∀ x ∈ frontier W,
                2 * ((2 * C2) * A) < metricScalarAt (D'.terminal.metric.restrictOpen U) x) ∧
              ∀ V : Set U, W ⊆ V → ∀ x : U, x ∉ interior V →
                (2 * C2) * A < metricScalarAt (D'.terminal.metric.restrictOpen U) x ∧
                ∀ (p : U) (nk : SpatialNeck (D'.terminal.metric.restrictOpen U) δ p)
                  (z : Sphere 2) (level : ℝ), |level| ≤ 4 → nk.map (z, level) = x →
                  Nonempty (SpatialNeck (D'.terminal.metric.restrictOpen U) δ x) ∨
                  ∃ K : CompactDomain U,
                    Nonempty (CapCore K.carrier) ∧
                    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
                    (∀ w ∈ K.carrier, A < metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) x / (2 * C2) <
                        metricScalarAt (D'.terminal.metric.restrictOpen U) w ∧
                      metricScalarAt (D'.terminal.metric.restrictOpen U) w <
                        (2 * C2) * metricScalarAt (D'.terminal.metric.restrictOpen U) x) := by
  obtain ⟨η, hη, hmain⟩ :=
    IncomingSlab.exists_uniform_component_spherical_region_of_spatiallyCanonical.{u}
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη C1 C2 q hC2 hq D hcanonical q' hqq'
  let C := 2 * C2
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hd : 0 < D.parameters.delta D.endTime := D.parameters.delta_pos _ hs
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hprotect, hscale, hscaleBound⟩ :=
    D.parameters.exists_neckRadius_le_protected_cutoff_scale_gt_with_bound hs hCpos q'
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn,
    (fun h => h.withNeckRadius hρ), hprotect, hscale, hscaleBound, ?_⟩
  let D' := D.withNeckRadius ρ hρ
  let A := ((D'.parameters.delta D'.endTime * D'.parameters.neckRadius D'.endTime) ^ 2)⁻¹
  have hprod : 0 < D.parameters.delta D.endTime * ρ D.endTime := mul_pos hd (hρ _ hs)
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hprod)
  have hAle : A ≤ C * A := by nlinarith
  have hprotected : ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹ ≤ A := by
    apply inv_anti₀ (sq_pos_of_pos hprod)
    nlinarith
  dsimp only
  intro y hy hnoncompact
  obtain ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow, hupper,
    hdisjoint, hfront, hlevel, hcollar, hfrontscalar, hexterior⟩ :=
    hmain δ hδη C1 C2 q hq D.stage D.startTime D.endTime D.slab D.terminal
      hcanonical A (C * A) y (hqq'.trans_lt hscale) le_rfl (hy.trans hAle) hnoncompact
  refine ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow,
    (fun x hx => hlow (hx.trans (hprotected.trans hAle))), ?_,
    hdisjoint, hfront, hlevel, hcollar, hfrontscalar, hexterior⟩
  intro x hx
  exact (hupper x hx).trans_eq (by change 8 * C2^2 * (C * A) = 8 * C2^2 * C * A; ring)

theorem exists_neckRadius_terminalCorePresentation_with_base_necks_of_spatiallyCanonical
    {ε : ℝ} (hε : 0 < ε) :
    ∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧ 104000 * εcan ≤ ε ∧
      ∀ C1 C2 : ℝ, 1 ≤ C2 →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ q : ℝ, 0 < q →
      ∀ D : OneStepIncoming.{u},
        D.slab.SpatiallyCanonicalBefore εcan C1 C2 q D.endTime →
        ∀ q' : ℝ, q ≤ q' →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          q' < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / C) ∧
          (∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
          ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
            (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
            |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
            ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
  classical
  obtain ⟨η₁, hη₁, hcutoff⟩ :=
    exists_neckRadius_spherical_region_with_scale_bound_of_spatiallyCanonical.{u}
  obtain ⟨η₂, hη₂, hends⟩ := exists_smooth_saved_end_decomposition_on_noncompact_component.{u,u}
  let δ := min η₁ (min η₂ (min (ε / 26000) (1 / 156000)))
  have hδ : 0 < δ := lt_min hη₁ (lt_min hη₂ (lt_min (by positivity) (by norm_num)))
  have hδ₁ : δ ≤ η₁ := min_le_left _ _
  have hδ₂ : δ ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : 26000 * δ ≤ ε := by
    have hh : δ ≤ ε / 26000 := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hδsmall : δ ≤ 1 / 156000 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ / 4, by positivity, by linarith, by linarith, ?_⟩
  intro C1 C2 hC2
  let C := 2 * C2
  let Λ := 8 * C2 ^ 2 * C
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hΛ : 1 ≤ Λ := by
    dsimp [Λ]
    have hsq : 1 ≤ C2 ^ 2 := by nlinarith
    have hp := mul_le_mul hsq hC (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg C2)
    nlinarith
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro q hq D hcanonical q' hqq'
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, hscale, hscaleBound, hregions⟩ :=
    hcutoff δ hδ hδ₁ C1 C2 q hC2 hq D hcanonical q' hqq'
  let D' := D.withNeckRadius ρ hρ
  let r := D.parameters.delta D.endTime * ρ D.endTime
  let A := (r ^ 2)⁻¹
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hr : 0 < r := mul_pos (D.parameters.delta_pos _ hs) (hρ _ hs)
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hr)
  have hproducer (c : ConnectedComponents D'.slab.terminalRegularOpen)
      (hc : ∃ y : D'.slab.terminalRegularOpen, ConnectedComponents.mk y = c ∧
        metricScalarAt D'.terminal.metric y ≤ A) :
      Nonempty (ComponentEndPresentation D'.terminal.metric
        {x | ConnectedComponents.mk x = c} A (Λ * A) ε) := by
    obtain ⟨y, hyc, hyA⟩ := hc
    let U := connectedComponentOpen (I := ThreeModel) y
    have hUeq : (U : Set D'.slab.terminalRegularOpen) = {x | ConnectedComponents.mk x = c} := by
      ext x
      exact ⟨fun hx => (ConnectedComponents.coe_eq_coe'.mpr hx).trans hyc,
        fun hx => ConnectedComponents.coe_eq_coe'.mp (hx.trans hyc.symm)⟩
    have hUclosed : IsClosed (U : Set D'.slab.terminalRegularOpen) := isClosed_connectedComponent
    by_cases hcompact : IsCompact (connectedComponent y)
    · have hcompact' : IsCompact {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ hcompact
      have hopen : IsOpen {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ U.isOpen
      have hclosed : IsClosed {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ hUclosed
      exact ⟨compactComponentPresentation D'.terminal.metric _ A (Λ * A) ε
        hopen hclosed hcompact' (fun _ => hUeq ▸ isConnected_connectedComponent)⟩
    · obtain ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow, hprotected,
        hupper, hpair, hfront, hlevel, _, _, hexterior⟩ := hregions y hyA hcompact
      let _ := hi
      let _ := hne
      obtain ⟨K, m, origin, Θ, charts, collar, _, hK, hconn, _, _, _, _, hzero,
        hlowK, _, hendsK, hdisjoint, hfrontK, hcover, hcharts, hcollar⟩ :=
        hends D' δ ε A C Λ hδ₂ hδε hA.le hC y hyA hcompact ι v neck level W hW hreg
          hlow hprotected hupper (fun i => (hlevel i).trans (by norm_num)) hpair hfront hexterior
      have hbase : ∀ i, ∃ (p : U) (N : SpatialNeck (D'.terminal.metric.restrictOpen U)
          (1 / 156000) p) (level : ℝ), |level| ≤ 3 ∧ ∀ z, Θ i (z, 0) = N.map (z, level) := by
        intro i
        exact ⟨v (origin i), (neck (origin i)).mono hδsmall (by norm_num),
          level (origin i), hlevel (origin i), hzero i⟩
      let Q := componentPresentationOfHalfCylinders K m Θ charts collar hK hconn
        hlowK hendsK hbase hdisjoint hfrontK hcover hcharts hcollar
      exact ⟨hUeq ▸ ComponentEndPresentation.toAmbient hUclosed Q⟩
  let assembled := assembleTerminalCorePresentation D' hε hΛ hr rfl hproducer
  let P := assembled.val
  have hbase : ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
      (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
      |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
      ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
    intro c e
    obtain ⟨p, N, level, hlevel, hmap⟩ := assembled.property c e
    refine ⟨p, N, level, hlevel, ?_, hmap⟩
    have hwindow : (N.center, level) ∈
        univ ×ˢ Ioo (-((1 / 156000 : ℝ)⁻¹)) ((1 / 156000 : ℝ)⁻¹) := by
      refine ⟨mem_univ _, abs_lt.mp ?_⟩
      exact hlevel.trans_lt (by norm_num)
    have hlo := (N.scalar_bounds_on_image_window ⟨(N.center, level), hwindow, rfl⟩).1
    have hupper := P.horn_base_scalar c e N.center
    rw [hmap] at hupper
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 4323 * (1 / 156000) := by norm_num
    have hscale := mul_le_mul_of_nonneg_right hhalf N.Q_pos.le
    change metricScalarAt D'.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹
    nlinarith
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, P.coreRadius_eq, ?_, ?_, ?_, hbase⟩
  · rw [P.coreRadius_eq]
    exact hscale
  · rw [P.coreRadius_eq]
    exact hscaleBound
  · intro x hx
    have hprotectA : ((D.parameters.protectedRadius D.endTime)^2)⁻¹ ≤ A := by
      apply inv_anti₀ (sq_pos_of_pos hr)
      have hp := D.parameters.protectedRadius_pos D.endTime hs
      change r ≤ D.parameters.protectedRadius D.endTime at hprotect
      nlinarith
    have hxA : metricScalarAt D'.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹ := by
      rw [P.coreRadius_eq]
      exact hx.trans hprotectA
    have hc := (P.component_iff_meets_low (ConnectedComponents.mk x)).mpr ⟨x, rfl, hxA⟩
    exact ⟨ConnectedComponents.mk x, hc,
      P.low_mem_interior_core _ hc x rfl hxA⟩

theorem exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_spatiallyCanonical
    {ε : ℝ} (hε : 0 < ε) :
    ∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧ 104000 * εcan ≤ ε ∧
      ∀ C1 C2 : ℝ, 1 ≤ C2 →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
      ∀ q originalCoreFloor protectedFloor : ℝ,
        0 < q → 0 < originalCoreFloor → 0 < protectedFloor →
      ∃ radiusFloor : ℝ, 0 < radiusFloor ∧
      ∀ D : OneStepIncoming.{u},
        originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
        protectedFloor ≤ D.parameters.protectedRadius D.endTime →
        D.slab.SpatiallyCanonicalBefore εcan C1 C2 q D.endTime →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          radiusFloor ≤ P.coreRadius ∧ radiusFloor ≤ ρ D.endTime ∧
          q < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q 0 + 1) / C) ∧
          (∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
          ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
            (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
            |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
            ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
  obtain ⟨εcan, hεcan, hεsmall, hεP, hproduce⟩ :=
    exists_neckRadius_terminalCorePresentation_with_base_necks_of_spatiallyCanonical.{u} hε
  refine ⟨εcan, hεcan, hεsmall, hεP, ?_⟩
  intro C1 C2 hC2
  obtain ⟨C, Λ, hC, hΛ, hproduce⟩ := hproduce C1 C2 hC2
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro q originalCoreFloor protectedFloor hq hcoreFloor hprotectedFloor
  let M := max (max (originalCoreFloor ^ 2)⁻¹ (protectedFloor ^ 2)⁻¹)
    (4 * (max q 0 + 1) / C)
  have hM : 0 < M :=
    (inv_pos.mpr (sq_pos_of_pos hcoreFloor)).trans_le
      ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨Real.sqrt M⁻¹, Real.sqrt_pos.mpr (inv_pos.mpr hM), ?_⟩
  intro D hcore hprotected hcanonical
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hscale, hupper, hlow, hbase⟩ := hproduce q hq D hcanonical q le_rfl
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hcoreInv : ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ ≤
      (originalCoreFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hcoreFloor) (by nlinarith)
  have hprotectedInv : (D.parameters.protectedRadius D.endTime ^ 2)⁻¹ ≤
      (protectedFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hprotectedFloor) (by nlinarith)
  have hupperM : (P.coreRadius ^ 2)⁻¹ ≤ M :=
    hupper.trans (max_le_max (max_le_max hcoreInv hprotectedInv) le_rfl)
  have hroot : Real.sqrt M⁻¹ ≤ P.coreRadius := by
    have hinv : M⁻¹ ≤ P.coreRadius ^ 2 := by
      simpa only [inv_inv] using
        inv_anti₀ (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos)) hupperM
    calc
      Real.sqrt M⁻¹ ≤ Real.sqrt (P.coreRadius ^ 2) := Real.sqrt_le_sqrt hinv
      _ = P.coreRadius := Real.sqrt_sq P.coreRadius_pos.le
  have hneck : P.coreRadius ≤ ρ D.endTime := by
    have hd := D.parameters.delta_lt_one D.endTime hs
    have hn := hρ D.endTime hs
    nlinarith [hradius]
  exact ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hroot, hroot.trans hneck, hscale, hupper, hlow, hbase⟩

end OneStepIncoming

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
