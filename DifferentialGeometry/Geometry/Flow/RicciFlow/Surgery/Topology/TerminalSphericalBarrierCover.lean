import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_finite_spherical_barrier_cover_of_canonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q : ℝ}
    (hδsmall : δ < 1 / 20000)
    (hcanonical : ∀ (x : P.Carrier) (t : ℝ), t ∈ Ioo a s → q < G.flow.scalar t x →
      ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x t, W.capTubeHasNeckChart (δ / 4))
    (A : ℝ) (y : G.terminalRegularOpen) (hA : 0 < A) (hqA : q < 4 * C2 * A)
    (hyA : metricScalarAt L.metric y ≤ A) (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ (s : Finset {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
      (K : {z : G.terminalRegularOpen //
        z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
          CompactDomain G.terminalRegularOpen),
      s.Nonempty ∧
      {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
        ⋃ p ∈ s, interior (K p).carrier ∧
      (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
        (∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
          metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
        ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v),
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
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
    L.exists_spherical_barrier_at_level_of_canonical hδsmall hA hqA p.property.2
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

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_finite_spherical_barrier_cover
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
        ∃ (s : Finset {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
          (K : {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
              CompactDomain G.terminalRegularOpen),
          s.Nonempty ∧
          {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
            ⋃ p ∈ s, interior (K p).carrier ∧
          (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
            (∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
              metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
            ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v),
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
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
  obtain ⟨C2, hC2, hcoverage⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      (by positivity : 0 < δ / 4) (by linarith : δ / 4 < 1 / 11)
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hcoverage P a s G
  refine ⟨q, hq, ?_⟩
  intro L A y hA hqA hyA hnoncompact
  exact L.exists_finite_spherical_barrier_cover_of_canonical hδsmall
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)
    A y hA hqA hyA hnoncompact

theorem TerminalLimitMetric.exists_finite_spherical_barrier_cover
    (L : G.TerminalLimitMetric) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
      ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
        ∃ (s : Finset {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A})
          (K : {z : G.terminalRegularOpen //
            z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} →
              CompactDomain G.terminalRegularOpen),
          s.Nonempty ∧
          {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = 4 * C2 * A} ⊆
            ⋃ p ∈ s, interior (K p).carrier ∧
          (∀ p ∈ s, p.val ∈ interior (K p).carrier ∧ (K p).carrier ⊆ connectedComponent y ∧
            (∀ z ∈ (K p).carrier, 2 * A < metricScalarAt L.metric z ∧
              metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
            ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v),
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
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
  obtain ⟨C2, hC2, hmain⟩ := exists_uniform_finite_spherical_barrier_cover.{u} hδ hδsmall
  obtain ⟨q, hq, hcover⟩ := hmain P a s G
  exact ⟨C2, q, hC2, hq, hcover L⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
