import DifferentialGeometry.Topology.Connected.SublevelBarrierSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrierFamily

noncomputable section

open Set Filter
open Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u v
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.isCompact_closure_connectedComponentIn_of_finite_barrier_cover
    (L : G.TerminalLimitMetric) {ι : Type v} (s : Finset ι)
    (K : ι → CompactDomain G.terminalRegularOpen) {A T : ℝ} (hAT : A ≤ T)
    (y : G.terminalRegularOpen)
    (hhigh : ∀ i ∈ s, ∀ z ∈ (K i).carrier, A < metricScalarAt L.metric z)
    (hcover : {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z = T} ⊆
      ⋃ i ∈ s, interior (K i).carrier)
    {J : Type*} (sphere : J → Set G.terminalRegularOpen)
    (hfront : (⋃ i ∈ s, frontier (K i).carrier) = ⋃ j, sphere j)
    {x : G.terminalRegularOpen} (hx : x ∈ connectedComponent y) (hRx : metricScalarAt L.metric x ≤ A) :
    IsCompact (closure (connectedComponentIn (⋃ j, sphere j)ᶜ x)) ∧
      closure (connectedComponentIn (⋃ j, sphere j)ᶜ x) ⊆
        {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z < T} := by
  classical
  let U : {i // i ∈ s} → Set G.terminalRegularOpen := fun i => (K i.val).carrier
  have hfront' : (⋃ i, frontier (U i)) = ⋃ j, sphere j := by
    rw [← hfront]
    ext z
    simp only [mem_iUnion, U]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.property, hi⟩
    · rintro ⟨i, hi, hz⟩
      exact ⟨⟨i, hi⟩, hz⟩
  have hcover' : {z : G.terminalRegularOpen |
      z ∈ connectedComponent y ∧ metricScalarAt L.metric z = T} ⊆ ⋃ i, interior (U i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  have hsub := DifferentialGeometry.Topology.closure_connectedComponentIn_compl_frontiers_subset_lt
    (metricScalarAt L.metric) (metricScalar_smooth L.metric).continuous hAT U
    (fun i => (K i.val).compact.isClosed) (fun i z hz => hhigh i.val i.property z hz) hcover' hx hRx
  rw [hfront'] at hsub
  refine ⟨(L.isCompact_scalar_sublevel T).of_isClosed_subset isClosed_closure
    (fun z hz => (hsub hz).2.le), hsub⟩

theorem TerminalLimitMetric.exists_finite_recorded_spherical_barriers_with_compact_component_closures_of_canonical
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
            {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z < 4 * C2 * A} := by
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
    L.exists_finite_recorded_spherical_barriers_of_canonical hδsmall hcanonical
      A y hA hqA hyA hnoncompact
  refine ⟨s, K, hs, hcover, hK, v, neck, level, sign, collar, hfront, hunion,
    hgeometry, hcollar, hcompact, hlow, ?_⟩
  intro x hx hRx
  exact L.isCompact_closure_connectedComponentIn_of_finite_barrier_cover s K
    (by nlinarith : A ≤ 4 * C2 * A) y
    (fun i hi z hz => lt_trans (by linarith : A < 2 * A) ((hK i hi).2.2 z hz).1)
    hcover (fun i : {p // p ∈ s} × Fin 2 =>
      range (fun z : Sphere 2 => (neck i.1).map (z, level i))) hunion hx hRx

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_finite_recorded_spherical_barriers_with_compact_component_closures
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
                {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z < 4 * C2 * A} := by
  obtain ⟨C2, hC2, hcoverage⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      (by positivity : 0 < δ / 4) (by linarith : δ / 4 < 1 / 11)
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hcoverage P a s G
  refine ⟨q, hq, ?_⟩
  intro L A y hA hqA hyA hnoncompact
  exact L.exists_finite_recorded_spherical_barriers_with_compact_component_closures_of_canonical hδsmall
    (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)
    A y hA hqA hyA hnoncompact

theorem TerminalLimitMetric.exists_finite_recorded_spherical_barriers_with_compact_component_closures
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
                {z : G.terminalRegularOpen | z ∈ connectedComponent y ∧ metricScalarAt L.metric z < 4 * C2 * A} := by
  obtain ⟨C2, hC2, hmain⟩ :=
    exists_uniform_finite_recorded_spherical_barriers_with_compact_component_closures.{u} hδ hδsmall
  obtain ⟨q, hq, hfamily⟩ := hmain P a s G
  exact ⟨C2, q, hC2, hq, hfamily L⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
