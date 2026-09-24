import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison
import DifferentialGeometry.Analysis.Estimates.UniformScaling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem exists_compact_neighborhood_comparison_supports
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      ∀ c (x : (G.Parent c).Carrier) (hx : x ∈ (Kc c).support.region),
        (⟨x.1, (Kc c).support_terminal x hx⟩ :
          (H.event i).incoming.terminalRegularOpen) ∈ interior K := by
  let : SecondCountableTopology (H.stage i.castSucc).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage i.castSucc).Carrier
  let : LocallyCompactSpace (H.event i).incoming.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace (H.event i).incoming.terminalRegularOpen
  let : LocallyConnectedSpace (H.stage i.succ).Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace (H.stage i.succ).Carrier
  let S : ConnectedComponents (H.stage i.succ).Carrier →
      Set (H.event i).incoming.terminalRegularOpen := fun c =>
    (fun x : (Kc c).support.region =>
      (⟨x.1.1, (Kc c).support_terminal x.1 x.2⟩ :
        (H.event i).incoming.terminalRegularOpen)) '' univ
  have hcompact : ∀ c, IsCompact (S c) := by
    intro c
    let : CompactSpace (Kc c).support.region :=
      isCompact_iff_compactSpace.mp (Kc c).support.compact
    let f : (Kc c).support.region → (H.event i).incoming.terminalRegularOpen :=
      fun x => ⟨x.1.1, (Kc c).support_terminal x.1 x.2⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    exact isCompact_univ.image hf
  obtain ⟨K, hK, hSK, _⟩ := exists_compact_between (isCompact_iUnion hcompact)
    isOpen_univ (subset_univ _)
  refine ⟨K, hK, ?_⟩
  intro c x hx
  exact hSK (mem_iUnion.mpr ⟨c, ⟨⟨x, hx⟩, mem_univ _, rfl⟩⟩)

theorem exists_comparison_support_neighborhood_quad_bound
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ c (x : (G.Parent c).Carrier), x ∈ (Kc c).support.region →
        ∃ U ∈ 𝓝 x,
          (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
          ∀ t ∈ Ioo d (H.time i.succ), ∀ y ∈ U,
            ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
            ∀ v : TangentSpace ThreeModel
                (⟨y.1, hy⟩ : (H.event i).incoming.terminalRegularOpen),
              (H.event i).terminal.metric.inner ⟨y.1, hy⟩ v v ≤ (1 + ε) *
                (((H.event i).incoming.flow.base.metric t).restrictOpen
                  (H.event i).incoming.terminalRegularOpen).inner ⟨y.1, hy⟩ v v := by
  obtain ⟨K, hK, hsupport⟩ := G.exists_compact_neighborhood_comparison_supports Kc
  obtain ⟨d, hd, hbound⟩ := (H.event i).terminal.exists_compact_quad_bound hK hε
  refine ⟨d, hd, ?_⟩
  intro c x hx
  let U : Set (G.Parent c).Carrier :=
    Subtype.val ⁻¹' (Subtype.val '' interior K)
  have hU : IsOpen U :=
    ((H.event i).incoming.terminalRegularRegion_isOpen.isOpenMap_subtype_val
      (interior K) isOpen_interior).preimage continuous_subtype_val
  have hxU : x ∈ U := ⟨⟨x.1, (Kc c).support_terminal x hx⟩, hsupport c x hx, rfl⟩
  refine ⟨U, hU.mem_nhds hxU, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, _, hz⟩ := hy
    exact hz ▸ z.2
  · intro t ht y hy hy' v
    obtain ⟨z, hzK, hz⟩ := hy
    have hyK : (⟨y.1, hy'⟩ : (H.event i).incoming.terminalRegularOpen) ∈ K := by
      have hyz : (⟨y.1, hy'⟩ : (H.event i).incoming.terminalRegularOpen) = z :=
        Subtype.ext hz.symm
      exact hyz ▸ interior_subset hzK
    exact hbound t ht ⟨y.1, hy'⟩ hyK v

theorem exists_compact_comparison_support_quad_modulus
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      (∀ c (x : (G.Parent c).Carrier) (hx : x ∈ (Kc c).support.region),
        (⟨x.1, (Kc c).support_terminal x hx⟩ :
          (H.event i).incoming.terminalRegularOpen) ∈ interior K) ∧
      ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ t ∈ Ioo d (H.time i.succ), 1 ≤ ell t) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ t ∈ Ioo d (H.time i.succ), ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
          (H.event i).terminal.metric.inner x v v ≤ (ell t) ^ 2 *
            (((H.event i).incoming.flow.base.metric t).restrictOpen
              (H.event i).incoming.terminalRegularOpen).inner x v v := by
  obtain ⟨K, hK, hsupport⟩ := G.exists_compact_neighborhood_comparison_supports Kc
  obtain ⟨d, hd, ell, hell, htend, hbound⟩ :=
    DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound
      (α := Σ x : K, TangentSpace ThreeModel x.1)
      (P := fun _ a => (H.event i).terminal.metric.inner a.1.1 a.2 a.2)
      (Q := fun t a => (((H.event i).incoming.flow.base.metric t).restrictOpen
        (H.event i).incoming.terminalRegularOpen).inner a.1.1 a.2 a.2)
      (s₀ := H.time i.castSucc) (T := H.time i.succ)
      (fun t a => DifferentialGeometry.metric_inner_self_nonneg _ a.1.1 a.2)
      (fun ε hε => by
        obtain ⟨d, hd, hbound⟩ := (H.event i).terminal.exists_compact_relative_quad_bound hK hε
        refine ⟨(d + H.time i.succ) / 2, ⟨?_, ?_⟩, ?_⟩
        · linarith [hd.1, hd.2]
        · linarith [hd.2]
        · intro t ht a
          rw [abs_sub_comm]
          exact hbound t ⟨by linarith [hd.2, ht.1], ht.2⟩ a.1.1 a.1.2 a.2)
  exact ⟨K, hK, hsupport, d, ⟨hd.1.le, hd.2⟩, ell, hell, htend,
    fun t ht x hx v => hbound t ht ⟨⟨x, hx⟩, v⟩⟩

theorem exists_comparison_support_neighborhood_quad_modulus
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ t ∈ Ioo d (H.time i.succ), 1 ≤ ell t) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c (x : (G.Parent c).Carrier), x ∈ (Kc c).support.region →
        ∃ U ∈ 𝓝 x,
          (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
          ∀ t ∈ Ioo d (H.time i.succ), ∀ y ∈ U,
            ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
            ∀ v : TangentSpace ThreeModel
                (⟨y.1, hy⟩ : (H.event i).incoming.terminalRegularOpen),
              (H.event i).terminal.metric.inner ⟨y.1, hy⟩ v v ≤ (ell t) ^ 2 *
                (((H.event i).incoming.flow.base.metric t).restrictOpen
                  (H.event i).incoming.terminalRegularOpen).inner ⟨y.1, hy⟩ v v := by
  obtain ⟨K, hK, hsupport, d, hd, ell, hell, htend, hbound⟩ :=
    G.exists_compact_comparison_support_quad_modulus Kc
  refine ⟨d, hd, ell, hell, htend, ?_⟩
  intro c x hx
  let U : Set (G.Parent c).Carrier :=
    Subtype.val ⁻¹' (Subtype.val '' interior K)
  have hU : IsOpen U :=
    ((H.event i).incoming.terminalRegularRegion_isOpen.isOpenMap_subtype_val
      (interior K) isOpen_interior).preimage continuous_subtype_val
  have hxU : x ∈ U := ⟨⟨x.1, (Kc c).support_terminal x hx⟩, hsupport c x hx, rfl⟩
  refine ⟨U, hU.mem_nhds hxU, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, _, hz⟩ := hy
    exact hz ▸ z.2
  · intro t ht y hy hy' v
    obtain ⟨z, hzK, hz⟩ := hy
    have hyK : (⟨y.1, hy'⟩ : (H.event i).incoming.terminalRegularOpen) ∈ K := by
      have hyz : (⟨y.1, hy'⟩ : (H.event i).incoming.terminalRegularOpen) = z :=
        Subtype.ext hz.symm
      exact hyz ▸ interior_subset hzK
    exact hbound t ht ⟨y.1, hy'⟩ hyK v

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
