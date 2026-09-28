import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapSideExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSpatialCanonicalAlternatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Neck.SpatialNormalization
import DifferentialGeometry.Topology.Connected.InteriorCollar

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem eventually_neck_alternative_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
      (x : D.slab.terminalRegularOpen), x ∈ P.hornHalfRange c e →
    ∀ {epsCan eps C1 C2 : ℝ}, 0 < eps → eps ≤ eta →
      4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt D.terminal.metric x →
      ∀ᶠ t in 𝓝[<] D.endTime,
        ∀ W : SpatialCanonicalWitness (D.slab.flow.base.metric t) epsCan C1 C2 x.val,
          W.capTubeHasNeckChart eps →
            ∃ neck : SpatialLocalNeck (D.slab.flow.base.metric t) epsCan x.val W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck := by
  obtain ⟨eta₁, heta₁, hT1⟩ := false_of_terminal_capSide.{u}
  set α : ℝ := min (eta₁ / 2) (1 / 20) with hαdef
  have hα : 0 < α := lt_min (by linarith) (by norm_num)
  have hα11 : α < 1 / 11 := (min_le_right _ _).trans_lt (by norm_num)
  have hα2 : 2 * α ≤ eta₁ := by
    have := min_le_left (eta₁ / 2) (1 / 20)
    linarith
  set δ : ℝ := α / 13000 with hδdef
  have hδ : 0 < δ := by positivity
  have hδsmall : δ < 1 / 20000 := by
    rw [hδdef]
    linarith
  have h13 : 13000 * δ ≤ α := by
    rw [hδdef]
    linarith
  refine ⟨min eta₁ (δ / 2), lt_min heta₁ (half_pos hδ), ?_⟩
  intro D ε Λ P hε c e x hx epsCan eps C1 C2 heps hepsη hscalar
  have hεT : ε ≤ eta₁ := hε.trans (min_le_left _ _)
  have hepsδ2 : eps ≤ δ / 2 := hepsη.trans (min_le_right _ _)
  have hepsδ : eps < δ := by linarith
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by
    have h1 : (δ / 2)⁻¹ ≤ eps⁻¹ := inv_anti₀ heps hepsδ2
    have h2 : (δ / 2)⁻¹ = 2 * δ⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have h3 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
    linarith
  have hc : c ∈ P.component := by
    by_contra hnot
    exact (P.hornIndex_empty c hnot).false e
  set ℓ := Λ * (P.coreRadius ^ 2)⁻¹ with hℓdef
  have hℓ : 0 < ℓ := by
    have := P.Lambda_ge_one
    have := P.coreRadius_pos
    positivity
  obtain ⟨⟨⟨y₀, u₀⟩, hu₀⟩, hpx⟩ := hx
  change P.horn c e (y₀, u₀) = x at hpx
  change (0 : ℝ) ≤ u₀ at hu₀
  have hRx : 0 < metricScalarAt D.terminal.metric x := by
    have h := P.horn_scalar_large c e y₀ u₀ hu₀
    rw [hpx] at h
    have : (0 : ℝ) < (P.coreRadius ^ 2)⁻¹ := by
      have := P.coreRadius_pos
      positivity
    linarith
  have hmk : ∀ q : HalfNeckCylinder, ConnectedComponents.mk (P.horn c e q.1) = c := by
    intro q
    have h : P.horn c e q.1 ∈ P.core c ∪
        ⋃ e, range (fun p : HalfNeckCylinder => P.horn c e p.1) :=
      Or.inr (mem_iUnion.mpr ⟨e, q, rfl⟩)
    rw [← P.horn_covers_component c hc] at h
    exact h
  have hmkx : ConnectedComponents.mk x = c := hpx ▸ hmk ⟨(y₀, u₀), hu₀⟩
  set b := P.horn c e (y₀, 0) with hbdef
  have hmkb : ConnectedComponents.mk b = c := hmk ⟨(y₀, 0), le_rfl⟩
  have hRb : metricScalarAt D.terminal.metric b ≤ ℓ := P.horn_base_scalar c e y₀
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨τ, hτ, hfreq⟩ := Filter.frequently_iff_seq_frequently.mp hnot
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  have hbad : ∀ n, ∃ W : SpatialCanonicalWitness (D.slab.flow.base.metric (τ (φ n))) epsCan C1 C2
      x.val, W.capTubeHasNeckChart eps ∧
        ∀ neck : SpatialLocalNeck (D.slab.flow.base.metric (τ (φ n))) epsCan x.val
          W.domain.carrier, W.alternative ≠ SpatialCanonicalAlternative.neck neck := by
    intro n
    have h := hφP n
    push Not at h
    exact h
  have hC2 : 1 ≤ C2 := (hbad 0).choose.one_le_comparison_constant
  have hbR : C2 * metricScalarAt D.terminal.metric b < metricScalarAt D.terminal.metric x := by
    have := mul_le_mul_of_nonneg_left hRb (zero_le_one.trans hC2)
    nlinarith
  have hbcomp : b.val ∈ connectedComponent x.val :=
    continuous_subtype_val.mapsTo_connectedComponent x
      (ConnectedComponents.coe_eq_coe'.mp (hmkb.trans hmkx.symm))
  have hτφ : Tendsto (fun n => τ (φ n)) atTop (𝓝[<] D.endTime) := hτ.comp hφ.tendsto_atTop
  have hnc := hτφ.eventually
    (D.terminal.eventually_spatial_neck_or_cap (eps := epsCan) (C1 := C1) x b hbcomp hbR)
  have hcapev : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (D.slab.flow.base.metric (τ (φ n)))
      epsCan C1 C2 x.val, W.capTubeHasNeckChart eps ∧
        ∃ cap : SpatialLocalCap (D.slab.flow.base.metric (τ (φ n))) epsCan x.val W.domain.carrier,
          ∃ depth, W.alternative = SpatialCanonicalAlternative.cap cap depth := by
    filter_upwards [hnc] with n hn
    obtain ⟨W, hW, hne⟩ := hbad n
    refine ⟨W, hW, (hn W).resolve_left ?_⟩
    rintro ⟨neck, hneck⟩
    exact hne neck hneck
  obtain ⟨ψ, hψ, hψP⟩ := extraction_of_eventually_atTop hcapev
  choose W hW cap depth hcap using hψP
  have hτψ : Tendsto (fun n => τ (φ (ψ n))) atTop (𝓝[<] D.endTime) :=
    hτφ.comp hψ.tendsto_atTop
  obtain ⟨n, v, nk, K, -, hxK, -, hKscalar, -, hfrK, -, -, -, col, -, hcol⟩ :=
    (D.terminal.eventually_spatial_cap_spherical_barrier hτψ x hRx hδ hδsmall hepsδ hfit
      W hW cap depth hcap).exists
  obtain ⟨out, -, houtmap⟩ := nk.exists_at_coordinate (a := 1 / 2) hα11 h13 nk.center
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num)
  obtain ⟨N, hNc, -, hNchart⟩ := out.exists_normalizedNeck_of_two_mul_le hα2
  have hNmap : ∀ z : neckBuffer (2 * α), N.chart z = nk.map (z.val.1, 1 / 2 + z.val.2) :=
    fun z => (hNchart z).trans (nk.translated_map_apply nk.center out houtmap z.val.1 z.val.2)
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hcQ : 2 * ℓ < metricScalarAt D.terminal.metric x / (2 * C2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hKhigh : ∀ w ∈ K.carrier, 2 * ℓ < metricScalarAt D.terminal.metric w :=
    fun w hw => hcQ.trans (hKscalar w hw).1
  have hxcore : x ∉ P.core c := by
    rcases hu₀.lt_or_eq with hpos | hzero
    · rw [← hpx]
      exact P.horn_pos_notMem_core c e y₀ hpos
    · have h := P.horn_base_scalar c e y₀
      rw [hzero, hpx] at h
      nlinarith
  have hcoreClosed : IsClosed (P.core c) := (P.core_isCompact c hc).isClosed
  have hKcore : K.carrier ⊆ (P.core c)ᶜ := by
    have hsub : K.carrier ⊆ (P.core c)ᶜ ∪ interior (P.core c) := by
      intro w hw
      by_cases hwc : w ∈ P.core c
      · right
        by_contra hwi
        have hwf : w ∈ frontier (P.core c) := by
          rw [hcoreClosed.frontier_eq]
          exact ⟨hwc, hwi⟩
        have := P.frontier_scalar_le c hc hwf
        linarith [hKhigh w hw]
      · exact Or.inl hwc
    exact K.connected.isPreconnected.subset_left_of_subset_union hcoreClosed.isOpen_compl
      isOpen_interior (disjoint_compl_left.mono_right interior_subset) hsub
      ⟨x, interior_subset hxK, hxcore⟩
  have hKcomp : ∀ w ∈ K.carrier, ConnectedComponents.mk w = c := fun w hw =>
    (ConnectedComponents.coe_eq_coe'.mpr
      (K.connected.isPreconnected.subset_connectedComponent (interior_subset hxK) hw)).trans hmkx
  obtain ⟨e', he'⟩ := P.exists_hornHalfRange_superset_of_isPreconnected hc
    K.connected.isPreconnected ⟨x, interior_subset hxK⟩ hKcomp hKcore
  have hee : e' = e := P.hornHalfRange_unique (he' (interior_subset hxK))
    ⟨⟨(y₀, u₀), hu₀⟩, hpx⟩
  subst hee
  have hKclosed : IsClosed K.carrier := K.compact.isClosed
  have hfrKsub : frontier K.carrier ⊆ K.carrier := hKclosed.frontier_subset
  have hNcenter : N.center ∈ P.hornHalfRange c e' := by
    rw [hNc]
    exact he' (hfrKsub (hfrK ▸ ⟨nk.center, rfl⟩))
  have hfrint : frontier (interior K.carrier) = N.chart '' {z | z.val.2 = 0} := by
    have h1 : frontier (interior K.carrier) = frontier K.carrier := by
      rw [frontier, interior_interior, K.regular_closed, hKclosed.frontier_eq]
    rw [h1, hfrK]
    have hN0 : (0 : ℝ) < (2 * α)⁻¹ := by positivity
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨⟨(q, 0), ?_⟩, rfl, ?_⟩
      · change -(2 * α)⁻¹ - 1 < 0 ∧ 0 < (2 * α)⁻¹ + 1
        constructor <;> linarith
      · rw [hNmap]
        norm_num
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.val.1, ?_⟩
      rw [hNmap]
      change z.val.2 = 0 at hz
      rw [hz, add_zero]
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  have hr := col.radius_pos
  let zero : DifferentialGeometry.Topology.symmetricOpenInterval col.radius :=
    ⟨0, neg_lt_zero.mpr hr, hr⟩
  have hcol0 : ∀ q : Sphere 2, col.toFun (q, zero) = nk.map (q, 1 / 2) := by
    intro q
    rw [(hcol (q, zero)).1]
    change nk.map (q, 1 / 2 + 0) = _
    rw [add_zero]
  have hinj := col.isOpenEmbedding_toFun.injective
  have hfrcol : ∀ q, col.toFun q ∈ frontier K.carrier → (q.2 : ℝ) = 0 := by
    intro q hq
    rw [hfrK] at hq
    obtain ⟨q', hq'⟩ := hq
    have := hinj ((hcol0 q').trans hq')
    rw [← this]
  set Cset := col.toFun '' {q | (q.2 : ℝ) < 0} with hCsetdef
  have hCpre : IsPreconnected Cset := by
    apply IsPreconnected.image _ _ col.isOpenEmbedding_toFun.continuous.continuousOn
    have hT : IsPreconnected
        {t : DifferentialGeometry.Topology.symmetricOpenInterval col.radius | (t : ℝ) < 0} := by
      have hind : Topology.IsInducing (Subtype.val :
          DifferentialGeometry.Topology.symmetricOpenInterval col.radius → ℝ) :=
        Topology.IsInducing.subtypeVal
      apply hind.isPreconnected_image.mp
      convert (isPreconnected_Ioo : IsPreconnected (Ioo (-col.radius) (0 : ℝ))) using 1
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.property.1, ht⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨r, h1, by linarith⟩, h2, rfl⟩
    have hprod := (isPreconnected_univ (α := Sphere 2)).prod hT
    convert hprod using 1
    ext q
    simp
  have hCK : Cset ⊆ interior K.carrier := by
    rintro _ ⟨q, hq, rfl⟩
    have hmem : col.toFun q ∈ K.carrier := (hcol q).2.mpr (le_of_lt hq)
    by_contra hint
    have hfr : col.toFun q ∈ frontier K.carrier := by
      rw [hKclosed.frontier_eq]
      exact ⟨hmem, hint⟩
    have := hfrcol q hfr
    change (q.2 : ℝ) < 0 at hq
    linarith
  have hloc : ∀ p ∈ frontier K.carrier, ∃ U : Set D.slab.terminalRegularOpen,
      IsOpen U ∧ p ∈ U ∧ U ∩ interior K.carrier ⊆ Cset := by
    intro p hp
    refine ⟨range col.toFun, col.isOpenEmbedding_toFun.isOpen_range, ?_, ?_⟩
    · have hp' := hp
      rw [hfrK] at hp'
      obtain ⟨q', rfl⟩ := hp'
      exact ⟨(q', zero), hcol0 q'⟩
    · rintro _ ⟨⟨q, rfl⟩, hqint⟩
      refine ⟨q, ?_, rfl⟩
      have hle := (hcol q).2.mp (interior_subset hqint)
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hq0 : q = (q.1, zero) := Prod.ext rfl (Subtype.ext heq)
        have hfr : col.toFun q ∈ frontier K.carrier := by
          rw [hq0, hcol0, hfrK]
          exact ⟨q.1, rfl⟩
        rw [hKclosed.frontier_eq] at hfr
        exact hfr.2 hqint
  have hconn : IsConnected (interior K.carrier) :=
    ⟨⟨x, hxK⟩, DifferentialGeometry.Topology.isPreconnected_interior_of_frontier_nhds
      K.connected.isPreconnected K.regular_closed hCpre hCK hloc⟩
  exact hT1 (P.monoEpsilon hεT) le_rfl c hc e' N hα2 le_rfl hNcenter (interior K.carrier)
    isOpen_interior hconn hfrint hcQ (U := 2 * C2 * metricScalarAt D.terminal.metric x)
    (fun z hz => by
      rw [K.regular_closed] at hz
      exact ⟨(hKscalar z hz).1.le, (hKscalar z hz).2.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
