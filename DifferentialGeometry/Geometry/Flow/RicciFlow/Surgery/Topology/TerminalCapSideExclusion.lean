import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationFrontierScalar

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem positiveHornMap_injective (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) : Function.Injective (P.positiveHornMap c e) := fun q q' h =>
  Subtype.ext (P.horn_injOn c e
    ⟨mem_univ _, le_of_lt (show (0 : ℝ) < q.val.2 from q.property.2)⟩
    ⟨mem_univ _, le_of_lt (show (0 : ℝ) < q'.val.2 from q'.property.2)⟩ h)

theorem false_of_frontier_eq_image_complementPair_sphere
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set positiveHornDomain} (p : ComplementPair S) (hS : S.Nonempty) {R : ℝ}
    (hlo : ∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left)
    (hhi : ∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ p.right)
    {W : Set D.slab.terminalRegularOpen} (hW : IsOpen W)
    (hfr : frontier W = P.positiveHornMap c e '' S) {cQ U : ℝ}
    (hcQ : Λ * (P.coreRadius ^ 2)⁻¹ < cQ)
    (hbd : ∀ z ∈ closure W, cQ ≤ metricScalarAt D.terminal.metric z ∧
      metricScalarAt D.terminal.metric z ≤ U) : False := by
  have hinj := P.positiveHornMap_injective c e
  have hcont : Continuous (P.positiveHornMap c e) :=
    (P.positiveHornMap_local c e).contMDiff.continuous
  have hWS : Disjoint W (P.positiveHornMap c e '' S) := by
    rw [← hfr, hW.frontier_eq]
    exact disjoint_sdiff_right
  have hclW : closure W ⊆ W ∪ P.positiveHornMap c e '' S := by
    rw [← hfr, hW.frontier_eq]
    exact fun w hw => (em (w ∈ W)).imp id fun h => ⟨hw, h⟩
  have hside : ∀ A : Set positiveHornDomain, IsPreconnected A → Disjoint A S →
      P.positiveHornMap c e '' A ⊆ W ∨ P.positiveHornMap c e '' A ⊆ (closure W)ᶜ := by
    intro A hA hAS
    refine (hA.image _ hcont.continuousOn).subset_or_subset hW isClosed_closure.isOpen_compl
      ((disjoint_compl_right (a := closure W)).mono_left subset_closure) ?_
    rintro _ ⟨q, hq, rfl⟩
    by_cases hcl : P.positiveHornMap c e q ∈ closure W
    · rcases hclW hcl with h | ⟨q', hq', he⟩
      · exact Or.inl h
      · exact absurd (hinj he ▸ hq') (disjoint_left.mp hAS hq)
    · exact Or.inr hcl
  obtain ⟨q0, hq0⟩ := hS
  have hq0W : P.positiveHornMap c e q0 ∈ closure W :=
    frontier_subset_closure (hfr ▸ mem_image_of_mem _ hq0)
  rcases hside p.right p.isConnected_right.isPreconnected p.right_disjoint_sphere with hR | hR
  · obtain ⟨uL, huL⟩ := P.horn_scalar_diverges c e U
    have hmax := le_max_right uL (Real.exp R)
    have hu : 0 < max uL (Real.exp R) + 1 := by linarith [Real.exp_pos R]
    let q : positiveHornDomain := ⟨(q0.val.1, max uL (Real.exp R) + 1), mem_univ _, hu⟩
    have hqR : q ∈ p.right := hhi q (by change Real.exp R < max uL (Real.exp R) + 1; linarith)
    have h1 := (hbd _ (subset_closure (hR ⟨q, hqR, rfl⟩))).2
    exact (not_le.mpr (huL q0.val.1 _ (by linarith [le_max_left uL (Real.exp R)]))) h1
  · have hopen : IsOpen (range (P.positiveHornMap c e)) :=
      (P.positiveHornMap_local c e).isOpenMap.isOpen_range
    obtain ⟨_, ⟨q, rfl⟩, hwW⟩ := mem_closure_iff.mp hq0W _ hopen ⟨q0, rfl⟩
    have hqS : q ∈ p.left ∪ p.right := by
      rw [p.union_eq_compl]
      exact fun h => disjoint_left.mp hWS hwW ⟨q, h, rfl⟩
    have hql : q ∈ p.left := hqS.resolve_right fun h => hR ⟨q, h, rfl⟩ (subset_closure hwW)
    rcases hside p.left p.isConnected_left.isPreconnected p.left_disjoint_sphere with hL | hL
    swap
    · exact hL ⟨q, hql, rfl⟩ (subset_closure hwW)
    set y := q0.val.1
    have hfc : ContinuousOn (fun u : ℝ => P.horn c e (y, u)) (Ici 0) :=
      (P.horn_smooth c e).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        fun u hu => ⟨mem_univ _, hu⟩
    have hε0 := Real.exp_pos (-R)
    have h0 : (0 : ℝ) ∈ closure (Ioo 0 (Real.exp (-R))) := by
      rw [closure_Ioo hε0.ne]
      exact left_mem_Icc.mpr hε0.le
    have hcw : ContinuousWithinAt (fun u : ℝ => P.horn c e (y, u)) (Ioo 0 (Real.exp (-R))) 0 :=
      (hfc 0 (mem_Ici.mpr le_rfl)).mono fun u hu => le_of_lt hu.1
    have himg : (fun u : ℝ => P.horn c e (y, u)) '' Ioo 0 (Real.exp (-R)) ⊆ W := by
      rintro _ ⟨u, hu, rfl⟩
      exact hL ⟨⟨(y, u), mem_univ _, hu.1⟩, hlo _ hu.2, rfl⟩
    have hbase : P.horn c e (y, 0) ∈ closure W := closure_mono himg (hcw.mem_closure_image h0)
    have h1 := (hbd _ hbase).1
    have h2 := P.horn_base_scalar c e y
    linarith

theorem false_of_terminal_capSide :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
    ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
      δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ P.hornHalfRange c e →
    ∀ (W : Set D.slab.terminalRegularOpen) {cQ U : ℝ}, IsOpen W → IsConnected W →
      frontier W = N.chart '' {z | z.val.2 = 0} →
      2 * (Λ * (P.coreRadius ^ 2)⁻¹) < cQ →
      (∀ z ∈ closure W, cQ ≤ metricScalarAt D.terminal.metric z ∧
        metricScalarAt D.terminal.metric z ≤ U) →
      False := by
  obtain ⟨eta, heta, hsep⟩ := exists_horn_neck_end_separation_tolerance.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro D ε Λ P hε c hc e δ k N hδ hk hcenter W cQ U hWo _ hfrW hcQ hbd
  have hεsmall : ε ≤ 1 / 8646 := hε.trans (min_le_right _ _)
  have hεpos : 0 < ε := N.delta_pos.trans_le hδ
  have hlarge : (1 : ℝ) ≤ ε⁻¹ := (le_inv_comm₀ (by norm_num) hεpos).mpr (by linarith)
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hlarge)
  have hk2 : 2 ≤ k := by omega
  have hδs : δ ≤ 1 / 8646 := hδ.trans hεsmall
  have hℓ : 0 < Λ * (P.coreRadius ^ 2)⁻¹ := by
    have := P.Lambda_ge_one
    have := P.coreRadius_pos
    positivity
  let z0 : neckBuffer δ := ⟨(N.sphereMark, 0), by
    change -δ⁻¹ - 1 < 0 ∧ 0 < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr N.delta_pos]⟩
  have hmark : N.chart z0 = N.center := N.marked
  have hz0 : N.chart z0 ∈ frontier W := hfrW ▸ ⟨z0, rfl, rfl⟩
  have hcW : N.center ∈ closure W := hmark ▸ frontier_subset_closure hz0
  have hscale : cQ ≤ N.scale := by
    rw [N.scale_scalar]
    exact (hbd _ hcW).1
  have hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale := by
    intro w hw
    have h1 := P.frontier_scalar_le c hc hw
    have hhalf : (1 / 2 : ℝ) * N.scale ≤ (1 - 4323 * δ) * N.scale :=
      mul_le_mul_of_nonneg_right (by linarith) N.scale_pos.le
    linarith
  obtain ⟨Θ, hΘ, hmap⟩ := P.exists_neck_coordinates_in_horn_of_frontier_scalar_lt c hc e N hk2
    (hδs.trans (by norm_num)) hcenter hfront
  obtain ⟨p, R, -, -, -, -, -, -, -, hlo, hhi, -⟩ := hsep P (hε.trans (min_le_left _ _))
    c e N hδ ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk) Θ hΘ hmap
  have hSig : N.chart '' {z | z.val.2 = 0} = P.positiveHornMap c e '' range (fun q : Sphere 2 =>
      Θ ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
        inv_pos.mpr N.delta_pos⟩) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨z.val.1, rfl⟩, ?_⟩
      change P.horn c e (Θ _).val = _
      rw [hmap]
      congr 1
      exact Subtype.ext (Prod.ext rfl (Eq.symm hz))
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨_, rfl, (hmap _).symm⟩
  exact P.false_of_frontier_eq_image_complementPair_sphere c e p ⟨_, ⟨N.sphereMark, rfl⟩⟩ hlo
    hhi hWo (hfrW.trans hSig) (by linarith) hbd

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
