import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CommonScaleHornNecks

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem closure_chart_subset_horn
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {r : ℝ} (hr : 0 ≤ r) (K : Set D.slab.terminalRegularOpen)
    (hK : IsCompact K) (hchart : range N.chart ⊆ K)
    (hKhorn : K ⊆ P.horn c e '' (univ ×ˢ Ioi r)) :
    IsCompact (closure (range N.chart)) ∧
      closure (range N.chart) ⊆ hornHalfRange P c e := by
  have hcl : closure (range N.chart) ⊆ K := closure_minimal hchart hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hcl,?_⟩
  intro x hx
  obtain ⟨q,hq,rfl⟩ := hKhorn (hcl hx)
  exact ⟨⟨q,hr.trans hq.2.le⟩,rfl⟩

private theorem scalar_lower_on_closure_chart
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k) (B : ℝ)
    (hlower : ∀ q, B ≤ metricScalarAt D.terminal.metric (N.chart q)) :
    ∀ x ∈ closure (range N.chart), B ≤ metricScalarAt D.terminal.metric x := by
  apply closure_minimal
  · rintro x ⟨q,rfl⟩
    exact hlower q
  · exact isClosed_le continuous_const (metricScalar_smooth D.terminal.metric).continuous

theorem exists_scale_threshold_disjoint_neck_family_in_horns
    (hε : ε ≤ 1 / 8646) {δ : ℝ} (hεδ : ε ≤ δ) (hδ1 : δ < 1)
    (hfit : δ⁻¹ + 1 < ε⁻¹) (r : ∀ c, P.hornIndex c → ℝ) (L : ℝ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
      ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
        (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
        (hδ : ∀ c e, δ₀ c e ≤ δ),
        (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y, t c e) ∧
          (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
          IsCompact (closure (range ((N c e).monoDelta (hδ c e) hδ1).chart)) ∧
          (∀ x ∈ closure (range ((N c e).monoDelta (hδ c e) hδ1).chart),
            Q / 2 ≤ metricScalarAt D.terminal.metric x) ∧
          Disjoint (closure (range ((N c e).monoDelta (hδ c e) hδ1).chart))
            {x | metricScalarAt D.terminal.metric x ≤ L} ∧
          ∃ Θ : neckBuffer δ → positiveHornDomain,
            IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
            (∀ q : neckBuffer δ,
              P.horn c e (Θ q).val = ((N c e).monoDelta (hδ c e) hδ1).chart q) ∧
            (∀ q : neckBuffer δ, r c e < (Θ q).val.2) ∧
            closure (range ((N c e).monoDelta (hδ c e) hδ1).chart) ⊆
              P.horn c e '' (univ ×ˢ Ioi (r c e))) ∧
        Pairwise (fun ce ce' : (c : ConnectedComponents D.slab.terminalRegularOpen) × P.hornIndex c =>
          Disjoint (closure (range ((N ce.1 ce.2).monoDelta (hδ ce.1 ce.2) hδ1).chart))
            (closure (range ((N ce'.1 ce'.2).monoDelta (hδ ce'.1 ce'.2) hδ1).chart))) ∧
        ∀ x : D.slab.terminalRegularOpen, metricScalarAt D.terminal.metric x ≤ L →
          x.val ∈ interior ((⋃ c, ⋃ e : P.hornIndex c,
            range (fun q : neckBuffer δ => (((N c e).monoDelta (hδ c e) hδ1).chart q).val))ᶜ) := by
  obtain ⟨C,hC,hfamily⟩ := P.exists_scale_threshold_neck_family_in_horns hε hεδ hδ1 hfit
    (fun c e => max (r c e) 0)
  refine ⟨max C (2 * L),lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro Q hQ y
  have hCQ : C < Q := (le_max_left _ _).trans_lt hQ
  have hLQ : L < Q / 2 := by linarith [lt_of_le_of_lt (le_max_right C (2*L)) hQ]
  obtain ⟨t,δ₀,k,N,hδ,hN⟩ := hfamily Q hCQ y
  have hclosure (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
      IsCompact (closure (range ((N c e).monoDelta (hδ c e) hδ1).chart)) ∧
        closure (range ((N c e).monoDelta (hδ c e) hδ1).chart) ⊆ hornHalfRange P c e := by
    obtain ⟨_,_,_,_,_,_,Θ,hΘ,hmap,hdepth,K,hK,hNK,hKhorn⟩ := hN c e
    exact P.closure_chart_subset_horn _ c e (le_max_right _ _) K hK hNK hKhorn
  refine ⟨t,δ₀,k,N,hδ,?_,?_,?_⟩
  · intro c e
    obtain ⟨ht,hcenter,hscale,hδ₀,hk,hscalar,Θ,hΘ,hmap,hdepth,K,hK,hNK,hKhorn⟩ := hN c e
    have hscalarcl := scalar_lower_on_closure_chart ((N c e).monoDelta (hδ c e) hδ1) (Q/2) hscalar
    refine ⟨ht,hcenter,hscale,hδ₀,hk,(hclosure c e).1,hscalarcl,?_,Θ,hΘ,hmap,?_,?_⟩
    · rw [disjoint_left]
      intro x hx hxL
      exact (not_lt_of_ge (le_trans (hscalarcl x hx) hxL)) hLQ
    · intro q
      exact (le_max_left _ _).trans_lt (hdepth q)
    · intro x hx
      obtain ⟨q,hq,rfl⟩ := hKhorn (closure_minimal hNK hK.isClosed hx)
      exact ⟨q,⟨hq.1,(le_max_left (r c e) 0).trans_lt (show max (r c e) 0 < q.2 from hq.2)⟩,rfl⟩
  · intro ce ce' hne
    exact (P.hornHalfRange_pairwise_disjoint hne).mono
      (hclosure ce.1 ce.2).2 (hclosure ce'.1 ce'.2).2
  · intro x hx
    let U : Set D.slab.terminalRegularOpen :=
      {z | metricScalarAt D.terminal.metric z < Q / 2}
    have hUopen : IsOpen U := isOpen_lt (metricScalar_smooth D.terminal.metric).continuous continuous_const
    have hxU : x ∈ U := hx.trans_lt hLQ
    have hVopen : IsOpen ((Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' U) :=
      D.slab.terminalRegularOpen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hUopen
    apply hVopen.subset_interior_iff.mpr ?_ (mem_image_of_mem Subtype.val hxU)
    rintro z ⟨w,hw,rfl⟩ hz
    obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    obtain ⟨e,q,hq⟩ := mem_iUnion.mp hc
    have heq : ((N c e).monoDelta (hδ c e) hδ1).chart q = w := Subtype.ext hq
    have hlow := (hN c e).2.2.2.2.2.1 q
    rw [heq] at hlow
    exact (not_lt_of_ge hlow) hw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
