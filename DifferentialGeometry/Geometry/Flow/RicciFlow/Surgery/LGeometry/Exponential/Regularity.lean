import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.MinimizingDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.WindowSolutionMap

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Connection (trivToE)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong (chartRepAt)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem contDiffAt_familySeed {β : P × ℝ → M} {p₀ : P} {s₀ : ℝ} (x0 : M)
    (hsrc : β (p₀, s₀) ∈ (chartAt H x0).source)
    (hβ : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (p₀, s₀)) :
    ContDiffAt ℝ ∞ (fun p : P => (extChartAt I x0 (β (p, s₀)),
      fderiv ℝ (fun s : ℝ => extChartAt I x0 (β (p, s))) s₀ (1 : ℝ))) p₀ := by
  let F : P × ℝ → E := fun q => extChartAt I x0 (β q)
  have hF : ContDiffAt ℝ ∞ F (p₀, s₀) := by
    have h := (contMDiffAt_extChartAt' (I := I) hsrc).comp (p₀, s₀) hβ
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  have hincl : ContDiffAt ℝ ∞ (fun p : P => (p, s₀)) p₀ := contDiffAt_id.prodMk contDiffAt_const
  have hpos : ContDiffAt ℝ ∞ (fun p : P => F (p, s₀)) p₀ := by
    simpa only [Function.comp_def] using hF.comp p₀ hincl
  have hvel : ContDiffAt ℝ ∞ (fun p : P => fderiv ℝ (fun s : ℝ => F (p, s)) s₀ (1 : ℝ)) p₀ :=
    (hF.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const
  exact hpos.prodMk hvel

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuousAt_lPhaseState {γ : ℝ → M} {r : ℝ}
    (hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ r)
    (hvel : DifferentiableAt ℝ (chartRepAt (I := I) γ (fun u => lVelocity (I := I) γ u) r) r) :
    ContinuousAt (fun s => (s, (extChartAt I (γ r) (γ s),
      trivToE I (γ r) (γ s) (lVelocity (I := I) γ s)))) r :=
  continuousAt_id.prodMk (((continuousAt_extChartAt (I := I) (γ r)).comp
    hmd.continuousAt).prodMk hvel.continuousAt)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_family_step (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) {γ : ℝ → M} {J : Set ℝ}
    (hγ : IsLRegularizedGeodesicOn S T γ J) {V₀ : Set P} {K₀ : Set ℝ} {p₀ : P}
    {β₀ : P × ℝ → M} {V : Set P} (hV : IsOpen V) (hpV : p₀ ∈ V) (hVV : V ⊆ V₀) {K : Set ℝ}
    (hK : IsOpen K) (hKc : IsPreconnected K) (hK₀K : K₀ ⊆ K) {β : P × ℝ → M}
    (hβ : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ K))
    (hgeo : ∀ p ∈ V, IsLRegularizedGeodesicOn S T (fun s => β (p, s)) K)
    (href : ∀ s ∈ K, β (p₀, s) = γ s) (hβ₀ : ∀ p ∈ V, ∀ s ∈ K₀, β (p, s) = β₀ (p, s))
    (x0 : M) {r r' ε : ℝ} (hr'K : r' ∈ K) (hr' : r' ∈ Ioo (r - ε) (r + ε))
    (hLJ : Ioo (r - ε) (r + ε) ⊆ J) (hsrc : γ r' ∈ (chartAt H x0).source)
    {W : Set (ℝ × (E × E))} (hW : IsOpen W)
    (hr'W : (r', (extChartAt I x0 (γ r'), trivToE I x0 (γ r') (lVelocity (I := I) γ r'))) ∈ W)
    {Ψ : (ℝ × (E × E)) × ℝ → E × E} (hΨ0 : ∀ q ∈ W, Ψ (q, q.1) = q.2)
    (hΨsm : ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (r - ε) (r + ε)))
    (hΨd : ∀ q ∈ W, ∀ s ∈ Ioo (r - ε) (r + ε),
      HasDerivAt (fun u => Ψ (q, u)) (lPhaseField S T x0 s (Ψ (q, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ (q, s)).1 ∈ interior (extChartAt I x0).target) :
    ∃ V' : Set P, IsOpen V' ∧ p₀ ∈ V' ∧ V' ⊆ V₀ ∧ ∃ β' : P × ℝ → M,
      ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β' (V' ×ˢ (K ∪ Ioo (r - ε) (r + ε))) ∧
      (∀ p ∈ V', IsLRegularizedGeodesicOn S T (fun s => β' (p, s))
        (K ∪ Ioo (r - ε) (r + ε))) ∧
      (∀ s ∈ K ∪ Ioo (r - ε) (r + ε), β' (p₀, s) = γ s) ∧
      ∀ p ∈ V', ∀ s ∈ K₀, β' (p, s) = β₀ (p, s) := by
  classical
  set L : Set ℝ := Ioo (r - ε) (r + ε) with hLdef
  have hprod : IsOpen (V ×ˢ K) := hV.prod hK
  have hβAt : ∀ p ∈ V, ∀ s ∈ K, ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (p, s) :=
    fun p hp s hs => (hβ (p, s) ⟨hp, hs⟩).contMDiffAt (hprod.mem_nhds ⟨hp, hs⟩)
  have hpos : ContinuousOn (fun p => β (p, r')) V := fun p hp =>
    ((hβAt p hp r' hr'K).comp p (contMDiffAt_id.prodMk contMDiffAt_const)).continuousAt
      |>.continuousWithinAt
  let V₁ : Set P := V ∩ (fun p => β (p, r')) ⁻¹' (chartAt H x0).source
  have hV₁ : IsOpen V₁ := hpos.isOpen_inter_preimage hV (chartAt H x0).open_source
  let σ : P → E × E := fun p => (extChartAt I x0 (β (p, r')),
    fderiv ℝ (fun s : ℝ => extChartAt I x0 (β (p, s))) r' (1 : ℝ))
  have hσ : ContDiffOn ℝ ∞ σ V₁ := fun p hp =>
    (contDiffAt_familySeed x0 hp.2 (hβAt p hp.1 r' hr'K)).contDiffWithinAt
  have hσv : ∀ p ∈ V₁, σ p = (extChartAt I x0 (β (p, r')),
      trivToE I x0 (β (p, r')) (lVelocity (I := I) (fun s => β (p, s)) r')) := fun p hp =>
    Prod.ext rfl (lPhaseSeed_velocity (I := I) x0 ((hgeo p hp.1 r' hr'K).2.1) hp.2)
  let V' : Set P := V₁ ∩ (fun p => ((r', σ p) : ℝ × (E × E))) ⁻¹' W
  have hV' : IsOpen V' :=
    (continuousOn_const.prodMk hσ.continuousOn).isOpen_inter_preimage hV₁ hW
  have hγβ : (fun s => β (p₀, s)) =ᶠ[𝓝 r'] γ :=
    eventually_of_mem (hK.mem_nhds hr'K) fun s hs => href s hs
  have hv₀ : lVelocity (I := I) (fun s => β (p₀, s)) r' = lVelocity (I := I) γ r' := by
    unfold lVelocity
    rw [hγβ.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
    rfl
  have hp₀₁ : p₀ ∈ V₁ := ⟨hpV, by simpa only [mem_preimage, href r' hr'K] using hsrc⟩
  have hσ₀ : σ p₀ = (extChartAt I x0 (γ r'), trivToE I x0 (γ r') (lVelocity (I := I) γ r')) := by
    rw [hσv p₀ hp₀₁, hv₀, href r' hr'K]
  have hp₀' : p₀ ∈ V' := by
    refine ⟨hp₀₁, ?_⟩
    change ((r', σ p₀) : ℝ × (E × E)) ∈ W
    rw [hσ₀]
    exact hr'W
  have hV'V : V' ⊆ V := fun p hp => hp.1.1
  let η : P × ℝ → M := fun q => (extChartAt I x0).symm (Ψ ((r', σ q.1), q.2)).1
  have hηsm : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ η (V' ×ˢ L) := by
    have hin : ContDiffOn ℝ ∞ (fun q : P × ℝ => (((r', σ q.1) : ℝ × (E × E)), q.2))
        (V' ×ˢ L) :=
      (contDiffOn_const.prodMk ((hσ.mono fun p hp => hp.1).comp contDiffOn_fst
        fun q hq => hq.1)).prodMk contDiffOn_snd
    have hmaps : MapsTo (fun q : P × ℝ => (((r', σ q.1) : ℝ × (E × E)), q.2)) (V' ×ˢ L)
        (W ×ˢ L) := fun q hq => ⟨hq.1.2, hq.2⟩
    have hph : ContDiffOn ℝ ∞ (fun q : P × ℝ => (Ψ ((r', σ q.1), q.2)).1) (V' ×ˢ L) :=
      (hΨsm.comp hin hmaps).fst
    have hphM : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, E) ∞
        (fun q : P × ℝ => (Ψ ((r', σ q.1), q.2)).1) (V' ×ˢ L) := hph.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphM
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x0).comp hphM
      fun q hq => interior_subset (s := (extChartAt I x0).target) (hΨd _ (hmaps hq).1 q.2 hq.2).2.2
  have hηd : ∀ p ∈ V', ∀ s ∈ L,
      HasDerivAt (fun u => Ψ ((r', σ p), u)) (lPhaseField S T x0 s (Ψ ((r', σ p), s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ ((r', σ p), s)).1 ∈ interior (extChartAt I x0).target :=
    fun p hp s hs => hΨd _ hp.2 s hs
  have hηgeo : ∀ p ∈ V', IsLRegularizedGeodesicOn S T (fun s => η (p, s)) L := fun p hp =>
    isLRegularizedGeodesicOn_lPhaseCurve S T x0 isOpen_Ioo (hηd p hp)
  have hmatch : ∀ p ∈ V', EqOn (fun s => β (p, s)) (fun s => η (p, s)) (K ∩ L) := by
    intro p hp
    have h0 : Ψ ((r', σ p), r') = σ p := hΨ0 _ hp.2
    exact eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn S hS T x0 hK hKc (hgeo p (hV'V hp))
      isOpen_Ioo isPreconnected_Ioo (hηd p hp) hr'K hr' hp.1.2 (h0.trans (hσv p hp.1))
  let β' : P × ℝ → M := fun q => if q.2 ∈ K then β q else η q
  have hβ'K : ∀ p s, s ∈ K → β' (p, s) = β (p, s) := fun p s hs => ite_eq_left hs
  have hβ'L : ∀ p ∈ V', ∀ s ∈ L, β' (p, s) = η (p, s) := by
    intro p hp s hs
    by_cases h : s ∈ K
    · rw [hβ'K p s h]
      exact hmatch p hp ⟨h, hs⟩
    · exact ite_eq_right h
  refine ⟨V', hV', hp₀', (hV'V.trans hVV), β', ?_, ?_, ?_, ?_⟩
  · rintro ⟨p, s⟩ ⟨hp, hs | hs⟩
    · have heq : β' =ᶠ[𝓝 (p, s)] β :=
        eventually_of_mem ((hK.preimage continuous_snd).mem_nhds hs) fun q hq => ite_eq_left hq
      exact ((hβAt p (hV'V hp) s hs).congr_of_eventuallyEq heq).contMDiffWithinAt
    · have hopen : IsOpen (V' ×ˢ L) := hV'.prod isOpen_Ioo
      have heq : β' =ᶠ[𝓝 (p, s)] η :=
        eventually_of_mem (hopen.mem_nhds ⟨hp, hs⟩) fun q hq => hβ'L q.1 hq.1 q.2 hq.2
      exact (((hηsm (p, s) ⟨hp, hs⟩).contMDiffAt
        (hopen.mem_nhds ⟨hp, hs⟩)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · intro p hp s hs
    rcases hs with hs | hs
    · exact (hgeo p (hV'V hp)).congr_of_eventuallyEq (fun u hu =>
        eventually_of_mem (hK.mem_nhds hu) fun t ht => hβ'K p t ht) s hs
    · exact (hηgeo p hp).congr_of_eventuallyEq (fun u hu =>
        eventually_of_mem (isOpen_Ioo.mem_nhds hu) fun t ht => hβ'L p hp t ht) s hs
  · have hηγ : EqOn γ (fun s => η (p₀, s)) L := by
      have h0 : Ψ ((r', σ p₀), r') = σ p₀ := hΨ0 _ hp₀'.2
      have hc := eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn S hS T x0 isOpen_Ioo
        isPreconnected_Ioo (fun s hs => hγ s (hLJ hs)) isOpen_Ioo isPreconnected_Ioo (hηd p₀ hp₀')
        hr' hr' hsrc (h0.trans hσ₀)
      intro s hs
      exact hc ⟨hs, hs⟩
    intro s hs
    rcases hs with hs | hs
    · rw [hβ'K p₀ s hs, href s hs]
    · rw [hβ'L p₀ hp₀' s hs]
      exact (hηγ hs).symm
  · intro p hp s hs
    rw [hβ'K p s (hK₀K hs)]
    exact hβ₀ p (hV'V hp) s hs

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedGeodesicFamily_along (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : IsLRegularizedGeodesicOn S T γ J) {V₀ : Set P} {K₀ : Set ℝ} {p₀ : P}
    (hV₀ : IsOpen V₀) (hp₀ : p₀ ∈ V₀) (hK₀ : IsOpen K₀) (hK₀c : IsPreconnected K₀)
    (hK₀J : K₀ ⊆ J) {β₀ : P × ℝ → M}
    (hβ₀ : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β₀ (V₀ ×ˢ K₀))
    (hgeo₀ : ∀ p ∈ V₀, IsLRegularizedGeodesicOn S T (fun s => β₀ (p, s)) K₀)
    (href₀ : ∀ s ∈ K₀, β₀ (p₀, s) = γ s) {c b : ℝ} (hc : c ∈ K₀) (hcb : uIcc c b ⊆ J) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ V₀ ∧ ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧
      K₀ ⊆ K ∧ b ∈ K ∧ K ⊆ J ∧ ∃ β : P × ℝ → M,
        ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ K) ∧
        (∀ p ∈ V, IsLRegularizedGeodesicOn S T (fun s => β (p, s)) K) ∧
        (∀ s ∈ K, β (p₀, s) = γ s) ∧ ∀ p ∈ V, ∀ s ∈ K₀, β (p, s) = β₀ (p, s) := by
  classical
  let Good : Set ℝ := {r | ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ V₀ ∧ ∃ K : Set ℝ, IsOpen K ∧
    IsPreconnected K ∧ K₀ ⊆ K ∧ r ∈ K ∧ K ⊆ J ∧ ∃ β : P × ℝ → M,
      ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ K) ∧
      (∀ p ∈ V, IsLRegularizedGeodesicOn S T (fun s => β (p, s)) K) ∧
      (∀ s ∈ K, β (p₀, s) = γ s) ∧ ∀ p ∈ V, ∀ s ∈ K₀, β (p, s) = β₀ (p, s)}
  have hGoodOpen : IsOpen Good := by
    rw [isOpen_iff_mem_nhds]
    rintro r ⟨V, hV, hpV, hVV, K, hK, hKc, hK₀K, hrK, hKJ, β, hβ, hgeo, href, hβeq⟩
    filter_upwards [hK.mem_nhds hrK] with r' hr'
    exact ⟨V, hV, hpV, hVV, K, hK, hKc, hK₀K, hr', hKJ, β, hβ, hgeo, href, hβeq⟩
  have hcGood : c ∈ Good := ⟨V₀, hV₀, hp₀, subset_rfl, K₀, hK₀, hK₀c, subset_rfl, hc, hK₀J, β₀,
    hβ₀, hgeo₀, href₀, fun _ _ _ _ => rfl⟩
  have hclosed : closure Good ∩ uIcc c b ⊆ Good := by
    rintro r ⟨hrcl, hrI⟩
    have hrJ := hcb hrI
    obtain ⟨hreg, hmd, hvel, -⟩ := hγ r hrJ
    set x0 := γ r with hx0
    have hz0 : (extChartAt I x0 (γ r)) ∈ interior (extChartAt I x0).target :=
      mem_interior_iff_mem_nhds.2 (extChartAt_target_mem_nhds (I := I) x0)
    obtain ⟨ε, hε, W, hW, hrW, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
      exists_lPhaseFlow_of_regular S hS T x0 (s0 := r)
        (extChartAt I x0 (γ r), trivToE I x0 (γ r) (lVelocity (I := I) γ r)) hreg hz0
    obtain ⟨δJ, hδJ, hballJ⟩ := Metric.isOpen_iff.1 hJ r hrJ
    have hst := continuousAt_lPhaseState hmd hvel
    have hsrcEv : ∀ᶠ s in 𝓝 r, γ s ∈ (chartAt H x0).source :=
      hmd.continuousAt.preimage_mem_nhds ((chartAt H x0).open_source.mem_nhds
        (mem_chart_source H x0))
    have hWEv : ∀ᶠ s in 𝓝 r, (s, (extChartAt I x0 (γ s),
        trivToE I x0 (γ s) (lVelocity (I := I) γ s))) ∈ W :=
      hst.preimage_mem_nhds (hW.mem_nhds hrW)
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (hsrcEv.and hWEv)
    set ε' := min ε δJ with hε'
    have hε'pos : 0 < ε' := lt_min hε hδJ
    have hLJ : Ioo (r - ε') (r + ε') ⊆ J := fun s hs => hballJ (by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hs.1, hs.2, min_le_right ε δJ])
    have hLsub : Ioo (r - ε') (r + ε') ⊆ Ioo (r - ε) (r + ε) := fun s hs =>
      ⟨by linarith [hs.1, min_le_left ε δJ], by linarith [hs.2, min_le_left ε δJ]⟩
    obtain ⟨r', hr'G, hr'd⟩ := Metric.mem_closure_iff.1 hrcl (min δ ε') (lt_min hδ hε'pos)
    rw [Real.dist_eq, abs_lt] at hr'd
    have hr'L : r' ∈ Ioo (r - ε') (r + ε') :=
      ⟨by linarith [hr'd.2, min_le_right δ ε'], by linarith [hr'd.1, min_le_right δ ε']⟩
    obtain ⟨hsrc, hr'W⟩ := hδs (show dist r' r < δ by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hr'd.1, hr'd.2, min_le_left δ ε'])
    obtain ⟨V, hV, hpV, hVV, K, hK, hKc, hK₀K, hr'K, hKJ, β, hβ, hgeo, href, hβeq⟩ := hr'G
    obtain ⟨V', hV', hpV', hV'V, β', hβ', hgeo', href', hβeq'⟩ :=
      exists_family_step S hS T hγ hV hpV hVV hK hKc hK₀K hβ hgeo href hβeq x0 hr'K hr'L hLJ
        hsrc hW hr'W (fun q hq => hΨ0 q hq) (hΨsm.mono (prod_mono subset_rfl hLsub))
        (fun q hq s hs => hΨd q hq s (hLsub hs))
    exact ⟨V', hV', hpV', hV'V, K ∪ Ioo (r - ε') (r + ε'), hK.union isOpen_Ioo,
      hKc.union r' hr'K hr'L isPreconnected_Ioo, subset_union_of_subset_left hK₀K _,
      Or.inr ⟨by linarith, by linarith⟩, union_subset hKJ hLJ, β', hβ', hgeo', href', hβeq'⟩
  have hall : uIcc c b ⊆ Good :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hGoodOpen ⟨c, left_mem_uIcc, hcGood⟩
      hclosed
  exact hall right_mem_uIcc

theorem exists_isLRegularizedGeodesicOn_extension_of_lRegularizedAction_le
    [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T a b : ℝ} (hab : a < b)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) (γ : ℝ → M) (hγc : Continuous γ)
    (hγ : Manifold.absolutelyContinuousOnInterval I γ a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) MeasureTheory.volume a b)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = γ a → δ b = γ b →
      lRegularizedAction S T γ a b ≤ lRegularizedAction S T δ a b) :
    ∃ α : ℝ → M, EqOn α γ (Icc a b) ∧ ∃ e : ℝ, 0 < e ∧
      IsLRegularizedGeodesicOn S T α (Ioo (a - e) (b + e)) := by
  obtain ⟨m, t, p, w, ht0, htmono, htlast, hsrc, hrep, -⟩ :=
    exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a b hab.le γ hγ hint (fun s hs => D.regular_subset (hreg s hs))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hc1 := lMinCurve_c1 S hS T a b hab t htmono ht0 htlast p γ hγc w hsrc hrep hreg hmin
  have hsol := lMinCurve_regularity S hS T a b hab t htmono ht0 htlast p γ hγc w hsrc hrep hreg
    hmin
  obtain ⟨α, hαγ, e, he, hα⟩ := exists_lRegularizedExtOn S hS T a b hab γ hc1 hreg hsol
  exact ⟨α, hαγ, e, he, hα⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {H : ObservedHistory.{u}}

private theorem mem_regularizedStage_Icc {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j)) :
    r ∈ Icc (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 ≤ r := ha.trans hr.1
  have ha2 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha hr.1 2
  have hb2 : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
  constructor
  · apply (Real.sqrt_le_left hr0).2
    have := le_min (show T - r ^ 2 ≤ T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.le_sqrt hr0 ?_).2
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      linarith
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      nlinarith

private theorem mem_regularizedStage_Ioo {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Ioo a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)) :
    r ∈ Ioo (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 < r := ha.trans_lt hr.1
  have ha2 : a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have hb2 : r ^ 2 < b ^ 2 := pow_lt_pow_left₀ hr.2 hr0.le two_ne_zero
  constructor
  · apply (Real.sqrt_lt' hr0).2
    have := lt_min (show T - r ^ 2 < T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.lt_sqrt hr0.le).2
    have := max_lt (show T - b ^ 2 < T - r ^ 2 by linarith) ht.1
    linarith

private theorem eq_of_mem_Ioo_of_mem_Icc {t : ℝ} {j k : Fin (H.eventCount + 1)}
    (hk : t ∈ Ioo (H.time k) (H.stageEndTime k)) (hj : t ∈ Icc (H.time j) (H.stageEndTime j)) :
    j = k := by
  rcases lt_trichotomy j k with h | h | h
  · have := stageEndTime_le_time_of_lt h
    linarith [hj.2, hk.1]
  · exact h
  · have := stageEndTime_le_time_of_lt h
    linarith [hj.1, hk.2]

private theorem exists_mem_Ioo_not_mem_range {T a b : ℝ} (hab : a < b) (ha : 0 ≤ a) :
    ∃ c ∈ Ioo a b, T - c ^ 2 ∉ range H.time := by
  have hfin : ((fun t => Real.sqrt (T - t)) '' range H.time).Finite :=
    (finite_range _).image _
  obtain ⟨c, hc, hcn⟩ := ((Ioo_infinite hab).sdiff hfin).nonempty
  refine ⟨c, hc, fun ⟨i, hi⟩ => hcn ⟨H.time i, ⟨i, rfl⟩, ?_⟩⟩
  change Real.sqrt (T - H.time i) = c
  rw [hi, sub_sub_cancel, Real.sqrt_sq (ha.trans hc.1.le)]

private theorem exists_stage_nhds {T c : ℝ} (hc : 0 < c) (h0 : 0 ≤ T - c ^ 2)
    (hh : T - c ^ 2 < H.horizon) (hne : T - c ^ 2 ∉ range H.time) :
    ∃ k : Fin (H.eventCount + 1), ∃ η > 0, η < c ∧
      ∀ r ∈ Ioo (c - η) (c + η), T - r ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k) := by
  set k := H.activeStage ⟨T - c ^ 2, h0, hh.le⟩
  have hkd : T - c ^ 2 ∈ H.stageDomain k := H.activeStage_mem _
  have hlt : T - c ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k) := by
    refine ⟨lt_of_le_of_ne (H.time_le_of_mem_stageDomain hkd) fun h => hne ⟨k, h⟩, ?_⟩
    cases hk : k using Fin.lastCases with
    | last => rw [stageEndTime_last]; exact hh
    | cast i =>
      rw [hk] at hkd
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hkd
      rw [stageEndTime_castSucc]
      exact hkd.2
  have hopen : IsOpen ((fun r : ℝ => T - r ^ 2) ⁻¹' Ioo (H.time k) (H.stageEndTime k)) :=
    isOpen_Ioo.preimage (by fun_prop)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen c hlt
  refine ⟨k, min η (c / 2), lt_min hη (by linarith), (min_le_right _ _).trans_lt (by linarith),
    fun r hr => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [hr.1, hr.2, min_le_left η (c / 2)]

namespace LWindow

variable {lo hi : Fin (H.eventCount + 1)} {T : ℝ}

private theorem mem_range_of_mem_Icc (W : H.LWindow lo hi T) {r : ℝ} (hr : r ∈ Ioo W.a W.b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j)) :
    lo ≤ j ∧ j ≤ hi := by
  have ha := W.nonneg
  have h1 : W.a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have h2 : r ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hr.2 (ha.trans hr.1.le) two_ne_zero
  constructor
  · by_contra h
    have := (stageEndTime_le_time_of_lt (not_le.1 h)).trans (H.time_le_of_mem_stageDomain W.lower)
    linarith [ht.2]
  · by_contra h
    have := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
      (stageEndTime_le_time_of_lt (not_le.1 h))
    linarith [ht.1]

private theorem contMDiffOn_invFun_smooth (W : H.LWindow lo hi T) (j : H.StageInterval lo hi)
    [Nonempty W.X] :
    ContMDiffOn ThreeModel ThreeModel ∞ (Function.invFun (W.f j)) (range (W.f j)) := by
  rintro _ ⟨x, rfl⟩
  have hx := W.localDiffeomorph j x
  have hev : Function.invFun (W.f j) =ᶠ[𝓝 (W.f j x)] hx.localInverse := by
    filter_upwards [hx.localInverse_open_source.mem_nhds hx.localInverse_mem_source] with y hy
    apply W.injective j
    rw [Function.invFun_eq ⟨_, hx.localInverse_right_inv hy⟩, hx.localInverse_right_inv hy]
  exact (hx.contMDiffAt_localInverse.congr_of_eventuallyEq hev).contMDiffWithinAt

end LWindow

section Transfer

variable {lo₁ hi₁ lo₂ hi₂ : Fin (H.eventCount + 1)} {T : ℝ}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_transfer_family (W₁ : H.LWindow lo₁ hi₁ T) (W₂ : H.LWindow lo₂ hi₂ T)
    {k : Fin (H.eventCount + 1)} (hk₁ : lo₁ ≤ k ∧ k ≤ hi₁) (hk₂ : lo₂ ≤ k ∧ k ≤ hi₂)
    {c η : ℝ} (hη : 0 < η) (hW₁ : Ioo (c - η) (c + η) ⊆ Ioo W₁.a W₁.b)
    (hc₂ : c ∈ Ioo W₂.a W₂.b)
    (hint : ∀ r ∈ Ioo (c - η) (c + η), T - r ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k))
    {V : Set ThreeSpace} (hV : IsOpen V) {Z₀ : ThreeSpace} (hZ₀ : Z₀ ∈ V)
    {β : ThreeSpace × ℝ → W₁.X}
    (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β
      (V ×ˢ Ioo (c - η) (c + η)))
    (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W₁.S T (fun s => β (Z, s)) (Ioo (c - η) (c + η)))
    {γ₂ : ℝ → W₂.X}
    (hagree : ∀ s ∈ Ioo (c - η) (c + η), W₁.f ⟨k, hk₁⟩ (β (Z₀, s)) = W₂.f ⟨k, hk₂⟩ (γ₂ s)) :
    ∃ V' : Set ThreeSpace, IsOpen V' ∧ Z₀ ∈ V' ∧ V' ⊆ V ∧ ∃ η' > 0, η' ≤ η ∧
      Ioo (c - η') (c + η') ⊆ Ioo W₂.a W₂.b ∧ ∃ β₂ : ThreeSpace × ℝ → W₂.X,
        ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₂
          (V' ×ˢ Ioo (c - η') (c + η')) ∧
        (∀ Z ∈ V', IsLRegularizedGeodesicOn W₂.S T (fun s => β₂ (Z, s))
          (Ioo (c - η') (c + η'))) ∧
        (∀ s ∈ Ioo (c - η') (c + η'), β₂ (Z₀, s) = γ₂ s) ∧
        ∀ Z ∈ V', ∀ s ∈ Ioo (c - η') (c + η'),
          W₂.f ⟨k, hk₂⟩ (β₂ (Z, s)) = W₁.f ⟨k, hk₁⟩ (β (Z, s)) := by
  classical
  have : Nonempty W₂.X := ⟨γ₂ c⟩
  have hcU : c ∈ Ioo (c - η) (c + η) := ⟨by linarith, by linarith⟩
  have hprod : IsOpen (V ×ˢ Ioo (c - η) (c + η)) := hV.prod isOpen_Ioo
  have hF : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞
      (fun q => W₁.f ⟨k, hk₁⟩ (β q)) (V ×ˢ Ioo (c - η) (c + η)) :=
    (W₁.localDiffeomorph _).contMDiff.comp_contMDiffOn hβ
  have hO : IsOpen ((V ×ˢ Ioo (c - η) (c + η)) ∩
      (fun q => W₁.f ⟨k, hk₁⟩ (β q)) ⁻¹' range (W₂.f ⟨k, hk₂⟩)) :=
    hF.continuousOn.isOpen_inter_preimage hprod (W₂.localDiffeomorph _).isOpen_range
  have hmem : ((Z₀, c) : ThreeSpace × ℝ) ∈ (V ×ˢ Ioo (c - η) (c + η)) ∩
      (fun q => W₁.f ⟨k, hk₁⟩ (β q)) ⁻¹' range (W₂.f ⟨k, hk₂⟩) :=
    ⟨⟨hZ₀, hcU⟩, ⟨γ₂ c, (hagree c hcU).symm⟩⟩
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds hmem)
  obtain ⟨V', hV'u, hV', hZ₀V'⟩ := mem_nhds_iff.1 hu
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hw (isOpen_Ioo.mem_nhds hc₂))
  set η' := min ρ η with hη'
  have hη'pos : 0 < η' := lt_min hρ hη
  have hsub : Ioo (c - η') (c + η') ⊆ w ∩ Ioo W₂.a W₂.b := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hs.1, hs.2, min_le_left ρ η])
  have hsubU : Ioo (c - η') (c + η') ⊆ Ioo (c - η) (c + η) := fun s hs =>
    ⟨by linarith [hs.1, min_le_right ρ η], by linarith [hs.2, min_le_right ρ η]⟩
  set K := Ioo (c - η') (c + η')
  have hrange : ∀ Z ∈ V' ∩ V, ∀ s ∈ K, W₁.f ⟨k, hk₁⟩ (β (Z, s)) ∈ range (W₂.f ⟨k, hk₂⟩) :=
    fun Z hZ s hs => (huw ⟨hV'u hZ.1, (hsub hs).1⟩).2
  let β₂ : ThreeSpace × ℝ → W₂.X := fun q => Function.invFun (W₂.f ⟨k, hk₂⟩) (W₁.f ⟨k, hk₁⟩ (β q))
  have hβ₂f : ∀ Z ∈ V' ∩ V, ∀ s ∈ K, W₂.f ⟨k, hk₂⟩ (β₂ (Z, s)) = W₁.f ⟨k, hk₁⟩ (β (Z, s)) :=
    fun Z hZ s hs => Function.invFun_eq (hrange Z hZ s hs)
  have hβ₂sm : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₂
      ((V' ∩ V) ×ˢ K) :=
    (LWindow.contMDiffOn_invFun_smooth W₂ ⟨k, hk₂⟩).comp
      (hF.mono (prod_mono inter_subset_right hsubU)) fun q hq => hrange q.1 hq.1 q.2 hq.2
  have hopen : IsOpen ((V' ∩ V) ×ˢ K) := (hV'.inter hV).prod isOpen_Ioo
  have htk : H.time k < H.stageEndTime k := (hint c hcU).1.trans (hint c hcU).2
  obtain ⟨G, -, hG⟩ := exists_incomingSlab_stageMetric k htk
  refine ⟨V' ∩ V, hV'.inter hV, ⟨hZ₀V', hZ₀⟩, inter_subset_right, η', hη'pos,
    min_le_right ρ η, fun s hs => (hsub hs).2, β₂, hβ₂sm, fun Z hZ => ?_, fun s hs => ?_,
    hβ₂f⟩
  · have hK₁ : K ⊆ Ioo (H.regularizedStageStart T W₁.a k) (H.regularizedStageEnd T W₁.b k) :=
      fun s hs => mem_regularizedStage_Ioo W₁.nonneg (hW₁ (hsubU hs)) (hint s (hsubU hs))
    have hK₂ : K ⊆ Ioo (H.regularizedStageStart T W₂.a k) (H.regularizedStageEnd T W₂.b k) :=
      fun s hs => mem_regularizedStage_Ioo W₂.nonneg (hsub hs).2 (hint s (hsubU hs))
    have hgeo₁ : IsLRegularizedGeodesicOn W₁.S T (fun s => β (Z, s)) K :=
      fun s hs => hgeo Z hZ.2 s (hsubU hs)
    have hstage := LWindow.isLRegularizedGeodesicOn_comp W₁ ⟨k, hk₁⟩ G.flow isOpen_Ioo hK₁
      (fun s hs => (hG _ (hint s (hsubU hs))).symm) (fun s hs => hint s (hsubU hs)) hgeo₁
    have hcomp : IsLRegularizedGeodesicOn G.flow T
        (W₂.f ⟨k, hk₂⟩ ∘ fun s => β₂ (Z, s)) K :=
      hstage.congr_of_eventuallyEq fun s hs =>
        eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr => hβ₂f Z hZ r hr
    have hcont : ∀ s ∈ K, ContinuousAt (fun r => β₂ (Z, r)) s := fun s hs =>
      (((hβ₂sm (Z, s) ⟨hZ, hs⟩).contMDiffAt (hopen.mem_nhds ⟨hZ, hs⟩)).comp s
        (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
    refine hcomp.of_comp_localPullMetric (W₂.localDiffeomorph ⟨k, hk₂⟩)
      (fun s hs => by rw [W₂.metric ⟨k, hk₂⟩ s (hK₂ hs), hG _ (hint s (hsubU hs))])
      (fun s hs _ => W₂.regular s (Ioo_subset_Icc_self (hsub hs).2))
      (fun s hs => eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr => hcont r hr)
      (fun s hs => eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr => (hcomp r hr).2.1)
  · apply W₂.injective ⟨k, hk₂⟩
    rw [hβ₂f Z₀ ⟨hZ₀V', hZ₀⟩ s hs]
    exact hagree s (hsubU hs)

end Transfer

section Prefix

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ}
  {p : (H.stage last).Carrier}

private theorem lo_le_of_lt_b {lo hi : Fin (H.eventCount + 1)} (W : H.LWindow lo hi T) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < W.b) {j : Fin (H.eventCount + 1)}
    (ht : T - r ^ 2 ≤ H.stageEndTime j) : lo ≤ j := by
  by_contra h
  have := (stageEndTime_le_time_of_lt (not_le.1 h)).trans (H.time_le_of_mem_stageDomain W.lower)
  have : r ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hr hr0 two_ne_zero
  linarith

variable (H) in
private def IsHistoryLGeodesicPrefix (T : ℝ) (p : (H.stage last).Carrier)
    (A : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) (Z : ThreeSpace)
    (c : ℝ) : Prop :=
  (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
    Real.sqrt (T - H.time i.succ) < c →
    (H.event i).RegularCrossing
      (A ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
      (A ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))) ∧
  (∀ s ∈ Ioo 0 c, ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
      (W : H.LWindow lo hi T), s ∈ Ioo W.a W.b ∧ W.b ≤ c ∧ ∃ γ : ℝ → W.X,
        IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
        ∀ j : H.StageInterval lo hi,
          EqOn (W.f j ∘ γ) (A ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
            (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
  ∃ (lo : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (W : H.LWindow lo last T) (x : W.X)
    (Zx : TangentSpace ThreeModel x), W.a = 0 ∧ W.b ≤ c ∧ W.f ⟨last, W.le, le_rfl⟩ x = p ∧
    mfderiv ThreeModel ThreeModel (W.f ⟨last, W.le, le_rfl⟩) x Zx = Z ∧
    W.b ∈ lRegularizedDomain W.S T x Zx ∧
    ∀ j : H.StageInterval lo last,
      EqOn (W.f j ∘ lRegularizedCurve W.S T x Zx) (A ⟨j.val, hlo.trans j.property.1, j.property.2⟩)
        (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T W.b j.val))

variable (H) in
private def HasPrefixFamily (T v : ℝ) (p : (H.stage last).Carrier)
    (α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) (Z₀ : ThreeSpace)
    (c : ℝ) : Prop :=
  ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
  ∃ A : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
    (∀ Z ∈ V, IsHistoryLGeodesicPrefix H T p (A Z) Z c) ∧
  ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) (γ : ℝ → W.X), c ∈ Ioo W.a W.b ∧
    IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
    (∀ j : H.StageInterval lo hi, ∀ r ∈ Ioo W.a W.b, r ≤ v →
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      W.f j (γ r) = α₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r) ∧
  ∃ (k : Fin (H.eventCount + 1)) (hk : lo ≤ k ∧ k ≤ hi) (η : ℝ), 0 < η ∧
    Ioo (c - η) (c + η) ⊆ Ioo W.a W.b ∧
    (∀ r ∈ Ioo (c - η) (c + η), T - r ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k)) ∧
  ∃ β : ThreeSpace × ℝ → W.X,
    ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ Ioo (c - η) (c + η)) ∧
    (∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun s => β (Z, s)) (Ioo (c - η) (c + η))) ∧
    (∀ s ∈ Ioo (c - η) (c + η), β (Z₀, s) = γ s) ∧
    ∀ Z ∈ V, ∀ r ∈ Ioc (c - η) c,
      A Z ⟨k, hlo.trans hk.1, hk.2.trans hhi⟩ r = W.f ⟨k, hk⟩ (β (Z, r))

end Prefix

section Step

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ} {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

private theorem isHistoryLGeodesicPrefix_congr
    {A A' : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier} {Z : ThreeSpace}
    {c c' : ℝ} (hcc' : c ≤ c') (hA : H.IsHistoryLGeodesicPrefix T p A Z c)
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      c ≤ Real.sqrt (T - H.time i.succ) → Real.sqrt (T - H.time i.succ) < c' →
      (H.event i).RegularCrossing
        (A' ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (A' ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hwin : ∀ s ∈ Ico c c', ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo)
      (hhi : hi ≤ last) (W : H.LWindow lo hi T), s ∈ Ioo W.a W.b ∧ W.b ≤ c' ∧ ∃ γ : ℝ → W.X,
        IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
        ∀ j : H.StageInterval lo hi,
          EqOn (W.f j ∘ γ) (A' ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
            (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (heq : ∀ j r, r ≤ c → A' j r = A j r) : H.IsHistoryLGeodesicPrefix T p A' Z c' := by
  obtain ⟨hc, hw, lo, hlo, W, x, Zx, ha, hb, hx, hZ, hdom, hbase⟩ := hA
  refine ⟨fun i hf hl hi => ?_, fun s hs => ?_, lo, hlo, W, x, Zx, ha, hb.trans hcc', hx, hZ,
    hdom, fun j r hr => ?_⟩
  · rcases lt_or_ge (Real.sqrt (T - H.time i.succ)) c with h | h
    · rw [heq _ _ h.le, heq _ _ h.le]
      exact hc i hf hl h
    · exact hcross i hf hl h hi
  · rcases lt_or_ge s c with h | h
    · obtain ⟨lo₁, hi₁, hlo₁, hhi₁, W₁, hs₁, hb₁, γ₁, hγ₁, he₁⟩ := hw s ⟨hs.1, h⟩
      refine ⟨lo₁, hi₁, hlo₁, hhi₁, W₁, hs₁, hb₁.trans hcc', γ₁, hγ₁, fun j r hr => ?_⟩
      rw [he₁ j hr, heq _ _ ((W₁.piece_subset j hr).2.trans hb₁)]
    · exact hwin s ⟨h, hs.2⟩
  · have hsub := W.piece_subset j (by rwa [ha])
    rw [hbase j hr, heq _ _ (hsub.2.trans hb)]

end Step

section StepFamily

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ} {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem hasPrefixFamily_step {Z₀ : ThreeSpace} {c c' : ℝ}
    (hP : H.HasPrefixFamily T v p α₀ Z₀ c) {lo' hi' : Fin (H.eventCount + 1)} (hlo' : first ≤ lo')
    (hhi' : hi' ≤ last) (W' : H.LWindow lo' hi' T) (γ' : ℝ → W'.X)
    (hγ' : IsLRegularizedGeodesicOn W'.S T γ' (Ioo W'.a W'.b))
    (href' : ∀ j : H.StageInterval lo' hi', ∀ r ∈ Ioo W'.a W'.b, r ≤ v →
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      W'.f j (γ' r) = α₀ ⟨j.val, hlo'.trans j.property.1, j.property.2.trans hhi'⟩ r)
    (hc : W'.a < c) (hcc' : c < c') (hc'b : c' < W'.b) (hc'v : c' ≤ v)
    (hne : T - c' ^ 2 ∉ range H.time) : H.HasPrefixFamily T v p α₀ Z₀ c' := by
  classical
  obtain ⟨V, hV, hZ₀V, A, hA, lo, hi, hlo, hhi, W, γ, hcW, hγ, href, k, hk, η, hη, hηW, hηk, β,
    hβ, hgeo, hβγ, hAβ⟩ := hP
  have hcpos : 0 < c := W'.nonneg.trans_lt hc
  have hkc := hηk c ⟨by linarith, by linarith⟩
  have hk' : lo' ≤ k ∧ k ≤ hi' :=
    LWindow.mem_range_of_mem_Icc W' ⟨hc, hcc'.trans hc'b⟩ ⟨hkc.1.le, hkc.2.le⟩
  set η₀ := min η (min (c - W'.a) (min (W'.b - c) (v - c))) with hη₀
  have hη₀pos : 0 < η₀ := lt_min hη (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hη₀le : η₀ ≤ η := min_le_left _ _
  have hη₀a : η₀ ≤ c - W'.a := (min_le_right _ _).trans (min_le_left _ _)
  have hη₀b : η₀ ≤ W'.b - c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη₀v : η₀ ≤ v - c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsubη : Ioo (c - η₀) (c + η₀) ⊆ Ioo (c - η) (c + η) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hagree : ∀ s ∈ Ioo (c - η₀) (c + η₀),
      W.f ⟨k, hk⟩ (β (Z₀, s)) = W'.f ⟨k, hk'⟩ (γ' s) := by
    intro s hs
    have hs' := hsubη hs
    have hks := hηk s hs'
    rw [hβγ s hs', href ⟨k, hk⟩ s (hηW hs') (by linarith [hs.2]) ⟨hks.1.le, hks.2.le⟩,
      href' ⟨k, hk'⟩ s ⟨by linarith [hs.1], by linarith [hs.2]⟩ (by linarith [hs.2])
        ⟨hks.1.le, hks.2.le⟩]
  obtain ⟨V₁, hV₁, hZ₀V₁, hV₁V, η₁, hη₁, hη₁le, hη₁W', β₁, hβ₁, hgeo₁, hβ₁γ', hβ₁f⟩ :=
    exists_transfer_family W W' hk hk' hη₀pos (fun s hs => hηW (hsubη hs))
      ⟨hc, hcc'.trans hc'b⟩ (fun r hr => hηk r (hsubη hr)) hV hZ₀V
      (hβ.mono (prod_mono subset_rfl hsubη)) (fun Z hZ s hs => hgeo Z hZ s (hsubη hs)) hagree
  have hcK₀ : c ∈ Ioo (c - η₁) (c + η₁) := ⟨by linarith, by linarith⟩
  have hcb : uIcc c c' ⊆ Ioo W'.a W'.b := by
    rw [uIcc_of_le hcc'.le]
    exact fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨V₂, hV₂, hZ₀V₂, hV₂V₁, K, hK, hKc, hK₀K, hc'K, hKJ, β₂, hβ₂, hgeo₂, hβ₂γ', hβ₂β₁⟩ :=
    exists_lRegularizedGeodesicFamily_along W'.S W'.solution T isOpen_Ioo hγ' hV₁ hZ₀V₁
      isOpen_Ioo isPreconnected_Ioo hη₁W' hβ₁ hgeo₁ hβ₁γ' hcK₀ hcb
  have hc'pos : 0 < c' := hcpos.trans hcc'
  have hc'0 : 0 ≤ T - c' ^ 2 := by
    have h1 := H.time_le_of_mem_stageDomain W'.lower
    have h2 : c' ^ 2 < W'.b ^ 2 := pow_lt_pow_left₀ hc'b hc'pos.le two_ne_zero
    linarith [H.time_nonneg lo']
  have hc'h : T - c' ^ 2 < H.horizon := by
    have h1 := (H.le_stageEndTime_of_mem_stageDomain W'.upper).trans
      (H.stageEndTime_le_horizon hi')
    have h2 : W'.a ^ 2 < c' ^ 2 := pow_lt_pow_left₀ (hc.trans hcc') W'.nonneg two_ne_zero
    linarith
  obtain ⟨k', η₂, hη₂, -, hη₂k'⟩ := exists_stage_nhds hc'pos hc'0 hc'h hne
  have hkc' := hη₂k' c' ⟨by linarith, by linarith⟩
  have hk'' : lo' ≤ k' ∧ k' ≤ hi' :=
    LWindow.mem_range_of_mem_Icc W' ⟨hc.trans hcc', hc'b⟩ ⟨hkc'.1.le, hkc'.2.le⟩
  have hk'k : k' ≤ k := by
    by_contra h
    have h1 := stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 : c ^ 2 < c' ^ 2 := pow_lt_pow_left₀ hcc' hcpos.le two_ne_zero
    linarith [hkc.2, hkc'.1]
  obtain ⟨η₃, hη₃, hball⟩ := Metric.isOpen_iff.1 hK c' hc'K
  set η' := min (min η₂ η₃) (c' - c) with hη'def
  have hη'pos : 0 < η' := lt_min (lt_min hη₂ hη₃) (by linarith)
  have hη'₂ : η' ≤ η₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hη'₃ : η' ≤ η₃ := (min_le_left _ _).trans (min_le_right _ _)
  have hη'c : η' ≤ c' - c := min_le_right _ _
  have hη'K : Ioo (c' - η') (c' + η') ⊆ K := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hs.1, hs.2])
  have hη'k' : ∀ r ∈ Ioo (c' - η') (c' + η'),
      T - r ^ 2 ∈ Ioo (H.time k') (H.stageEndTime k') :=
    fun r hr => hη₂k' r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let A' : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z j r => if r ≤ c then A Z j r else
      if h : lo' ≤ j.val ∧ j.val ≤ hi' then W'.f ⟨j.val, h⟩ (β₂ (Z, r)) else A Z j r
  have hA'le : ∀ Z j r, r ≤ c → A' Z j r = A Z j r := fun Z j r h => ite_eq_left h
  have hA'gt : ∀ Z (j : H.StageInterval first last) r (h : lo' ≤ j.val ∧ j.val ≤ hi'), c < r →
      A' Z j r = W'.f ⟨j.val, h⟩ (β₂ (Z, r)) := fun Z j r h hr => by
    change (if r ≤ c then A Z j r else
      if h : lo' ≤ j.val ∧ j.val ≤ hi' then W'.f ⟨j.val, h⟩ (β₂ (Z, r)) else A Z j r) = _
    rw [ite_eq_right (not_le.2 hr), dite_eq_left h]
  have hcore : ∀ Z ∈ V₂, ∀ r ∈ Ioc (c - η₁) c,
      A Z ⟨k, hlo.trans hk.1, hk.2.trans hhi⟩ r = W'.f ⟨k, hk'⟩ (β₂ (Z, r)) := by
    intro Z hZ r hr
    have hr₁ : r ∈ Ioo (c - η₁) (c + η₁) := ⟨hr.1, by linarith [hr.2]⟩
    have hrη : r ∈ Ioc (c - η) c := ⟨by linarith [hr.1], hr.2⟩
    rw [hAβ Z (hV₁V (hV₂V₁ hZ)) r hrη, hβ₂β₁ Z hZ r hr₁, hβ₁f Z (hV₂V₁ hZ) r hr₁]
  refine ⟨V₂, hV₂, hZ₀V₂, A', fun Z hZ => ?_, lo', hi', hlo', hhi', W', γ',
    ⟨hc.trans hcc', hc'b⟩, hγ', href', k', hk'', η', hη'pos, fun s hs => hKJ (hη'K hs), hη'k',
    β₂, hβ₂.mono (prod_mono subset_rfl hη'K), fun Z hZ s hs => hgeo₂ Z hZ s (hη'K hs),
    fun s hs => hβ₂γ' s (hη'K hs), fun Z hZ r hr => hA'gt Z _ r hk'' (by linarith [hr.1])⟩
  have hZV : Z ∈ V := hV₁V (hV₂V₁ hZ)
  refine isHistoryLGeodesicPrefix_congr hcc'.le (hA Z hZV) (fun i hf hl h1 h2 => ?_)
    (fun s hs => ?_) (fun j r hr => hA'le Z j r hr)
  · rcases eq_or_lt_of_le h1 with h | h
    · exfalso
      have hwpos : 0 < Real.sqrt (T - H.time i.succ) := h ▸ hcpos
      have hT : T - c ^ 2 = H.time i.succ := by
        rw [h, Real.sq_sqrt (Real.sqrt_pos.1 hwpos).le]
        ring
      have hik := eq_of_mem_Ioo_of_mem_Icc hkc
        (show T - c ^ 2 ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
          by rw [hT]; exact ⟨le_rfl, H.time_le_stageEndTime _⟩)
      rw [hT, hik] at hkc
      exact lt_irrefl _ hkc.1
    · have hwpos : 0 < Real.sqrt (T - H.time i.succ) := hcpos.trans h
      have hT : T - Real.sqrt (T - H.time i.succ) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt (Real.sqrt_pos.1 hwpos).le]
        ring
      have hwW : Real.sqrt (T - H.time i.succ) ∈ Ioo W'.a W'.b := ⟨hc.trans h, h2.trans hc'b⟩
      have hold := LWindow.mem_range_of_mem_Icc W' hwW (j := i.castSucc) (by
        rw [hT, stageEndTime_castSucc]
        exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
      have hnew := LWindow.mem_range_of_mem_Icc W' hwW (j := i.succ) (by
        rw [hT]
        exact ⟨le_rfl, H.time_le_stageEndTime _⟩)
      rw [hA'gt Z _ _ hold h, hA'gt Z _ _ hnew h]
      exact W'.crossing i hold.1 hnew.2 _
  · have hlow : c - η₁ / 2 ∈ Ioo (c - η₁) (c + η₁) := ⟨by linarith, by linarith⟩
    have hlowη : c - η₁ / 2 ∈ Ioo (c - η) (c + η) :=
      ⟨by linarith [hη₁le, hη₀le], by linarith⟩
    have hup : T - (c - η₁ / 2) ^ 2 ∈ H.stageDomain k :=
      H.mem_stageDomain_of_mem_Ioo (hηk _ hlowη)
    have hdown : T - c' ^ 2 ∈ H.stageDomain k' := H.mem_stageDomain_of_mem_Ioo hkc'
    refine ⟨k', k, hlo'.trans hk''.1, hk'.2.trans hhi',
      W'.restrict hk''.1 hk'.2 hk'k (hη₁W' hlow).1.le (show c - η₁ / 2 < c' by linarith)
        hc'b.le hup hdown, ⟨show c - η₁ / 2 < s by linarith [hs.1], hs.2⟩, le_rfl,
      fun r => β₂ (Z, r),
      fun r hr => hgeo₂ Z hZ r (hKc.Icc_subset (hK₀K hlow) hc'K (Ioo_subset_Icc_self hr)),
      fun j r hr => ?_⟩
    have hrI : r ∈ Icc (c - η₁ / 2) c' := LWindow.piece_subset _ j hr
    have hrt : T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) :=
      LWindow.mem_Icc_of_mem_piece _ j hr
    have hj' : lo' ≤ j.val ∧ j.val ≤ hi' :=
      ⟨hk''.1.trans j.property.1, j.property.2.trans hk'.2⟩
    change W'.f ⟨j.val, hj'⟩ (β₂ (Z, r)) = _
    rcases le_or_gt r c with hrc | hrc
    · have hrη : r ∈ Ioo (c - η) (c + η) := ⟨by linarith [hrI.1, hη₁le, hη₀le], by linarith⟩
      obtain ⟨jv, hj1, hj2⟩ := j
      have hjk : jv = k := eq_of_mem_Ioo_of_mem_Icc (hηk r hrη) hrt
      subst hjk
      rw [hA'le Z _ r hrc]
      exact (hcore Z hZ r ⟨by linarith [hrI.1], hrc⟩).symm
    · rw [hA'gt Z _ r hj' hrc]

end StepFamily

section BaseFamily

variable {first last : Fin (H.eventCount + 1)} {T v : ℝ} {p : (H.stage last).Carrier}
  {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_hasPrefixFamily_base {Z₀ : ThreeSpace} (hv : 0 < v)
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hZ₀ : H.HasHistoryLInitialVector T α₀ p Z₀) :
    ∃ c₁, 0 < c₁ ∧ c₁ < v ∧ H.HasPrefixFamily T v p α₀ Z₀ c₁ := by
  classical
  obtain ⟨lo₀, hlo₀, W₀, x, Zx₀, ha₀, hx, hZx₀, hdom, heq₀⟩ := hZ₀
  have hb₀ : 0 < W₀.b := ha₀ ▸ W₀.lt
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V', hV', hZV', K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W₀.S W₀.solution T hJo hJc h0J hbJ hcurve
  have hIcc : Icc 0 W₀.b ⊆ K := hKc.Icc_subset h0K hbK
  obtain ⟨c₁, hc₁, hne⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) (lt_min hb₀ hv) le_rfl
  have hc₁b : c₁ < W₀.b := hc₁.2.trans_le (min_le_left _ _)
  have hc₁v : c₁ < v := hc₁.2.trans_le (min_le_right _ _)
  have hTup : T - 0 ^ 2 ∈ H.stageDomain last := by
    have h := W₀.upper
    rwa [ha₀] at h
  have hT0 : T ∈ H.stageDomain last := by simpa using hTup
  have hc₁0 : 0 ≤ T - c₁ ^ 2 := by
    have := H.time_le_of_mem_stageDomain hlower
    have h2 : c₁ ^ 2 < v ^ 2 := pow_lt_pow_left₀ hc₁v hc₁.1.le two_ne_zero
    linarith [H.time_nonneg first]
  have hc₁h : T - c₁ ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT0).trans (H.stageEndTime_le_horizon last)
    have : 0 < c₁ ^ 2 := pow_pos hc₁.1 2
    linarith
  obtain ⟨k₀, η, hη, hηc, hηk⟩ := exists_stage_nhds hc₁.1 hc₁0 hc₁h hne
  have hkc := hηk c₁ ⟨by linarith, by linarith⟩
  have hc₁a : W₀.a < c₁ := by rw [ha₀]; exact hc₁.1
  have hk₀ : lo₀ ≤ k₀ ∧ k₀ ≤ last :=
    LWindow.mem_range_of_mem_Icc W₀ ⟨hc₁a, hc₁b⟩ ⟨hkc.1.le, hkc.2.le⟩
  set η₀ := min η (W₀.b - c₁) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by linarith)
  have hη₀η : η₀ ≤ η := min_le_left _ _
  have hη₀b : η₀ ≤ W₀.b - c₁ := min_le_right _ _
  have hsub : Ioo (c₁ - η₀) (c₁ + η₀) ⊆ Ioo W₀.a W₀.b := fun s hs => by
    rw [ha₀]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsubK : Ioo (c₁ - η₀) (c₁ + η₀) ⊆ K := fun s hs => hIcc ⟨by linarith [hs.1], by
    linarith [hs.2]⟩
  let e := (W₀.localDiffeomorph ⟨last, W₀.le, le_rfl⟩).mfderivToContinuousLinearEquiv
    (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩ x) →L[ℝ]
      TangentSpace ThreeModel x)
  have hLe : ∀ Z : ThreeSpace, mfderiv ThreeModel ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩) x
      (L Z) = Z := fun Z => e.apply_symm_apply Z
  have hLZ₀ : L Z₀ = Zx₀ := by
    have h : e Zx₀ = Z₀ := hZx₀
    have h2 : e.symm (e Zx₀) = Zx₀ := e.symm_apply_apply Zx₀
    rw [h] at h2
    exact h2
  let V : Set ThreeSpace := L ⁻¹' V'
  have hV : IsOpen V := hV'.preimage L.continuous
  have hZ₀V : Z₀ ∈ V := by
    change L Z₀ ∈ V'
    rw [hLZ₀]
    exact hZV'
  let β₀ : ThreeSpace × ℝ → W₀.X := fun q => fam (L q.1, q.2)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (V ×ˢ K) := by
    have hmap : ContMDiff (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ThreeSpace × ℝ => (L q.1, q.2)) :=
      (L.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact hfam.comp hmap.contMDiffOn fun q hq => ⟨hq.1, hq.2⟩
  have hcurveZ : ∀ Z ∈ V, IsLRegularizedCurveOn W₀.S T (fun s => β₀ (Z, s)) K x (L Z) :=
    fun Z hZ => hfamc (L Z) hZ
  let A : ThreeSpace → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z j r => if h : r ≤ c₁ ∧ lo₀ ≤ j.val then W₀.f ⟨j.val, h.2, j.property.2⟩ (β₀ (Z, r))
      else α₀ j r
  have hA : ∀ Z (j : H.StageInterval first last) r (h : r ≤ c₁ ∧ lo₀ ≤ j.val),
      A Z j r = W₀.f ⟨j.val, h.2, j.property.2⟩ (β₀ (Z, r)) := fun Z j r h => dite_eq_left h
  have hup0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := hTup
  have hdown : T - c₁ ^ 2 ∈ H.stageDomain k₀ := H.mem_stageDomain_of_mem_Ioo hkc
  have hTlast : H.time last ≤ T := H.time_le_of_mem_stageDomain hT0
  refine ⟨c₁, hc₁.1, hc₁v, V, hV, hZ₀V, A, fun Z hZ => ?_, lo₀, last, hlo₀, le_rfl, W₀,
    lRegularizedCurve W₀.S T x Zx₀, ⟨hc₁a, hc₁b⟩, ?_, ?_, k₀, hk₀, η₀, hη₀, hsub,
    fun r hr => hηk r ⟨by linarith [hr.1], by linarith [hr.2]⟩, β₀,
    hβ₀.mono (prod_mono subset_rfl hsubK), fun Z hZ s hs => (hcurveZ Z hZ).2.2 s (hsubK hs),
    fun s hs => ?_, fun Z hZ r hr => hA Z _ r ⟨hr.2, hk₀.1⟩⟩
  · let W'' := W₀.restrict hk₀.1 le_rfl hk₀.2 (by rw [ha₀]) hc₁.1 hc₁b.le hup0 hdown
    refine ⟨fun i hf hl hw => ?_, fun s hs => ?_, k₀, hlo₀.trans hk₀.1, W'', x, L Z, rfl,
      le_rfl, hx, hLe Z, ⟨fun s => β₀ (Z, s), K, hK, hKc, h0K, hIcc ⟨hc₁.1.le, hc₁b.le⟩,
        hcurveZ Z hZ⟩, fun j r hr => ?_⟩
    · have hsq : T - Real.sqrt (T - H.time i.succ) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt (by linarith [H.time_strictMono.monotone hl])]
        ring
      have hold : lo₀ ≤ i.castSucc := lo_le_of_lt_b W₀ (Real.sqrt_nonneg _) (hw.trans hc₁b)
        (by rw [hsq, stageEndTime_castSucc])
      have hnew : lo₀ ≤ i.succ := hold.trans i.castSucc_lt_succ.le
      rw [hA Z _ _ ⟨hw.le, hold⟩, hA Z _ _ ⟨hw.le, hnew⟩]
      exact W₀.crossing i hold hl _
    · refine ⟨k₀, last, hlo₀.trans hk₀.1, le_rfl, W'', hs, le_rfl, fun r => β₀ (Z, r),
        fun r hr => (hcurveZ Z hZ).2.2 r (hIcc ⟨hr.1.le, hr.2.le.trans hc₁b.le⟩),
        fun j r hr => ?_⟩
      have hrI : r ∈ Icc 0 c₁ := LWindow.piece_subset _ j hr
      change W₀.f ⟨j.val, hk₀.1.trans j.property.1, j.property.2⟩ (β₀ (Z, r)) = _
      rw [hA Z _ r ⟨hrI.2, hk₀.1.trans j.property.1⟩]
    · have hrI : r ∈ Icc 0 c₁ := LWindow.piece_subset W'' j hr
      have hcur := lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hcurveZ Z hZ)
        (hIcc ⟨hrI.1, hrI.2.trans hc₁b.le⟩)
      change W₀.f ⟨j.val, hk₀.1.trans j.property.1, j.property.2⟩
        (lRegularizedCurve W₀.S T x (L Z) r) = _
      rw [hcur, hA Z _ r ⟨hrI.2, hk₀.1.trans j.property.1⟩]
  · intro s hs
    rw [ha₀] at hs
    have hsJ : s ∈ J := hJc.Icc_subset h0J hbJ (Ioo_subset_Icc_self hs)
    exact isLRegularizedGeodesicOn_lRegularizedCurve W₀.S W₀.solution T x Zx₀ s
      ⟨α, J, hJo, hJc, h0J, hsJ, hcurve⟩
  · intro j r hr hrv ht
    have hr' : r ∈ Icc (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T W₀.b j.val) := by
      rw [ha₀] at hr
      exact mem_regularizedStage_Icc le_rfl ⟨hr.1.le, hr.2.le⟩ ht
    exact heq₀ j hr'
  · change fam (L Z₀, s) = lRegularizedCurve W₀.S T x Zx₀ s
    rw [hLZ₀]
    exact (lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hfamc Zx₀ hZV')
      (hsubK hs)).symm

end BaseFamily

section OpenDomain

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

variable (H) in
def historyLExpOpenDomain (hle : first ≤ last) (T v : ℝ) (p : (H.stage last).Carrier) :
    Set (TangentSpace ThreeModel p) :=
  {Z | ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
    H.IsHistoryLGeodesicOn hle T v α ∧ H.HasHistoryLInitialVector T α p Z ∧
    ∃ W : H.LWindow first first T, v ∈ Ioo W.a W.b ∧ ∃ γ : ℝ → W.X,
      IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
      EqOn (W.f ⟨first, le_rfl, le_rfl⟩ ∘ γ) (α ⟨first, le_rfl, hle⟩) (Ioc W.a v)}

theorem historyLExpOpenDomain_subset_historyLExpDomain :
    H.historyLExpOpenDomain hle T v p ⊆ H.historyLExpDomain hle T v p :=
  fun _ ⟨α, hα, hZ, _⟩ => ⟨α, hα, hZ⟩

private theorem mem_Ioo_of_mem_Ioo_window (W : H.LWindow first first T) (hv : v ∈ Ioo W.a W.b) :
    T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
  have h1 : W.a ^ 2 < v ^ 2 := pow_lt_pow_left₀ hv.1 W.nonneg two_ne_zero
  have h2 : v ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hv.2 (W.nonneg.trans hv.1.le) two_ne_zero
  exact ⟨(H.time_le_of_mem_stageDomain W.lower).trans_lt (by linarith),
    lt_of_lt_of_le (by linarith) (H.le_stageEndTime_of_mem_stageDomain W.upper)⟩

private theorem not_mem_range_of_mem_Ioo {t : ℝ} {k : Fin (H.eventCount + 1)}
    (ht : t ∈ Ioo (H.time k) (H.stageEndTime k)) : t ∉ range H.time := by
  rintro ⟨j, rfl⟩
  have h := eq_of_mem_Ioo_of_mem_Icc ht ⟨le_rfl, H.time_le_stageEndTime j⟩
  subst h
  exact lt_irrefl _ ht.1

private theorem hasPrefixFamily_end (hv : 0 < v)
    {α₀ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier} {Z₀ : ThreeSpace}
    (hα₀ : H.IsHistoryLGeodesicOn hle T v α₀) (hZ₀ : H.HasHistoryLInitialVector T α₀ p Z₀)
    (W : H.LWindow first first T) (hvW : v ∈ Ioo W.a W.b) (γ : ℝ → W.X)
    (hγ : IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b))
    (hγα : EqOn (W.f ⟨first, le_rfl, le_rfl⟩ ∘ γ) (α₀ ⟨first, le_rfl, hle⟩) (Ioc W.a v)) :
    H.HasPrefixFamily T v p α₀ Z₀ v := by
  obtain ⟨c₁, hc₁, hc₁v, hP₁⟩ := exists_hasPrefixFamily_base hv hα₀.1 hZ₀
  set S : Set ℝ := {c | c ≤ v ∧ H.HasPrefixFamily T v p α₀ Z₀ c} with hSdef
  have hSne : S.Nonempty := ⟨c₁, hc₁v.le, hP₁⟩
  have hSbdd : BddAbove S := ⟨v, fun c hc => hc.1⟩
  have hsv : sSup S ≤ v := csSup_le hSne fun c hc => hc.1
  have hc₁s : c₁ ≤ sSup S := le_csSup hSbdd ⟨hc₁v.le, hP₁⟩
  have key : ∀ {lo' hi' : Fin (H.eventCount + 1)} (hlo' : first ≤ lo') (hhi' : hi' ≤ last)
      (W' : H.LWindow lo' hi' T) (γ' : ℝ → W'.X),
      IsLRegularizedGeodesicOn W'.S T γ' (Ioo W'.a W'.b) →
      (∀ j : H.StageInterval lo' hi', ∀ r ∈ Ioo W'.a W'.b, r ≤ v →
        T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
        W'.f j (γ' r) = α₀ ⟨j.val, hlo'.trans j.property.1, j.property.2.trans hhi'⟩ r) →
      W'.a < sSup S → ∀ c' ∈ Ioo (sSup S) W'.b, c' ≤ v → T - c' ^ 2 ∉ range H.time →
      H.HasPrefixFamily T v p α₀ Z₀ c' := by
    intro lo' hi' hlo' hhi' W' γ' hγ' href' ha c' hc' hc'v hne
    obtain ⟨c, hcS, hac⟩ := exists_lt_of_lt_csSup hSne ha
    exact hasPrefixFamily_step hcS.2 hlo' hhi' W' γ' hγ' href' hac
      ((le_csSup hSbdd hcS).trans_lt hc'.1) hc'.2 hc'v hne
  have hsvEq : sSup S = v := by
    by_contra hne'
    have hlt : sSup S < v := lt_of_le_of_ne hsv hne'
    have hs0 : 0 < sSup S := hc₁.trans_le hc₁s
    obtain ⟨lo', hi', hlo', hhi', W', hsW', hbv, γ', hγ', heq'⟩ := hα₀.2.2.1 (sSup S) ⟨hs0, hlt⟩
    obtain ⟨c', hc', hne⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) hsW'.2 hs0.le
    have hc'v : c' ≤ v := hc'.2.le.trans hbv
    have hP := key hlo' hhi' W' γ' hγ' (fun j r hr _ ht => heq' j
      (mem_regularizedStage_Icc W'.nonneg ⟨hr.1.le, hr.2.le⟩ ht)) hsW'.1 c' hc' hc'v hne
    exact absurd (le_csSup hSbdd ⟨hc'v, hP⟩) (not_le.2 hc'.1)
  have hne : T - v ^ 2 ∉ range H.time :=
    not_mem_range_of_mem_Ioo (mem_Ioo_of_mem_Ioo_window W hvW)
  have haS : W.a < sSup S := by rw [hsvEq]; exact hvW.1
  obtain ⟨c, hcS, hac⟩ := exists_lt_of_lt_csSup hSne haS
  rcases eq_or_lt_of_le hcS.1 with h | h
  · have hP := hcS.2
    rwa [h] at hP
  · refine hasPrefixFamily_step hcS.2 le_rfl hle W γ hγ (fun j r hr hrv _ => ?_) hac h hvW.2 le_rfl
      hne
    obtain ⟨jv, h1, h2⟩ := j
    obtain rfl : jv = first := le_antisymm h2 h1
    exact hγα ⟨hr.1, hrv⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_nhds_contMDiffOn_historyLExp (hv : 0 < v) {Z₀ : TangentSpace ThreeModel p}
    (hZ₀ : Z₀ ∈ H.historyLExpOpenDomain hle T v p) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ H.historyLExpOpenDomain hle T v p ∧
      ∃ g : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ g V ∧
        ∀ Z ∈ V, ∀ hZ : Z ∈ H.historyLExpDomain hle T v p,
          H.historyLExp hle T v p ⟨Z, hZ⟩ = g Z := by
  obtain ⟨α₀, hα₀, hinit, W, hvW, γ, hγ, hγα⟩ := hZ₀
  obtain ⟨V, hV, hZ₀V, A, hA, lo, hi, hlo, hhi, Wv, γv, -, -, -, k, hk, η, hη, hηW, hηk, β, hβ,
    hgeo, -, hAβ⟩ := hasPrefixFamily_end hv hα₀ hinit W hvW γ hγ hγα
  have hvk := hηk v ⟨by linarith, by linarith⟩
  have hfk : first = k := eq_of_mem_Ioo_of_mem_Icc hvk
    ⟨H.time_le_of_mem_stageDomain hα₀.1, H.le_stageEndTime_of_mem_stageDomain hα₀.1⟩
  subst hfk
  have hβv : ∀ Z ∈ V, ContinuousAt (fun r => β (Z, r)) v := fun Z hZ =>
    (((hβ (Z, v) ⟨hZ, by constructor <;> linarith⟩).contMDiffAt
      ((hV.prod isOpen_Ioo).mem_nhds ⟨hZ, by constructor <;> linarith⟩)).comp v
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  have hmem : ∀ Z ∈ V, H.IsHistoryLGeodesicOn hle T v (A Z) ∧
      H.HasHistoryLInitialVector T (A Z) p Z ∧
      ∃ W : H.LWindow first first T, v ∈ Ioo W.a W.b ∧ ∃ γ : ℝ → W.X,
        IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
        EqOn (W.f ⟨first, le_rfl, le_rfl⟩ ∘ γ) (A Z ⟨first, le_rfl, hle⟩) (Ioc W.a v) := by
    intro Z hZ
    obtain ⟨hcross, hwin, lo₀, hlo₀, W₀, x, Zx, ha₀, -, hx, hZx, hdom, hbase⟩ := hA Z hZ
    refine ⟨⟨hα₀.1, fun i hf hl => hcross i hf hl ?_, hwin, ?_⟩,
      ⟨lo₀, hlo₀, W₀, x, Zx, ha₀, hx, hZx, hdom, hbase⟩, ?_⟩
    · have h1 : H.stageEndTime first ≤ H.time i.succ := by
        rw [← stageEndTime_castSucc]
        exact H.stageEndTime_mono hf
      exact (Real.sqrt_lt' hv).2 (by linarith [hvk.2])
    · have hg : ContinuousAt (fun r => Wv.f ⟨first, hk⟩ (β (Z, r))) v :=
        (Wv.localDiffeomorph _).contMDiff.continuous.continuousAt.comp (hβv Z hZ)
      refine hg.continuousWithinAt.congr_of_eventuallyEq ?_ (hAβ Z hZ v ⟨by linarith, le_rfl⟩)
      filter_upwards [Ioo_mem_nhdsLT (show v - η < v by linarith)] with r hr
      exact hAβ Z hZ r ⟨hr.1, hr.2.le⟩
    · have hl : v - η / 2 ∈ Ioo (v - η) (v + η) := ⟨by linarith, by linarith⟩
      have hu : v + η / 2 ∈ Ioo (v - η) (v + η) := ⟨by linarith, by linarith⟩
      refine ⟨Wv.restrict hk.1 hk.2 le_rfl (hηW hl).1.le (by linarith) (hηW hu).2.le
          (H.mem_stageDomain_of_mem_Ioo (hηk _ hl)) (H.mem_stageDomain_of_mem_Ioo (hηk _ hu)),
        show v - η / 2 < v ∧ v < v + η / 2 from ⟨by linarith, by linarith⟩,
        fun r => β (Z, r), fun r (hr : r ∈ Ioo (v - η / 2) (v + η / 2)) =>
          hgeo Z hZ r ⟨by linarith [hr.1], by linarith [hr.2]⟩,
        fun r (hr : r ∈ Ioc (v - η / 2) v) => (hAβ Z hZ r ⟨by linarith [hr.1], hr.2⟩).symm⟩
  refine ⟨V, hV, hZ₀V, fun Z hZ => ⟨A Z, hmem Z hZ⟩, fun Z => Wv.f ⟨first, hk⟩ (β (Z, v)), ?_,
    fun Z hZ hZ' => ?_⟩
  · exact (Wv.localDiffeomorph _).contMDiff.comp_contMDiffOn (hβ.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      fun Z hZ => ⟨hZ, by constructor <;> linarith⟩)
  · rw [historyLExp_eq hv ⟨Z, hZ'⟩ (hmem Z hZ).1 (hmem Z hZ).2.1]
    exact hAβ Z hZ v ⟨by linarith, le_rfl⟩

theorem isOpen_historyLExpOpenDomain (hv : 0 < v) : IsOpen (H.historyLExpOpenDomain hle T v p) :=
  isOpen_iff_forall_mem_open.2 fun _ hZ =>
    let ⟨V, hV, hZV, hVsub, _⟩ := exists_nhds_contMDiffOn_historyLExp hv hZ
    ⟨V, hVsub, hV, hZV⟩

theorem exists_contMDiffOn_historyLExp (hv : 0 < v) (q : (H.stage first).Carrier) :
    ∃ f : ThreeSpace → (H.stage first).Carrier,
      ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ f (H.historyLExpOpenDomain hle T v p) ∧
      ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), f Z = H.historyLExp hle T v p ⟨Z, hZ⟩ := by
  classical
  refine ⟨fun Z => if hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
    H.historyLExp hle T v p ⟨Z, hZ⟩ else q, fun Z hZ => ?_, fun Z hZ => dite_eq_left hZ⟩
  obtain ⟨V, hV, hZV, hVsub, g, hg, hgeq⟩ := exists_nhds_contMDiffOn_historyLExp hv hZ
  refine (((hg Z hZV).contMDiffAt (hV.mem_nhds hZV)).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hV.mem_nhds hZV] with Z' hZ'
  have hd := historyLExpOpenDomain_subset_historyLExpDomain (hVsub hZ')
  exact (dite_eq_left hd).trans (hgeq Z' hZ' hd)

end OpenDomain

section Minimizer

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v : ℝ}
  {p : (H.stage last).Carrier}

theorem historyMinDomain_subset_historyLExpOpenDomain (hv : 0 < v)
    (hend : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    H.historyMinDomain hle T B v p ⊆ H.historyLExpOpenDomain hle T v p := by
  rintro Z ⟨α, hgeo, hinit, hα, hp, hmin₀, hfin⟩
  have hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v) := by
    rw [hp]
    exact hmin₀
  refine ⟨α, hgeo, hinit, ?_⟩
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hinit
    have h := W₀.upper_mem_Icc
    rwa [ha₀] at h
  have hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)) := fun i hf hl => by
    obtain ⟨z, -, h1, h2⟩ := hgeo.2.1 i hf hl
    exact ⟨z, h1, h2⟩
  have hopen : IsOpen ((fun r : ℝ => T - r ^ 2) ⁻¹' Ioo (H.time first) (H.stageEndTime first)) :=
    isOpen_Ioo.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen v hend
  set δ := min ε v / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hδε : δ < ε := by linarith [min_le_left ε v]
  have hδv : δ < v := by linarith [min_le_right ε v]
  have hin : ∀ r, v - δ ≤ r → r ≤ v + δ → T - r ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) :=
    fun r h1 h2 => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith)
  have hlo := hin (v - δ) le_rfl (by linarith)
  have hhi := hin (v + δ) (by linarith) le_rfl
  obtain ⟨Wb, hWa, hWb, hr⟩ := LWindow.exists_stage (T := T) first (by linarith : 0 ≤ v - δ)
    (by linarith : v - δ < v + δ) hhi.1 hlo.2
  have hup : T - (v - δ) ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hlo
  have hdown : T - v ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hend
  let Ws := Wb.restrict le_rfl le_rfl le_rfl hWa.le (by linarith : v - δ < v)
    (by rw [hWb]; linarith)
    hup hdown
  have hrange : ∀ j : H.StageInterval first first,
      MapsTo (α ⟨j.val, le_rfl.trans j.property.1, j.property.2.trans hle⟩)
        (Icc (H.regularizedStageStart T Ws.a j.val) (H.regularizedStageEnd T Ws.b j.val))
        (range (Ws.f j)) := fun j r _ => by
    have h : range (Ws.f j) = univ := hr ⟨j.val, j.property⟩
    rw [h]
    exact mem_univ _
  have hua : (0 : ℝ) ≤ Ws.a := show (0 : ℝ) ≤ v - δ by linarith
  have hbv : Ws.b ≤ v := le_rfl
  obtain ⟨γ, hγc, hγ, heq, -⟩ := Ws.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq hle
    le_rfl hle le_rfl hua hbv hupper hgeo.1 hfloor α hα hnode hmin hfin hrange
  obtain ⟨α', hα'γ, e, he, hgeo'⟩ :=
    exists_isLRegularizedGeodesicOn_extension_of_lRegularizedAction_le Ws.S Ws.solution Ws.lt
      Ws.regular γ hγc hγ
      (Ws.intervalIntegrable_lRegularizedLagrangian_of_ne_top le_rfl hle le_rfl hua hbv hupper
        hgeo.1 hfloor α hα hfin γ hγ heq)
      (fun δ' hδ' hδa hδb => Ws.lRegularizedAction_le_of_regularizedCost_eq hle le_rfl hle le_rfl
        hua hbv hupper hgeo.1 hfloor α hα hnode hmin hfin γ hγ heq δ' hδ' hδa hδb)
  set ρ := min (e / 2) δ with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) hδpos
  have hρe : ρ < e := by linarith [min_le_left (e / 2) δ]
  have hρδ : ρ ≤ δ := min_le_right _ _
  have hvρ := hin (v + ρ) (by linarith) (by linarith)
  refine ⟨Wb.restrict le_rfl le_rfl le_rfl hWa.le (by linarith : v - δ < v + ρ)
      (by rw [hWb]; linarith) hup (H.mem_stageDomain_of_mem_Ioo hvρ),
    show v - δ < v ∧ v < v + ρ from ⟨by linarith, by linarith⟩, α',
    fun r (hr : r ∈ Ioo (v - δ) (v + ρ)) => hgeo' r
      (show r ∈ Ioo (v - δ - e) (v + e) from ⟨by linarith [hr.1], by linarith [hr.2]⟩),
    fun r (hr : r ∈ Ioc (v - δ) v) => ?_⟩
  have hrI : r ∈ Icc (v - δ) v := ⟨hr.1.le, hr.2⟩
  have ht := hin r hr.1.le (by linarith [hr.2])
  have hpiece : r ∈ Icc (H.regularizedStageStart T Ws.a first)
      (H.regularizedStageEnd T Ws.b first) :=
    mem_regularizedStage_Icc hua hrI ⟨ht.1.le, ht.2.le⟩
  have h := heq ⟨first, le_rfl, le_rfl⟩ hpiece
  change Wb.f ⟨first, le_rfl, le_rfl⟩ (α' r) = α ⟨first, le_rfl, hle⟩ r
  rw [hα'γ hrI]
  exact h

theorem exists_isOpen_superset_historyMinDomain_contMDiffOn_historyLExp (hv : 0 < v)
    (hend : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (q : (H.stage first).Carrier) :
    ∃ U : Set ThreeSpace, IsOpen U ∧ H.historyMinDomain hle T B v p ⊆ U ∧
      ∃ f : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel 1 f U ∧
        ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), f Z = H.historyLExp hle T v p ⟨Z, hZ⟩ :=
  let ⟨f, hf, hfeq⟩ := exists_contMDiffOn_historyLExp (hle := hle) (p := p) hv q
  ⟨_, isOpen_historyLExpOpenDomain hv, historyMinDomain_subset_historyLExpOpenDomain hv hend hfloor,
    f, hf.of_le (by decide), hfeq⟩

end Minimizer

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
