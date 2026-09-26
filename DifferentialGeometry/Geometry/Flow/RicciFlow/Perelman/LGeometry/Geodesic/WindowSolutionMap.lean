import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedStartCurve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Analysis.ODE.Flow (exists_flow_on)
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Connection (trivToE trivFromE trivToE_trivFromE
  trivFromE_trivToE)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem hasDerivAt_lPhase_fst (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x0 : M)
    {z : ℝ → E × E} {s : ℝ} (h : HasDerivAt z (lPhaseField S T x0 s (z s)) s) :
    HasDerivAt (fun r => (z r).1) (z s).2 s := by
  simpa [lPhaseField, Function.comp_def] using hasFDerivAt_fst.comp_hasDerivAt s h

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem differentiableAt_extChartAt_transition {x0 x1 : M} {y : E}
    (hy : y ∈ (extChartAt I x0).target)
    (hsrc : (extChartAt I x0).symm y ∈ (extChartAt I x1).source) :
    DifferentiableAt ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) y := by
  have h := contDiffWithinAt_ext_coord_change (I := I) (n := ∞) x1 x0 (y := y) ⟨hy, hsrc⟩
  rw [I.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.differentiableAt (by simp)
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem eqOn_of_lPhaseCurve_eqOn (x0 : M) {z z' : ℝ → E × E} {U : Set ℝ}
    (hU : IsOpen U)
    (hz : ∀ s ∈ U, HasDerivAt (fun r => (z r).1) (z s).2 s ∧
      (z s).1 ∈ interior (extChartAt I x0).target)
    (hz' : ∀ s ∈ U, HasDerivAt (fun r => (z' r).1) (z' s).2 s ∧
      (z' s).1 ∈ interior (extChartAt I x0).target)
    (h : EqOn (lPhaseCurve (I := I) x0 z) (lPhaseCurve (I := I) x0 z') U) :
    EqOn z z' U := by
  have h1 : EqOn (fun r => (z r).1) (fun r => (z' r).1) U := by
    intro s hs
    have e := congrArg (extChartAt I x0) (h hs)
    simp only [lPhaseCurve] at e
    rwa [(extChartAt I x0).right_inv (interior_subset (hz s hs).2),
      (extChartAt I x0).right_inv (interior_subset (hz' s hs).2)] at e
  intro s hs
  have hd' := (hz' s hs).1.congr_of_eventuallyEq (h1.eventuallyEq_of_mem (hU.mem_nhds hs))
  exact Prod.ext (h1 hs) ((hz s hs).1.unique hd')

theorem exists_lPhaseFlow_of_regular (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x0 : M) {s0 : ℝ} (z0 : E × E)
    (hT : T - s0 ^ 2 ∈ D.regular) (hz0 : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × (E × E)), IsOpen W ∧ (s0, z0) ∈ W ∧
      W ⊆ Ioo (s0 - ε) (s0 + ε) ×ˢ univ ∧
      ∃ Ψ : (ℝ × (E × E)) × ℝ → E × E,
        (∀ p ∈ W, Ψ (p, p.1) = p.2) ∧
        ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (s0 - ε) (s0 + ε)) ∧
        ∀ p ∈ W, ∀ s ∈ Ioo (s0 - ε) (s0 + ε),
          HasDerivAt (fun r => Ψ (p, r)) (lPhaseField S T x0 s (Ψ (p, s))) s ∧
            T - s ^ 2 ∈ D.regular ∧ (Ψ (p, s)).1 ∈ interior (extChartAt I x0).target := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Ω : Set (ℝ × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ D.regular ∧ p.2.1 ∈ interior (extChartAt I x0).target}
  have hΩ : IsOpen Ω :=
    (D.regular_isOpen.preimage (continuous_const.sub (continuous_fst.pow 2))).inter
      (isOpen_interior.preimage continuous_snd.fst)
  let vf : ℝ × (E × E) → ℝ × (E × E) := fun p => ((1 : ℝ), lPhaseField S T x0 p.1 p.2)
  have hvf : ContDiffOn ℝ ∞ vf Ω := by
    intro p hp
    change ContDiffWithinAt ℝ ∞
      (fun q : ℝ × (E × E) => ((1 : ℝ), Function.uncurry (lPhaseField S T x0) q)) Ω p
    exact (contDiffAt_const.prodMk (lPhaseField_smoothAt S hS T x0 hp.1 hp.2)).contDiffWithinAt
  let p0 : ℝ × (E × E) := (s0, z0)
  have hp0 : p0 ∈ Ω := ⟨hT, hz0⟩
  obtain ⟨ε₀, hε₀, hlocal⟩ :=
    exists_flow_on hΩ hvf isCompact_singleton (singleton_subset_iff.mpr hp0)
  obtain ⟨W₀, hW₀, hp0W₀, Ψ₀, hΨ₀0, hΨ₀sm, hΨ₀d, hΨ₀m⟩ := hlocal p0 (mem_singleton p0)
  have htime : ∀ q ∈ W₀, ∀ r ∈ Ioo (-ε₀) ε₀, (Ψ₀ (q, r)).1 = q.1 + r := by
    intro q hq
    have hzero : (0 : ℝ) ∈ Ioo (-ε₀) ε₀ := ⟨by linarith, hε₀⟩
    let phi : ℝ → ℝ := fun r => (Ψ₀ (q, r)).1 - q.1
    have hphi : ∀ r ∈ Ioo (-ε₀) ε₀, HasDerivAt phi 1 r := by
      intro r hr
      have hfst := hasFDerivAt_fst.comp_hasDerivAt r (hΨ₀d q hq r hr)
      simpa [phi, vf, Function.comp_def] using hfst.sub_const q.1
    have hphi0 : phi 0 = 0 := by
      simp only [phi, hΨ₀0 q hq, sub_self]
    intro r hr
    have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
      phi hzero hphi hphi0 r hr
    simp only [phi] at h
    linarith
  let W : Set (ℝ × (E × E)) := W₀ ∩ Ioo (s0 - ε₀ / 2) (s0 + ε₀ / 2) ×ˢ univ
  have hrel : ∀ p ∈ W, ∀ s ∈ Ioo (s0 - ε₀ / 2) (s0 + ε₀ / 2), s - p.1 ∈ Ioo (-ε₀) ε₀ := by
    intro p hp s hs
    have h1 := hp.2.1
    constructor <;> linarith [h1.1, h1.2, hs.1, hs.2]
  refine ⟨ε₀ / 2, by positivity, W, hW₀.inter (isOpen_Ioo.prod isOpen_univ),
    ⟨hp0W₀, ⟨by linarith, by linarith⟩, mem_univ _⟩, inter_subset_right,
    fun q => (Ψ₀ (q.1, q.2 - q.1.1)).2, ?_, ?_, ?_⟩
  · intro p hp
    simp only [sub_self, hΨ₀0 p hp.1]
  · have hlift : ContDiff ℝ ∞ (fun q : (ℝ × (E × E)) × ℝ => (q.1, q.2 - q.1.1)) :=
      contDiff_fst.prodMk (contDiff_snd.sub contDiff_fst.fst)
    have hmaps : MapsTo (fun q : (ℝ × (E × E)) × ℝ => (q.1, q.2 - q.1.1))
        (W ×ˢ Ioo (s0 - ε₀ / 2) (s0 + ε₀ / 2)) (W₀ ×ˢ Ioo (-ε₀) ε₀) :=
      fun q hq => ⟨hq.1.1, hrel q.1 hq.1 q.2 hq.2⟩
    exact (hΨ₀sm.comp hlift.contDiffOn hmaps).snd
  · intro p hp s hs
    have hr := hrel p hp s hs
    have hts : (Ψ₀ (p, s - p.1)).1 = s := by
      rw [htime p hp.1 _ hr]
      ring
    obtain ⟨hm1, hm2⟩ : Ψ₀ (p, s - p.1) ∈ Ω := hΨ₀m ⟨hp.1, hr⟩
    rw [hts] at hm1
    refine ⟨?_, hm1, hm2⟩
    have hd := (hΨ₀d p hp.1 _ hr).comp_sub_const s p.1
    have hsnd := hasFDerivAt_snd.comp_hasDerivAt s hd
    have hval : (vf (Ψ₀ (p, s - p.1))).2 = lPhaseField S T x0 s (Ψ₀ (p, s - p.1)).2 := by
      change lPhaseField S T x0 (Ψ₀ (p, s - p.1)).1 _ = _
      rw [hts]
    simpa [Function.comp_def, hval] using hsnd

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isLRegularizedGeodesicOn_lRegularizedCurve (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M) (Z : TangentSpace I x) :
    IsLRegularizedGeodesicOn S T (lRegularizedCurve S T x Z) (lRegularizedDomain S T x Z) := by
  intro r hr
  obtain ⟨J, hJ, hJc, h0J, hrJ, hα⟩ := lRegularizedChosen_spec S T x Z hr
  have heq := lRegularizedCurve_eqOn S hS T hJ hJc h0J hα
  have hone : IsLRegularizedGeodesicOn S T (lRegularizedChosen S T x Z hr) {r} := by
    intro s hs
    rw [mem_singleton_iff.mp hs]
    exact hα.2.2 r hrJ
  refine hone.congr_of_eventuallyEq (fun s hs => ?_) r rfl
  rw [mem_singleton_iff.mp hs]
  exact heq.eventuallyEq_of_mem (hJ.mem_nhds hrJ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x0 : M) {α : ℝ → M} {J K : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (hα : IsLRegularizedGeodesicOn S T α J)
    {z : ℝ → E × E} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hz : ∀ s ∈ K, HasDerivAt z (lPhaseField S T x0 s (z s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x0).target)
    {s₁ : ℝ} (hs₁J : s₁ ∈ J) (hs₁K : s₁ ∈ K) (hsrc : α s₁ ∈ (chartAt H x0).source)
    (hzs₁ : z s₁ = (extChartAt I x0 (α s₁),
      trivToE (I := I) x0 (α s₁) (lVelocity (I := I) α s₁))) :
    EqOn α (lPhaseCurve (I := I) x0 z) (J ∩ K) := by
  have hq := hasDerivAt_lPhase_fst S T x0 (hz s₁ hs₁K).1
  have hpos : α s₁ = lPhaseCurve (I := I) x0 z s₁ := by
    change α s₁ = (extChartAt I x0).symm (z s₁).1
    rw [hzs₁]
    refine ((extChartAt I x0).left_inv ?_).symm
    rw [extChartAt_source]
    exact hsrc
  have hbase : α s₁ ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc
  have hvel : lVelocity (I := I) α s₁ = lVelocity (I := I) (lPhaseCurve (I := I) x0 z) s₁ := by
    rw [lPhase_velocity (I := I) x0 z s₁ hq (hz s₁ hs₁K).2.2]
    change _ = trivFromE (I := I) x0 (lPhaseCurve (I := I) x0 z s₁) (z s₁).2
    rw [← hpos, hzs₁]
    exact (trivFromE_trivToE (I := I) x0 hbase _).symm
  exact lRegularizedSolution_eqOn S hS T hJ hJc hs₁J hK hKc hs₁K hα
    (isLRegularizedGeodesicOn_lPhaseCurve S T x0 hK hz) hpos hvel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eqOn_lRegularizedCurve_lPhaseCurve (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x0 : M) {x : M} {Z : TangentSpace I x}
    {z : ℝ → E × E} {K : Set ℝ} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hz : ∀ s ∈ K, HasDerivAt z (lPhaseField S T x0 s (z s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x0).target)
    {s₁ : ℝ} (hs₁ : s₁ ∈ lRegularizedDomain S T x Z) (hs₁K : s₁ ∈ K)
    (hsrc : lRegularizedCurve S T x Z s₁ ∈ (chartAt H x0).source)
    (hzs₁ : z s₁ = (extChartAt I x0 (lRegularizedCurve S T x Z s₁),
      trivToE (I := I) x0 (lRegularizedCurve S T x Z s₁)
        (lVelocity (I := I) (lRegularizedCurve S T x Z) s₁))) :
    EqOn (lRegularizedCurve S T x Z) (lPhaseCurve (I := I) x0 z)
      (lRegularizedDomain S T x Z ∩ K) :=
  eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn S hS T x0 (lRegularizedDomain_isOpen S T x Z)
    (lRegularizedDomain_preconn S T x Z) (isLRegularizedGeodesicOn_lRegularizedCurve S hS T x Z)
    hK hKc hz hs₁ hs₁K hsrc hzs₁

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eqOn_lRegularizedCurve_lPhaseCurve_of_initial (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : ℝ} (hT : T ∈ D.regular) (x0 : M) {x : M}
    {Z : TangentSpace I x} {z : ℝ → E × E} {K : Set ℝ} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hz : ∀ s ∈ K, HasDerivAt z (lPhaseField S T x0 s (z s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x0).target)
    (h0K : (0 : ℝ) ∈ K) (hsrc : x ∈ (chartAt H x0).source)
    (hz0 : z 0 = (extChartAt I x0 x, trivToE (I := I) x0 x ((2 : ℝ) • Z))) :
    EqOn (lRegularizedCurve S T x Z) (lPhaseCurve (I := I) x0 z)
      (lRegularizedDomain S T x Z ∩ K) := by
  refine eqOn_lRegularizedCurve_lPhaseCurve S hS T x0 hK hKc hz
    (zero_mem_lRegularizedDomain S hS T x Z hT) h0K (by rw [lRegularizedCurve_zero]; exact hsrc) ?_
  rw [hz0, lRegularizedCurve_velocity_zero S hS T x Z hT, lRegularizedCurve_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lPhaseState_eqOn (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x0 : M) {z z' : ℝ → E × E} {K K' : Set ℝ} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hz : ∀ s ∈ K, HasDerivAt z (lPhaseField S T x0 s (z s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x0).target)
    (hK' : IsOpen K') (hKc' : IsPreconnected K')
    (hz' : ∀ s ∈ K', HasDerivAt z' (lPhaseField S T x0 s (z' s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z' s).1 ∈ interior (extChartAt I x0).target)
    {s₁ : ℝ} (hs₁K : s₁ ∈ K) (hs₁K' : s₁ ∈ K') (h : z s₁ = z' s₁) :
    EqOn z z' (K ∩ K') := by
  have hq' := hasDerivAt_lPhase_fst S T x0 (hz' s₁ hs₁K').1
  have hint' := (hz' s₁ hs₁K').2.2
  have htgt := interior_subset hint'
  have hsrc : lPhaseCurve (I := I) x0 z' s₁ ∈ (chartAt H x0).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x0).map_target htgt
  have hbase : lPhaseCurve (I := I) x0 z' s₁ ∈
      (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc
  have hzs₁ : z s₁ = (extChartAt I x0 (lPhaseCurve (I := I) x0 z' s₁),
      trivToE (I := I) x0 (lPhaseCurve (I := I) x0 z' s₁)
        (lVelocity (I := I) (lPhaseCurve (I := I) x0 z') s₁)) := by
    rw [h]
    refine Prod.ext ((extChartAt I x0).right_inv htgt).symm ?_
    rw [lPhase_velocity (I := I) x0 z' s₁ hq' hint']
    exact (trivToE_trivFromE (I := I) x0 hbase _).symm
  have hc := eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn S hS T x0 hK' hKc'
    (isLRegularizedGeodesicOn_lPhaseCurve S T x0 hK' hz') hK hKc hz hs₁K' hs₁K hsrc hzs₁
  exact eqOn_of_lPhaseCurve_eqOn x0 (hK.inter hK')
    (fun s hs => ⟨hasDerivAt_lPhase_fst S T x0 (hz s hs.1).1, (hz s hs.1).2.2⟩)
    (fun s hs => ⟨hasDerivAt_lPhase_fst S T x0 (hz' s hs.2).1, (hz' s hs.2).2.2⟩)
    (fun s hs => (hc ⟨hs.2, hs.1⟩).symm)

theorem lPhaseFlow_comp_eqOn (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x0 : M) {W₁ W₂ : Set (ℝ × (E × E))}
    {L₁ L₂ : Set ℝ} (hL₁ : IsOpen L₁) (hL₁c : IsPreconnected L₁) (hL₂ : IsOpen L₂)
    (hL₂c : IsPreconnected L₂) {Ψ₁ Ψ₂ : (ℝ × (E × E)) × ℝ → E × E}
    (hΨ₁d : ∀ p ∈ W₁, ∀ s ∈ L₁,
      HasDerivAt (fun r => Ψ₁ (p, r)) (lPhaseField S T x0 s (Ψ₁ (p, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ₁ (p, s)).1 ∈ interior (extChartAt I x0).target)
    (hΨ₂0 : ∀ q ∈ W₂, Ψ₂ (q, q.1) = q.2)
    (hΨ₂d : ∀ q ∈ W₂, ∀ s ∈ L₂,
      HasDerivAt (fun r => Ψ₂ (q, r)) (lPhaseField S T x0 s (Ψ₂ (q, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ₂ (q, s)).1 ∈ interior (extChartAt I x0).target)
    {p : ℝ × (E × E)} (hp : p ∈ W₁) {s₁ : ℝ} (hs₁ : s₁ ∈ L₁ ∩ L₂)
    (hq : (s₁, Ψ₁ (p, s₁)) ∈ W₂) :
    EqOn (fun s => Ψ₂ ((s₁, Ψ₁ (p, s₁)), s)) (fun s => Ψ₁ (p, s)) (L₁ ∩ L₂) := by
  have h := lPhaseState_eqOn S hS T x0 hL₂ hL₂c (hΨ₂d _ hq) hL₁ hL₁c (hΨ₁d p hp) hs₁.2 hs₁.1
    (hΨ₂0 _ hq)
  exact fun s hs => h ⟨hs.2, hs.1⟩

theorem exists_lPhaseFlow_union (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x0 : M) {W₁ W₂ : Set (ℝ × (E × E))}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) {L₁ L₂ : Set ℝ} (hL₁ : IsOpen L₁)
    (hL₁c : IsPreconnected L₁) (hL₂ : IsOpen L₂) (hL₂c : IsPreconnected L₂)
    {Ψ₁ Ψ₂ : (ℝ × (E × E)) × ℝ → E × E} (hΨ₁sm : ContDiffOn ℝ ∞ Ψ₁ (W₁ ×ˢ L₁))
    (hΨ₁d : ∀ p ∈ W₁, ∀ s ∈ L₁,
      HasDerivAt (fun r => Ψ₁ (p, r)) (lPhaseField S T x0 s (Ψ₁ (p, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ₁ (p, s)).1 ∈ interior (extChartAt I x0).target)
    (hΨ₂0 : ∀ q ∈ W₂, Ψ₂ (q, q.1) = q.2) (hΨ₂sm : ContDiffOn ℝ ∞ Ψ₂ (W₂ ×ˢ L₂))
    (hΨ₂d : ∀ q ∈ W₂, ∀ s ∈ L₂,
      HasDerivAt (fun r => Ψ₂ (q, r)) (lPhaseField S T x0 s (Ψ₂ (q, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (Ψ₂ (q, s)).1 ∈ interior (extChartAt I x0).target)
    {s₁ : ℝ} (hs₁ : s₁ ∈ L₁ ∩ L₂) :
    IsOpen {p | p ∈ W₁ ∧ (s₁, Ψ₁ (p, s₁)) ∈ W₂} ∧
      ∃ Ψ : (ℝ × (E × E)) × ℝ → E × E,
        ContDiffOn ℝ ∞ Ψ ({p | p ∈ W₁ ∧ (s₁, Ψ₁ (p, s₁)) ∈ W₂} ×ˢ (L₁ ∪ L₂)) ∧
        ∀ p ∈ W₁, (s₁, Ψ₁ (p, s₁)) ∈ W₂ →
          (∀ s ∈ L₁, Ψ (p, s) = Ψ₁ (p, s)) ∧
          (∀ s ∈ L₂, Ψ (p, s) = Ψ₂ ((s₁, Ψ₁ (p, s₁)), s)) ∧
          ∀ s ∈ L₁ ∪ L₂,
            HasDerivAt (fun r => Ψ (p, r)) (lPhaseField S T x0 s (Ψ (p, s))) s ∧
              T - s ^ 2 ∈ D.regular ∧ (Ψ (p, s)).1 ∈ interior (extChartAt I x0).target := by
  classical
  let W : Set (ℝ × (E × E)) := {p | p ∈ W₁ ∧ (s₁, Ψ₁ (p, s₁)) ∈ W₂}
  let a : ℝ × (E × E) → ℝ × (E × E) := fun p => (s₁, Ψ₁ (p, s₁))
  have ha : ContDiffOn ℝ ∞ a W₁ :=
    contDiffOn_const.prodMk
      (hΨ₁sm.comp (contDiffOn_id.prodMk contDiffOn_const) fun p hp => ⟨hp, hs₁.1⟩)
  have hWo : IsOpen W := ha.continuousOn.isOpen_inter_preimage hW₁ hW₂
  let Ψ : (ℝ × (E × E)) × ℝ → E × E := fun q => if q.2 ∈ L₁ then Ψ₁ q else Ψ₂ (a q.1, q.2)
  have h1 : ∀ q : (ℝ × (E × E)) × ℝ, q.2 ∈ L₁ → Ψ q = Ψ₁ q := fun q hq => if_pos hq
  have h2 : ∀ q : (ℝ × (E × E)) × ℝ, q.1 ∈ W → q.2 ∈ L₂ → Ψ q = Ψ₂ (a q.1, q.2) := by
    intro q hq hq2
    by_cases h : q.2 ∈ L₁
    · rw [h1 q h]
      exact (lPhaseFlow_comp_eqOn S hS T x0 hL₁ hL₁c hL₂ hL₂c hΨ₁d hΨ₂0 hΨ₂d hq.1 hs₁ hq.2
        ⟨h, hq2⟩).symm
    · exact if_neg h
  have hG : ContDiffOn ℝ ∞ (fun q : (ℝ × (E × E)) × ℝ => Ψ₂ (a q.1, q.2)) (W ×ˢ L₂) :=
    hΨ₂sm.comp ((ha.comp contDiffOn_fst fun q hq => hq.1.1).prodMk contDiffOn_snd)
      fun q hq => ⟨hq.1.2, hq.2⟩
  have hA : ContDiffOn ℝ ∞ Ψ (W ×ˢ L₁) :=
    (hΨ₁sm.mono (prod_mono (fun p hp => hp.1) subset_rfl)).congr fun q hq => h1 q hq.2
  have hB : ContDiffOn ℝ ∞ Ψ (W ×ˢ L₂) := hG.congr fun q hq => h2 q hq.1 hq.2
  refine ⟨hWo, Ψ, ?_, ?_⟩
  · intro q hq
    rcases hq.2 with h | h
    · exact ((hA q ⟨hq.1, h⟩).contDiffAt ((hWo.prod hL₁).mem_nhds ⟨hq.1, h⟩)).contDiffWithinAt
    · exact ((hB q ⟨hq.1, h⟩).contDiffAt ((hWo.prod hL₂).mem_nhds ⟨hq.1, h⟩)).contDiffWithinAt
  intro p hp₁ hp₂
  have hp : p ∈ W := ⟨hp₁, hp₂⟩
  refine ⟨fun s hs => h1 (p, s) hs, fun s hs => h2 (p, s) hp hs, ?_⟩
  intro s hs
  rcases hs with h | h
  · obtain ⟨hd, hreg, hint⟩ := hΨ₁d p hp₁ s h
    have heq : (fun r => Ψ (p, r)) =ᶠ[𝓝 s] fun r => Ψ₁ (p, r) :=
      eventuallyEq_of_mem (hL₁.mem_nhds h) fun r hr => h1 (p, r) hr
    rw [h1 (p, s) h]
    exact ⟨hd.congr_of_eventuallyEq heq, hreg, hint⟩
  · obtain ⟨hd, hreg, hint⟩ := hΨ₂d (a p) hp₂ s h
    have heq : (fun r => Ψ (p, r)) =ᶠ[𝓝 s] fun r => Ψ₂ (a p, r) :=
      eventuallyEq_of_mem (hL₂.mem_nhds h) fun r hr => h2 (p, r) hp hr
    rw [h2 (p, s) hp h]
    exact ⟨hd.congr_of_eventuallyEq heq, hreg, hint⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem contDiffOn_extChartAt_coordChange_prod_fderiv (x0 x1 : M) :
    ContDiffOn ℝ ∞ (fun z : E × E => (extChartAt I x1 ((extChartAt I x0).symm z.1),
      fderiv ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) z.1 z.2))
      {z | z.1 ∈ (extChartAt I x0).target ∧
        (extChartAt I x0).symm z.1 ∈ (extChartAt I x1).source} := by
  let O : Set E :=
    {y | y ∈ (extChartAt I x0).target ∧ (extChartAt I x0).symm y ∈ (extChartAt I x1).source}
  have hO : IsOpen O :=
    (continuousOn_extChartAt_symm x0).isOpen_inter_preimage (isOpen_extChartAt_target x0)
      (isOpen_extChartAt_source x1)
  have hφ : ContDiffOn ℝ ∞ (extChartAt I x1 ∘ (extChartAt I x0).symm) O :=
    (contDiffOn_ext_coord_change (I := I) (n := ∞) x1 x0).mono fun y hy => ⟨hy.1, hy.2⟩
  have hmaps : MapsTo (Prod.fst : E × E → E)
      {z | z.1 ∈ (extChartAt I x0).target ∧
        (extChartAt I x0).symm z.1 ∈ (extChartAt I x1).source} O := fun z hz => hz
  exact (hφ.comp contDiffOn_fst hmaps).prodMk
    (((hφ.fderiv_of_isOpen hO (by simp)).comp contDiffOn_fst hmaps).clm_apply contDiffOn_snd)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eqOn_lPhaseCurve_of_coordChange (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) {x0 x1 : M} {z₀ z₁ : ℝ → E × E} {K₀ K₁ : Set ℝ}
    (hK₀ : IsOpen K₀) (hK₀c : IsPreconnected K₀)
    (hz₀ : ∀ s ∈ K₀, HasDerivAt z₀ (lPhaseField S T x0 s (z₀ s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z₀ s).1 ∈ interior (extChartAt I x0).target)
    (hK₁ : IsOpen K₁) (hK₁c : IsPreconnected K₁)
    (hz₁ : ∀ s ∈ K₁, HasDerivAt z₁ (lPhaseField S T x1 s (z₁ s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z₁ s).1 ∈ interior (extChartAt I x1).target)
    {s₁ : ℝ} (hs₁₀ : s₁ ∈ K₀) (hs₁₁ : s₁ ∈ K₁)
    (hsrc : (extChartAt I x0).symm (z₀ s₁).1 ∈ (extChartAt I x1).source)
    (h : z₁ s₁ = (extChartAt I x1 ((extChartAt I x0).symm (z₀ s₁).1),
      fderiv ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) (z₀ s₁).1 (z₀ s₁).2)) :
    EqOn (lPhaseCurve (I := I) x0 z₀) (lPhaseCurve (I := I) x1 z₁) (K₀ ∩ K₁) := by
  have hq₀ := hasDerivAt_lPhase_fst S T x0 (hz₀ s₁ hs₁₀).1
  have hy₀ : (z₀ s₁).1 ∈ (extChartAt I x0).target := interior_subset (hz₀ s₁ hs₁₀).2.2
  have hφd := differentiableAt_extChartAt_transition hy₀ hsrc
  let w : ℝ → E × E := fun r => (extChartAt I x1 ((extChartAt I x0).symm (z₀ r).1),
    fderiv ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) (z₀ r).1 (z₀ r).2)
  have hw : w s₁ = z₁ s₁ := h.symm
  have hwq : HasDerivAt (fun r => (w r).1) (w s₁).2 s₁ := by
    have h := hφd.hasFDerivAt.comp_hasDerivAt s₁ hq₀
    exact h
  have hwint : (w s₁).1 ∈ interior (extChartAt I x1).target := by
    rw [hw]
    exact (hz₁ s₁ hs₁₁).2.2
  have hgerm : lPhaseCurve (I := I) x0 z₀ =ᶠ[𝓝 s₁] lPhaseCurve (I := I) x1 w := by
    have hc : ContinuousAt (fun r => (extChartAt I x0).symm (z₀ r).1) s₁ :=
      ContinuousAt.comp (g := (extChartAt I x0).symm) (f := fun r => (z₀ r).1)
        (continuousAt_extChartAt_symm'' hy₀) hq₀.continuousAt
    filter_upwards [hc.preimage_mem_nhds ((isOpen_extChartAt_source x1).mem_nhds hsrc)]
      with r hr
    exact ((extChartAt I x1).left_inv hr).symm
  have hpos : lPhaseCurve (I := I) x0 z₀ s₁ = lPhaseCurve (I := I) x1 z₁ s₁ :=
    hgerm.eq_of_nhds.trans (congrArg (fun q : E × E => (extChartAt I x1).symm q.1) hw)
  have hvel : lVelocity (I := I) (lPhaseCurve (I := I) x0 z₀) s₁ =
      lVelocity (I := I) (lPhaseCurve (I := I) x1 z₁) s₁ := by
    have h1 : lVelocity (I := I) (lPhaseCurve (I := I) x0 z₀) s₁ =
        lVelocity (I := I) (lPhaseCurve (I := I) x1 w) s₁ := by
      simp only [lVelocity]
      rw [hgerm.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
      rfl
    have h2 : lVelocity (I := I) (lPhaseCurve (I := I) x1 w) s₁ =
        lVelocity (I := I) (lPhaseCurve (I := I) x1 z₁) s₁ := by
      rw [lPhase_velocity (I := I) x1 w s₁ hwq hwint, lPhase_velocity (I := I) x1 z₁ s₁
        (hasDerivAt_lPhase_fst S T x1 (hz₁ s₁ hs₁₁).1) (hz₁ s₁ hs₁₁).2.2]
      change trivFromE (I := I) x1 ((extChartAt I x1).symm (w s₁).1) (w s₁).2 =
        trivFromE (I := I) x1 ((extChartAt I x1).symm (z₁ s₁).1) (z₁ s₁).2
      rw [hw]
    exact h1.trans h2
  exact lRegularizedSolution_eqOn S hS T hK₀ hK₀c hs₁₀ hK₁ hK₁c hs₁₁
    (isLRegularizedGeodesicOn_lPhaseCurve S T x0 hK₀ hz₀)
    (isLRegularizedGeodesicOn_lPhaseCurve S T x1 hK₁ hz₁) hpos hvel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lPhaseState_eq_coordChange (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) {x0 x1 : M} {z₀ z₁ : ℝ → E × E} {K₀ K₁ : Set ℝ}
    (hK₀ : IsOpen K₀) (hK₀c : IsPreconnected K₀)
    (hz₀ : ∀ s ∈ K₀, HasDerivAt z₀ (lPhaseField S T x0 s (z₀ s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z₀ s).1 ∈ interior (extChartAt I x0).target)
    (hK₁ : IsOpen K₁) (hK₁c : IsPreconnected K₁)
    (hz₁ : ∀ s ∈ K₁, HasDerivAt z₁ (lPhaseField S T x1 s (z₁ s)) s ∧ T - s ^ 2 ∈ D.regular ∧
      (z₁ s).1 ∈ interior (extChartAt I x1).target)
    {s₁ : ℝ} (hs₁₀ : s₁ ∈ K₀) (hs₁₁ : s₁ ∈ K₁)
    (hsrc : (extChartAt I x0).symm (z₀ s₁).1 ∈ (extChartAt I x1).source)
    (h : z₁ s₁ = (extChartAt I x1 ((extChartAt I x0).symm (z₀ s₁).1),
      fderiv ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) (z₀ s₁).1 (z₀ s₁).2)) :
    ∀ s ∈ K₀ ∩ K₁, (extChartAt I x0).symm (z₀ s).1 ∈ (extChartAt I x1).source ∧
      z₁ s = (extChartAt I x1 ((extChartAt I x0).symm (z₀ s).1),
        fderiv ℝ (extChartAt I x1 ∘ (extChartAt I x0).symm) (z₀ s).1 (z₀ s).2) := by
  have hc := eqOn_lPhaseCurve_of_coordChange S hS T hK₀ hK₀c hz₀ hK₁ hK₁c hz₁ hs₁₀ hs₁₁ hsrc h
  have hsrcAll : ∀ s ∈ K₀ ∩ K₁,
      (extChartAt I x0).symm (z₀ s).1 ∈ (extChartAt I x1).source := by
    intro s hs
    have e : (extChartAt I x0).symm (z₀ s).1 = (extChartAt I x1).symm (z₁ s).1 := hc hs
    rw [e]
    exact (extChartAt I x1).map_target (interior_subset (hz₁ s hs.2).2.2)
  have hfst : ∀ s ∈ K₀ ∩ K₁,
      (z₁ s).1 = extChartAt I x1 ((extChartAt I x0).symm (z₀ s).1) := by
    intro s hs
    have e : (extChartAt I x0).symm (z₀ s).1 = (extChartAt I x1).symm (z₁ s).1 := hc hs
    rw [e, (extChartAt I x1).right_inv (interior_subset (hz₁ s hs.2).2.2)]
  intro s hs
  refine ⟨hsrcAll s hs, Prod.ext (hfst s hs) ?_⟩
  have hd := (differentiableAt_extChartAt_transition (interior_subset (hz₀ s hs.1).2.2)
    (hsrcAll s hs)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lPhase_fst S T x0 (hz₀ s hs.1).1)
  have heq : (fun r => (z₁ r).1) =ᶠ[𝓝 s]
      ((extChartAt I x1 ∘ (extChartAt I x0).symm) ∘ fun r => (z₀ r).1) :=
    eventuallyEq_of_mem ((hK₀.inter hK₁).mem_nhds hs) fun r hr => hfst r hr
  exact (hasDerivAt_lPhase_fst S T x1 (hz₁ s hs.2).1).unique (hd.congr_of_eventuallyEq heq)

end DifferentialGeometry.PDE.RicciFlow.Perelman
