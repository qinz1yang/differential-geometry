import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelLocalPull
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

def partialDiffeomorphOfInjective [Nonempty M] {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hinj : Injective f) : PartialDiffeomorph I J M N ∞ :=
  have he : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  { toPartialEquiv := (he.toOpenPartialHomeomorph f).toPartialEquiv
    open_source := (he.toOpenPartialHomeomorph f).open_source
    open_target := (he.toOpenPartialHomeomorph f).open_target
    contMDiffOn_toFun := hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      have hy' : y ∈ range f := by
        rw [← he.toOpenPartialHomeomorph_target f]
        exact hy
      obtain ⟨x, rfl⟩ := hy'
      have hloc := (hf x).contMDiffAt_localInverse
      refine (hloc.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(hf x).localInverse.open_source.mem_nhds (hf x).localInverse_mem_source]
        with z hz
      have hfz : f ((hf x).localInverse z) = z := (hf x).localInverse_right_inv hz
      change (he.toOpenPartialHomeomorph f).symm z = (hf x).localInverse z
      conv_lhs => rw [← hfz]
      exact he.toOpenPartialHomeomorph_left_inv f }

@[simp]
theorem partialDiffeomorphOfInjective_apply [Nonempty M] {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) (x : M) :
    partialDiffeomorphOfInjective hf hinj x = f x := rfl

theorem partialDiffeomorphOfInjective_source [Nonempty M] {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    (partialDiffeomorphOfInjective hf hinj).source = univ := rfl

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open DifferentialGeometry.Topology

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
  {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
  [T2Space N]

omit [IsManifold ThreeModel ∞ N] [T2Space N] in
theorem isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val
    {Ξ : N → H.backwardSurvivorIncomingDomain first last hle G}
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun v => (Ξ v).val.val) :=
  (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val G.terminalRegularOpen)
    (isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G)
      hΞ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞
        ((Subtype.val : G.terminalRegularOpen → (H.stage last).Carrier) ∘
          (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ)))

omit [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N] in
theorem injective_backwardSurvivorIncomingDomain_val_val
    {Ξ : N → H.backwardSurvivorIncomingDomain first last hle G} (hΞ : Injective Ξ) :
    Injective (fun v => (Ξ v).val.val) :=
  fun _ _ h => hΞ (Subtype.ext (Subtype.ext h))

theorem localPullMetric_scaleMetric_backwardSurvivorIncomingMetric (L : G.TerminalLimitMetric)
    (g : ℝ → SmoothRiemannianMetric ThreeModel (H.stage last).Carrier)
    (hG : ∀ v, G.flow.base.metric v = g v)
    (hL : L.metric = (g s).restrictOpen G.terminalRegularOpen)
    {Ξ : N → H.backwardSurvivorIncomingDomain first last hle G}
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) {c : ℝ} (hc : 0 < c) {v : ℝ}
    (hv : v ≤ s) :
    localPullMetric (scaleMetric c hc (H.backwardSurvivorIncomingMetric first last hle G L v))
        Ξ hΞ =
      scaleMetric c hc (localPullMetric (g v) (fun w => (Ξ w).val.val)
        (H.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val first last hle G hΞ)) := by
  have hext : L.extendedMetric v = (g v).restrictOpen G.terminalRegularOpen := by
    rcases hv.lt_or_eq with h | rfl
    · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_before _ h, hG]
    · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal, hL]
  rw [localPullMetric_scaleMetric]
  congr 1
  have hval := isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen
  have hinc := H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G
  rw [backwardSurvivorIncomingMetric, hext, ← localPullMetric_subtype_val,
    localPullMetric_comp _ _ _ hval hinc (isLocalDiffeomorph_comp hval hinc),
    localPullMetric_comp _ _ _ (isLocalDiffeomorph_comp hval hinc) hΞ
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_comp hval hinc) hΞ)]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (Gk : P.IncomingSlab a s)
  {N : Type} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
  [T2Space N] [Nonempty N]

theorem orientedWitness_of_scaled_localPull_window {T' : ℝ} {hT' : 0 ≤ T'}
    (S : SolutionOn (I := ThreeModel) (M := N) (RealTimeInterval.closed 0 T' hT'))
    {Φ : N → P.Carrier} (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ) (hinj : Injective Φ)
    {q b t : ℝ} (hq : 0 < q) (hba : b ≤ a) (hat : a < t) (hts : t < s) (hT : q * (t - b) ≤ T')
    (hmetric : ∀ τ ∈ Icc 0 T', a ≤ b + τ / q →
      S.base.metric τ = localPullMetric (scaleMetric q hq (Gk.flow.base.metric (b + τ / q))) Φ hΦ)
    {δ κ : ℝ} {z : N} (hw : OrientedWitness S (P.orientation.pullback hΦ) δ κ z (q * (t - b)))
    (hage : (δ * Gk.flow.scalar t (Φ z))⁻¹ ≤ t - a) :
    OrientedWitness Gk.flow P.orientation δ κ (Φ z) t := by
  set T := q * (t - b) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTmem : T ∈ (RealTimeInterval.closed 0 T' hT').carrier := ⟨hT0, hT⟩
  have htmem : t ∈ (RealTimeInterval.closedOpen a s Gk.lt).carrier := ⟨hat.le, hts⟩
  have htT : b + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST : S.base.metric T =
      localPullMetric (scaleMetric q hq (Gk.flow.base.metric t)) Φ hΦ := by
    rw [hmetric T hTmem (by rw [htT]; exact hat.le), htT]
  have hscal : S.scalar T z = q⁻¹ * Gk.flow.scalar t (Φ z) := by
    change metricScalarAt (S.base.metric T) z = _
    rw [hST, metricScalarAt_localPullMetric_scaleMetric]
    rfl
  have hw0 := hw
  obtain ⟨W, -⟩ := hw0
  have hRS : 0 < S.scalar T z := W.scalar_pos
  have hRG : 0 < Gk.flow.scalar t (Φ z) := by
    rw [hscal] at hRS
    exact pos_of_mul_pos_right hRS (inv_nonneg.mpr hq.le)
  have hδ : 0 < δ := W.eps_pos
  have hw1 : OrientedWitness (parabolicSolution S T 1 one_pos hTmem)
      (P.orientation.pullback hΦ) δ κ z 0 := by
    refine (orientedWitness_paraSolution_iff S _ one_pos hTmem 0 z δ κ).mpr ?_
    rw [parabolicTime_zero]
    exact hw
  have hscal1 : (parabolicSolution S T 1 one_pos hTmem).scalar 0 z = S.scalar T z := by
    rw [parabolicSolution_scalar]
    simp
  have hwinq : (δ * (parabolicSolution S T 1 one_pos hTmem).scalar 0 z)⁻¹ =
      q * (δ * Gk.flow.scalar t (Φ z))⁻¹ := by
    rw [hscal1, hscal]
    field_simp
  have hlow : ∀ σ ∈ Icc (0 - (δ * (parabolicSolution S T 1 one_pos hTmem).scalar 0 z)⁻¹) 0,
      a ≤ t + σ / q ∧ σ ≤ 0 := by
    intro σ hσ
    rw [hwinq] at hσ
    refine ⟨?_, hσ.2⟩
    have h1 : -(δ * Gk.flow.scalar t (Φ z))⁻¹ ≤ σ / q := by
      rw [le_div_iff₀ hq]
      linarith [hσ.1]
    linarith
  let Φp := partialDiffeomorphOfInjective hΦ hinj
  have hpush := OrientedWitness.ofLocalPull_of_pullback
    (S' := parabolicSolution Gk.flow t q hq htmem) (o := P.orientation) Φp rfl hΦ hw1
    (by
      change parabolicTime t q 0 ∈ Ico a s
      rw [parabolicTime_zero]
      exact htmem)
    (by
      intro σ hσ
      obtain ⟨h1, h2⟩ := hlow σ hσ
      change t + σ / q ∈ Ico a s
      refine ⟨h1, ?_⟩
      have : σ / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 hq.le
      linarith)
    (by
      intro σ hσ
      obtain ⟨h1, h2⟩ := hlow σ hσ
      have hτ : T + σ ∈ Icc 0 T' := by
        refine ⟨?_, by linarith⟩
        have h4 : q * (t + σ / q - b) = T + σ := by
          rw [hTdef, mul_sub, mul_add, mul_div_cancel₀ _ hq.ne']
          ring
        have h3 : q * (a - b) ≤ q * (t + σ / q - b) :=
          mul_le_mul_of_nonneg_left (by linarith) hq.le
        have h5 : 0 ≤ q * (a - b) := mul_nonneg hq.le (by linarith)
        linarith
      have hbt : b + (T + σ) / q = t + σ / q := by
        rw [add_div, ← htT]
        ring
      have hm := hmetric (T + σ) hτ (by rw [hbt]; exact h1)
      rw [hbt] at hm
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      simp only [parabolicSolution_metric, scaleMetric_inner, one_mul]
      change (S.base.metric (T + σ / 1)).inner x v w = _
      rw [div_one, hm]
      rfl)
  have hfin := (orientedWitness_paraSolution_iff Gk.flow P.orientation hq htmem 0 (Φ z) δ κ).mp
    hpush
  rwa [parabolicTime_zero] at hfin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
  {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
  [T2Space N]

theorem window_metric_eq_localPullMetric_scaleMetric (L : G.TerminalLimitMetric)
    (g : ℝ → SmoothRiemannianMetric ThreeModel (H.stage last).Carrier)
    (hG : ∀ v, G.flow.base.metric v = g v)
    (hL : L.metric = (g s).restrictOpen G.terminalRegularOpen)
    {Ξ : N → H.backwardSurvivorIncomingDomain first last hle G}
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hgflow : ∀ v ∈ Icc (H.time last) s,
      gflow v = H.backwardSurvivorIncomingMetric first last hle G L v)
    {D : Geometry.Curvature.RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := N) D)
    {b q : ℝ} (hq : 0 < q)
    (hS : ∀ τ, S.base.metric τ = localPullMetric (scaleMetric q hq (gflow (b + τ / q))) Ξ hΞ)
    {τ : ℝ} (hτ : b + τ / q ∈ Icc (H.time last) s) :
    S.base.metric τ = localPullMetric (scaleMetric q hq (g (b + τ / q))) (fun w => (Ξ w).val.val)
      (H.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val first last hle G hΞ) := by
  rw [hS, hgflow _ hτ, H.localPullMetric_scaleMetric_backwardSurvivorIncomingMetric first last hle
    G L g hG hL hΞ hq hτ.2, localPullMetric_scaleMetric]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
