import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialSlabUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FiniteTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ComponentBallTransfer

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (solutionOnRestrictOpen)
open DifferentialGeometry.PDE.RicciFlow.Perelman (FlowMetricBall)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section ComponentTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem FlowMetricBall.isKappaNoncollapsed_of_restrict_connectedComponent
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {time : D.FlowTime}
    (U : Opens M) [SigmaCompactSpace U] (B : FlowMetricBall S time)
    (hU : U = connectedComponentOpen (I := I) B.center) {κ ρ : ℝ}
    (hK : KappaNoncollapsedBelowScale (solutionOnRestrictOpen S U) κ ρ)
    (hBρ : B.radius ≤ ρ) (hB : B.IsRmControlled) : B.IsKappaNoncollapsed κ := by
  subst hU
  rw [← FlowMetricBall.onConnectedComponent_noncollapsed_iff]
  refine hK.2 time _ hBρ ⟨hB.1, fun t ht x hx => ?_⟩
  have hx' : (x : M) ∈ B.setAt t := by
    change riemannianEDistOf ((S.base.metric t).restrictOpen _)
      (connectedComponentPoint (I := I) B.center) x < _ at hx
    rwa [DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen] at hx
  change B.radius ^ 4 * FlowMetricBall.rmNormSq (solutionOnRestrictOpen S _) t x ≤ 1
  rw [rmNormSq_restrict_connCompOpen]
  exact hB.2 t ht x hx'

end ComponentTransfer

section Components

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

private local instance componentSigmaCompact (p : M) :
    SigmaCompactSpace (connectedComponentOpen (I := I) p) :=
  (isClosed_connectedComponent (x := p)).sigmaCompactSpace

theorem no_local_collapsing_of_compactSpace {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S) {ρ : ℝ} (hρ : 0 < ρ) : NoLocalCollapsing S ρ := by
  classical
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, one_pos, hρ, fun _ B => (IsEmpty.false B.center).elim⟩
  have hcomp (p : M) :
      NoLocalCollapsing (solutionOnRestrictOpen S (connectedComponentOpen (I := I) p)) ρ := by
    let : ConnectedSpace (connectedComponentOpen (I := I) p) :=
      connectedComponentOpen_connectedSpace p
    let : CompactSpace (connectedComponentOpen (I := I) p) :=
      isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := p)).isCompact
    exact no_local_collapsing hT _ (isSolutionOn_restrict_connCompOpen S hS p) hρ
  choose rep hrep using ConnectedComponents.surjective_coe (α := M)
  choose k hk hK using fun c : ConnectedComponents M => hcomp (rep c)
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min k
  refine ⟨k c₀, hk c₀, hρ, fun time B hBρ hB => ?_⟩
  have hU : connectedComponentOpen (I := I) (rep B.center) =
      connectedComponentOpen (I := I) B.center :=
    SetLike.coe_injective (ConnectedComponents.coe_eq_coe.mp (hrep B.center))
  obtain ⟨-, hvol⟩ := FlowMetricBall.isKappaNoncollapsed_of_restrict_connectedComponent _ B hU
    (hK B.center) hBρ hB
  refine ⟨hk c₀, le_trans ?_ hvol⟩
  gcongr
  exact hc₀ _

end Components

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u

theorem noLocalCollapsing_incomingSlab (P : OrientedThreeStage.{u}) {a s : ℝ}
    (G : P.IncomingSlab a s) {ρ : ℝ} (hρ : 0 < ρ) : Perelman.NoLocalCollapsing G.flow ρ := by
  let D' := RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)
  let S' := (G.flow.timeShift a).timeRestrict D'
  have hS' : IsSolutionOn S' := by
    apply isSolutionOn_timeRestrict _
    · rw [RealTimeInterval.timeShift_closedOpen_carrier]
      exact Subset.rfl
    · rw [RealTimeInterval.timeShift_closedOpen_regular]
      exact Subset.rfl
    · exact isSolutionOn_timeShift G.equation a
  obtain ⟨κ, hκ, -, hK⟩ := Perelman.no_local_collapsing_of_compactSpace _ S' hS' hρ
  refine ⟨κ, hκ, hρ, fun τ B hBρ hB => ?_⟩
  have hτ : (τ : ℝ) ∈ Ico a s := τ.2
  let τ' : D'.FlowTime := ⟨τ - a, show (τ : ℝ) - a ∈ Ico 0 (s - a) from
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  let B' : FlowMetricBall S' τ' := ⟨B.center, B.radius, B.radius_pos⟩
  obtain ⟨hsub, hbound⟩ := hB
  have hmem {t : ℝ} (ht : t ∈ Icc ((τ' : ℝ) - B'.radius ^ 2) τ') :
      t + a ∈ Icc ((τ : ℝ) - B.radius ^ 2) τ := by
    change t ∈ Icc ((τ : ℝ) - a - B.radius ^ 2) (τ - a) at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hB' : B'.IsRmControlled := by
    refine ⟨fun t ht => ?_, fun t ht x hx => hbound (t + a) (hmem ht) x hx⟩
    have h : t + a ∈ Ico a s := hsub (hmem ht)
    exact show t ∈ Ico 0 (s - a) from ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨-, hvol⟩ := hK τ' B' hBρ hB'
  refine ⟨hκ, hvol.trans_eq ?_⟩
  have hm : S'.base.metric (τ' : ℝ) = G.flow.base.metric τ := by
    change G.flow.base.metric ((τ : ℝ) - a + a) = _
    rw [sub_add_cancel]
  simp only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    Integral.Measure.volumeMeasureOn_eq_metric, SolutionOn.family_metric, hm]
  rfl

theorem exists_uniform_kappaNoncollapsed_initial_of_pos (P : OrientedThreeStage.{u})
    (g : P.Metric) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ κ > 0, ∃ η > 0, ∀ (s : ℝ) (G : P.IncomingSlab 0 s), G.flow.base.metric 0 = g →
      ∀ (τ : (RealTimeInterval.closedOpen 0 s G.lt).FlowTime)
        (B : FlowMetricBall G.flow τ), (τ : ℝ) ≤ η → B.radius ≤ ρ →
          B.IsRmControlled → B.IsKappaNoncollapsed κ :=
  P.exists_uniform_kappaNoncollapsed_initial g fun _ G _ => P.noLocalCollapsing_incomingSlab G hρ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
