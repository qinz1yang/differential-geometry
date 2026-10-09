import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_contMDiff_action_lt_on_carrier
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [TopologicalSpace.PseudoMetrizableSpace M] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {T u v : ℝ} (huv : u ≤ v) (α : ℝ → M)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume u v)
    (hclock : ∀ r ∈ Icc u v, T - r ^ 2 ∈ D.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧ β u = α u ∧ β v = α v ∧
      IntervalIntegrable (lRegularizedLagrangian S T β) volume u v ∧
      lRegularizedAction S T β u v < lRegularizedAction S T α u v + ε := by
  obtain ⟨β, hβ, hβu, hβv, hact⟩ :=
    exists_lRegularizedAction_c1_lt_of_absolutelyContinuousOnInterval
      S hS.smoothMetric ⟨hS.scalarCont⟩ T u v huv α hα hint hclock hε
  refine ⟨β, hβ, hβu, hβv, ?_, hact⟩
  have hc := lRegularizedLagrangian_continuousOn_carrier S hS β hβ
  exact (hc.comp (f := fun r : ℝ => (T, r))
    (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc huv

namespace OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem exists_contMDiff_action_lt
    (L : G.TerminalLimitMetric) {T u v : ℝ} {α : ℝ → P.Carrier}
    (hu : 0 ≤ u) (huv : u ≤ v) (hupper : T - u ^ 2 ≤ s) (hlower : a ≤ T - v ^ 2)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α u v)
    (hterminal : T - u ^ 2 = s → α u ∈ G.terminalRegularOpen)
    (hint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → P.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧ β u = α u ∧ β v = α v ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T β) volume u v ∧
      lRegularizedAction G.flow T β u v < lRegularizedAction G.flow T α u v + ε := by
  rcases huv.eq_or_lt with rfl | huv
  · exact ⟨fun _ => α u, contMDiff_const, rfl, rfl, by simp,
      by simpa only [lRegularizedAction, intervalIntegral.integral_same, zero_add] using hε⟩
  rcases hupper.lt_or_eq with hupper | hupper
  · let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
    apply exists_contMDiff_action_lt_on_carrier G.flow G.equation huv.le α hα hint ?_ hε
    intro r hr
    change a ≤ T - r ^ 2 ∧ T - r ^ 2 < s
    constructor
    · nlinarith [sq_le_sq₀ (hu.trans hr.1) (hu.trans huv.le) |>.2 hr.2]
    · nlinarith [sq_le_sq₀ hu (hu.trans hr.1) |>.2 hr.1]
  · exact L.exists_contMDiff_action_lt_of_terminal_curve hu huv hupper hlower hα
      (hterminal hupper) hint hε

end OrientedThreeStage.IncomingSlab

namespace ObservedHistory

universe u
variable (H : ObservedHistory.{u})

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_stage_action_lt_of_absolutelyContinuousOnInterval
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last) (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (j : H.StageInterval first last) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → (H.stage j.val).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β ∧
      β (H.regularizedStageStart T u j.val) = α j (H.regularizedStageStart T u j.val) ∧
      β (H.regularizedStageEnd T v j.val) = α j (H.regularizedStageEnd T v j.val) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T β) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      H.stageRegularizedAction j.val T β (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) <
        H.stageRegularizedAction j.val T (α j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) + ε := by
  have hupper' : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hb := H.regularizedStage_bounds hu huv hupper' hlower j
  have hc := H.regularizedStage_endpoint_clocks hupper' huv hu j
  rcases hb.2.1.eq_or_lt with heq | hlt
  · refine ⟨fun _ => α j (H.regularizedStageStart T u j.val), contMDiff_const, rfl, ?_, ?_, ?_⟩
    · rw [heq]
    · rw [heq]
    · simp only [stageRegularizedAction, heq, intervalIntegral.integral_same, zero_add]
      exact hε
  rcases j with ⟨j, hj⟩
  cases j using Fin.lastCases with
  | last =>
    have hlast : H.time (Fin.last H.eventCount) < H.horizon := by
      by_contra hn
      have hcollapsed : H.stageEndTime (Fin.last H.eventCount) ≤ H.time (Fin.last H.eventCount) := by
        simpa only [H.stageEndTime_last] using le_of_not_gt hn
      have horder : H.regularizedStageEnd T v (Fin.last H.eventCount) ≤
          H.regularizedStageStart T u (Fin.last H.eventCount) := by
        apply Real.sqrt_le_sqrt
        apply sub_le_sub_left
        exact (min_le_right _ _).trans (hcollapsed.trans (le_max_right _ _))
      exact (not_lt_of_ge horder) hlt
    let : TopologicalSpace.MetrizableSpace (H.stage (Fin.last H.eventCount)).Carrier :=
      Manifold.metrizableSpace ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
    have hclock (r : ℝ) (hr : r ∈ Icc (H.regularizedStageStart T u (Fin.last H.eventCount))
        (H.regularizedStageEnd T v (Fin.last H.eventCount))) :
        T - r ^ 2 ∈ (RealTimeInterval.closed (H.time (Fin.last H.eventCount)) H.horizon hlast.le).carrier := by
      have hs0 : 0 ≤ H.regularizedStageStart T u (Fin.last H.eventCount) := hu.trans hb.1
      have hr0 := hs0.trans hr.1
      have he0 := hs0.trans hb.2.1
      have hlo := le_max_right (T - v ^ 2) (H.time (Fin.last H.eventCount))
      have hhi := min_le_right (T - u ^ 2) (H.stageEndTime (Fin.last H.eventCount))
      have hcstart : T - H.regularizedStageStart T u (Fin.last H.eventCount) ^ 2 =
          min (T - u ^ 2) H.horizon := by
        simpa only [H.stageEndTime_last] using hc.1
      rw [H.stageEndTime_last] at hhi
      change H.time (Fin.last H.eventCount) ≤ T - r ^ 2 ∧ T - r ^ 2 ≤ H.horizon
      constructor
      · nlinarith [sq_le_sq₀ hr0 he0 |>.2 hr.2, hc.2]
      · nlinarith [sq_le_sq₀ hs0 hr0 |>.2 hr.1, hcstart]
    have hLagEq (γ : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) :
        H.stageRegularizedLagrangian (Fin.last H.eventCount) T γ =
          lRegularizedLagrangian (H.finalSlab hlast).flow T γ :=
      funext (H.stageRegularizedLagrangian_last hlast T γ)
    obtain ⟨β, hβ, hβu, hβv, hβint, hβact⟩ :=
      exists_contMDiff_action_lt_on_carrier (H.finalSlab hlast).flow (H.finalSlab hlast).equation
        hlt.le (α ⟨Fin.last H.eventCount, hj⟩) (hα _) (by simpa only [hLagEq] using hint ⟨_, hj⟩)
        hclock hε
    refine ⟨β, hβ, hβu, hβv, ?_, ?_⟩
    · simpa only [hLagEq] using hβint
    · simpa only [H.stageRegularizedAction_last hlast] using hβact
  | cast i =>
    have hs0 : 0 ≤ H.regularizedStageStart T u i.castSucc := hu.trans hb.1
    have hStageUpper : T - (H.regularizedStageStart T u i.castSucc) ^ 2 ≤ H.time i.succ := by
      rw [hc.1, H.stageEndTime_castSucc]
      exact min_le_right _ _
    have hStageLower : H.time i.castSucc ≤ T - (H.regularizedStageEnd T v i.castSucc) ^ 2 := by
      rw [hc.2]
      exact le_max_right _ _
    have hterminal : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = H.time i.succ →
        α ⟨i.castSucc, hj⟩ (H.regularizedStageStart T u i.castSucc) ∈
          (H.event i).incoming.terminalRegularOpen := by
      intro heq
      have hil : i.succ ≤ last := by
        by_contra hn
        have hlast : last = i.castSucc := by
          apply Fin.ext
          change last.val = i.val
          have hjle : i.val ≤ last.val := hj.2
          have hnot : ¬ i.val + 1 ≤ last.val := hn
          omega
        have huclock : H.regularizedStageStart T u i.castSucc = u :=
          H.regularizedStageStart_eq_of_mem_Icc hu (by simpa only [← hlast] using hupper')
        rw [huclock] at heq
        have huStrict : T - u ^ 2 < H.time i.succ := by
          exact (show T - u ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) from
            by simpa only [hlast, stageDomain, Fin.lastCases_castSucc] using hupper).2
        exact (ne_of_lt huStrict) heq
      obtain ⟨z, hz, _⟩ := hnodes i hj.1 hil
      have hzmem := ((H.event i).oldTerminal z).property
      rw [(H.event i).oldTerminal_eq z, hz] at hzmem
      simpa only [H.regularizedStageStart_castSucc_eq_event_clock hupper' i hil] using hzmem
    have hLagEq (γ : ℝ → (H.stage i.castSucc).Carrier) :
        H.stageRegularizedLagrangian i.castSucc T γ = lRegularizedLagrangian (H.event i).incoming.flow T γ :=
      funext (H.stageRegularizedLagrangian_castSucc i T γ)
    obtain ⟨β, hβ, hβu, hβv, hβint, hβact⟩ :=
      OrientedThreeStage.IncomingSlab.exists_contMDiff_action_lt (H.event i).terminal hs0 hlt.le
        hStageUpper hStageLower (hα ⟨_, hj⟩) hterminal (by simpa only [hLagEq] using hint ⟨_, hj⟩) hε
    refine ⟨β, hβ, hβu, hβv, ?_, ?_⟩
    · simpa only [hLagEq] using hβint
    · simpa only [H.stageRegularizedAction_castSucc] using hβact

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T B u v A : ℝ}
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : (A : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ∈ H.regularizedC1ActionValues first last hle T u v p q, C < A + ε := by
  classical
  obtain ⟨hu, huv, htop, hlower, α, hα, hstart, hend, hnode, hsum⟩ := hA
  have hscalarα (j : H.StageInterval first last) :
      ∀ᵐ t ∂volume.restrict (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hscalar j t ht (α j t)
  have hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_contra hnot
    have htop' : H.regularizedExtendedAction first last T B u v α = ⊤ :=
      (H.regularizedExtendedAction_eq_top_iff first last hu huv htop hlower α hα hscalarα).mpr (by simpa only [not_forall] using hnot)
    rw [hsum] at htop'
    exact WithTop.coe_ne_top htop'
  have hsumReal : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) = A := by
    apply WithTop.coe_injective
    exact (H.regularizedExtendedAction_eq_sum_action first last hu huv htop hlower α hint hscalarα).symm.trans hsum
  have hne : Nonempty (H.StageInterval first last) := ⟨⟨first, le_rfl, hle⟩⟩
  let N := Fintype.card (H.StageInterval first last)
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hεN : 0 < ε / N := div_pos hε hN
  have hex (j : H.StageInterval first last) :=
    H.exists_contMDiff_stage_action_lt_of_absolutelyContinuousOnInterval hu huv hupper hlower
      α hα hint hnode j hεN
  choose β hβ hβstart hβend hβint hβact using hex
  let C := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (β j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  refine ⟨C, ⟨hu, huv, htop, hlower, β, hβ, hβint, ?_, ?_, ?_, rfl⟩, ?_⟩
  · have hs := hβstart ⟨last, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc hu htop] at hs
    exact hs.trans hstart
  · have hs := hβend ⟨first, le_rfl, hle⟩
    rw [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hlower] at hs
    exact hs.trans hend
  · intro i hi hl
    obtain ⟨z, hzold, hznew⟩ := hnode i hi hl
    have ho := hβstart ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
    have hn := hβend ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock htop i hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hlower i hi] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  · have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr hne)
      (fun j (_ : j ∈ Finset.univ) => hβact j)
    rw [Finset.sum_add_distrib, hsumReal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hnε : (Fintype.card (H.StageInterval first last) : ℝ) * (ε / N) = ε := by
      dsimp only [N]
      field_simp
    simpa only [C, hnε] using hs

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedCost_eq_regularizedC1Cost
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q = H.regularizedC1Cost first last hle T u v p q := by
  apply le_antisymm (H.regularizedCost_le_regularizedC1Cost first last hle T B u v hscalar p q)
  by_cases hne : (H.regularizedActionValues first last hle T B u v p q).Nonempty
  · apply le_csInf hne
    intro A hA
    cases A using WithTop.recTopCoe with
    | top => exact le_top
    | coe A =>
      obtain ⟨C, hC, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
        first last hle hupper hscalar p q hA (ε := 1) zero_lt_one
      have hfinite : H.regularizedC1Cost first last hle T u v p q ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top
          (H.regularizedC1Cost_le_of_competitor first last hle T u v B hscalar p q hC)
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hfinite
      rw [← hc]
      apply WithTop.coe_le_coe.mpr
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨r, hr, hrA⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
        first last hle hupper hscalar p q hA hε
      have hh := H.regularizedC1Cost_le_of_competitor first last hle T u v B hscalar p q hr
      rw [← hc] at hh
      exact (WithTop.coe_le_coe.mp hh).trans hrA.le
  · rw [H.regularizedCost_eq_top_of_no_competitor first last hle T B u v p q
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type u}
  [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]

theorem regularizedCost_eq_of_minimal_of_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric ThreeModel X) {T u v μ B r : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hμ : 0 ≤ μ) (hr : 0 < r)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hmin : ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ u = η u → γ v = η v →
      lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v)
    (hpole : η u ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g (η u) z)
    (haction : lRegularizedAction S T η u v ≤
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    H.regularizedCost first last hle T B u v (f ⟨last, hle, le_rfl⟩ (η u))
        (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η u v : WithTop ℝ) := by
  have hupper' : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
  apply H.regularizedC1Cost_eq_of_minimal_of_lower_action_confined first last hle f hf hinj hcross
    S hS T hu huv hupper' hlower htime hmetric η hη hmin
  intro α hα hint hstart _ hnode hlow
  have hstay : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K) :=
    H.mapsTo_common_compact_set_of_sum_stageRegularizedAction_lt first last hle
      f hf hinj K hK hcross hu huv hupper' hlower S g hμ hr hmetric hcompare α hα hint
      (fun j t ht => hscalar j t ht (α j t)) (η u) hpole hfront hstart hnode (hlow.trans_le haction)
  intro j t ht
  obtain ⟨z, _, hz⟩ := hstay j ht
  exact ⟨z, hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_regularizedCost_minimum_of_action_lt_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hreg : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.regular)
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (y : X) (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ u = x) (hend : γ v = y)
    (hact : lRegularizedAction S T γ u v <
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧ η v = y ∧
      MapsTo η (Icc u v) K ∧ lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v ∧
      (lRegularizedAction S T η u v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) ∧
      H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) = (lRegularizedAction S T η u v : WithTop ℝ) := by
  have hupper' : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier :=
    fun t ht => D.regular_subset (hreg t ht)
  obtain ⟨η, hη, hηu, hηv, hηK, hηact, hmin⟩ :=
    H.exists_lRegularizedMinC1_of_action_lt_history_escape_barrier first last hle f hf hinj K hK hcross
      hu huv hupper' hlower S hS hreg g hμ hr hmetric hcompare
      (fun j t ht z => hscalar j t ht (f j z)) x hx hfront y γ hγ hstart hend hact
  refine ⟨η, hη, hηu, hηv, hηK, hηact, ?_, ?_⟩
  · have hmem := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle hscalar
      (f ⟨last, hle, le_rfl⟩ (η u)) (f ⟨first, le_rfl, hle⟩ (η v))
      (H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross S hS T
        hu huv.le hupper' hlower htime hmetric η hη)
    simpa only [hηu, hηv] using hmem
  · have heq := H.regularizedCost_eq_of_minimal_of_compact_barrier first last hle f hf hinj K hK hcross
      S hS g hu huv.le hμ hr hupper hlower htime hmetric hcompare hscalar η hη
      (fun δ hδ hδu hδv => hmin δ hδ (hδu.trans hηu) (hδv.trans hηv))
      (hηu.symm ▸ hx) (by simpa only [hηu] using hfront) (hηact.trans hact.le)
    simpa only [hηu, hηv] using heq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_regularizedCost_minimum_of_joint_metric_of_action_lt_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc u v, T - t ^ 2 ∈ J)
    (hreg : ∀ t ∈ Ioo u v, T - t ^ 2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (y : X) (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ u = x) (hend : γ v = y)
    (hact : lRegularizedAction S T γ u v <
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧ η v = y ∧
      MapsTo η (Icc u v) K ∧ lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v ∧
      (lRegularizedAction S T η u v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) ∧
      H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) = (lRegularizedAction S T η u v : WithTop ℝ) := by
  have htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier := fun t ht => hJ (hclock t ht)
  have hupper' : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jlast) :=
    .of_continuous_injective_isOpenMap (hf jlast).contMDiff.continuous (hinj jlast) (hf jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  have hconf : ∀ α : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → α u = x → α v = y →
      lRegularizedAction S T α u v ≤ lRegularizedAction S T γ u v → MapsTo α (Icc u v) K := by
    intro α hα hαu _ hαact
    exact H.mapsTo_of_lRegularizedAction_lt_history_escape_barrier first last hle f hf hinj K hK hcross
      hu huv.le hupper' hlower S hS htime g hμ hr hmetric hcompare
      (fun j t ht z => hscalar j t ht (f j z)) x hx hfront α hα hαu (hαact.trans_lt hact)
  obtain ⟨η, hη, hηu, hηv, hηK, hmin⟩ :=
    exists_lRegularizedMinC1_of_compact_action_sublevel_of_spatial_derivatives S hS T huv
      J hJ hclock hreg (S.chartGram_spatial_fderiv_continuousOn_of_joint_metric J hsmooth)
      (S.scalarOnE_spatial_fderiv_continuousOn_of_joint_metric J hsmooth) x y γ hγ hstart hend K hK hconf
  have hηact := hmin γ hγ hstart hend
  refine ⟨η, hη, hηu, hηv, hηK, hηact, ?_, ?_⟩
  · have hmem := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle hscalar
      (f ⟨last, hle, le_rfl⟩ (η u)) (f ⟨first, le_rfl, hle⟩ (η v))
      (H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross S hS T
        hu huv.le hupper' hlower htime hmetric η hη)
    simpa only [hηu, hηv] using hmem
  · have heq := H.regularizedCost_eq_of_minimal_of_compact_barrier first last hle f hf hinj K hK hcross
      S hS g hu huv.le hμ hr hupper hlower htime hmetric hcompare hscalar η hη
      (fun δ hδ hδu hδv => hmin δ hδ (hδu.trans hηu) (hδv.trans hηv))
      (hηu.symm ▸ hx) (by simpa only [hηu] using hfront) (hηact.trans hact.le)
    simpa only [hηu, hηv] using heq

theorem exists_regularizedCost_spatial_minimum_of_compact_action_sublevel
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc u v, T - t ^ 2 ∈ J)
    (hreg : ∀ t ∈ Ioo u v, T - t ^ 2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    {B A : ℝ}
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X)
    (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ u = x)
    (hact : lRegularizedAction S T γ u v < A)
    (hcoercive : ∀ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) →
      α ⟨last, hle, le_rfl⟩ u = f ⟨last, hle, le_rfl⟩ x →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = α ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = α ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) < A →
      ∀ j, MapsTo (α j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧
      MapsTo η (Icc u v) K ∧ lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v ∧
      (lRegularizedAction S T η u v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ∧
      H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η u v : WithTop ℝ) ∧
      ∀ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ≤
          H.regularizedCost first last hle T B u v (f ⟨last, hle, le_rfl⟩ x) q := by
  have htime : ∀ t ∈ Icc u v, T - t ^ 2 ∈ D.carrier := fun t ht => hJ (hclock t ht)
  have hupper' : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jlast) :=
    .of_continuous_injective_isOpenMap (hf jlast).contMDiff.continuous (hinj jlast) (hf jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  have hconf : ∀ α : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → α u = x →
      lRegularizedAction S T α u v ≤ lRegularizedAction S T γ u v → MapsTo α (Icc u v) K := by
    intro α hα hαu hαact
    obtain ⟨hint, hsum⟩ := H.intervalIntegrable_and_sum_stageRegularizedAction_of_common_curve
      first last hle f hf S hS T hu huv.le hupper' hlower htime hmetric α hα
    have hproject := hcoercive (fun j => f j ∘ α)
      (fun j => ((hf j).contMDiff.of_le (by norm_num)).comp hα) hint
      (by change f ⟨last, hle, le_rfl⟩ (α u) = _; rw [hαu])
      (fun i hi hl => by
        obtain ⟨z, _, hz, hzg⟩ := hcross i hi hl (α (Real.sqrt (T - H.time i.succ)))
        exact ⟨z, hz, hzg⟩)
      (hsum.trans_lt (hαact.trans_lt hact))
    exact H.mapsTo_of_stage_projections_mem first last hle f hinj K hu
      (H.time_le_of_mem_stageDomain hlower) hupper'.2 α hproject
  obtain ⟨η, hη, hηu, hηK, hmin⟩ :=
    exists_lRegularizedMinC1_free_endpoint_of_compact_action_sublevel_of_spatial_derivatives S hS T huv
      J hJ hclock hreg (S.chartGram_spatial_fderiv_continuousOn_of_joint_metric J hsmooth)
      (S.scalarOnE_spatial_fderiv_continuousOn_of_joint_metric J hsmooth) x γ hγ hstart K hK hconf
  have hηact := hmin γ hγ hstart
  have hglobal : ∀ q : (H.stage first).Carrier,
      ∀ A ∈ H.regularizedC1ActionValues first last hle T u v (f ⟨last, hle, le_rfl⟩ x) q,
        lRegularizedAction S T η u v ≤ A := by
    intro q A hA
    rcases hA with ⟨_, _, _, _, α, hα, hint, hstartα, _, hnode, rfl⟩
    by_contra hnot
    have hlow := lt_of_not_ge hnot
    have hstayK := hcoercive α hα hint hstartα hnode
      (hlow.trans (hηact.trans_lt hact))
    have hstay : ∀ j, MapsTo (α j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (range (f j)) := by
      intro j t ht
      obtain ⟨z, _, hz⟩ := hstayK j ht
      exact ⟨z, hz⟩
    have hbound : lRegularizedAction S T η u v ≤
        ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨δ, hδ, hδstart, _, hδact⟩ :=
        H.exists_lRegularizedAction_lt_of_confined_history_curves first last hle f hf hinj hcross
          S hS T hu huv.le hupper' hlower htime hmetric α hα hstay hnode hε
      have hδu : δ u = x := hinj ⟨last, hle, le_rfl⟩ (hδstart.trans hstartα)
      exact (hmin δ hδ hδu).trans hδact.le
    exact hlow.not_ge hbound
  have hmemC1 : lRegularizedAction S T η u v ∈ H.regularizedC1ActionValues first last hle T u v
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) := by
    have hmem := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross
      S hS T hu huv.le hupper' hlower htime hmetric η hη
    simpa only [hηu] using hmem
  have hcost : H.regularizedCost first last hle T B u v
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) =
        (lRegularizedAction S T η u v : WithTop ℝ) := by
    rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
    exact H.regularizedC1Cost_eq_of_minimum first last hle T u v _ _ _ hmemC1
      (hglobal (f ⟨first, le_rfl, hle⟩ (η v)))
  refine ⟨η, hη, hηu, hηK, hηact,
    H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle hscalar _ _ hmemC1,
    hcost, ?_⟩
  intro q
  rw [hcost, H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
  by_cases hne : (H.regularizedC1ActionValues first last hle T u v (f ⟨last, hle, le_rfl⟩ x) q).Nonempty
  · apply le_csInf (hne.image (fun A : ℝ => (A : WithTop ℝ)))
    rintro A ⟨r, hr, rfl⟩
    exact WithTop.coe_le_coe.mpr (hglobal q r hr)
  · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v _ q
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

theorem exists_regularizedCost_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc u v, T - t ^ 2 ∈ J)
    (hreg : ∀ t ∈ Ioo u v, T - t ^ 2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ u = x)
    (hact : lRegularizedAction S T γ u v <
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧
      MapsTo η (Icc u v) K ∧ lRegularizedAction S T η u v ≤ lRegularizedAction S T γ u v ∧
      (lRegularizedAction S T η u v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ∧
      H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η u v : WithTop ℝ) ∧
      ∀ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ≤
          H.regularizedCost first last hle T B u v (f ⟨last, hle, le_rfl⟩ x) q := by
  apply H.exists_regularizedCost_spatial_minimum_of_compact_action_sublevel first last hle
    f hf hinj K hK hcross hu huv hupper hlower S hS J hJ hclock hreg hsmooth hmetric hscalar
    x γ hγ hstart hact
  intro α hα hint hstartα hnode hαact
  exact H.mapsTo_common_compact_set_of_sum_stageRegularizedAction_lt first last hle
    f hf hinj K hK hcross hu huv.le
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
    hlower S g hμ hr hmetric hcompare α hα hint
    (fun j t ht => hscalar j t ht (α j t)) x hx hfront hstartα hnode hαact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_history_regularizedCost_minimum_of_action_lt_compact_barrier
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → W → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set W) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hclock : ∀ t ∈ Icc u v, T - t ^ 2 ∈ Icc c s)
    (g : SmoothRiemannianMetric ThreeModel W) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      (L.closedSolution W hcs.le).base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo u v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ ((L.closedSolution W hcs.le).base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : W) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (y : W) (γ : ℝ → W) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ u = x) (hend : γ v = y)
    (hact : lRegularizedAction (L.closedSolution W hcs.le) T γ u v <
      μ * r ^ 2 / (2 * (v - u)) - (2 * B / 3) * (v ^ 3 - u ^ 3)) :
    ∃ η : ℝ → W, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η u = x ∧ η v = y ∧
      MapsTo η (Icc u v) K ∧ lRegularizedAction (L.closedSolution W hcs.le) T η u v ≤ lRegularizedAction (L.closedSolution W hcs.le) T γ u v ∧
      (lRegularizedAction (L.closedSolution W hcs.le) T η u v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) ∧
      H.regularizedCost first last hle T B u v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ y) = (lRegularizedAction (L.closedSolution W hcs.le) T η u v : WithTop ℝ) := by
  have hregular : ∀ t ∈ Ioo u v, T - t ^ 2 ∈ Ioo c s := by
    intro t ht
    have ht0 : 0 ≤ t := hu.trans ht.1.le
    have hsqu := (sq_lt_sq₀ hu ht0).mpr ht.1
    have hsqv := (sq_lt_sq₀ ht0 (hu.trans huv.le)).mpr ht.2
    have hcu := hclock u ⟨le_rfl, huv.le⟩
    have hcv := hclock v ⟨huv.le, le_rfl⟩
    exact ⟨hcv.1.trans_lt (sub_lt_sub_left hsqv T), (sub_lt_sub_left hsqu T).trans_le hcu.2⟩
  exact H.exists_regularizedCost_minimum_of_joint_metric_of_action_lt_compact_barrier first last hle
    f hf hinj K hK hcross hu huv hupper hlower
    (L.closedSolution W hcs.le) (L.closedSolution_isSolutionOn W hac hcs)
    (Icc c s) Subset.rfl hclock hregular (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs)
    g hμ hr hmetric hcompare hscalar x hx hfront y γ hγ hstart hend hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryAttainment

theorem exists_regularizedCost_minimizer_of_ne_top
    (H : ObservedHistory.{uHistoryAttainment})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (hB : 0 ≤ B)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hfinite : H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v gamma =
        H.regularizedCost first last hle T B u v p q := by
  classical
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u v p q, A = ⊤ :=
    fun h => hfinite ((H.regularizedCost_eq_top_iff first last hle T B u v p q).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← ha] at hA
  have hu : 0 ≤ u := hA.1
  have huv : u ≤ v := hA.2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hA.2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hA.2.2.2.1
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q hA (ε := 1) zero_lt_one
  let V := H.regularizedC1ActionValues first last hle T u v p q
  have hV : V.Nonempty := ⟨c, hc⟩
  have hbdd : BddBelow V :=
    H.regularizedC1ActionValues_bddBelow_of_scalar_lower first last hle T u v B hscalar p q
  obtain ⟨values, hanti, hlim, hvalues⟩ := exists_seq_tendsto_sInf hV hbdd
  choose alpha halpha hint hstart hend hnodes hsum using fun n => (hvalues n).2.2.2.2
  have haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 (sInf V)) := by
    simpa only [hsum] using hlim
  obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, hgammaAction⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action first last hle
      hu huv hupper hpast p q (values 0) B (sInf V) hB alpha
      (fun n j => (halpha n j).contMDiffOn) hint hstart hend hnodes
      (fun n j t ht => hscalar j t ht (alpha n j t))
      (fun n => by rw [hsum n]; exact hanti (Nat.zero_le n)) haction
  have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
    gamma hgammaInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar j t ht (gamma j t))
  have hmember : H.regularizedExtendedAction first last T B u v gamma ∈
      H.regularizedActionValues first last hle T B u v p q :=
    ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, hgammaV, hgammaNodes, rfl⟩
  refine ⟨gamma, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, ?_⟩
  apply le_antisymm ?_ (H.regularizedCost_le_of_competitor first last hle T B u v p q hmember)
  rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p q, hext]
  apply le_csInf (hV.image (fun r : ℝ => (r : WithTop ℝ)))
  rintro _ ⟨r, hr, rfl⟩
  exact WithTop.coe_le_coe.mpr (hgammaAction.trans (csInf_le hbdd hr))

theorem exists_regularizedCost_spatial_minimizer
    (H : ObservedHistory.{uHistoryAttainment})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ∃ (q : (H.stage first).Carrier) (m : ℝ)
      (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier),
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v gamma = (m : WithTop ℝ) ∧
      (m : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q ∧
      H.regularizedCost first last hle T B u v p q = (m : WithTop ℝ) ∧
      ∀ z : (H.stage first).Carrier, (m : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
  classical
  obtain ⟨q₀, hq₀⟩ := hfinite
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u v p q₀, A = ⊤ :=
    fun h => hq₀ ((H.regularizedCost_eq_top_iff first last hle T B u v p q₀).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← ha] at hA
  have hu : 0 ≤ u := hA.1
  have huv : u ≤ v := hA.2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hA.2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hA.2.2.2.1
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q₀ hA (ε := 1) zero_lt_one
  let V : Set ℝ := {r | ∃ q : (H.stage first).Carrier,
    r ∈ H.regularizedC1ActionValues first last hle T u v p q}
  have hV : V.Nonempty := ⟨c, q₀, hc⟩
  have hbdd : BddBelow V := by
    refine ⟨-(2 * B / 3) * (v ^ 3 - u ^ 3), ?_⟩
    rintro r ⟨q, hr⟩
    exact H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B hscalar p q hr
  obtain ⟨values, hanti, hlim, hvalues⟩ := exists_seq_tendsto_sInf hV hbdd
  choose endpoints hvaluesEnd using hvalues
  choose alpha halpha hint hstart hend hnodes hsum using fun n => (hvaluesEnd n).2.2.2.2
  have haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 (sInf V)) := by
    simpa only [hsum] using hlim
  obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaNodes, hgammaAction⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_free_endpoint first last hle
      hu huv hupper hpast p (values 0) (max B 0) (sInf V) (le_max_right _ _) alpha
      (fun n j => (halpha n j).contMDiffOn) hint hstart hnodes
      (fun n j t ht => (neg_le_neg (le_max_left B 0)).trans (hscalar j t ht (alpha n j t)))
      (fun n => by rw [hsum n]; exact hanti (Nat.zero_le n)) haction
  let q := gamma ⟨first, le_rfl, hle⟩ v
  let m := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  have hext : H.regularizedExtendedAction first last T B u v gamma = (m : WithTop ℝ) :=
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
      gamma hgammaInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (gamma j t))
  have hmember : (m : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q :=
    ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, rfl, hgammaNodes, hext⟩
  have hmin (z : (H.stage first).Carrier) :
      (m : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
    rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
    by_cases hne : (H.regularizedC1ActionValues first last hle T u v p z).Nonempty
    · apply le_csInf (hne.image (fun r : ℝ => (r : WithTop ℝ)))
      rintro _ ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (hgammaAction.trans (csInf_le hbdd ⟨z, hr⟩))
    · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p z
        (Set.not_nonempty_iff_eq_empty.mp hne)]
      exact le_top
  exact ⟨q, m, gamma, hgammaAC, hgammaInt, hgammaU, rfl, hgammaNodes, hext, hmember,
    le_antisymm (H.regularizedCost_le_of_competitor first last hle T B u v p q hmember) (hmin q), hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
