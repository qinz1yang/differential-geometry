import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainMainC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongStepC11SG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingStarC11SC

/-!
# Wire: the producer `strong` field to the ch12 consumer premise (C11SG, S16 G2; S16CEIL)

`PreparedSpatialState.strong` carries per-state constants `C1S C2S`; since O-CH11-S16CEIL the state
also carries the shared bound `C1S_le : C1S ≤ strongC1_C11SC C.epsilon C.C1` (Base `1`, Step `max`
with the class field `C1strong_le`), where `strongC1_C11SC` is a closed term of `C.epsilon` fixed
before `P / g / B / κ`.  `hstrong_of_stateStrong_C11SG` therefore turns `∀ n, (S.state n).strong`
**without any extra premise** into the premise `hstrong` of `hfull_of_stateStrong_C12X` /
`strongCanonicalSupplyV2_of_stateStrong_C12X` at the shared ceiling
`C1ceil_C11SC C = C1star_C12X C Ccore Cu`, `C2ceil_C11SC C = C2star_C12X C Ccore Cu`
(which also dominates the old ceiling `max C.C1s C.Cbirth`, `max C.C2s (max C.Cbirth Cgrad)`).
The former explicit uniform bound `hb` is gone.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace GC.LongTime.Ch11

open GC.GeneralFlow

universe u

/-- **Strong field to the hext premise**, at the shared ceiling `C1ceil_C11SC C / C2ceil_C11SC C`;
no uniform-bound premise (the state's `C1S_le / C2S_le` pay it). -/
theorem hstrong_of_stateStrong_C11SG {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g) :
    ∀ n : ℕ, ∀ t : Icc (0 : ℝ) (S.state n).history.toHistory.horizon,
      (t : ℝ) < preparedSpatialHorizon n →
      (S.state n).history.time ((S.state n).history.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : ((S.state n).history.toHistory.stageAt t).Carrier,
        ((S.state n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) C.epsilon (C1ceil_C11SC.{u} C)
            (C2ceil_C11SC.{u} C) x,
          W.capTubeHasNeckChart C.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ) (G : ((S.state n).history.stage
                ((S.state n).history.toHistory.activeStage t)).IncomingSlab
                ((S.state n).history.time ((S.state n).history.toHistory.activeStage t)) s'),
              (∀ τ ∈ Icc ((S.state n).history.time
                  ((S.state n).history.toHistory.activeStage t)) (t : ℝ),
                G.flow.base.metric τ = (S.state n).history.toHistory.stageMetric
                  ((S.state n).history.toHistory.activeStage t) τ) ∧
              (S.state n).history.toHistory.HistoryStrongNeckFull_C12X
                ((S.state n).history.toHistory.activeStage t) G C.epsilon x t := by
  intro n t ht hreg x hx
  have h : StrongAtC11SG (S.state n).history.toHistory C.epsilon (S.state n).C1S
      (S.state n).C2S t x := (S.state n).strong t ht hreg x hx
  exact strongAtIdx_transport_C11SG rfl HEq.rfl HEq.rfl
    ((S.state n).C1S_le.trans (strongC1_le_C1ceil_C11SC C))
    ((S.state n).C2S_le.trans (strongC2_le_C2ceil_C11SC C))
    (fun s' G hagree hN => ⟨s', G, hagree, hN⟩) h

/-- **G2 consumer**: the producer `strong` field alone gives the S16 item
`StrongCanonicalSupplyV2_C11E` at the shared ceiling on the chain's own surgery `(F, q)`
(through `strongCanonicalSupplyV2_of_stateStrong_C12X`); no `hb`, no other S16 input. -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      StrongCanonicalSupplyV2_C11E F q.neckRadius C.epsilon (C1ceil_C11SC.{u} C)
        (C2ceil_C11SC.{u} C) := by
  obtain ⟨F, q, -, -, hTower, -, -, -, -, -, hpref, -⟩ :=
    S.exists_surgery_with_spatial_control_and_decay
  exact ⟨F, q, strongCanonicalSupplyV2_of_stateStrong_C12X S F hTower q
    (fun n t ht => (hpref n t ht).2.1) _ _ (hstrong_of_stateStrong_C11SG S)⟩

end GC.LongTime.Ch11

end
