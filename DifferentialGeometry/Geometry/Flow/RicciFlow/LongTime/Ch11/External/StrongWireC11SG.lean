import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainMainC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongStepC11SG

/-!
# Wire: the producer `strong` field to the ch12 consumer premise (C11SG, S16 G2)

`PreparedSpatialState.strong` carries per-state constants `C1S C2S` (the class constants of
`native_strongFull_of_classFull_C12X` are not uniform).  `hstrong_of_stateStrong_C11SG` turns
`∀ n, (S.state n).strong` plus the **explicit uniform bound** (R-S16 D-1: `C1S ≤ max C1s Cbirth`,
`C2S ≤ max C2s (max Cbirth Cgrad)`) into the premise `hstrong` of
`exists_w1_params_strong_C12X` (constants of `canonical`).  The uniform bound is the only open
input; it follows once the class producers use the uniform Full class producer (S16F, hwin).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace GC.LongTime.Ch11

open GC.GeneralFlow

universe u

/-- **Strong field to the hext premise** (conditional on the explicit uniform bound `hb`). -/
theorem hstrong_of_stateStrong_C11SG {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (hb : ∀ n : ℕ, (S.state n).C1S ≤ max C.C1s C.Cbirth ∧
      (S.state n).C2S ≤ max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) :
    ∀ n : ℕ, ∀ t : Icc (0 : ℝ) (S.state n).history.toHistory.horizon,
      (t : ℝ) < preparedSpatialHorizon n →
      (S.state n).history.time ((S.state n).history.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : ((S.state n).history.toHistory.stageAt t).Carrier,
        ((S.state n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) C.epsilon (max C.C1s C.Cbirth)
            (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
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
  exact strongAtIdx_transport_C11SG rfl HEq.rfl HEq.rfl (hb n).1 (hb n).2
    (fun s' G hagree hN => ⟨s', G, hagree, hN⟩) h

/-- **G2 consumer**: the producer `strong` field plus the explicit uniform bound give the S16 item
`StrongCanonicalSupplyV2_C11E` of the enhanced tuple (through `exists_w1_params_strong_C12X`);
no other S16 input. -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hb : ∀ n : ℕ, (S.state n).C1S ≤ max C.C1s C.Cbirth ∧
      (S.state n).C2S ≤ max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (ε C1 C2 : ℝ),
      StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 := by
  obtain ⟨F, q, -, -, ε, C1, C2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS⟩ :=
    exists_w1_params_strong_C12X S hP3 hprof (hstrong_of_stateStrong_C11SG S hb)
  exact ⟨F, q, ε, C1, C2, hS⟩

end GC.LongTime.Ch11

end
