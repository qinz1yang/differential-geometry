import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (TruncatedNeck)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

private def strongNeckBody (K : ObservedHistory.{u}) (k : Fin (K.eventCount + 1)) {s : ℝ}
    (G : (K.stage k).IncomingSlab (K.time k) s) (eps : ℝ) (y : (K.stage k).Carrier) (t : ℝ)
    (first : Fin (K.eventCount + 1)) (O : Opens (K.stage k).Carrier)
    (f : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O → (K.event j).incoming.terminalRegularOpen)
    (hf : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j hj hl)) : Prop :=
  ∃ (hts : K.time first < s) (gflow : ℝ → SmoothRiemannianMetric ThreeModel O),
    K.time first ≤ t - 1 / 5 * (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin K.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (K.time j.castSucc) (K.time j.succ),
        gflow τ = localPullMetric ((K.event j).terminal.extendedMetric τ) (f j hj hl)
          (hf j hj hl)) ∧
    (∀ τ ∈ Ico (K.time k) s, gflow τ = (G.flow.base.metric τ).restrictOpen O) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen (K.time first) s hts)) ∧
    ∃ z : O, z.val = y ∧
      Nonempty (TruncatedNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := O)
          (RealTimeInterval.closedOpen (K.time first) s hts)) eps (1 / 5) z t)

private theorem historyStrongNeck_iff_exists_strongNeckBody (K : ObservedHistory.{u})
    (k : Fin (K.eventCount + 1)) {s : ℝ} (G : (K.stage k).IncomingSlab (K.time k) s)
    (eps : ℝ) (y : (K.stage k).Carrier) (t : ℝ) :
    K.HistoryStrongNeck k G eps y t ↔ ∃ (first : Fin (K.eventCount + 1)) (hle : first ≤ k),
      K.strongNeckBody k G eps y t first (K.backwardSurvivorDomain first k hle)
        (K.backwardSurvivorTerminalMap first k hle)
        (K.backwardSurvivorTerminalMap_isLocalDiffeomorph first k hle) := by
  rfl

private theorem strongNeckBody_congr (K : ObservedHistory.{u}) (k : Fin (K.eventCount + 1))
    {s : ℝ} (G : (K.stage k).IncomingSlab (K.time k) s) (eps : ℝ) (y : (K.stage k).Carrier)
    (t : ℝ) (first : Fin (K.eventCount + 1)) {O₁ O₂ : Opens (K.stage k).Carrier}
    (f₁ : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O₁ → (K.event j).incoming.terminalRegularOpen)
    (f₂ : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O₂ → (K.event j).incoming.terminalRegularOpen)
    (hf₁ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₁ j hj hl))
    (hf₂ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₂ j hj hl))
    (hO : O₁ = O₂)
    (hf : ∀ j hj hl (x : O₁), f₁ j hj hl x = f₂ j hj hl ⟨x.val, hO ▸ x.property⟩) :
    K.strongNeckBody k G eps y t first O₁ f₁ hf₁ ↔
      K.strongNeckBody k G eps y t first O₂ f₂ hf₂ := by
  subst hO
  have : f₁ = f₂ := funext fun j => funext fun hj => funext fun hl => funext fun x => hf j hj hl x
  subst this
  rfl

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (T : ℝ) (hT : H.horizon ≤ T)
  (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
  (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount))

theorem backwardSurvivorDomain_extendHorizon (first k : Fin (H.eventCount + 1))
    (hle : first ≤ k) :
    (H.extendHorizon T hT S hS).toHistory.backwardSurvivorDomain first k hle =
      H.toHistory.backwardSurvivorDomain first k hle := by
  ext q
  exact ⟨fun ⟨A⟩ => ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩,
    fun ⟨A⟩ => ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩⟩

theorem historyStrongNeck_extendHorizon_iff (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ) :
    (H.extendHorizon T hT S hS).toHistory.HistoryStrongNeck k G eps y t ↔
      H.toHistory.HistoryStrongNeck k G eps y t := by
  refine (ObservedHistory.historyStrongNeck_iff_exists_strongNeckBody
    (H.extendHorizon T hT S hS).toHistory k G eps y t).trans (Iff.trans ?_
      (ObservedHistory.historyStrongNeck_iff_exists_strongNeckBody H.toHistory k G eps y t).symm)
  refine exists_congr fun first => exists_congr fun hle => ?_
  exact ObservedHistory.strongNeckBody_congr H.toHistory k G eps y t first _ _ _ _
    (H.backwardSurvivorDomain_extendHorizon T hT S hS first k hle) fun j hj hl x => by
      apply Subtype.ext
      let A := Classical.choice x.property
      exact (H.toHistory.backwardSurvivorMap_eq_point first k hle j.castSucc hj
        (j.castSucc_lt_succ.le.trans hl) _ ⟨A.point, A.endpoint_eq, A.crossing⟩).symm

theorem stronglyCanonicalAt_extendHorizon_iff (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 : ℝ) (y : (H.stage k).Carrier)
    (t : ℝ) :
    (H.extendHorizon T hT S hS).StronglyCanonicalAt k G ε ε₁ C1 C2 y t ↔
      H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t :=
  exists_congr fun _ => and_congr_right fun _ =>
    imp_congr_right fun _ => H.historyStrongNeck_extendHorizon_iff T hT S hS k G ε₁ y t

theorem stronglyCanonicalBefore_extendHorizon_iff (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan t₀ : ℝ) :
    (H.extendHorizon T hT S hS).StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀ ↔
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀ :=
  forall_congr' fun y => forall_congr' fun t => imp_congr_right fun _ => imp_congr_right fun _ =>
    H.stronglyCanonicalAt_extendHorizon_iff T hT S hS k G ε ε₁ C1 C2 y t

theorem eventSlabsStronglyCanonical_extendHorizon_iff (ε ε₁ C1 C2 qcan : ℝ)
    (k : Fin (H.eventCount + 1)) :
    (H.extendHorizon T hT S hS).EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan k ↔
      H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan k :=
  forall_congr' fun j => imp_congr_right fun _ =>
    H.stronglyCanonicalBefore_extendHorizon_iff T hT S hS j.castSucc _ ε ε₁ C1 C2 qcan _

theorem exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {T : ℝ}
    (hat : H.time (Fin.last H.eventCount) < T) (hTs : T < s) {ε ε₁ C1 C2 qcan : ℝ}
    (hcan : H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1 C2 qcan s)
    (v : Icc (0 : ℝ)
      (H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.horizon)
    (hv : (H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage
      v = Fin.last H.eventCount) :
    ∃ (s' : ℝ) (G' : ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).stage
        ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage
          v)).IncomingSlab
        ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).time
          ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage
            v)) s'),
      (v : ℝ) < s' ∧
      (∀ τ ∈ Icc ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).time
          ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage
            v)) (v : ℝ),
        G'.flow.base.metric τ =
          (H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.stageMetric
            ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage
              v) τ) ∧
      (H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).StronglyCanonicalBefore
        ((H.extendHorizon T (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG).toHistory.activeStage v)
        G' ε ε₁ C1 C2 qcan s' := by
  rw [hv]
  refine ⟨s, G, v.2.2.trans_lt hTs, fun τ hτ => ?_,
    (H.stronglyCanonicalBefore_extendHorizon_iff T _ _ hG _ G ε ε₁ C1 C2 qcan s).2 hcan⟩
  exact (H.stageMetric_extendHorizon_last (hend ▸ hat.le) (G.closedPrefix T hat hTs) hG hat
    τ).symm

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
