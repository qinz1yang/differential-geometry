import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapFreeFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeGeometricHorizon
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

def InitialFiniteFreeFactorBound (P : OrientedThreeStage.{u}) (N : ℕ) : Prop :=
  ∀ (p : P.Carrier) (G : Type u) [Group G], Finite G →
    GC.Group.IsFreeFactor G (FundamentalGroup P.Carrier p) → Nat.card G ≤ N

theorem completed_history_freeFactor {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (hinit : InitialIdentification P g H.toHistory)
    (hc : ∀ i : Fin H.eventCount, Nonempty (SmoothCutCapCompletion (H.coreEvent i).transition))
    (j : Fin (H.eventCount + 1)) (q : (H.stage j).Carrier) :
    ∃ p : P.Carrier, GC.Group.IsFreeFactor (FundamentalGroup (H.stage j).Carrier q)
      (FundamentalGroup P.Carrier p) := by
  induction j using Fin.induction with
  | zero =>
      let e := fundamentalGroupMulEquivOfHomotopyEquiv
        hinit.map.symm.toHomeomorph.toHomotopyEquiv q (hinit.map.symm q) rfl
      exact ⟨hinit.map.symm q, (GC.Group.IsFreeFactor.refl _).congr (MulEquiv.refl _) e⟩
  | succ i ih =>
      obtain ⟨h⟩ := hc i
      obtain ⟨p, hp⟩ := GC.Surgery.actual_retained_freeFactor
        (SphericalCutCapTransition.ofSmoothCutCapTransition (H.coreEvent i).transition h) q
      obtain ⟨p₀, h₀⟩ := ih p
      exact ⟨p₀, hp.trans h₀⟩

theorem stage_degree_of_freeFactor_ancestry {P Q : OrientedThreeStage.{u}} (N : ℕ)
    (hb : InitialFiniteFreeFactorBound P N)
    (ha : ∀ q : Q.Carrier, ∃ p : P.Carrier,
      GC.Group.IsFreeFactor (FundamentalGroup Q.Carrier q) (FundamentalGroup P.Carrier p)) :
    StageFiniteDegreeBound Q N := by
  intro U x hU y hfinite
  let M := Q.toClosedOrientedManifold
  have heq : U = M.componentSet (ConnectedComponents.mk x) := by
    exact hU.trans (M.componentSet_mk (show M.Carrier from x)).symm
  let e : U ≃ₜ (M.component (ConnectedComponents.mk x)).Carrier := Homeomorph.setCongr heq
  let a := (fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv y (e y) rfl).trans
    (GC.Surgery.componentFundamentalGroupEquiv M _ (e y))
  obtain ⟨p, hp⟩ := ha y.val
  exact hb p (FundamentalGroup U y) hfinite
    (hp.congr a.symm (MulEquiv.refl _))

theorem uniformHistoryDegree_of_completed_freeFactorBound
    (P : OrientedThreeStage.{u}) (g : P.Metric) (N : ℕ)
    (hb : InitialFiniteFreeFactorBound P N)
    (hc : ∀ (H : RetainedCoreHistory.{u}) {B : ℝ} {p : CutoffParameters} {δ ρ : ℝ},
      H.InCutoffClass g B p δ ρ → ∀ i : Fin H.eventCount,
        Nonempty (SmoothCutCapCompletion (H.coreEvent i).transition)) :
    UniformHistoryDegreeBound P g N := by
  intro H B p δ ρ hH j
  exact stage_degree_of_freeFactor_ancestry N hb
    (completed_history_freeFactor H hH.1.some (hc H hH) j)

theorem general_strong_canonical_of_completed_freeFactorBound
    (P : OrientedThreeStage.{u}) (g : P.Metric) (N : ℕ) (hN : 0 < N)
    (hb : InitialFiniteFreeFactorBound P N)
    (hc : ∀ (H : RetainedCoreHistory.{u}) {B : ℝ} {p : CutoffParameters} {δ ρ : ℝ},
      H.InCutoffClass g B p δ ρ → ∀ i : Fin H.eventCount,
        Nonempty (SmoothCutCapCompletion (H.coreEvent i).transition)) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  general_strong_canonical_of_history_degree P g
    ⟨N, hN, uniformHistoryDegree_of_completed_freeFactorBound P g N hb hc⟩

end GC.GeneralFlow
