import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TubeFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteInitialDegree
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

theorem retained_history_freeFactor {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (hinit : InitialIdentification P g H.toHistory)
    (j : Fin (H.eventCount + 1)) (q : (H.stage j).Carrier) :
    ∃ p : P.Carrier, GC.Group.IsFreeFactor (FundamentalGroup (H.stage j).Carrier q)
      (FundamentalGroup P.Carrier p) := by
  induction j using Fin.induction with
  | zero =>
      let e := fundamentalGroupMulEquivOfHomotopyEquiv
        hinit.map.symm.toHomeomorph.toHomotopyEquiv q (hinit.map.symm q) rfl
      exact ⟨hinit.map.symm q, (GC.Group.IsFreeFactor.refl _).congr (MulEquiv.refl _) e⟩
  | succ i ih =>
      obtain ⟨p, hp⟩ := GC.Surgery.smooth_retained_freeFactor (H.coreEvent i).transition q
      obtain ⟨p₀, h₀⟩ := ih p
      exact ⟨p₀, hp.trans h₀⟩

theorem uniformHistoryDegree_of_initial_freeFactorBound
    (P : OrientedThreeStage.{u}) (g : P.Metric) (N : ℕ)
    (hb : InitialFiniteFreeFactorBound P N) : UniformHistoryDegreeBound P g N := by
  intro H B p δ ρ hH j
  exact stage_degree_of_freeFactor_ancestry N hb
    (retained_history_freeFactor H hH.1.some j)

theorem strong_canonical_of_initial_freeFactorBound
    (P : OrientedThreeStage.{u}) (g : P.Metric) (N : ℕ) (hN : 0 < N)
    (hb : InitialFiniteFreeFactorBound P N) : CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  general_strong_canonical_of_history_degree P g
    ⟨N, hN, uniformHistoryDegree_of_initial_freeFactorBound P g N hb⟩

theorem uniform_history_degree_of_finite_initial_groups
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hf : ∀ p : P.Carrier, Finite (FundamentalGroup P.Carrier p)) :
    ∃ N : ℕ, 0 < N ∧ UniformHistoryDegreeBound P g N := by
  obtain ⟨N, hN, hb⟩ := initial_freeFactorBound_of_finite_groups P hf
  exact ⟨N, hN, uniformHistoryDegree_of_initial_freeFactorBound P g N hb⟩

theorem strong_canonical_of_finite_initial_groups
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hf : ∀ p : P.Carrier, Finite (FundamentalGroup P.Carrier p)) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  general_strong_canonical_of_history_degree P g
    (uniform_history_degree_of_finite_initial_groups P g hf)

end GC.GeneralFlow
