import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CompletedHistoryDegree
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

theorem initial_component_card_bound (P : OrientedThreeStage.{u}) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : P.Carrier, Nat.card (FundamentalGroup P.Carrier p) ≤ N := by
  classical
  let M := P.toClosedOrientedManifold
  let : Finite (ConnectedComponents M.Carrier) := M.finite_components
  let : Fintype (ConnectedComponents M.Carrier) := Fintype.ofFinite _
  let x : ∀ c : ConnectedComponents M.Carrier, (M.component c).Carrier :=
    fun c => Classical.choice inferInstance
  let d : ConnectedComponents M.Carrier → ℕ :=
    fun c => Nat.card (FundamentalGroup (M.component c).Carrier (x c))
  refine ⟨1 + ∑ c, d c, by omega, ?_⟩
  intro p
  let c := ConnectedComponents.mk (show M.Carrier from p)
  let y : (M.component c).Carrier := ⟨p, rfl⟩
  let e := (GC.Surgery.componentFundamentalGroupEquiv M c y).symm.trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y (x c))
  have he : Nat.card (FundamentalGroup P.Carrier p) = d c := Nat.card_congr e.toEquiv
  rw [he]
  have hs : d c ≤ ∑ a, d a := Finset.single_le_sum (fun a _ => Nat.zero_le (d a)) (Finset.mem_univ c)
  omega

theorem initial_freeFactorBound_of_finite_groups (P : OrientedThreeStage.{u})
    (hf : ∀ p : P.Carrier, Finite (FundamentalGroup P.Carrier p)) :
    ∃ N : ℕ, 0 < N ∧ InitialFiniteFreeFactorBound P N := by
  obtain ⟨N, hN, hb⟩ := initial_component_card_bound P
  refine ⟨N, hN, ?_⟩
  intro p G hG hfinite hfactor
  let := hf p
  exact (GC.Group.finite_freeFactor_card_le hfactor).trans (hb p)

theorem uniformHistoryDegree_of_finite_initial_groups
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hf : ∀ p : P.Carrier, Finite (FundamentalGroup P.Carrier p))
    (hc : ∀ (H : RetainedCoreHistory.{u}) {B : ℝ} {p : CutoffParameters} {δ ρ : ℝ},
      H.InCutoffClass g B p δ ρ → ∀ i : Fin H.eventCount,
        Nonempty (SmoothCutCapCompletion (H.coreEvent i).transition)) :
    ∃ N : ℕ, 0 < N ∧ UniformHistoryDegreeBound P g N := by
  obtain ⟨N, hN, hb⟩ := initial_freeFactorBound_of_finite_groups P hf
  exact ⟨N, hN, uniformHistoryDegree_of_completed_freeFactorBound P g N hb hc⟩

theorem general_strong_canonical_of_finite_initial_groups
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hf : ∀ p : P.Carrier, Finite (FundamentalGroup P.Carrier p))
    (hc : ∀ (H : RetainedCoreHistory.{u}) {B : ℝ} {p : CutoffParameters} {δ ρ : ℝ},
      H.InCutoffClass g B p δ ρ → ∀ i : Fin H.eventCount,
        Nonempty (SmoothCutCapCompletion (H.coreEvent i).transition)) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  general_strong_canonical_of_history_degree P g
    (uniformHistoryDegree_of_finite_initial_groups P g hf hc)

end GC.GeneralFlow
