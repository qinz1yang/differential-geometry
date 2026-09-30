import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FixedFactorComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.InitialDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryFreeFactors
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

theorem initial_finite_freeFactor_bound (P : OrientedThreeStage.{u}) :
    ∃ N : ℕ, 0 < N ∧ InitialFiniteFreeFactorBound P N := by
  classical
  let M := P.toClosedOrientedManifold
  let : Finite (ConnectedComponents M.Carrier) := M.finite_components
  let : Fintype (ConnectedComponents M.Carrier) := Fintype.ofFinite _
  let x : ∀ c : ConnectedComponents M.Carrier, (M.component c).Carrier :=
    fun c => Classical.choice inferInstance
  have h : ∀ c : ConnectedComponents M.Carrier, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (A : Type u) [Group A] [Finite A],
      GC.Group.IsFreeFactor A (FundamentalGroup P.Carrier (x c).val) → Nat.card A ≤ N :=
    fun c => GC.Group.exists_finite_freeFactor_order_bound
      (initial_finiteIndecomposablePresentation P (x c).val)
  choose d hd hb using h
  refine ⟨1 + ∑ c, d c, by omega, ?_⟩
  intro p A hA hfinite hfactor
  let := hfinite
  let c := ConnectedComponents.mk (show M.Carrier from p)
  let y : (M.component c).Carrier := ⟨p, rfl⟩
  let e := (GC.Surgery.componentFundamentalGroupEquiv M c y).symm.trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y (x c)).trans
      (GC.Surgery.componentFundamentalGroupEquiv M c (x c)))
  have he : GC.Group.IsFreeFactor A (FundamentalGroup P.Carrier (x c).val) :=
    hfactor.congr (MulEquiv.refl A) e
  have hcard := hb c A he
  have hs : d c ≤ ∑ a, d a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (d a)) (Finset.mem_univ c)
  omega

theorem general_uniform_history_degree (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ N : ℕ, 0 < N ∧ UniformHistoryDegreeBound P g N := by
  obtain ⟨N, hN, hb⟩ := initial_finite_freeFactor_bound P
  exact ⟨N, hN, uniformHistoryDegree_of_initial_freeFactorBound P g N hb⟩

end GC.GeneralFlow
