import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelChild
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportBasic

set_option autoImplicit false

/-!
# CP1-D2 (G3): the kernel of a connected marked space is unchanged across a surgery event

For one actual surgery event `E : MetricCutCapEvent P Q a s`, if `u : X → P` (pre-surgery slice)
and `v : X → Q` (post-surgery slice) correspond through the regular crossing of the event
(i.e. lie in the unchanged region `old` and `v = oldOutput`) and `X` is connected, then
`ker (π₁ X → π₁ P) = ker (π₁ X → π₁ Q)`.  Proof: both maps factor through the same component of
the retained core, which injects `π₁` into `P` (sphere cut) and into `Q` (capping), then AT11.
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology GC.Surgery

namespace GC.LongTime.CuspP1

universe u v

theorem kernel_eq_of_regularCrossing_CPD2 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) {X : Type v} [TopologicalSpace X] [PreconnectedSpace X]
    (u : C(X, P.Carrier)) (v : C(X, Q.Carrier))
    (hcross : ∀ y, E.RegularCrossing (u y) (v y)) (x : X) :
    (FundamentalGroup.map u x).ker = (FundamentalGroup.map v x).ker := by
  classical
  let Etr := E.transition
  have hz : ∀ y, ∃ w : E.old, (w.1.1 : P.Carrier) = u y ∧ E.oldOutput w = v y := by
    intro y
    obtain ⟨w, -, hw1, hw2⟩ := hcross y
    exact ⟨w, hw1, hw2⟩
  choose z hzu hzv using hz
  -- the lift `X → core`
  have hacont : Continuous fun y => (z y).1 := by
    apply continuous_induced_rng.2
    exact u.continuous.congr fun y => (hzu y).symm
  let a₀ : C(X, Etr.trace.tubes.core) := ⟨fun y => (z y).1, hacont⟩
  -- the child component of `v x`
  let c : ConnectedComponents Q.Carrier := ConnectedComponents.mk (v x)
  have hpres : ∀ y, Etr.trace.presentation (Etr.trace.capping.coreInclusion (a₀ y)) =
      Sum.inl (v y) := fun y => (E.oldOutput_eq (z y)).trans (congrArg Sum.inl (hzv y))
  have hc : Etr.childCoreComponent c = ConnectedComponents.mk (a₀ x) := by
    unfold SmoothCutCapTransition.childCoreComponent CutCapTopology.childCore
    rw [Equiv.symm_apply_eq]
    change ConnectedComponents.mk _ = _
    simp only [Capping.componentEquiv, Equiv.ofBijective_apply, Capping.componentMap_mk]
    congr 1
    exact (Etr.trace.presentation.symm_apply_eq).mpr (hpres x).symm
  have hmem : ∀ y, ConnectedComponents.mk (a₀ y) = Etr.childCoreComponent c := by
    intro y
    rw [hc]
    have hpc : IsPreconnected (Set.range a₀) := isPreconnected_range a₀.continuous
    have := hpc.subset_connectedComponent (x := a₀ x) ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ConnectedComponents.coe_eq_coe'.mpr this
  let a' : C(X, Etr.ChildCore c) := ⟨fun y => ⟨a₀ y, hmem y⟩, a₀.continuous.subtype_mk _⟩
  have hm := injective_coreComponentToParent_CPD2 Etr (Etr.childCoreComponent c) (a' x)
  have hp := injective_childCoreToQ_CPD2 Etr c (a' x)
  obtain ⟨h1, h2⟩ := kernel_common_core a' (coreComponentToParent_CPD2 Etr
    (Etr.childCoreComponent c)) (childCoreToQ_CPD2 Etr c) x hm hp
  have eu : (coreComponentToParent_CPD2 Etr (Etr.childCoreComponent c)).comp a' = u := by
    ext y; exact hzu y
  have ev : (childCoreToQ_CPD2 Etr c).comp a' = v := by
    ext y
    have h := Etr.childCoreInclusionFun_eq c (a' y)
    have h' := hpres y
    change Etr.trace.presentation (Etr.trace.capping.coreInclusion (a₀ y)) = _ at h
    rw [h'] at h
    exact (Sum.inl.inj h).symm
  rw [← eu, ← ev]
  exact h1.trans h2

end GC.LongTime.CuspP1
