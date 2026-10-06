import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.Fibers
import Mathlib.Topology.Covering.Basic

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem existsUnique_covering_lift_of_connected_fibers
    {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    (σ : C(loopCircle, loopCircle)) (hσ : Function.Surjective σ)
    (hfiber : ∀ θ, IsConnected (σ ⁻¹' {θ}))
    (p : E → B) (hp : IsCoveringMap p)
    (γ : C(loopCircle, B)) (δ : C(loopCircle, E))
    (hproj : ∀ θ, p (δ θ) = γ (σ θ)) :
    ∃! γLift : C(loopCircle, E),
      (∀ θ, p (γLift θ) = γ θ) ∧ δ = γLift.comp σ := by
  have hfactor : Function.FactorsThrough δ σ := by
    intro x y hxy
    let : PreconnectedSpace (σ ⁻¹' {σ x}) :=
      Subtype.preconnectedSpace (hfiber (σ x)).isPreconnected
    have hconst : ∀ a b : σ ⁻¹' {σ x}, δ a = δ b :=
      hp.const_of_comp (δ.continuous.comp continuous_subtype_val)
        (fun a b => by rw [hproj, hproj, a.property, b.property])
    exact hconst ⟨x, rfl⟩ ⟨y, hxy.symm⟩
  have hquot : _root_.Topology.IsQuotientMap σ :=
    σ.continuous.isClosedMap.isQuotientMap σ.continuous hσ
  let γLift : C(loopCircle, E) := hquot.lift δ hfactor
  have hcomp : γLift.comp σ = δ := hquot.lift_comp δ hfactor
  refine ⟨γLift, ⟨?_, hcomp.symm⟩, ?_⟩
  · intro θ
    obtain ⟨t, rfl⟩ := hσ θ
    exact (congrArg p (DFunLike.congr_fun hcomp t)).trans (hproj t)
  · intro η hη
    ext θ
    obtain ⟨t, rfl⟩ := hσ θ
    exact (DFunLike.congr_fun hη.2 t).symm.trans (DFunLike.congr_fun hcomp t).symm

/-- A covering lift of a weakly monotone parametrized loop descends uniquely
to a lift of the loop, preserving the original phase map. -/
theorem IsWeaklyMonotoneOnce.existsUnique_covering_lift_of_comp
    {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (p : E → B) (hp : IsCoveringMap p)
    (γ : C(loopCircle, B)) (δ : C(loopCircle, E))
    (hproj : ∀ θ, p (δ θ) = γ (σ θ)) :
    ∃! γLift : C(loopCircle, E),
      (∀ θ, p (γLift θ) = γ θ) ∧ δ = γLift.comp σ :=
  existsUnique_covering_lift_of_connected_fibers σ hσ.surjective
    hσ.isConnected_fiber p hp γ δ hproj

end DifferentialGeometry.Geometry
