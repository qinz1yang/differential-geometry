import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreRestoration
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction

/-!
The same Euclidean patch transports through the actual regular-fibre filling map, preserving
its full source, its exact image and its literal pointwise composite.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {q : PlaneLift.{u} × Circle | ‖q.1.down‖ ≤ 3} ⊆ φ.source)
  (S : CompactCarrier.{u})
  (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
  (p : PartialDiffeomorph (𝓡 3) S.model
    (EuclideanSpace ℝ (Fin 3)) S.Carrier ∞)

omit h3 in
def restorationPatchMap (x : EuclideanSpace ℝ (Fin 3)) : M.Carrier :=
  regularFibreRestorationFill M φ (g.symm (p x))

include h3

theorem restorationPatchMap_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (restorationPatchMap M φ S g p) p.source :=
  ((regularFibreRestorationFill_smooth M φ h3).comp g.symm.contMDiff).comp_contMDiffOn
    p.contMDiffOn

theorem restorationPatchMap_mfderiv_bijective (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ p.source) :
    Bijective (mfderiv (𝓡 3) (𝓡 3) (restorationPatchMap M φ S g p) x) := by
  let f := regularFibreRestorationFill M φ
  have hf := (regularFibreRestorationFill_smooth M φ h3).mdifferentiableAt (by simp)
    (x := g.symm (p x))
  have hg := g.symm.contMDiff.mdifferentiableAt (by simp) (x := p x)
  have hp := p.mdifferentiableAt (by simp) hx
  change Bijective (mfderiv (𝓡 3) (𝓡 3) (f ∘ g.symm ∘ p) x)
  rw [mfderiv_comp x hf (hg.comp x hp), mfderiv_comp x hg hp]
  exact (regularFibreRestorationFill_bijective_mfderiv M φ h3 (g.symm (p x))).comp
    (((g.symm.mfderivToContinuousLinearEquiv (by simp) (p x)).bijective).comp
      (carrierSurgeryPatchTangentEquiv p hx).bijective)

theorem restorationPatchMap_localDiffeomorph :
    IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (restorationPatchMap M φ S g p) p.source := by
  intro x
  let f := restorationPatchMap M φ S g p
  have hs := restorationPatchMap_contMDiffOn M φ h3 S g p
  have hb := restorationPatchMap_mfderiv_bijective M φ h3 S g p x.val x.property
  let A := (LinearEquiv.ofBijective (mfderiv (𝓡 3) (𝓡 3) f x.val).toLinearMap hb
    ).toContinuousLinearEquiv
  apply isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    f hs p.open_source x.val x.property A
  exact (hs.contMDiffAt (p.open_source.mem_nhds x.property)).mdifferentiableAt
    (by simp) |>.hasMFDerivAt

theorem exists_restorationTransportedPatch (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ p.source) :
    ∃ q : PartialDiffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) M.Carrier ∞,
      q.source = p.source ∧ q.target = (restorationPatchMap M φ S g p) '' p.source ∧
        ∀ y, q y = regularFibreRestorationFill M φ (g.symm (p y)) := by
  have hi : InjOn (restorationPatchMap M φ S g p) p.source := by
    intro a ha b hb h
    apply p.injOn ha hb
    apply g.symm.injective
    exact regularFibreRestorationFill_injective M φ h3 h
  obtain ⟨q, hs, ht, he⟩ :=
    (restorationPatchMap_localDiffeomorph M φ h3 S g p).exists_partialDiffeomorph_of_injOn
      p.open_source ⟨x, hx⟩ hi
  exact ⟨q, hs, ht, fun y => congrFun he y⟩

end GC.GraphManifold
