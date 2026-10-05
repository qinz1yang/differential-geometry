import DifferentialGeometry.Geometry.Thurston.FlatTorusCoords
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Raw graph presentations from actual translation-periodic Euclidean covers

Whole torus coordinates yield a smooth circle submersion and its actual embedded torus fibre.
The empty-boundary closed model allows arbitrary original carrier models and orientations;
the resulting raw presentation is transported back to that same carrier. The periodic-cover
entry uses the original map and full real basis, without rectangularity or a metric comparison.
These are torus recognition tiers, rather than a classification of all flat three-manifolds.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.FlatTorus

universe u

theorem nonempty_rawGraphPresentation_of_closedTorusCoordinates
    (Q : ConnectedClosedOrientedManifold.{u} 3)
    (e : Q.Carrier ≃ₘ⟮𝓡 3, torusModel.prod (𝓡 1)⟯ (Torus × Circle)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  let p : Q.Carrier → Circle := fun x => (e x).2
  let i : Torus → Torus × Circle := fun t => (t, 1)
  let f : Torus → Q.Carrier := e.symm ∘ i
  have hp : ContMDiff (𝓡 3) (𝓡 1) ∞ p := contMDiff_snd.comp e.contMDiff
  have hsub : ∀ x, Surjective (mfderiv (𝓡 3) (𝓡 1) p x) := by
    intro x
    obtain ⟨D, hD⟩ := e.isInvertible_mfderiv (by simp) (x := x)
    change Surjective (mfderiv (𝓡 3) (𝓡 1) (Prod.snd ∘ e) x)
    rw [mfderiv_comp x mdifferentiableAt_snd (e.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_snd, ← hD]
    intro v
    refine ⟨D.symm (0, v), ?_⟩
    change (D (D.symm (0, v))).2 = v
    exact congrArg Prod.snd (D.apply_symm_apply (0, v))
  have hi : ContMDiff torusModel (torusModel.prod (𝓡 1)) ∞ i :=
    contMDiff_id.prodMk contMDiff_const
  have himm : IsImmersion torusModel (torusModel.prod (𝓡 1)) ∞ i := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hi
    intro t v w hvw
    have hf : MDifferentiableAt torusModel torusModel (id : Torus → Torus) t :=
      mdifferentiableAt_id
    have hc : MDifferentiableAt torusModel (𝓡 1) (fun t : Torus => (1 : Circle)) t :=
      mdifferentiableAt_const
    change mfderiv torusModel (torusModel.prod (𝓡 1)) (fun t : Torus => (id t, 1)) t v =
      mfderiv torusModel (torusModel.prod (𝓡 1)) (fun t : Torus => (id t, 1)) t w at hvw
    rw [mfderiv_prodMk hf hc, mfderiv_id, mfderiv_const] at hvw
    exact congrArg Prod.fst hvw
  have hf : IsSmoothEmbedding torusModel (𝓡 3) ∞ f := by
    refine ⟨himm.isLocalDiffeomorphOn_comp_of_ne_zero ?_ (by simp), ?_⟩
    · exact fun y => e.symm.isLocalDiffeomorph y.val
    · exact e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (1 : Circle))
  have hr : range f = p ⁻¹' {1} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change (e (e.symm (t, 1))).2 = 1
      rw [e.apply_symm_apply]
    · intro hx
      change (e x).2 = 1 at hx
      refine ⟨(e x).1, ?_⟩
      change e.symm ((e x).1, 1) = x
      rw [← hx, e.symm_apply_apply]
  exact Assembly.exists_rawGraphPresentation_of_torusBundle (NoCuts.carrier Q)
    (closedCarrier_boundary_eq_empty Q) p hp hsub f hf hr

theorem nonempty_rawGraphPresentation_of_torusCoordinates
    (W : CompactCarrier.{u}) [instW : ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (e : W.Carrier ≃ₘ⟮W.model, torusModel.prod (𝓡 1)⟯ (Torus × Circle)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨Q, d, hd⟩ := Assembly.exists_closedModel_of_boundary_eq_empty W hboundary
  obtain ⟨G⟩ := nonempty_rawGraphPresentation_of_closedTorusCoordinates Q (d.symm.trans e)
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph G d.symm

theorem rawGraphPresentation_of_periodicEuclideanCover
    (W : CompactCarrier.{u}) [instW : ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (b : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (p : EuclideanSpace ℝ (Fin 3) → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ m : Fin 3 → ℤ, y - x = ∑ i, m i • b i) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨e, he⟩ := exists_diffeomorph_torus_of_periodicCover W b p hp hs hrel
  exact nonempty_rawGraphPresentation_of_torusCoordinates W hboundary e

end GC.GraphManifold.FlatTorus
