import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransportApplications
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderClosing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminalSplit
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding

/-!
# Chapter-14 assembly, L3-S²: oriented `S²`-bundles over the circle

Lane ASM-L3 (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §0.7 and
§3 L3; frozen statements in the interface file, §3).

* `nonempty_diffeomorph_sphereTwoTimesCircle_of_orientedSphereBundle`: a closed oriented
  `3`-manifold fibred over the circle with an actual `S²` fibre over `1` is `S² × S¹`. The two
  opposite slabs of the cut map (`CircleFibre.exists_circleSlabs`) are the input of the double-slab
  recognition `DoubleCylinder.nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs`,
  which derives the degree `+1` of the monodromy from the orientation of the total space
  (`sphereDiffeomorphDegree_eq_one_of_closed_cylinder_return`) and then uses the flattened isotopy
  of `SphereMappingTorusTrivialization.lean:36–78`.
* `exists_sphereTwoTimesCircle_of_sphereBundle` (**L3-S²**, frozen): the same on a carrier with empty
  boundary, through the closed model of B0 (`exists_closedModel_of_boundary_eq_empty`).
* `exists_rawGraphPresentation_of_sphereTwoTimesCircle_diffeomorph` (**S²×S¹ adapter**, frozen): the
  universe-`u` raw presentation `sphereTwoTimesCircleUliftRawGraphPresentation`
  (`Seifert/NormalizeTerminalSplit.lean:63`) transported by G1
  (`nonempty_rawGraphPresentation_of_carrierDiffeomorph`). No universe lift is needed: the tree has
  the universe-`u` presentation already.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

theorem nonempty_unitSphere_three : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- **Oriented `S²`-bundles over the circle are `S² × S¹`** (closed boundaryless form). -/
theorem nonempty_diffeomorph_sphereTwoTimesCircle_of_orientedSphereBundle {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] (o : ManifoldOrientation (𝓡 3) M 3)
    (p : M → Circle) (hp : ContMDiff (𝓡 3) (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv (𝓡 3) (𝓡 1) p x))
    (f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    Nonempty (M ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) := by
  have := nonempty_unitSphere_three
  obtain ⟨A, P, φ, hA, hP, h0, h1, hmeet, hcover⟩ :=
    Ehresmann.CircleFibre.exists_circleSlabs p hp hsub f hf hr
  exact DoubleCylinder.nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs
    (Manifold.smoothOrientationOfManifoldOrientation (𝓡 3)
      (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr o.dimension_eq.symm) o))
    A P φ (Diffeomorph.refl (𝓡 2) _ ∞) hA hP h0 h1 hmeet hcover

/-- **L3-S² (recognition).** An oriented `S²`-bundle over the circle is `S² × S¹`. Route: cut,
interval trivialization, degree-one monodromy, `exists_sphereMappingTorusIsotopy_of_degree_one`
and `sphereMappingTorusDiffeomorphSphereTwoTimesCircle`
(`Topology/ThreeManifold/SphereMappingTorusTrivialization.lean:36–78`). -/
theorem exists_sphereTwoTimesCircle_of_sphereBundle (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : ClosureSphere.{u} → W.Carrier) (hf : IsSmoothEmbedding (𝓡 2) W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    Nonempty (W.Carrier ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) := by
  obtain ⟨Q, e, -⟩ := exists_closedModel_of_boundary_eq_empty W hW
  let p' : Q.Carrier → Circle := p ∘ e.symm
  have hp' : ContMDiff (𝓡 3) (𝓡 1) ∞ p' := hp.comp e.symm.contMDiff
  have hsub' : ∀ y, Surjective (mfderiv (𝓡 3) (𝓡 1) p' y) := by
    intro y
    rw [mfderiv_comp y (hp.mdifferentiableAt (by simp))
      (e.symm.contMDiff.mdifferentiableAt (by simp))]
    obtain ⟨L, hL⟩ := e.symm.isInvertible_mfderiv (x := y) (by simp)
    rw [ContinuousLinearMap.coe_comp, ← hL]
    exact (hsub _).comp L.surjective
  let up : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u} :=
    uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let f' : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Q.Carrier := fun z => e (f (up z))
  have hfu : ContMDiff (𝓡 2) W.model ∞ (f ∘ up) := hf.contMDiff.comp up.contMDiff
  have hf'c : ContMDiff (𝓡 2) (𝓡 3) ∞ f' := e.contMDiff.comp hfu
  have hf' : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' := by
    refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hf'c
      fun z => ?_, e.toHomeomorph.isEmbedding.comp
        (hf.isEmbedding.comp up.toHomeomorph.isEmbedding)⟩
    change Injective (mfderiv (𝓡 2) (𝓡 3) (e ∘ (f ∘ up)) z)
    rw [mfderiv_comp z (e.contMDiff.mdifferentiableAt (by simp))
      (hfu.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp,
      mfderiv_comp z (hf.contMDiff.mdifferentiableAt (by simp))
      (up.contMDiff.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    obtain ⟨Le, hLe⟩ := e.isInvertible_mfderiv (x := (f ∘ up) z) (by simp)
    obtain ⟨Lu, hLu⟩ := up.isInvertible_mfderiv (x := z) (by simp)
    rw [← hLe, ← hLu]
    exact Le.injective.comp
      (((hf.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp Lu.injective)
  have hr' : range f' = p' ⁻¹' {1} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have h : f (up z) ∈ p ⁻¹' {1} := hr ▸ mem_range_self _
      change p (e.symm (e (f (up z)))) = 1
      rw [e.symm_apply_apply]
      exact h
    · intro hy
      have h : e.symm y ∈ range f := by
        rw [hr]
        exact hy
      obtain ⟨w, hw⟩ := h
      refine ⟨up.symm w, ?_⟩
      change e (f (up (up.symm w))) = y
      rw [up.apply_symm_apply, hw, e.apply_symm_apply]
  obtain ⟨D⟩ := nonempty_diffeomorph_sphereTwoTimesCircle_of_orientedSphereBundle Q.orientation
    p' hp' hsub' f' hf' hr'
  exact ⟨e.trans D⟩

section Adapter

attribute [local instance] uliftChartedSpace isManifold_ulift

/-- **S²×S¹ adapter.** Raw presentation of any carrier diffeomorphic to `S² × S¹`, from
`sphereTwoTimesCircleRawGraphPresentation` (`GraphManifold/SphereProduct.lean:203`, universe `0`)
lifted to universe `u` and transported by G1 (`Closure/CarrierDiffeomorphTransport.lean:38`).
The universe-`u` form is `sphereTwoTimesCircleUliftRawGraphPresentation`; the connectedness of the
source carrier needed by G1 is transported from `W` along the diffeomorphism. -/
theorem exists_rawGraphPresentation_of_sphereTwoTimesCircle_diffeomorph (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier]
    (e : W.Carrier ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    Nonempty (RawGraphPresentation W) := by
  let C := NoCuts.carrier sphereTwoTimesCircleLift.ulift.{0, u}
  let d : C.Carrier ≃ₘ⟮C.model, W.model⟯ W.Carrier :=
    (sphereTwoTimesCircleUliftProduct.{u}.trans
      ((uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.prodCongr
        sphereOneDiffeomorphCircle.symm)).trans e.symm
  have : PreconnectedSpace C.Carrier :=
    (d.toHomeomorph.connectedSpace_iff.mpr inferInstance).toPreconnectedSpace
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph
    sphereTwoTimesCircleUliftRawGraphPresentation.{u} d

end Adapter

end GC.GraphManifold.Assembly
