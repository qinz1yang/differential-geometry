import DifferentialGeometry.Topology.LocalDegree.LinearComposition
import DifferentialGeometry.Topology.LocalDegree.CoordinateChangeHomotopy
import DifferentialGeometry.Topology.LocalDegree.AffineCoordinate
import DifferentialGeometry.Topology.LocalDegree.LinearDegree

set_option autoImplicit false
open Metric Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_isolating_straightening {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) (A : E ≃L[ℝ] F)
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x)
    {V : F → F} {S : ℝ} (hS : IsolatingRadius V (φ x) S) :
    ∃ R, ∃ hQ : IsolatingRadius (fun y => A.symm (V (φ y))) x R,
      ∃ hG : IsolatingRadius (fun y => A.symm (V (φ x + A (y - x)))) x R,
        ∀ r : Ioc (0 : ℝ) R,
          Nonempty ((sphereMap (fun y => A.symm (V (φ y))) x R
            hQ.continuousOn hQ.nonzero r).Homotopy
              (sphereMap (fun y => A.symm (V (φ x + A (y - x)))) x R
                hG.continuousOn hG.nonzero r)) := by
  obtain ⟨R, hR, hQ, hQz, hG, hGz, hH⟩ :=
    exists_sphereMap_coordinateStraightening_homotopy φ hn hx A hA hS.pos
      hS.continuousOn hS.nonzero
  have heq : _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
      (fun y => φ x + A (y - x)) V = fun y => A.symm (V (φ x + A (y - x))) :=
    funext fun y => mpullback_affineCoordinate_eq A x y (φ x) V
  have hGc : ContinuousOn (fun y => A.symm (V (φ x + A (y - x)))) (closedBall x R) := by
    simpa only [heq] using hG
  have hGcz : ∀ y ∈ closedBall x R, y ≠ x → A.symm (V (φ x + A (y - x))) ≠ 0 := by
    simpa only [heq] using! hGz
  have hQ0 : A.symm (V (φ x)) = 0 := by rw [hS.zero, map_zero]
  have hG0 : A.symm (V (φ x + A (x - x))) = 0 := by
    simpa only [sub_self, map_zero, add_zero] using hQ0
  have hiQ : IsolatingRadius (fun y => A.symm (V (φ y))) x R :=
    ⟨hR, hQ, fun y hy =>
      ⟨fun he => by by_contra hne; exact hQz y hy hne he, fun he => he ▸ hQ0⟩⟩
  have hiG : IsolatingRadius (fun y => A.symm (V (φ x + A (y - x)))) x R :=
    ⟨hR, hGc, fun y hy =>
      ⟨fun he => by by_contra hne; exact hGcz y hy hne he, fun he => he ▸ hG0⟩⟩
  refine ⟨R, hiQ, hiG, fun r => ⟨((hH r).choose).cast rfl ?_⟩⟩
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  erw [sphereMap_apply, sphereMap_apply, mpullback_affineCoordinate_eq A x _ (φ x) V]

theorem isolatedZero_comp_partialDiffeomorph {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) (A : E ≃L[ℝ] F)
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x)
    {V : F → F} (hV : isolatedZero V (φ x)) : isolatedZero (fun y => V (φ y)) x := by
  obtain ⟨R, hQ, _⟩ := exists_isolating_straightening φ hn hx A hA hV.choose_spec
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    isolatedZero_linear_postcomp A ⟨R, hQ⟩

variable {d : ℕ}

theorem euclideanLocalDegree_comp_partialDiffeomorph {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin (d + 1))) n)
    (hn : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ φ.source)
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x)
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hV : isolatedZero V (φ x)) :
    euclideanLocalDegree (fun y => V (φ y)) x
        (isolatedZero_comp_partialDiffeomorph φ hn hx A hA hV) =
      euclideanSphereDegree (linearSphereMap A) * euclideanLocalDegree V (φ x) hV := by
  obtain ⟨R, hQ, hG, hH⟩ := exists_isolating_straightening φ hn hx A hA hV.choose_spec
  have hQG : euclideanLocalDegree (fun y => A.symm (V (φ y))) x ⟨R, hQ⟩ =
      euclideanLocalDegree (fun y => A.symm (V (φ x + A (y - x)))) x ⟨R, hG⟩ := by
    let r : Ioc (0 : ℝ) R := ⟨R, hQ.pos, le_rfl⟩
    erw [euclideanLocalDegree_eq_sphereDegree _ hQ r,
      euclideanLocalDegree_eq_sphereDegree _ hG r]
    exact euclideanSphereDegree_eq_of_homotopy (hH r).some
  have hGV : euclideanLocalDegree (fun y => A.symm (V (φ x + A (y - x)))) x ⟨R, hG⟩ =
      euclideanLocalDegree V (φ x) hV :=
    euclideanLocalDegree_affineCoordinate A x (φ x) hV
  calc
    _ = euclideanSphereDegree (linearSphereMap A) *
        euclideanLocalDegree (fun y => A.symm (V (φ y))) x ⟨R, hQ⟩ := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        euclideanLocalDegree_linear_postcomp A ⟨R, hQ⟩
    _ = _ := congrArg (fun z => euclideanSphereDegree (linearSphereMap A) * z) (hQG.trans hGV)

theorem euclideanLocalDegree_comp_partialDiffeomorph_eq_sign_det {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin (d + 1))) n)
    (hn : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ φ.source)
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x)
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hV : isolatedZero V (φ x)) :
    euclideanLocalDegree (fun y => V (φ y)) x
        (isolatedZero_comp_partialDiffeomorph φ hn hx A hA hV) =
      (SignType.sign (LinearMap.det (fderiv ℝ φ x).toLinearMap) : ℤ) *
        euclideanLocalDegree V (φ x) hV := by
  rw [euclideanLocalDegree_comp_partialDiffeomorph φ hn hx A hA hV,
    euclideanSphereDegree_linearEquiv]
  change (SignType.sign (LinearMap.det A.toContinuousLinearMap.toLinearMap) : ℤ) * _ = _
  rw [hA]

end DifferentialGeometry.LocalDegree
