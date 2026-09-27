import DifferentialGeometry.Topology.Homology.Local.ClosedBall
import DifferentialGeometry.Topology.Homology.Local.FiniteSetDecomposition

set_option autoImplicit false
noncomputable section
open CategoryTheory Set Metric
namespace DifferentialGeometry.Homology
universe u
variable {E : Type u} [PseudoMetricSpace E] (a : E) (r : ℝ)
  {k : Type u} [Ring k] (A : ModuleCat.{u} k) (Z : Set E) (hZ : Z ⊆ ball a r)

include hZ in
private theorem closedBallBoundary_mapsTo_compl :
    MapsTo (Subtype.val : closedBall a r → E) {y : closedBall a r | y.val ∈ sphere a r} Zᶜ := by
  intro y hy hz
  exact (ne_of_lt (hZ hz)) (mem_sphere.mp hy)


def closedBallPunctureHomologyMap (n : ℕ) :
    relativeHomology (TopCat.of (closedBall a r)) {y : closedBall a r | y.val ∈ sphere a r} A n ⟶
      relativeHomology (TopCat.of E) Zᶜ A n :=
  relativeHomologyMap A (X := TopCat.of (closedBall a r)) (Y := TopCat.of E)
    (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(closedBall a r,E)))
    (closedBallBoundary_mapsTo_compl a r Z hZ) n


@[reassoc]
theorem closedBallPunctureHomologyMap_projection (p : Z) (n : ℕ) :
    closedBallPunctureHomologyMap a r A Z hZ n ≫ finitePunctureProjection (TopCat.of E) Z A p n =
      closedBallLocalHomologyMap a r A p.val (hZ p.property) n := by
  unfold closedBallPunctureHomologyMap finitePunctureProjection closedBallLocalHomologyMap
  exact (relativeHomologyMap_comp A (X := TopCat.of (closedBall a r)) (Y := TopCat.of E)
    (Z := TopCat.of E) (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(closedBall a r,E)))
    (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := Zᶜ) (v := ({p.val}ᶜ : Set E))
    (closedBallBoundary_mapsTo_compl a r Z hZ) (𝟙 (TopCat.of E))
    (fun x hx he => by
      change x = p.val at he
      exact hx (he.symm ▸ p.property)) n).symm


theorem closedBallPunctureHomologyMap_fundamentalClass {d : ℕ}
    (a : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r)
    (Z : Set (EuclideanSpace ℝ (Fin (d + 1)))) (hZ : Z ⊆ ball a r) (hfinite : Z.Finite) :
    finitePunctureHomologyLinearEquiv (TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) Z
      (ModuleCat.of ℤ ℤ) hfinite (d + 1)
      (closedBallPunctureHomologyMap (E := EuclideanSpace ℝ (Fin (d + 1))) a r (ModuleCat.of ℤ ℤ) Z hZ (d + 1)
        (euclideanClosedBallFundamentalClass a r hr)) =
      fun p : Z => euclideanLocalGeneratorAt p.val := by
  funext p
  rw [finitePunctureHomologyLinearEquiv_apply]
  exact (congrArg (fun g => g (euclideanClosedBallFundamentalClass a r hr))
    (closedBallPunctureHomologyMap_projection a r (ModuleCat.of ℤ ℤ) Z hZ p (d + 1))).trans
      (closedBallLocalHomologyMap_fundamentalClass a r hr p.val (hZ p.property))


theorem closedBallPunctureHomologyMap_fundamentalClass_eq_finsum {d : ℕ}
    (a : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r)
    (Z : Set (EuclideanSpace ℝ (Fin (d + 1)))) (hZ : Z ⊆ ball a r) (hfinite : Z.Finite) :
    closedBallPunctureHomologyMap (E := EuclideanSpace ℝ (Fin (d + 1))) a r (ModuleCat.of ℤ ℤ)
      Z hZ (d + 1) (euclideanClosedBallFundamentalClass a r hr) =
    ∑ᶠ p : Z, finitePunctureHomologyInclusion (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      Z (ModuleCat.of ℤ ℤ) hfinite (d + 1) p (euclideanLocalGeneratorAt p.val) := by
  rw [finsum_finitePunctureHomologyInclusion (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
    Z (ModuleCat.of ℤ ℤ) hfinite (d + 1) (fun p => euclideanLocalGeneratorAt p.val)]
  apply (finitePunctureHomologyLinearEquiv (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
    Z (ModuleCat.of ℤ ℤ) hfinite (d + 1)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact closedBallPunctureHomologyMap_fundamentalClass a r hr Z hZ hfinite
end DifferentialGeometry.Homology
