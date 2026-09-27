import DifferentialGeometry.Topology.Homology.Local.Translation
import DifferentialGeometry.Topology.Homeomorph.SphereAffine
import DifferentialGeometry.Topology.Homotopy.SphereRadial

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric DifferentialGeometry.Topology DifferentialGeometry.LocalDegree
namespace DifferentialGeometry.Homology
universe u
section Metric
variable {E : Type u} [PseudoMetricSpace E] (a : E) (r : ℝ)
  {k : Type u} [Ring k] (A : ModuleCat.{u} k)

private theorem closedBallBoundary_mapsTo (p : E) (hp : p ∈ ball a r) :
    MapsTo (Subtype.val : closedBall a r → E) {y : closedBall a r | y.val ∈ sphere a r}
      ({p}ᶜ : Set E) := by
  intro y hy he
  change y.val = p at he
  have hs := mem_sphere.mp hy
  rw [he] at hs
  exact (ne_of_lt hp) hs


def closedBallLocalHomologyMap (p : E) (hp : p ∈ ball a r) (n : ℕ) :
    relativeHomology (TopCat.of (closedBall a r)) {y : closedBall a r | y.val ∈ sphere a r} A n ⟶
      relativeHomology (TopCat.of E) ({p}ᶜ : Set E) A n :=
  relativeHomologyMap A (X := TopCat.of (closedBall a r)) (Y := TopCat.of E)
    (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(closedBall a r,E)))
    (closedBallBoundary_mapsTo a r p hp) n

end Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (a : E) (r : ℝ) (hr : 0 < r)

private def closedBallBoundaryHomeomorph :
    sphere (0 : E) 1 ≃ₜ {y : closedBall a r | y.val ∈ sphere a r} :=
  (sphereAffineHomeomorph a r hr).trans {
    toFun := fun y => ⟨⟨y.val,sphere_subset_closedBall y.property⟩,y.property⟩
    invFun := fun y => ⟨y.val.val,y.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

variable {k : Type u} [Ring k] (A : ModuleCat.{u} k)


def closedBallBoundaryHomologyIso (n : ℕ) :
    relativeHomology (TopCat.of (closedBall a r)) {y : closedBall a r | y.val ∈ sphere a r} A (n + 1) ≅
      reducedSingularHomology A (TopCat.of (sphere (0 : E) 1)) n := by
  let _ : ContractibleSpace (closedBall a r) :=
    (convex_closedBall a r).contractibleSpace ⟨a,mem_closedBall_self hr.le⟩
  exact relativeReducedConnectingIso _ _ A n ≪≫
    reducedSingularHomologyIso A
      (X := TopCat.of {y : closedBall a r | y.val ∈ sphere a r})
      (Y := TopCat.of (sphere (0 : E) 1)) (closedBallBoundaryHomeomorph a r hr).symm.toHomotopyEquiv n

private theorem closedBallLocalHomologyMap_sphere_comparison (p : E) (hp : p ∈ ball a r) (n : ℕ) :
    (closedBallBoundaryHomologyIso a r hr A n).inv ≫
      closedBallLocalHomologyMap a r A p hp (n + 1) ≫
      (localTranslationHomologyIso E p A (n + 1)).hom ≫
      (relativeReducedConnectingIso (TopCat.of E) ({0}ᶜ : Set E) A n).hom ≫
      (reducedSingularHomologyIso A (X := TopCat.of ({0}ᶜ : Set E))
        (Y := TopCat.of (sphere (0 : E) 1)) (puncturedSpaceSphereHomotopyEquiv E) n).hom =
      𝟙 _ := by
  let _ : ContractibleSpace (closedBall a r) :=
    (convex_closedBall a r).contractibleSpace ⟨a,mem_closedBall_self hr.le⟩
  let i : TopCat.of (closedBall a r) ⟶ TopCat.of E :=
    TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(closedBall a r,E))
  let t : TopCat.of E ⟶ TopCat.of E :=
    TopCat.ofHom (⟨fun y => y-p,continuous_id.sub continuous_const⟩ : C(E,E))
  have hi : MapsTo i {y : closedBall a r | y.val ∈ sphere a r} ({p}ᶜ : Set E) :=
    closedBallBoundary_mapsTo a r p hp
  have ht : MapsTo t ({p}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hy => sub_ne_zero.mpr hy
  have hn := relativeReducedConnectingIso_naturality A (X := TopCat.of (closedBall a r))
    (Y := TopCat.of E) (i ≫ t) (ht.comp hi) n
  rw [relativeHomologyMap_comp A i hi t ht] at hn
  dsimp only [closedBallBoundaryHomologyIso,Iso.trans_inv]
  simp only [Category.assoc]
  change reducedSingularHomologyMap A (X := TopCat.of (sphere (0 : E) 1))
      (Y := TopCat.of {y : closedBall a r | y.val ∈ sphere a r})
      (TopCat.ofHom (closedBallBoundaryHomeomorph a r hr)) n ≫
      (relativeReducedConnectingIso (TopCat.of (closedBall a r))
        {y : closedBall a r | y.val ∈ sphere a r} A n).inv ≫
      relativeHomologyMap A (X := TopCat.of (closedBall a r)) (Y := TopCat.of E)
        (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({p}ᶜ : Set E)) i hi (n + 1) ≫ relativeHomologyMap A (X := TopCat.of E) (Y := TopCat.of E)
        (s := ({p}ᶜ : Set E)) (t := ({0}ᶜ : Set E)) t ht (n + 1) ≫
      (relativeReducedConnectingIso (TopCat.of E) ({0}ᶜ : Set E) A n).hom ≫
      reducedSingularHomologyMap A (X := TopCat.of ({0}ᶜ : Set E))
        (Y := TopCat.of (sphere (0 : E) 1)) (TopCat.ofHom (puncturedSpaceSphereHomotopyEquiv E).toFun) n = _
  have hn' := congrArg (fun g => g ≫
    reducedSingularHomologyMap A (X := TopCat.of ({0}ᶜ : Set E))
        (Y := TopCat.of (sphere (0 : E) 1)) (TopCat.ofHom (puncturedSpaceSphereHomotopyEquiv E).toFun) n) hn
  simp only [Category.assoc] at hn'
  rw [← hn',Iso.inv_hom_id_assoc,← reducedSingularHomologyMap_comp,← reducedSingularHomologyMap_comp]
  have he : (TopCat.ofHom (closedBallBoundaryHomeomorph a r hr)) ≫
      relativeSubspaceMap (X := TopCat.of (closedBall a r)) (Y := TopCat.of E) (i ≫ t) (ht.comp hi) ≫
      TopCat.ofHom (puncturedSpaceSphereHomotopyEquiv E).toFun =
      TopCat.ofHom (sphereRadialMap a r p hp) := by
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    change ((puncturedSpaceSphereHomotopyEquiv E) _ : E) = (sphereRadialMap a r p hp v : E)
    rw [sphereRadialMap_apply]
    exact (puncturedSpaceSphereHomotopyEquiv_apply E _).trans rfl
  rw [he]
  exact (reducedSingularHomologyMap_eq_of_homotopy A (sphereRadialHomotopy a r p hp) n).symm.trans
    (reducedSingularHomologyMap_id A n)


def euclideanClosedBallFundamentalClass {d : ℕ} (a : EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (hr : 0 < r) :
    relativeHomology (TopCat.of (closedBall a r)) {y : closedBall a r | y.val ∈ sphere a r}
      (ModuleCat.of ℤ ℤ) (d + 1) :=
  (closedBallBoundaryHomologyIso a r hr (ModuleCat.of ℤ ℤ) d).inv (euclideanSphereTopGenerator d)


theorem closedBallLocalHomologyMap_fundamentalClass {d : ℕ}
    (a : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r)
    (p : EuclideanSpace ℝ (Fin (d + 1))) (hp : p ∈ ball a r) :
    closedBallLocalHomologyMap a r (ModuleCat.of ℤ ℤ) p hp (d + 1)
      (euclideanClosedBallFundamentalClass a r hr) = euclideanLocalGeneratorAt p := by
  apply (ModuleCat.mono_iff_injective (localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).hom).mp inferInstance
  rw [euclideanLocalGeneratorAt_translate]
  apply (ModuleCat.mono_iff_injective (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom).mp inferInstance
  have h := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (closedBallLocalHomologyMap_sphere_comparison a r hr (ModuleCat.of ℤ ℤ) p hp d)
  change (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
    ((localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).hom
      (closedBallLocalHomologyMap a r (ModuleCat.of ℤ ℤ) p hp (d + 1)
        (euclideanClosedBallFundamentalClass a r hr))) = euclideanSphereTopGenerator d at h
  exact h.trans (congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id).symm


theorem euclideanClosedBallFundamentalClass_ne_zero {d : ℕ}
    (a : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r) :
    euclideanClosedBallFundamentalClass a r hr ≠ 0 := by
  intro h
  have hh := congrArg (closedBallLocalHomologyMap a r (ModuleCat.of ℤ ℤ) a (mem_ball_self hr) (d + 1)) h
  rw [closedBallLocalHomologyMap_fundamentalClass,map_zero] at hh
  exact euclideanLocalGeneratorAt_ne_zero a hh
end DifferentialGeometry.Homology
