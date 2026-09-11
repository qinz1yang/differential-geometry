import DifferentialGeometry.Topology.Homology.LiftedSphere
import DifferentialGeometry.Topology.Homotopy.SphereNaturality









noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology


def liftedHomotopySphereDown (n : ℕ) :
    C(liftedHomotopySphere.{u} n, sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨ULift.down, Homeomorph.ulift.continuous⟩

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]



def freeSphereHomologyImage (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      integralSingularHomology (n + 1) X :=
  ZerothHomotopy.lift (fun f => integralSingularHomologyMap (n + 1)
    (f.comp (liftedHomotopySphereDown n)) c) (fun {_ _} h =>
      LinearMap.congr_fun (integralSingularHomologyMap_homotopic (n + 1)
        (((homotopic_iff_joined _ _).mpr ⟨h⟩).comp (Homotopic.refl (liftedHomotopySphereDown n)))) c)


theorem freeSphereHomologyImage_mk (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n c (ZerothHomotopy.mk f) =
      integralSingularHomologyMap (n + 1) (f.comp (liftedHomotopySphereDown n)) c := rfl


theorem freeSphereHomologyImage_natural (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) (f : C(X, Y))
    (a : ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n c (freeSpherePostcompose n f a) =
      integralSingularHomologyMap (n + 1) f (freeSphereHomologyImage n c a) := by
  induction a using ZerothHomotopy.rec with
  | mk g =>
      change integralSingularHomologyMap (n + 1)
        (f.comp (g.comp (liftedHomotopySphereDown n))) c = _
      rw [integralSingularHomologyMap_comp]
      rfl



def sphereHurewicz (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    HomotopyGroup (Fin (n + 1)) X x → integralSingularHomology (n + 1) X :=
  (freeSphereHomologyImage n c) ∘ (homotopyGroupToFreeSphere n x)


theorem sphereHurewicz_mk (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (Γ : GenLoop (Fin (n + 1)) X x) :
    sphereHurewicz n x c ⟦Γ⟧ = integralSingularHomologyMap (n + 1)
      ((genLoopSphereHomeomorph n x Γ).val.comp (liftedHomotopySphereDown n)) c := rfl


theorem sphereHurewicz_one (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    sphereHurewicz n x c 1 = 0 := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_one, freeSphereHomologyImage_mk]
  change integralSingularHomologyMap (n + 1) (ContinuousMap.const _ x) c = 0
  rw [integralSingularHomologyMap_const (n + 1) (by omega)]
  rfl


theorem sphereHurewicz_transport (n : ℕ) {x y : X} (p : Path x y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n y c (homotopyGroupTransport n p a) = sphereHurewicz n x c a := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_transport]
  rfl


theorem sphereHurewicz_natural (n : ℕ) (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n y c (homotopyGroupBasedMap f x y hf a) =
      integralSingularHomologyMap (n + 1) f (sphereHurewicz n x c a) := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_natural, freeSphereHomologyImage_natural]
  rfl

end DifferentialGeometry.Topology
