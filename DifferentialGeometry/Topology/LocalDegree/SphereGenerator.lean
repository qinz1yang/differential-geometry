import DifferentialGeometry.Topology.LocalDegree.SphereHomology
import DifferentialGeometry.Topology.LocalDegree.ZeroSphere

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Poincare.LocalDegree
open Poincare.Homology


abbrev EuclideanSphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

def euclideanZeroSphereHomeomorphReal : EuclideanSphere 0 ≃ₜ ZeroSphere :=
  ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.toHomeomorph).subtype
    (fun x ↦ by
      simp only [Metric.mem_sphere, dist_zero_right]
      exact ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.norm_map x).symm ▸ Iff.rfl)


@[simp]
theorem euclideanZeroSphereHomeomorphReal_north :
    euclideanZeroSphereHomeomorphReal (euclideanNorth 0) = zeroSpherePositive := by
  apply Subtype.ext
  apply (OrthonormalBasis.singleton (Fin 1) ℝ).repr.injective
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr
      ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm (euclideanNorth 0).val) =
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr 1
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  have hi : i = 0 := Fin.eq_zero i
  simp [euclideanNorth, hi]

private def moduleIsoAddEquiv {A B : ModuleCat ℤ} (e : A ≅ B) : A ≃+ B where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congr($(e.hom_inv_id) x)
  right_inv x := congr($(e.inv_hom_id) x)
  map_add' x y := e.hom.hom.map_add' x y

def realZeroSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere) 0 ≃+ zeroSphereReducedH0 where
  toFun c := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere)).hom c
  invFun c := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere)).inv c
  left_inv c := congr($((reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).hom_inv_id) c)
  right_inv c := congr($((reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).inv_hom_id) c)
  map_add' c d := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).hom.hom.map_add' c d


theorem realZeroSphereReducedHomologyEquiv_map (f : C(ZeroSphere, ZeroSphere))
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere) 0) :
    realZeroSphereReducedHomologyEquiv
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) 0 c) =
      zeroSphereReducedMap f (realZeroSphereReducedHomologyEquiv c) := by
  apply Subtype.ext
  exact congr($(reducedSingularHomologyZeroIso_naturality (ModuleCat.of ℤ ℤ) (TopCat.ofHom f)) c)

def euclideanZeroSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere 0)) 0 ≃+ ℤ :=
  (moduleIsoAddEquiv (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
    euclideanZeroSphereHomeomorphReal.toHomotopyEquiv 0)).trans
      (realZeroSphereReducedHomologyEquiv.trans zeroSphereReducedEquiv)


theorem euclideanZeroSphereReducedHomologyEquiv_apply
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere 0)) 0) :
    euclideanZeroSphereReducedHomologyEquiv c =
      zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
          (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0 c)) := rfl

def euclideanSphereTopReducedHomologyEquiv : (d : ℕ) →
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d ≃+ ℤ
  | 0 => euclideanZeroSphereReducedHomologyEquiv
  | d + 1 => (moduleIsoAddEquiv
      (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d)).trans
        (euclideanSphereTopReducedHomologyEquiv d)


@[simp]
theorem euclideanSphereTopReducedHomologyEquiv_zero :
    euclideanSphereTopReducedHomologyEquiv 0 = euclideanZeroSphereReducedHomologyEquiv := rfl

theorem euclideanSphereTopReducedHomologyEquiv_succ (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere (d + 1))) (d + 1)) :
    euclideanSphereTopReducedHomologyEquiv (d + 1) c =
      euclideanSphereTopReducedHomologyEquiv d
        ((euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom c) := rfl


def euclideanSphereTopGenerator (d : ℕ) :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d :=
  (euclideanSphereTopReducedHomologyEquiv d).symm 1


@[simp]
theorem euclideanSphereTopReducedHomologyEquiv_generator (d : ℕ) :
    euclideanSphereTopReducedHomologyEquiv d (euclideanSphereTopGenerator d) = 1 :=
  (euclideanSphereTopReducedHomologyEquiv d).apply_symm_apply 1


theorem euclideanSphereTopGenerator_ne_zero (d : ℕ) : euclideanSphereTopGenerator d ≠ 0 := by
  intro h
  have hh := congrArg (euclideanSphereTopReducedHomologyEquiv d) h
  simp at hh


theorem euclideanSphereTopReducedHomologyEquiv_smul_generator (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    euclideanSphereTopReducedHomologyEquiv d c • euclideanSphereTopGenerator d = c := by
  apply (euclideanSphereTopReducedHomologyEquiv d).injective
  simp


theorem euclideanSphereTopGenerator_unique_coefficient (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    ∃! m : ℤ, c = m • euclideanSphereTopGenerator d := by
  refine ⟨euclideanSphereTopReducedHomologyEquiv d c,
    (euclideanSphereTopReducedHomologyEquiv_smul_generator d c).symm, ?_⟩
  intro m hm
  have h := congrArg (euclideanSphereTopReducedHomologyEquiv d) hm
  simpa using h.symm

theorem euclideanSphereTopGenerator_zero_comparison :
    realZeroSphereReducedHomologyEquiv
      (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0
          (euclideanSphereTopGenerator 0)) = zeroSphereGenerator := by
  apply zeroSphereReducedEquiv.injective
  change euclideanSphereTopReducedHomologyEquiv 0 (euclideanSphereTopGenerator 0) = _
  rw [euclideanSphereTopReducedHomologyEquiv_generator, zeroSphereReducedEquiv_generator]


theorem euclideanSphereTopGenerator_connecting (d : ℕ) :
    (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
        (euclideanSphereTopGenerator (d + 1)) = euclideanSphereTopGenerator d := by
  apply (euclideanSphereTopReducedHomologyEquiv d).injective
  rw [← euclideanSphereTopReducedHomologyEquiv_succ]
  simp

end Poincare.LocalDegree
