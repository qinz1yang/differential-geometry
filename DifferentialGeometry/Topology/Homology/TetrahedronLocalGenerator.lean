import DifferentialGeometry.Topology.Homology.EuclideanSimplexGenerator
import DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality
import DifferentialGeometry.Topology.Homology.SimplexLocalHomology

noncomputable section

namespace DifferentialGeometry.Topology.SimplexDegree

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def liftedTetrahedronBarycenter : ULift.{u} (stdSimplex ℝ (Fin 4)) :=
  ULift.up stdSimplex.barycenter

def tetrahedronIdentitySimplex :
    C(stdSimplex ℝ (Fin 4), ULift.{u} (stdSimplex ℝ (Fin 4))) :=
  ⟨ULift.up, continuous_uliftUp⟩

theorem tetrahedronIdentitySimplex_face_ne_barycenter (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    tetrahedronIdentitySimplex.{u} (orientedSimplexFace i q) ≠
      liftedTetrahedronBarycenter := by
  intro h
  apply standardTetrahedronSimplex_face_ne_zero.{u} i q
  apply ULift.ext
  apply (positiveTetrahedron_zero_iff _).mpr
  intro j
  have he := congrArg (fun v : ULift.{u} (stdSimplex ℝ (Fin 4)) => v.down.val j) h
  simpa [tetrahedronIdentitySimplex, liftedTetrahedronBarycenter,
    stdSimplex.barycenter_apply] using he

private def tetrahedronCoordinateHomeomorph :
    liftedSphereSpace.{u} 1 ≃ₜ ULift.{u} (Fin 3 → ℝ) where
  toFun v := ULift.up ![(1 + 3 * v.down 0 - v.down 1 - v.down 2) / 4,
    (1 - v.down 0 + 3 * v.down 1 - v.down 2) / 4,
    (1 - v.down 0 - v.down 1 + 3 * v.down 2) / 4]
  invFun t := ULift.up (WithLp.toLp 2 ![2 * t.down 0 + t.down 1 + t.down 2 - 1,
    t.down 0 + 2 * t.down 1 + t.down 2 - 1,
    t.down 0 + t.down 1 + 2 * t.down 2 - 1])
  left_inv v := by
    apply ULift.ext
    ext i
    fin_cases i <;> simp <;> ring
  right_inv t := by
    apply ULift.ext
    funext i
    fin_cases i <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def tetrahedronCoordinateSimplex :
    C(stdSimplex ℝ (Fin 4), ULift.{u} (Fin 3 → ℝ)) :=
  ⟨fun q => ULift.up (fun i => q.val i.succ),
    continuous_uliftUp.comp (continuous_pi fun i =>
      (continuous_apply i.succ).comp continuous_subtype_val)⟩

private theorem tetrahedronCoordinateHomeomorph_zero :
    tetrahedronCoordinateHomeomorph.{u} 0 = ULift.up (fun _ => (1 / 4 : ℝ)) := by
  apply ULift.ext
  funext i
  fin_cases i <;> norm_num [tetrahedronCoordinateHomeomorph]

private theorem tetrahedronCoordinateHomeomorph_standardTetrahedronSimplex :
    (⟨tetrahedronCoordinateHomeomorph.{u}, tetrahedronCoordinateHomeomorph.continuous⟩ :
      C(liftedSphereSpace.{u} 1, ULift.{u} (Fin 3 → ℝ))).comp
        standardTetrahedronSimplex = tetrahedronCoordinateSimplex := by
  ext q i
  have hq := q.property.2
  simp [Fin.sum_univ_succ] at hq
  change (tetrahedronCoordinateHomeomorph.{u} (ULift.up (positiveTetrahedron q))).down i =
    q.val i.succ
  fin_cases i <;>
    simp [tetrahedronCoordinateHomeomorph, positiveTetrahedron_coordinate] <;> linarith

private theorem tetrahedronCoordinateSimplex_face_ne_center (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    tetrahedronCoordinateSimplex.{u} (orientedSimplexFace i q) ≠
      ULift.up (fun _ => (1 / 4 : ℝ)) := by
  rw [← tetrahedronCoordinateHomeomorph_standardTetrahedronSimplex,
    ← tetrahedronCoordinateHomeomorph_zero]
  exact tetrahedronCoordinateHomeomorph.injective.ne
    (standardTetrahedronSimplex_face_ne_zero i q)

private theorem tetrahedronCoordinateSimplex_localClass_generator_aux :
    Function.Bijective (fun z : ℤ => z •
      simplexLocalClass (tetrahedronCoordinateHomeomorph.{u} 0)
        tetrahedronCoordinateSimplex.{u} (fun i q => by
          rw [← tetrahedronCoordinateHomeomorph_standardTetrahedronSimplex]
          exact tetrahedronCoordinateHomeomorph.injective.ne
            (standardTetrahedronSimplex_face_ne_zero i q))) := by
  let e := (integralLocalHomologyHomeomorphIso 3
    tetrahedronCoordinateHomeomorph.{u} 0).toLinearEquiv
  have hgen : Function.Bijective (fun z : ℤ => z • e euclideanStandardSimplexClass) :=
    (bijective_zsmul_iff_of_linearEquiv e euclideanStandardSimplexClass).mpr
      euclideanStandardSimplexClass_generator
  change Function.Bijective (fun z : ℤ => z •
    (integralLocalHomologyHomeomorphIso 3 tetrahedronCoordinateHomeomorph.{u} 0).hom.hom
      (simplexLocalClass 0 standardTetrahedronSimplex
        standardTetrahedronSimplex_face_ne_zero)) at hgen
  simpa only [integralLocalHomologyHomeomorphIso_simplexLocalClass,
    tetrahedronCoordinateHomeomorph_standardTetrahedronSimplex] using hgen

private theorem tetrahedronCoordinateSimplex_localClass_generator :
    Function.Bijective (fun z : ℤ => z •
      simplexLocalClass (ULift.up (fun _ => (1 / 4 : ℝ)))
        tetrahedronCoordinateSimplex.{u} tetrahedronCoordinateSimplex_face_ne_center) := by
  have transport (p q : ULift.{u} (Fin 3 → ℝ)) (heq : p = q)
      (hp : ∀ i t, tetrahedronCoordinateSimplex (orientedSimplexFace i t) ≠ p)
      (hq : ∀ i t, tetrahedronCoordinateSimplex (orientedSimplexFace i t) ≠ q) :
      Function.Bijective (fun z : ℤ => z •
        simplexLocalClass p tetrahedronCoordinateSimplex hp) →
      Function.Bijective (fun z : ℤ => z •
        simplexLocalClass q tetrahedronCoordinateSimplex hq) := by
    subst q
    exact id
  exact transport _ _ tetrahedronCoordinateHomeomorph_zero _ _
    tetrahedronCoordinateSimplex_localClass_generator_aux

private theorem liftedSimplexCoordinateInclusion_barycenter :
    liftedSimplexCoordinateInclusion 3 liftedTetrahedronBarycenter.{u} =
      ULift.up (fun _ => (1 / 4 : ℝ)) := by
  apply ULift.ext
  funext i
  norm_num [liftedSimplexCoordinateInclusion, simplexCoordinateInclusion,
    liftedTetrahedronBarycenter, stdSimplex.barycenter_apply]

theorem simplexIdentityLocalClass_generator :
    Function.Bijective (fun z : ℤ => z • simplexLocalClass
      liftedTetrahedronBarycenter.{u} tetrahedronIdentitySimplex
        tetrahedronIdentitySimplex_face_ne_barycenter) := by
  let p := liftedTetrahedronBarycenter.{u}
  let c := simplexLocalClass p tetrahedronIdentitySimplex
    tetrahedronIdentitySimplex_face_ne_barycenter
  let f := integralRelativeHomologyMap 3 (liftedSimplexCoordinateInclusion 3)
    (liftedSimplexCoordinateInclusion_mapsTo_pointComplement 3 p)
  have hf : Function.Bijective f :=
    integralRelativeHomologyMap_liftedSimplexCoordinateInclusion_bijective 3 3 p
      Simplex.barycenter_mem_openCell
  have hfaces (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
      tetrahedronCoordinateSimplex.{u} (orientedSimplexFace i q) ≠
        liftedSimplexCoordinateInclusion 3 p := by
    rw [show p = liftedTetrahedronBarycenter from rfl,
      liftedSimplexCoordinateInclusion_barycenter]
    exact tetrahedronCoordinateSimplex_face_ne_center i q
  have himg : f c = simplexLocalClass (liftedSimplexCoordinateInclusion 3 p)
      tetrahedronCoordinateSimplex hfaces :=
    integralRelativeHomologyMap_simplexLocalClass
      (liftedSimplexCoordinateInclusion 3) _ _ _ _ _
  have htarget : Function.Bijective (fun z : ℤ => z •
      simplexLocalClass (liftedSimplexCoordinateInclusion 3 p)
        tetrahedronCoordinateSimplex hfaces) := by
    have transport (p q : ULift.{u} (Fin 3 → ℝ)) (heq : p = q)
        (hp : ∀ i t, tetrahedronCoordinateSimplex (orientedSimplexFace i t) ≠ p)
        (hq : ∀ i t, tetrahedronCoordinateSimplex (orientedSimplexFace i t) ≠ q) :
        Function.Bijective (fun z : ℤ => z •
          simplexLocalClass p tetrahedronCoordinateSimplex hp) →
        Function.Bijective (fun z : ℤ => z •
          simplexLocalClass q tetrahedronCoordinateSimplex hq) := by
      subst q
      exact id
    exact transport _ _ liftedSimplexCoordinateInclusion_barycenter.symm _ _
      tetrahedronCoordinateSimplex_localClass_generator
  have hgen : Function.Bijective (fun z : ℤ => f (z • c)) := by
    simpa only [map_zsmul, himg] using htarget
  exact ⟨fun a b h => hgen.1 (congrArg f h), fun y => by
    obtain ⟨z, hz⟩ := hgen.2 (f y)
    exact ⟨z, hf.1 hz⟩⟩

end DifferentialGeometry.Topology.SimplexDegree
