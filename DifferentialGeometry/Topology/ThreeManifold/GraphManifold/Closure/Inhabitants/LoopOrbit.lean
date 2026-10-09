import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRimProduct

/-!
The genuine full-circle trivialization on S³ where the first Clifford coordinate is nonzero.
Its base records the second coordinate, and its circle rotates only the first coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private def orbitRadius (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt (1 - ‖z‖ ^ 2)

private theorem orbitRadius_pos {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    0 < orbitRadius z := by
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg z]

private theorem orbitPair_norm {z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖z‖ < 1) (t : Circle) :
    ‖orbitRadius z • (t : ℂ)‖ ^ 2 + ‖modelPlaneComplex z‖ ^ 2 = 1 := by
  rw [norm_smul, orbitRadius, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Circle.norm_coe, mul_one, Real.sq_sqrt (by nlinarith [norm_nonneg z]),
    modelPlaneComplex.norm_map]
  ring

private def orbitMap (p : EuclideanSpace ℝ (Fin 2) × Circle) : SphereCarrier.{0} :=
  if hp : ‖p.1‖ < 1 then
    sphereOfPair (orbitRadius p.1 • (p.2 : ℂ)) (modelPlaneComplex p.1)
      (orbitPair_norm hp p.2)
  else sphereOfPair 1 0 (by simp)

private theorem orbitMap_first {p : EuclideanSpace ℝ (Fin 2) × Circle}
    (hp : ‖p.1‖ < 1) : sphereFirst (orbitMap p) = orbitRadius p.1 • (p.2 : ℂ) := by
  simp only [orbitMap, hp, ↓reduceDIte, sphereFirst_sphereOfPair]

private theorem orbitMap_second {p : EuclideanSpace ℝ (Fin 2) × Circle}
    (hp : ‖p.1‖ < 1) : sphereSecond (orbitMap p) = modelPlaneComplex p.1 := by
  simp only [orbitMap, hp, ↓reduceDIte, sphereSecond_sphereOfPair]

private def orbitInverse (p : SphereCarrier.{0}) : EuclideanSpace ℝ (Fin 2) × Circle :=
  (modelPlaneComplex.symm (sphereSecond p), unitOf (sphereFirst p))

private theorem orbitInverse_source {p : SphereCarrier.{0}} (hp : sphereFirst p ≠ 0) :
    ‖(orbitInverse p).1‖ < 1 := by
  rw [orbitInverse, modelPlaneComplex.symm.norm_map]
  have h := norm_sphereFirst_sq_add p
  have hn : 0 < ‖sphereFirst p‖ := norm_pos_iff.mpr hp
  nlinarith [norm_nonneg (sphereSecond p)]

private theorem orbitRadius_inverse (p : SphereCarrier.{0}) :
    orbitRadius (orbitInverse p).1 = ‖sphereFirst p‖ := by
  unfold orbitRadius orbitInverse
  rw [modelPlaneComplex.symm.norm_map]
  have h := norm_sphereFirst_sq_add p
  have he : 1 - ‖sphereSecond p‖ ^ 2 = ‖sphereFirst p‖ ^ 2 := by linarith
  rw [he, Real.sqrt_sq (norm_nonneg _)]

private theorem orbitSource_open :
    IsOpen {p : EuclideanSpace ℝ (Fin 2) × Circle | ‖p.1‖ < 1} :=
  isOpen_lt (continuous_norm.comp continuous_fst) continuous_const

private theorem orbitTarget_open : IsOpen {p : SphereCarrier.{0} | sphereFirst p ≠ 0} :=
  isOpen_ne.preimage contMDiff_sphereFirst.continuous

private theorem orbitMap_smooth : ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ orbitMap
    {p : EuclideanSpace ℝ (Fin 2) × Circle | ‖p.1‖ < 1} := by
  have hr : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : EuclideanSpace ℝ (Fin 2) × Circle => orbitRadius p.1)
      {p | ‖p.1‖ < 1} := by
    intro p hp
    change ‖p.1‖ < 1 at hp
    have hpos : 0 < 1 - ‖p.1‖ ^ 2 := by nlinarith [norm_nonneg p.1]
    have hd : ContDiffAt ℝ ∞ orbitRadius p.1 :=
      (Real.contDiffAt_sqrt hpos.ne').comp p.1
        (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt
    exact (hd.contMDiffAt.comp p contMDiff_fst.contMDiffAt).contMDiffWithinAt
  refine contMDiffOn_of_sphereFirst_sphereSecond orbitSource_open ?_ ?_
  · apply (contMDiffOn_smul_of_real hr
      (contMDiff_circle_coe.comp contMDiff_snd).contMDiffOn).congr
    intro p hp
    exact orbitMap_first hp
  · apply (modelPlaneComplex.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_fst).contMDiffOn.congr
    intro p hp
    exact orbitMap_second hp

private theorem orbitInverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ orbitInverse
    {p : SphereCarrier.{0} | sphereFirst p ≠ 0} := by
  refine ContMDiffOn.prodMk ?_ ?_
  · exact (modelPlaneComplex.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_sphereSecond).contMDiffOn
  · exact contMDiffOn_unitOf.comp contMDiff_sphereFirst.contMDiffOn (fun p hp => hp)

def loopCircleCoordinates : PartialDiffeomorph ((𝓡 2).prod (𝓡 1)) (𝓡 3)
    (EuclideanSpace ℝ (Fin 2) × Circle) SphereCarrier.{0} ∞ where
  toFun := orbitMap
  invFun := orbitInverse
  source := {p | ‖p.1‖ < 1}
  target := {p | sphereFirst p ≠ 0}
  map_source' := by
    intro p hp
    change sphereFirst (orbitMap p) ≠ 0
    rw [orbitMap_first hp]
    exact smul_ne_zero (orbitRadius_pos hp).ne' (Circle.coe_ne_zero p.2)
  map_target' := fun p hp => orbitInverse_source hp
  left_inv' := by
    intro p hp
    refine Prod.ext ?_ ?_
    · change modelPlaneComplex.symm (sphereSecond (orbitMap p)) = p.1
      rw [orbitMap_second hp, LinearIsometryEquiv.symm_apply_apply]
    · change unitOf (sphereFirst (orbitMap p)) = p.2
      rw [orbitMap_first hp]
      exact unitOf_smul (orbitRadius_pos hp) p.2
  right_inv' := by
    intro p hp
    apply sphere_ext
    · rw [orbitMap_first (orbitInverse_source hp), orbitRadius_inverse p]
      exact norm_smul_unitOf (sphereFirst p)
    · rw [orbitMap_second (orbitInverse_source hp)]
      exact modelPlaneComplex.apply_symm_apply (sphereSecond p)
  open_source := orbitSource_open
  open_target := orbitTarget_open
  contMDiffOn_toFun := orbitMap_smooth
  contMDiffOn_invFun := orbitInverse_smooth

theorem loopCircleCoordinates_source : loopCircleCoordinates.source =
    {p | ‖p.1‖ < 1} := rfl

theorem loopCircleCoordinates_target : loopCircleCoordinates.target =
    {p | sphereFirst p ≠ 0} := rfl

theorem loopCircleCoordinates_second {p : EuclideanSpace ℝ (Fin 2) × Circle}
    (hp : ‖p.1‖ < 1) : sphereSecond (loopCircleCoordinates p) = modelPlaneComplex p.1 :=
  orbitMap_second hp

theorem loopCircleCoordinates_first {p : EuclideanSpace ℝ (Fin 2) × Circle}
    (hp : ‖p.1‖ < 1) : sphereFirst (loopCircleCoordinates p) =
      Real.sqrt (1 - ‖p.1‖ ^ 2) • (p.2 : ℂ) := orbitMap_first hp

theorem loopCircleCoordinates_inverse (p : SphereCarrier.{0}) :
    loopCircleCoordinates.symm p =
      (modelPlaneComplex.symm (sphereSecond p), unitOf (sphereFirst p)) := rfl

end GC.GraphManifold.Assembly
