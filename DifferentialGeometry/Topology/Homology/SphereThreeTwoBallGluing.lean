import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeTransport
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import DifferentialGeometry.Topology.Homology.HurewiczThreeWitness
import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier
import DifferentialGeometry.Topology.Homology.OpenCoverSphereLinking

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Metric Set

universe u

namespace DifferentialGeometry.Topology

private def snocVec (x : Fin 3 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  fun i => if h : (i : ℕ) < 3 then x ⟨i, h⟩ else t

private theorem snocVec_continuous :
    Continuous fun q : (Fin 3 → ℝ) × ℝ => snocVec q.1 q.2 := by
  rw [continuous_pi_iff]
  intro i
  unfold snocVec
  by_cases h : (i : ℕ) < 3
  · simp only [dif_pos h]
    exact (continuous_apply (ι := Fin 3) (A := fun _ : Fin 3 => ℝ) ⟨i, h⟩).comp
      continuous_fst
  · simp only [dif_neg h]
    exact continuous_snd

private theorem snocVec_castSucc (x : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    snocVec x t i.castSucc = x i := by
  unfold snocVec
  split_ifs with h
  · exact congrArg x (Fin.ext rfl)
  · exact absurd i.isLt h

private theorem snocVec_last (x : Fin 3 → ℝ) (t : ℝ) :
    snocVec x t (Fin.last 3) = t := by
  unfold snocVec
  split_ifs with h
  · exact absurd h (by decide)
  · rfl

private def ballAmbient (p : EuclideanSpace ℝ (Fin 3) × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (snocVec (fun i => p.1 i) p.2)

private theorem ballAmbient_continuous : Continuous ballAmbient := by
  have hfst : Continuous fun p : EuclideanSpace ℝ (Fin 3) × ℝ => p.1 := continuous_fst
  have hproj : Continuous fun p : EuclideanSpace ℝ (Fin 3) × ℝ => (fun i => p.1 i) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hfst
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
    (snocVec_continuous.comp (hproj.prodMk continuous_snd))

private theorem ballAmbient_norm_sq (p : EuclideanSpace ℝ (Fin 3) × ℝ) :
    ‖ballAmbient p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  rw [ballAmbient, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc, WithLp.ofLp_toLp,
    snocVec_last, Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq p.1]
  rw [show (∑ i : Fin 3, ‖snocVec (fun i => p.1 i) p.2 i.castSucc‖ ^ 2)
      = ∑ i : Fin 3, ‖p.1 i‖ ^ 2 from
    Finset.sum_congr rfl fun i _ => by rw [snocVec_castSucc]]

private def ballAmbientOne (v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => v (Fin.castSucc i))

private theorem ballAmbientOne_norm_sq (v : EuclideanSpace ℝ (Fin 4)) :
    ‖ballAmbientOne v‖ ^ 2 = ∑ i : Fin 3, (v (Fin.castSucc i)) ^ 2 := by
  rw [ballAmbientOne, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

private def sphereThreeGluingAmbient (p : SphereThree) : EuclideanSpace ℝ (Fin 4) :=
  ballAmbient (ballAmbientOne p.1, p.1 (Fin.last 3))

private theorem sphereThree_norm_sq_split (v : EuclideanSpace ℝ (Fin 4)) :
    ‖v‖ ^ 2 = (∑ i : Fin 3, (v (Fin.castSucc i)) ^ 2) + (v (Fin.last 3)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem sphereThreeProjection_split (p : SphereThree) :
    (∑ i : Fin 3, (p.1 (Fin.castSucc i)) ^ 2) + (p.1 (Fin.last 3)) ^ 2 = 1 := by
  rw [← sphereThree_norm_sq_split p.1, norm_eq_of_mem_sphere p]
  norm_num

private theorem sphereThreeGluingAmbient_norm_sq (p : SphereThree) :
    ‖sphereThreeGluingAmbient p‖ ^ 2 = 1 := by
  have hp : ‖p.1‖ = 1 := norm_eq_of_mem_sphere p
  rw [sphereThreeGluingAmbient, ballAmbient_norm_sq, ballAmbientOne_norm_sq]
  nlinarith [sphereThree_norm_sq_split p.1, hp]

private theorem sphereThreeGluingAmbient_continuous : Continuous sphereThreeGluingAmbient := by
  have hproj : Continuous fun p : SphereThree => ballAmbientOne p.1 := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
    exact continuous_pi fun i =>
      (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i.castSucc).comp continuous_subtype_val
  have hlast : Continuous fun p : SphereThree => p.1 (Fin.last 3) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (Fin.last 3)).comp continuous_subtype_val
  exact ballAmbient_continuous.comp (hproj.prodMk hlast)

private def sphereThreeGluingPoint (p : SphereThree) : SphereThree :=
  ⟨sphereThreeGluingAmbient p, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hsq := sphereThreeGluingAmbient_norm_sq p
    nlinarith [norm_nonneg (sphereThreeGluingAmbient p)]⟩

private theorem sphereThreeGluingPoint_continuous : Continuous sphereThreeGluingPoint :=
  sphereThreeGluingAmbient_continuous.subtype_mk _

private theorem sphereThreeGluingAmbient_eq (p : SphereThree) :
    sphereThreeGluingAmbient p = p.1 := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;>
    simp [sphereThreeGluingAmbient, ballAmbient, ballAmbientOne, snocVec, WithLp.ofLp_toLp]

private def sphereThreeProjection (p : SphereThree) :
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨ballAmbientOne p.1, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hsq : ‖ballAmbientOne p.1‖ ^ 2 ≤ 1 := by
      rw [ballAmbientOne_norm_sq]
      linarith [sphereThreeProjection_split p, sq_nonneg (p.1 (Fin.last 3))]
    nlinarith [norm_nonneg (ballAmbientOne p.1)]⟩

private theorem sphereThreeProjection_norm_sq (p : SphereThree) :
    ‖(sphereThreeProjection p).1‖ ^ 2 + (p.1 (Fin.last 3)) ^ 2 = 1 := by
  rw [show (sphereThreeProjection p).1 = ballAmbientOne p.1 from rfl, ballAmbientOne_norm_sq]
  exact sphereThreeProjection_split p

def sphereThreeNorthBallMap : C(closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, SphereThree) where
  toFun x := ⟨ballAmbient (x.1, Real.sqrt (1 - ‖x.1‖ ^ 2)), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hx : ‖x.1‖ ≤ 1 := by
      have h := Metric.mem_closedBall.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    have hnn : 0 ≤ 1 - ‖x.1‖ ^ 2 := by nlinarith [norm_nonneg x.1]
    have hsq := ballAmbient_norm_sq (x.1, Real.sqrt (1 - ‖x.1‖ ^ 2))
    rw [Real.sq_sqrt hnn] at hsq
    have h1 : ‖ballAmbient (x.1, Real.sqrt (1 - ‖x.1‖ ^ 2))‖ ^ 2 = 1 := by
      rw [hsq]; ring
    nlinarith [norm_nonneg (ballAmbient (x.1, Real.sqrt (1 - ‖x.1‖ ^ 2)))]⟩
  continuous_toFun := by
    have hsqrt : Continuous fun x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        Real.sqrt (1 - ‖x.1‖ ^ 2) :=
      Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2))
    exact (ballAmbient_continuous.comp (continuous_subtype_val.prodMk hsqrt)).subtype_mk _

def sphereThreeSouthBallMap : C(closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, SphereThree) where
  toFun x := ⟨ballAmbient (x.1, -Real.sqrt (1 - ‖x.1‖ ^ 2)), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hx : ‖x.1‖ ≤ 1 := by
      have h := Metric.mem_closedBall.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    have hnn : 0 ≤ 1 - ‖x.1‖ ^ 2 := by nlinarith [norm_nonneg x.1]
    have hsq := ballAmbient_norm_sq (x.1, -Real.sqrt (1 - ‖x.1‖ ^ 2))
    rw [neg_sq, Real.sq_sqrt hnn] at hsq
    have h1 : ‖ballAmbient (x.1, -Real.sqrt (1 - ‖x.1‖ ^ 2))‖ ^ 2 = 1 := by
      rw [hsq]; ring
    nlinarith [norm_nonneg (ballAmbient (x.1, -Real.sqrt (1 - ‖x.1‖ ^ 2)))]⟩
  continuous_toFun := by
    have hsqrt : Continuous fun x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        -Real.sqrt (1 - ‖x.1‖ ^ 2) :=
      (Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2))).neg
    exact (ballAmbient_continuous.comp (continuous_subtype_val.prodMk hsqrt)).subtype_mk _

theorem sphereThreeNorthBallMap_eq_southBallMap_on_boundary
    (q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereThreeNorthBallMap (sphereBallBoundaryInclusion 3 q) =
      sphereThreeSouthBallMap (sphereBallBoundaryInclusion 3 q) := by
  have hq : ‖q.1‖ = 1 := norm_eq_of_mem_sphere q
  have hzero : Real.sqrt (1 - ‖q.1‖ ^ 2) = 0 := by
    rw [hq]; norm_num
  refine Subtype.ext ?_
  simp only [sphereThreeNorthBallMap, sphereThreeSouthBallMap, sphereBallBoundaryInclusion,
    ContinuousMap.coe_mk, hzero, neg_zero]

private theorem sphereThreeNorthBallMap_projection (p : SphereThree)
    (hp : 0 ≤ p.1 (Fin.last 3)) :
    sphereThreeNorthBallMap (sphereThreeProjection p) = sphereThreeGluingPoint p := by
  have hsqrt : Real.sqrt (1 - ‖ballAmbientOne p.1‖ ^ 2) = p.1 (Fin.last 3) := by
    rw [show (1 : ℝ) - ‖ballAmbientOne p.1‖ ^ 2 = (p.1 (Fin.last 3)) ^ 2 from by
      rw [ballAmbientOne_norm_sq]
      linarith [sphereThreeProjection_split p], Real.sqrt_sq hp]
  refine Subtype.ext ?_
  change ballAmbient (ballAmbientOne p.1, Real.sqrt (1 - ‖ballAmbientOne p.1‖ ^ 2)) =
    ballAmbient (ballAmbientOne p.1, p.1 (Fin.last 3))
  rw [hsqrt]

private theorem sphereThreeSouthBallMap_projection (p : SphereThree)
    (hp : p.1 (Fin.last 3) ≤ 0) :
    sphereThreeSouthBallMap (sphereThreeProjection p) = sphereThreeGluingPoint p := by
  have hsqrt : Real.sqrt (1 - ‖ballAmbientOne p.1‖ ^ 2) = -p.1 (Fin.last 3) := by
    rw [show (1 : ℝ) - ‖ballAmbientOne p.1‖ ^ 2 = (p.1 (Fin.last 3)) ^ 2 from by
      rw [ballAmbientOne_norm_sq]
      linarith [sphereThreeProjection_split p], Real.sqrt_sq_eq_abs, abs_of_nonpos hp]
  refine Subtype.ext ?_
  change ballAmbient (ballAmbientOne p.1, -Real.sqrt (1 - ‖ballAmbientOne p.1‖ ^ 2)) =
    ballAmbient (ballAmbientOne p.1, p.1 (Fin.last 3))
  rw [hsqrt, neg_neg]

def sphereThreeTwoBallGluedMap : C(SphereThree, SphereThree) where
  toFun := sphereThreeGluingPoint
  continuous_toFun := sphereThreeGluingPoint_continuous

theorem sphereThreeTwoBallGluedMap_apply_of_nonneg (p : SphereThree)
    (hp : 0 ≤ p.1 (Fin.last 3)) :
    sphereThreeTwoBallGluedMap p = sphereThreeNorthBallMap (sphereThreeProjection p) :=
  (sphereThreeNorthBallMap_projection p hp).symm

theorem sphereThreeTwoBallGluedMap_apply_of_neg (p : SphereThree) (hp : p.1 (Fin.last 3) < 0) :
    sphereThreeTwoBallGluedMap p = sphereThreeSouthBallMap (sphereThreeProjection p) :=
  (sphereThreeSouthBallMap_projection p (le_of_lt hp)).symm

theorem sphereThreeTwoBallGluedMap_eq_id :
    sphereThreeTwoBallGluedMap = ContinuousMap.id SphereThree :=
  ContinuousMap.ext fun p => Subtype.ext (sphereThreeGluingAmbient_eq p)

def sphereThreeTwoBallGluedLoop : C(SphereThree, liftedHomotopySphere.{0} 2) :=
  (euclideanSphereToLiftedHomotopySphere.{0} 2).comp sphereThreeTwoBallGluedMap

theorem freeSphereHomologyImage_sphereThreeTwoBallGluedLoop
    (c : integralSingularHomology 3 (liftedHomotopySphere.{0} 2)) :
    freeSphereHomologyImage 2 c (ZerothHomotopy.mk sphereThreeTwoBallGluedLoop) = c := by
  rw [freeSphereHomologyImage_mk]
  have hcomp : sphereThreeTwoBallGluedLoop.comp (liftedHomotopySphereDown 2) =
      ContinuousMap.id (liftedHomotopySphere.{0} 2) := by
    rw [sphereThreeTwoBallGluedLoop, ContinuousMap.comp_assoc, sphereThreeTwoBallGluedMap_eq_id,
      ContinuousMap.id_comp]
    exact euclideanSphereToLiftedHomotopySphere_comp_down 2
  rw [hcomp, integralSingularHomologyMap_id, LinearMap.id_apply]

theorem freeSphereHomologyImage_sphereThreeTwoBallGluedLoop_ne_zero :
    freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{0} 2)
      (ZerothHomotopy.mk sphereThreeTwoBallGluedLoop) ≠ 0 := by
  rw [freeSphereHomologyImage_sphereThreeTwoBallGluedLoop]
  exact integralLiftedSphereGenerator_ne_zero 2

theorem gluedSphereMap_const_eq_const {X : Type u} [TopologicalSpace X] (p : X)
    (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (ContinuousMap.const _ p) (sphereBallBoundaryInclusion 3 q) =
        (ContinuousMap.const _ p) (sphereBallBoundaryInclusion 3 q)) :
    gluedSphereMap 2 (ContinuousMap.const _ p) (ContinuousMap.const _ p) h =
      ContinuousMap.const _ p := by
  refine ContinuousMap.ext fun q => ?_
  simp only [gluedSphereMap, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  split_ifs <;> rfl

theorem freeSphereHomologyImage_gluedSphereMap_const_eq_zero {X : Type u} [TopologicalSpace X]
    (p : X)
    (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (ContinuousMap.const _ p) (sphereBallBoundaryInclusion 3 q) =
        (ContinuousMap.const _ p) (sphereBallBoundaryInclusion 3 q))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) :
    freeSphereHomologyImage 2 c
      (ZerothHomotopy.mk (gluedSphereMap 2 (ContinuousMap.const _ p)
        (ContinuousMap.const _ p) h)) = 0 := by
  rw [gluedSphereMap_const_eq_const p h, freeSphereHomologyImage_const]

theorem hurewiczThreeSphereGeneration_sphereThree_of_liftedHomotopySphere
    (h : HurewiczThreeSphereGeneration (liftedHomotopySphere.{0} 2)) :
    HurewiczThreeSphereGeneration SphereThree :=
  (hurewiczThreeSphereGeneration_iff_of_homotopyEquiv
    (Homeomorph.ulift (X := SphereThree)).toHomotopyEquiv).mp h

theorem hurewiczThreeSphereGeneration_sphereThree_of_cubeSphereFundamentalClass
    (hgen : IsSphereHomologyGenerator.{0} 2 cubeSphereFundamentalClass) :
    HurewiczThreeSphereGeneration SphereThree :=
  hurewiczThreeSphereGeneration_sphereThree_of_liftedHomotopySphere
    (hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass hgen)

private noncomputable def complSingletonHomeomorph {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    ({x}ᶜ : Set X) ≃ₜ ({(e x)}ᶜ : Set Y) where
  toFun y := ⟨e y.1, by
    intro hy
    exact y.2 (e.injective hy)⟩
  invFun y := ⟨e.symm y.1, by
    intro hy
    refine y.2 ?_
    simp only [Set.mem_singleton_iff]
    rw [← e.apply_symm_apply y.1, hy]⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem noncompactPoincareDualityTwoOne_of_homeomorph {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : noncompactPoincareDualityTwoOne X) :
    noncompactPoincareDualityTwoOne Y := by
  obtain ⟨iso⟩ := h
  exact ⟨(integralSingularHomologyHomotopyEquiv 2 e.toHomotopyEquiv).symm.toModuleIso ≪≫
    iso ≪≫
    (integralSingularCohomologyEquivOfHomeomorph (Homeomorph.onePointCongr e) 1).toModuleIso⟩

theorem noncompactPoincareDualityTwoOne_liftedHomotopySphere_compl_singleton
    (x : liftedHomotopySphere.{0} 2) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set (liftedHomotopySphere.{0} 2)) :=
  noncompactPoincareDualityTwoOne_of_homeomorph
    (complSingletonHomeomorph (Homeomorph.ulift (X := SphereThree)) x).symm
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton
      (Homeomorph.ulift (X := SphereThree) x))

end DifferentialGeometry.Topology
