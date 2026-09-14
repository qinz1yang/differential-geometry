import DifferentialGeometry.Topology.Homology.ContractibleCoverOneEvaluation
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import DifferentialGeometry.Topology.Homology.SphereRank
import Mathlib.Data.Fin.VecNotation

noncomputable section

universe u

open Set Metric ContinuousMap CategoryTheory CategoryTheory.Limits AlgebraicTopology Module

namespace DifferentialGeometry.Topology

abbrev PuncturePlane := EuclideanSpace ℝ (Fin 2)

abbrev PunctureCircle := Metric.sphere (0 : PuncturePlane) 1

def circlePoint (θ : ℝ) : PuncturePlane := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

theorem continuous_circlePoint : Continuous circlePoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [circlePoint] using Real.continuous_cos
  · simpa [circlePoint] using Real.continuous_sin

theorem circlePoint_norm (θ : ℝ) : ‖circlePoint θ‖ = 1 := by
  rw [circlePoint, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]

theorem circlePoint_coord_one (θ : ℝ) : circlePoint θ 1 = Real.sin θ := by
  simp [circlePoint]

def circleElement (θ : ℝ) : PunctureCircle :=
  ⟨circlePoint θ, by rw [mem_sphere, dist_zero_right, circlePoint_norm]⟩

theorem continuous_circleElement : Continuous circleElement :=
  Continuous.subtype_mk continuous_circlePoint _

def circlePole : PunctureCircle := circleElement (Real.pi / 2)

theorem circleElement_coord_one (θ : ℝ) : (circleElement θ : PuncturePlane) 1 = Real.sin θ :=
  circlePoint_coord_one θ

theorem circlePole_coord_one : (circlePole : PuncturePlane) 1 = 1 := by
  simp [circlePole, circleElement, circlePoint, Real.sin_pi_div_two]

theorem neg_circlePole_coord_one : ((-circlePole : PunctureCircle) : PuncturePlane) 1 = -1 := by
  simp [circlePole, circleElement, circlePoint, Real.sin_pi_div_two]

theorem circleElement_ne_circlePole_of_sin_ne_one (θ : ℝ) (h : Real.sin θ ≠ 1) :
    circleElement θ ≠ circlePole := by
  intro he
  apply h
  have hc := congrArg (fun y : PuncturePlane => y 1) (congrArg Subtype.val he)
  simpa [circlePole, circleElement, circlePoint, Real.sin_pi_div_two] using hc

theorem circleElement_ne_neg_circlePole_of_sin_ne_neg_one (θ : ℝ) (h : Real.sin θ ≠ -1) :
    circleElement θ ≠ -circlePole := by
  intro he
  apply h
  have hc := congrArg (fun y : PuncturePlane => y 1) (congrArg Subtype.val he)
  simpa [circlePole, circleElement, circlePoint, Real.sin_pi_div_two] using hc

theorem circleElement_ne_circlePole_of_sin_nonpos (θ : ℝ) (h : Real.sin θ ≤ 0) :
    circleElement θ ≠ circlePole :=
  circleElement_ne_circlePole_of_sin_ne_one θ (by linarith)

theorem circleElement_ne_neg_circlePole_of_sin_nonneg (θ : ℝ) (h : 0 ≤ Real.sin θ) :
    circleElement θ ≠ -circlePole :=
  circleElement_ne_neg_circlePole_of_sin_ne_neg_one θ (by linarith)

theorem sin_pi_add_mul_pi_le_zero (s : unitInterval) :
    Real.sin (Real.pi + Real.pi * (s : ℝ)) ≤ 0 := by
  have h2 : Real.pi + Real.pi * (s : ℝ) = Real.pi * (s : ℝ) + Real.pi := by ring
  rw [h2, Real.sin_add_pi]
  have hs0 : (0 : ℝ) ≤ Real.pi * (s : ℝ) := mul_nonneg Real.pi_pos.le s.property.1
  have hs1 : Real.pi * (s : ℝ) ≤ Real.pi := by
    simpa using mul_le_mul_of_nonneg_left s.property.2 Real.pi_pos.le
  have := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hs1
  linarith

theorem sin_mul_pi_nonneg (s : unitInterval) : 0 ≤ Real.sin (Real.pi * (s : ℝ)) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le s.property.1)
    (by simpa using mul_le_mul_of_nonneg_left s.property.2 Real.pi_pos.le)

def circleEast : PunctureCircle := circleElement 0

def circleWest : PunctureCircle := circleElement Real.pi

theorem circleElement_two_pi : circleElement (2 * Real.pi) = circleEast := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [circleEast, circleElement, circlePoint, Real.cos_two_pi, Real.sin_two_pi]

theorem circleElement_three_pi_div_two : circleElement (3 * Real.pi / 2) = -circlePole := by
  have h3 : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
  rw [h3]
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [circlePole, circleElement, circlePoint, Real.cos_add_pi, Real.sin_add_pi]

theorem circleEast_ne_circlePole : circleEast ≠ circlePole :=
  circleElement_ne_circlePole_of_sin_ne_one 0 (by simp)

theorem circleEast_ne_neg_circlePole : circleEast ≠ -circlePole :=
  circleElement_ne_neg_circlePole_of_sin_ne_neg_one 0 (by simp)

theorem circleWest_ne_circlePole : circleWest ≠ circlePole :=
  circleElement_ne_circlePole_of_sin_ne_one Real.pi (by simp)

theorem circleWest_ne_neg_circlePole : circleWest ≠ -circlePole :=
  circleElement_ne_neg_circlePole_of_sin_ne_neg_one Real.pi (by simp)

theorem circleWest_ne_circleEast : circleWest ≠ circleEast := by
  intro h
  have hc := congrArg (fun y : PuncturePlane => y 0) (congrArg Subtype.val h)
  simp only [circleEast, circleWest, circleElement, circlePoint, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Real.cos_zero, Real.cos_pi] at hc
  norm_num at hc

abbrev polePunctured : Set PunctureCircle := {circlePole}ᶜ

abbrev antipolePunctured : Set PunctureCircle := {-circlePole}ᶜ

theorem circleEast_mem_polePunctured : circleEast ∈ polePunctured := by
  simp only [polePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleEast_ne_circlePole

theorem circleWest_mem_polePunctured : circleWest ∈ polePunctured := by
  simp only [polePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleWest_ne_circlePole

theorem circleEast_mem_antipolePunctured : circleEast ∈ antipolePunctured := by
  simp only [antipolePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleEast_ne_neg_circlePole

theorem circleWest_mem_antipolePunctured : circleWest ∈ antipolePunctured := by
  simp only [antipolePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleWest_ne_neg_circlePole

theorem antipoleArc_mem (s : unitInterval) :
    circleElement (Real.pi * (s : ℝ)) ∈ antipolePunctured := by
  simp only [antipolePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleElement_ne_neg_circlePole_of_sin_nonneg _ (sin_mul_pi_nonneg s)

theorem poleArc_mem (s : unitInterval) :
    circleElement (Real.pi + Real.pi * (s : ℝ)) ∈ polePunctured := by
  simp only [polePunctured, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact circleElement_ne_circlePole_of_sin_nonpos _ (sin_pi_add_mul_pi_le_zero s)

def circleUpperArc :
    Path (⟨circleEast, circleEast_mem_antipolePunctured⟩ : ↥antipolePunctured)
      ⟨circleWest, circleWest_mem_antipolePunctured⟩ where
  toFun s := ⟨circleElement (Real.pi * (s : ℝ)), antipoleArc_mem s⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_circleElement.comp (continuous_const.mul continuous_subtype_val)) antipoleArc_mem
  source' := by
    refine Subtype.ext ?_
    simp [circleEast]
  target' := by
    refine Subtype.ext ?_
    simp [circleWest]

def circleLowerArc :
    Path (⟨circleWest, circleWest_mem_polePunctured⟩ : ↥polePunctured)
      ⟨circleEast, circleEast_mem_polePunctured⟩ where
  toFun s := ⟨circleElement (Real.pi + Real.pi * (s : ℝ)), poleArc_mem s⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_circleElement.comp
      (continuous_const.add (continuous_const.mul continuous_subtype_val))) poleArc_mem
  source' := by
    refine Subtype.ext ?_
    simp [circleWest]
  target' := by
    refine Subtype.ext ?_
    change circleElement (Real.pi + Real.pi * ((1 : unitInterval) : ℝ)) = circleEast
    rw [show Real.pi + Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi by
      simp
      ring]
    exact circleElement_two_pi

def circleHalfPoint : unitInterval := ⟨1 / 2, by norm_num⟩

theorem circleUpperArc_halfPoint :
    ((circleUpperArc circleHalfPoint : ↥antipolePunctured) : PunctureCircle) = circlePole := by
  have h : Real.pi * ((circleHalfPoint : ℝ)) = Real.pi / 2 := by
    rw [show ((circleHalfPoint : unitInterval) : ℝ) = 1 / 2 from rfl]
    ring
  change circleElement (Real.pi * (circleHalfPoint : ℝ)) = circlePole
  rw [h]
  rfl

theorem circleLowerArc_halfPoint :
    ((circleLowerArc circleHalfPoint : ↥polePunctured) : PunctureCircle) = -circlePole := by
  have h : Real.pi + Real.pi * ((circleHalfPoint : ℝ)) = 3 * Real.pi / 2 := by
    norm_num [circleHalfPoint]
    ring
  change circleElement (Real.pi + Real.pi * (circleHalfPoint : ℝ)) = -circlePole
  rw [h]
  exact circleElement_three_pi_div_two

def circleLowerArcChain : integralSingularCoefficients ⟶
    (integralSingularChains ↥polePunctured).X 1 :=
  integralChainHom 1 (integralPathChain circleLowerArc)

def circleUpperArcChain : integralSingularCoefficients ⟶
    (integralSingularChains ↥antipolePunctured).X 1 :=
  integralChainHom 1 (integralPathChain circleUpperArc)

theorem circleLowerArcChain_boundary :
    circleLowerArcChain ≫ (integralSingularChains ↥polePunctured).d 1 0 =
      integralChainHom 0 (integralVertexChain
          (⟨circleEast, circleEast_mem_polePunctured⟩ : ↥polePunctured) -
        integralVertexChain
          (⟨circleWest, circleWest_mem_polePunctured⟩ : ↥polePunctured)) := by
  unfold circleLowerArcChain
  rw [integralChainHom_d, integralPathChain_boundary]

theorem circleUpperArcChain_boundary :
    circleUpperArcChain ≫ (integralSingularChains ↥antipolePunctured).d 1 0 =
      integralChainHom 0 (integralVertexChain
          (⟨circleWest, circleWest_mem_antipolePunctured⟩ : ↥antipolePunctured) -
        integralVertexChain
          (⟨circleEast, circleEast_mem_antipolePunctured⟩ : ↥antipolePunctured)) := by
  unfold circleUpperArcChain
  rw [integralChainHom_d, integralPathChain_boundary]

def circleArcCycle : integralSingularCoefficients ⟶
    (integralSingularChains PunctureCircle).X 1 :=
  circleLowerArcChain ≫
      (integralSingularChainMap (singularSubspaceInclusion polePunctured)).f 1 +
    circleUpperArcChain ≫
      (integralSingularChainMap (singularSubspaceInclusion antipolePunctured)).f 1

private theorem integralChainHom_neg {X : Type u} [TopologicalSpace X] (n : ℕ)
    (c : (integralSingularChains X).X n) :
    integralChainHom n (-c) = -integralChainHom n c := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, integralChainHom_hom, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  rw [smul_neg]

theorem circleArcCycle_boundary :
    circleArcCycle ≫ (integralSingularChains PunctureCircle).d 1 0 = 0 := by
  unfold circleArcCycle
  rw [Preadditive.add_comp]
  rw [Category.assoc, Category.assoc]
  rw [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm]
  rw [← Category.assoc, ← Category.assoc]
  rw [circleLowerArcChain_boundary, circleUpperArcChain_boundary]
  rw [integralChainHom_comp_map, integralChainHom_comp_map]
  have hA : ((integralSingularChainMap (singularSubspaceInclusion polePunctured)).f 0)
        (integralVertexChain (⟨circleEast, circleEast_mem_polePunctured⟩ : ↥polePunctured) -
          integralVertexChain (⟨circleWest, circleWest_mem_polePunctured⟩ : ↥polePunctured)) =
      integralVertexChain circleEast - integralVertexChain circleWest := by
    rw [map_sub, integralVertexChain_map, integralVertexChain_map]
    rfl
  have hB : ((integralSingularChainMap (singularSubspaceInclusion antipolePunctured)).f 0)
        (integralVertexChain
            (⟨circleWest, circleWest_mem_antipolePunctured⟩ : ↥antipolePunctured) -
          integralVertexChain
            (⟨circleEast, circleEast_mem_antipolePunctured⟩ : ↥antipolePunctured)) =
      integralVertexChain circleWest - integralVertexChain circleEast := by
    rw [map_sub, integralVertexChain_map, integralVertexChain_map]
    rfl
  rw [hA, hB, sub_eq_add_neg, sub_eq_add_neg, integralChainHom_add, integralChainHom_add,
    integralChainHom_neg, integralChainHom_neg]
  abel

def circleArcIntersection : integralSingularCoefficients ⟶
    (integralSingularChains
      ↥(subspaceIntersection polePunctured antipolePunctured)).X 0 :=
  integralChainHom 0 (integralVertexChain
    (⟨⟨circleWest, circleWest_mem_antipolePunctured⟩, circleWest_mem_polePunctured⟩ :
      ↥(subspaceIntersection polePunctured antipolePunctured)) -
    integralVertexChain
      (⟨⟨circleEast, circleEast_mem_antipolePunctured⟩, circleEast_mem_polePunctured⟩ :
      ↥(subspaceIntersection polePunctured antipolePunctured)))

theorem circleArcIntersection_inclusion :
    circleArcIntersection ≫ (integralSingularChainMap
        (singularSubspaceInclusion
          (subspaceIntersection polePunctured antipolePunctured))).f 0 =
      circleUpperArcChain ≫ (integralSingularChains ↥antipolePunctured).d 1 0 := by
  unfold circleArcIntersection
  rw [integralChainHom_comp_map, circleUpperArcChain_boundary]
  congr 1
  rw [map_sub, integralVertexChain_map, integralVertexChain_map]
  rfl

theorem circleArcIntersection_boundary :
    circleArcIntersection ≫ (integralSingularChains
      ↥(subspaceIntersection polePunctured antipolePunctured)).d 0 0 = 0 := by
  rw [(integralSingularChains
      ↥(subspaceIntersection polePunctured antipolePunctured)).shape 0 0 (by simp),
    Limits.comp_zero]

local instance : PathConnectedSpace PunctureCircle :=
  unitSphere_pathConnected_of_finrank (E := PuncturePlane) (by norm_num)

theorem integralSphereHomologyOneReducedEquiv_circlePoleArcCycle_apply_val :
    (integralSphereHomologyOneReducedEquiv circlePole
        (integralHomologyClassOf 0 circleArcCycle circleArcCycle_boundary)).val =
      integralSingularHomologyMap 0 (spherePoleIntersectionHomotopyEquiv circlePole).toFun
        (((integralSingularChains
              ↥(subspaceIntersection polePunctured antipolePunctured)).liftCycles
            circleArcIntersection 0 ChainComplex.next_nat_zero circleArcIntersection_boundary ≫
          (integralSingularChains
              ↥(subspaceIntersection polePunctured antipolePunctured)).homologyπ 0)
          (ULift.up 1)) :=
  integralSphereHomologyOneReducedEquiv_liftCycles_apply circlePole circleArcCycle
    circleArcCycle_boundary circleLowerArcChain circleUpperArcChain rfl circleArcIntersection
    circleArcIntersection_inclusion

private theorem homologicalComplex_liftCycles_zero
    {K : HomologicalComplex (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)} (i j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j)
    (hk : (0 : integralSingularCoefficients ⟶ K.X i) ≫ K.d i j = 0) :
    K.liftCycles (0 : integralSingularCoefficients ⟶ K.X i) j hj hk = 0 := by
  rw [← cancel_mono (K.iCycles i), Limits.zero_comp, HomologicalComplex.liftCycles_i]

theorem integralSphereHomologyOneReducedEquiv_eq_zero_of_mem_poleComplement
    (z : integralSingularCoefficients ⟶ (integralSingularChains PunctureCircle).X 1)
    (hz : z ≫ (integralSingularChains PunctureCircle).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains ↥polePunctured).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion polePunctured)).f 1 = z) :
    integralSphereHomologyOneReducedEquiv circlePole
      (integralHomologyClassOf 0 z hz) = 0 := by
  have h := integralSphereHomologyOneReducedEquiv_liftCycles_apply circlePole z hz zA 0
    (by rw [hsplit, Limits.zero_comp, add_zero]) 0 (by simp)
  have hz' : integralHomologyClassOf 0 z hz =
      (((integralSingularChains PunctureCircle).liftCycles z 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains PunctureCircle).homologyπ 1) (ULift.up 1)) := rfl
  rw [hz']
  refine Subtype.ext ?_
  rw [h]
  simp only [homologicalComplex_liftCycles_zero]
  have hz0 : (integralSingularHomologyMap 0 (spherePoleIntersectionHomotopyEquiv circlePole).toFun)
      (0 : integralSingularHomology 0
        ↥(subspaceIntersection polePunctured antipolePunctured)) = 0 :=
    map_zero _
  simpa using hz0

theorem integralHomologyContractibleCoverEquiv_apply_eq_zero_of_mem_left (n : ℕ)
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains ↥A).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) = z) :
    integralHomologyContractibleCoverEquiv n A B hA hB hcover
      (((integralSingularChains X).liftCycles z (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
        (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) = 0 := by
  have h := integralHomologyContractibleCoverEquiv_liftCycles_apply n A B hA hB hcover z hz zA 0
    (by rw [hsplit, Limits.zero_comp, add_zero]) 0 (by simp) (by simp)
  rw [h]
  simp only [homologicalComplex_liftCycles_zero]
  simp

end DifferentialGeometry.Topology
