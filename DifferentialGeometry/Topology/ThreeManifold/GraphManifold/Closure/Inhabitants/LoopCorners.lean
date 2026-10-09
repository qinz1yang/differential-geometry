import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCoreFace

/-!
The two genuine plane corner charts descended from the same loop rims and free circle action.
Their actual orbit coordinates retain every circle angle and the fixed rim box.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private abbrev actualLoopRim (b : Bool) :=
  standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b

private def cornerRadius (v : ℝ × ℝ) : ℝ :=
  neckRadius (1 / 16) (1 + (1 / 16) * v.1) ((1 / 16) * v.2)

private def cornerHeight (b : Bool) (v : ℝ × ℝ) : ℝ :=
  if b then 4 - (1 + (1 / 16) * v.2) * capCos (1 + (1 / 16) * v.1)
  else (1 + (1 / 16) * v.2) * capCos (1 + (1 / 16) * v.1)

private theorem cornerPlane_norm (θ : Circle) : ‖planeOfCircle θ‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

private theorem cornerRadius_pos {v : ℝ × ℝ} (hv : v ∈ rimBox 2) : 0 < cornerRadius v := by
  have hx := (abs_lt.mp hv.1).1
  have hy := (abs_lt.mp hv.2).1
  have hs : 0 < 1 + (1 / 16 : ℝ) * v.1 := by linarith
  rw [cornerRadius, ← neckRatio_mul hs.ne']
  exact mul_pos (neckRatio_pos (by norm_num) (by norm_num) (by linarith)) hs

private theorem cornerRadius_bound {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    cornerRadius v < 9 / 8 := by
  have hr := neckRadius_le_left (ε := (1 / 16)) (by norm_num)
    (1 + (1 / 16 : ℝ) * v.1) ((1 / 16 : ℝ) * v.2)
  have hx := (abs_lt.mp hv.1).2
  change cornerRadius v ≤ 1 + (1 / 16 : ℝ) * v.1 at hr
  linarith

private theorem cornerNeck_mem (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    neckRim (1 / 16) (θ, v) ∈ neckDomain (1 / 16) := by
  have hx := abs_lt.mp hv.1
  have hy := abs_lt.mp hv.2
  have hs : 0 ≤ 1 + (1 / 16 : ℝ) * v.1 := by linarith [hx.1]
  change ‖(1 + (1 / 16 : ℝ) * v.1) • planeOfCircle θ‖ < 1 + 2 * (1 / 16 : ℝ) ∧
    |(1 / 16 : ℝ) * v.2| < 2 * (1 / 16 : ℝ)
  rw [norm_smul, Real.norm_of_nonneg hs, cornerPlane_norm, mul_one, abs_lt]
  exact ⟨by linarith [hx.2], by constructor <;> linarith [hy.1, hy.2]⟩

private theorem cornerPoint_eq (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    actualLoopRim b (θ, v) =
      modelSphere.{0} 1 (cornerRadius v • planeOfCircle θ, cornerHeight b v) := by
  change (modelNeck.{0} (len := 1) (ε := (1 / 16 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 0 b) (neckRim (1 / 16) (θ, v)) = _
  rw [modelNeck_apply]
  change modelSphere.{0} 1
    (zoneChartMap (1 / 16) (modelBase (0 : Fin 1))
      (neckFlip b (neckRim (1 / 16) (θ, v)))) = _
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, zoneChartMap_neckFlip (by norm_num) (by norm_num) 0 b (cornerNeck_mem θ hv)]
  have hs : 0 ≤ 1 + (1 / 16 : ℝ) * v.1 := by linarith [(abs_lt.mp hv.1).1]
  have hn : ‖(neckRim (1 / 16) (θ, v)).1‖ = 1 + (1 / 16 : ℝ) * v.1 := by
    rw [neckRim, norm_smul, Real.norm_of_nonneg hs, cornerPlane_norm, mul_one]
  rw [hn]
  change modelSphere.{0} 1
    (neckRatio (1 / 16) (1 + (1 / 16 : ℝ) * v.1) ((1 / 16 : ℝ) * v.2) •
      ((1 + (1 / 16 : ℝ) * v.1) • planeOfCircle θ),
      if b then 0 + 4 - (1 + (1 / 16 : ℝ) * v.2) * capCos (1 + (1 / 16 : ℝ) * v.1)
      else 0 + (1 + (1 / 16 : ℝ) * v.2) * capCos (1 + (1 / 16 : ℝ) * v.1)) = _
  rw [smul_smul, neckRatio_mul (by linarith [(abs_lt.mp hv.1).1])]
  cases b <;> simp [cornerHeight, cornerRadius] <;> rfl

private theorem cornerPoint_source (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    ‖cornerRadius v • planeOfCircle θ‖ ^ 2 ≤ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (cornerRadius_pos hv).le, cornerPlane_norm, mul_one]
  nlinarith [cornerRadius_pos hv, cornerRadius_bound hv]

def loopRimOrbitBase (b : Bool) (v : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  modelPlaneComplex.symm (sphereSecond (actualLoopRim b (1, v)))

private theorem cornerBase_eq (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopRimOrbitBase b v = modelPlaneComplex.symm
      (modelSecond 1 (cornerRadius v • planeOfCircle θ, cornerHeight b v)) := by
  rw [loopRimOrbitBase, cornerPoint_eq b 1 hv]
  have hs := sphereSecond_modelSphere.{0} 1
    (p := (cornerRadius v • planeOfCircle 1, cornerHeight b v)) (cornerPoint_source 1 hv)
  rw [hs]
  congr 1
  simp only [modelSecond, norm_smul, cornerPlane_norm]

theorem loopRimOrbit_inverse (b : Bool) (θ : Circle) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    loopCircleCoordinates.symm (actualLoopRim b (θ, v)) = (loopRimOrbitBase b v, θ) := by
  rw [cornerPoint_eq b θ hv, loopCircleCoordinates_inverse]
  refine Prod.ext ?_ ?_
  · have hs := sphereSecond_modelSphere.{0} 1
      (p := (cornerRadius v • planeOfCircle θ, cornerHeight b v)) (cornerPoint_source θ hv)
    rw [hs]
    exact (cornerBase_eq b θ hv).symm
  · have hs := sphereFirst_modelSphere.{0} 1
      (p := (cornerRadius v • planeOfCircle θ, cornerHeight b v)) (cornerPoint_source θ hv)
    rw [hs, modelFirst, map_smul, smul_smul]
    have he : modelPlaneComplex (planeOfCircle θ) = (θ : ℂ) :=
      modelPlaneComplex.apply_symm_apply (θ : ℂ)
    rw [he]
    exact unitOf_smul (mul_pos (by positivity) (cornerRadius_pos hv)) θ

private theorem cornerPoint_target (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) : sphereFirst (actualLoopRim b (θ, v)) ≠ 0 := by
  rw [cornerPoint_eq b θ hv]
  have hs := sphereFirst_modelSphere.{0} 1
    (p := (cornerRadius v • planeOfCircle θ, cornerHeight b v)) (cornerPoint_source θ hv)
  rw [hs, modelFirst]
  apply smul_ne_zero (by positivity)
  rw [← modelPlaneComplex.map_zero]
  apply modelPlaneComplex.injective.ne
  apply smul_ne_zero (cornerRadius_pos hv).ne'
  exact norm_ne_zero_iff.mp (by rw [cornerPlane_norm]; norm_num)

private def cornerOrbit (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 2).prod (𝓡 1))
      (Circle × (ℝ × ℝ)) (EuclideanSpace ℝ (Fin 2) × Circle) ∞ :=
  (actualLoopRim b).trans loopCircleCoordinates.symm

private theorem cornerOrbit_source (b : Bool) :
    (cornerOrbit b).source = Set.univ ×ˢ rimBox 2 := by
  ext p
  constructor
  · intro hp
    exact ⟨mem_univ p.1, (standardLoopBallHandleCycle.rim_source
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (p := p)).mp hp.1⟩
  · rintro ⟨hu, hp⟩
    exact ⟨(standardLoopBallHandleCycle.rim_source
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (p := p)).mpr hp,
      cornerPoint_target b p.1 hp⟩

private theorem cornerOrbit_apply (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) : cornerOrbit b (θ, v) = (loopRimOrbitBase b v, θ) :=
  loopRimOrbit_inverse b θ v hv

private theorem cornerBox_open : IsOpen (rimBox 2) :=
  (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

def loopCornerChart (b : Bool) : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2)
    (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)) ∞ where
  toFun := loopRimOrbitBase b
  invFun z := ((cornerOrbit b).symm (z, 1)).2
  source := rimBox 2
  target := {z | (z, (1 : Circle)) ∈ (cornerOrbit b).target}
  map_source' := by
    intro v hv
    have hf := (cornerOrbit b).map_source
      (show (1, v) ∈ (cornerOrbit b).source by rw [cornerOrbit_source]; exact ⟨trivial,hv⟩)
    rwa [cornerOrbit_apply b 1 hv] at hf
  map_target' := by
    intro z hz
    have hf := (cornerOrbit b).map_target hz
    rw [cornerOrbit_source] at hf
    exact hf.2
  left_inv' := by
    intro v hv
    have hf := (cornerOrbit b).left_inv
      (show (1, v) ∈ (cornerOrbit b).source by rw [cornerOrbit_source]; exact ⟨trivial,hv⟩)
    rw [cornerOrbit_apply b 1 hv] at hf
    exact congrArg Prod.snd hf
  right_inv' := by
    intro z hz
    have hs := (cornerOrbit b).map_target hz
    rw [cornerOrbit_source] at hs
    have hf := (cornerOrbit b).right_inv hz
    rw [cornerOrbit_apply b _ hs.2] at hf
    exact congrArg Prod.fst hf
  open_source := cornerBox_open
  open_target := (cornerOrbit b).open_target.preimage
    (continuous_id.prodMk continuous_const)
  contMDiffOn_toFun := by
    have hh : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 2).prod (𝓡 1)) ∞
        (fun v : ℝ × ℝ => cornerOrbit b (1, v)) (rimBox 2) :=
      (cornerOrbit b).contMDiffOn_toFun.comp
        (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun v hv => by rw [cornerOrbit_source]; exact ⟨trivial,hv⟩)
    apply (contMDiff_fst.comp_contMDiffOn hh).congr
    intro v hv
    exact (congrArg Prod.fst (cornerOrbit_apply b 1 hv)).symm
  contMDiffOn_invFun :=
    contMDiff_snd.comp_contMDiffOn
      ((cornerOrbit b).symm.contMDiffOn_toFun.comp
        (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun z hz => hz))

theorem loopCornerChart_source (b : Bool) : (loopCornerChart b).source = rimBox 2 := rfl

theorem loopCornerChart_apply (b : Bool) (v : ℝ × ℝ) :
    loopCornerChart b v = loopRimOrbitBase b v := rfl

theorem loopCornerChart_disjoint :
    Disjoint (loopCornerChart false).target (loopCornerChart true).target := by
  apply Set.disjoint_left.mpr
  intro z hf ht
  have hd := standardLoopBallHandleCycle.rim_disjoint
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ false
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ true (by simp)
  exact Set.disjoint_left.mp hd hf.2 ht.2


theorem loopCornerChart_unitDisc (b : Bool) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ (loopCornerChart b).target) : ‖z‖ < 1 := hz.1

theorem loopRim_core_disjoint (b : Bool) :
    Disjoint (actualLoopRim b).target (range loopComplementVertex.map) := by
  apply Set.disjoint_left.mpr
  intro p hp hc
  have hq := (actualLoopRim b).map_target hp
  have hv : ((actualLoopRim b).symm p).2 ∈ rimBox 2 :=
    (standardLoopBallHandleCycle.rim_source
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).mp hq
  have he : p = modelSphere.{0} 1
      (cornerRadius ((actualLoopRim b).symm p).2 •
        planeOfCircle ((actualLoopRim b).symm p).1,
        cornerHeight b ((actualLoopRim b).symm p).2) :=
    ((actualLoopRim b).right_inv hp).symm.trans
      (cornerPoint_eq b ((actualLoopRim b).symm p).1 hv)
  have hh := cliffordHeight_modelSphere.{0} 1
    (p := (cornerRadius ((actualLoopRim b).symm p).2 •
      planeOfCircle ((actualLoopRim b).symm p).1,
      cornerHeight b ((actualLoopRim b).symm p).2))
    (cornerPoint_source ((actualLoopRim b).symm p).1 hv)
  rw [norm_smul, Real.norm_of_nonneg (cornerRadius_pos hv).le,
    cornerPlane_norm, mul_one] at hh
  rw [loopComplementVertex_range] at hc
  change 3 / 4 ≤ cliffordHeight p at hc
  rw [he, hh] at hc
  nlinarith [cornerRadius_pos hv, cornerRadius_bound hv]

end GC.GraphManifold.Assembly
