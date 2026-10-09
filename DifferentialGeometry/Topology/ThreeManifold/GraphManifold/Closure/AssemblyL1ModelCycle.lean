import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelPieces
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Chapter-14 assembly, item L1, group G3a: the pieces of the model cycle as maps into `S³`

The necks, balls and handles of the model cycle (`modelNeck`, `modelBall`, `modelHandle`) with
their charts (`modelBallChart`, `modelHandleChart`), and the fields of the cycle normal form that
follow from the formulas alone: smoothness, bijective differentials, injectivity, the cap and end
identities (`modelBall_cap`, `modelHandle_end`), the rounded union in the necks
(`modelNeck_mem_solidTorusSet_iff`) and the disjointness of the neck targets.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsM_ASML1d : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothM_ASML1d : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsM_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothM_ASML1d : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The charts of the closed 2-cell indexed as `ClosedCell (1 + 1)`. -/
local instance diskChartsSuccM_ASML1d :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-- The smooth structure of the closed 2-cell indexed as `ClosedCell (1 + 1)`. -/
local instance diskSmoothSuccM_ASML1d : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The charts of the closed 3-cell indexed as `ClosedCell (2 + 1)`. -/
local instance ballChartsSuccM_ASML1d :
    ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The charts of the closed 3-cell with model indexed as `2 + 1`. -/
local instance ballChartsMixM_ASML1d : ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

variable {len : ℕ} {ε : ℝ}

/-! ## The charts -/

/-- The neck `(k, b)` of the model cycle. -/
def modelNeck (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) (b : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3) ModelSpace SphereCarrier.{u} ∞ :=
  zoneChart.{u} hε hε' hlen (modelBase k) (neckFlip b).toHomeomorph
    (fun x => (neckFlip b).isLocalDiffeomorph x) (isOpen_modelNeckDomain ε) (neckFlip_mapsTo hε hε' b)

theorem modelNeck_source (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (b : Bool) : (modelNeck.{u} hlen hε hε' k b).source = neckDomain ε :=
  (zoneChart_spec.{u} hε hε' hlen (modelBase k) (neckFlip b).toHomeomorph
    (fun x => (neckFlip b).isLocalDiffeomorph x) (isOpen_modelNeckDomain ε)
    (neckFlip_mapsTo hε hε' b)).1

theorem modelNeck_target (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (b : Bool) : (modelNeck.{u} hlen hε hε' k b).target =
      (fun q => zoneSphere.{u} len ε (modelBase k) (neckFlip b q)) '' neckDomain ε :=
  (zoneChart_spec.{u} hε hε' hlen (modelBase k) (neckFlip b).toHomeomorph
    (fun x => (neckFlip b).isLocalDiffeomorph x) (isOpen_modelNeckDomain ε)
    (neckFlip_mapsTo hε hε' b)).2.1

theorem modelNeck_apply (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) (b : Bool)
    (q : ModelSpace) :
    modelNeck.{u} hlen hε hε' k b q = zoneSphere.{u} len ε (modelBase k) (neckFlip b q) :=
  congrFun (zoneChart_spec.{u} hε hε' hlen (modelBase k) (neckFlip b).toHomeomorph
    (fun x => (neckFlip b).isLocalDiffeomorph x) (isOpen_modelNeckDomain ε)
    (neckFlip_mapsTo hε hε' b)).2.2 q

/-- The handle chart `k` of the model cycle. -/
def modelHandleChart (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3) ModelSpace SphereCarrier.{u} ∞ :=
  zoneChart.{u} hε hε' hlen (modelBase k) modelId.toHomeomorph
    (fun x => modelId.isLocalDiffeomorph x) isOpen_zoneDomain (mapsTo_id _)

theorem modelHandleChart_source (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    (modelHandleChart.{u} hlen hε hε' k).source = zoneDomain :=
  (zoneChart_spec.{u} hε hε' hlen (modelBase k) modelId.toHomeomorph
    (fun x => modelId.isLocalDiffeomorph x) isOpen_zoneDomain (mapsTo_id _)).1

theorem modelHandleChart_apply (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (y : ModelSpace) : modelHandleChart.{u} hlen hε hε' k y = zoneSphere.{u} len ε (modelBase k) y :=
  congrFun (zoneChart_spec.{u} hε hε' hlen (modelBase k) modelId.toHomeomorph
    (fun x => modelId.isLocalDiffeomorph x) isOpen_zoneDomain (mapsTo_id _)).2.2 y

/-- The ball chart `k` of the model cycle. -/
def modelBallChart (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{u} ∞ :=
  ballChart'.{u} hε hε' hlen (modelBase k)

theorem modelBallChart_source (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    (modelBallChart.{u} hlen hε hε' k).source = ball 0 (6 / 5) :=
  (ballChart'_spec.{u} hε hε' hlen (modelBase k)).1

theorem modelBallChart_apply (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (x : EuclideanSpace ℝ (Fin 3)) :
    modelBallChart.{u} hlen hε hε' k x = ballSphere.{u} len ε (modelBase k) x :=
  congrFun (ballChart'_spec.{u} hε hε' hlen (modelBase k)).2.2 x

/-! ## The balls and the handles -/

/-- The ball `k` of the model cycle. -/
def modelBall (len : ℕ) (ε : ℝ) (k : Fin len) (x : ClosedCell 3) : SphereCarrier.{u} :=
  ballSphere.{u} len ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))

/-- The handle `k` of the model cycle. -/
def modelHandle (len : ℕ) (ε : ℝ) (k : Fin len) (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    SphereCarrier.{u} :=
  zoneSphere.{u} len ε (modelBase k) ((q.1 : ModelPlane), (q.2 : ℝ))

theorem closedCell_mem_ball (x : ClosedCell 3) :
    (x : EuclideanSpace ℝ (Fin 3)) ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (6 / 5) := by
  rw [mem_ball_zero_iff]
  have : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  linarith

theorem modelBall_smooth (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (modelBall.{u} len ε k) := by
  intro x
  set C := modelBallChart.{u} hlen hε hε' k
  have hx : (x : EuclideanSpace ℝ (Fin 3)) ∈ C.source := by
    rw [modelBallChart_source]
    exact closedCell_mem_ball x
  have hC := C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds hx)
  have hval := (DifferentialGeometry.Topology.Handle.closedCellInclusion_contMDiff 2).contMDiffAt
    (x := x)
  have h := hC.comp x hval
  have heq : (C ∘ fun v : ClosedCell 3 => (v : EuclideanSpace ℝ (Fin 3))) = modelBall.{u} len ε k := by
    funext v
    simp only [Function.comp_apply, modelBall, C, modelBallChart_apply]
  rw [heq] at h
  exact h

theorem modelBall_mfderiv (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (x : ClosedCell 3) : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (modelBall.{u} len ε k) x) := by
  set C := modelBallChart.{u} hlen hε hε' k
  have hx : (x : EuclideanSpace ℝ (Fin 3)) ∈ C.source := by
    rw [modelBallChart_source]
    exact closedCell_mem_ball x
  have hC := C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds hx)
  have hval := DifferentialGeometry.Topology.Handle.closedCellInclusion_contMDiff 2
  have heq : modelBall.{u} len ε k = C ∘ fun v : ClosedCell 3 => (v : EuclideanSpace ℝ (Fin 3)) := by
    funext v
    simp only [Function.comp_apply, modelBall, C, modelBallChart_apply]
  rw [heq, mfderiv_comp x (hC.mdifferentiableAt (by simp)) ((hval x).mdifferentiableAt (by simp))]
  have h1 := ((C.isLocalDiffeomorphAt _ _ _ hx).isInvertible_mfderiv (by simp)).bijective
  have h2 := DifferentialGeometry.Topology.Manifold.closedCell_inclusion_mfderiv_bijective 2 x
  exact h1.comp h2

theorem modelBall_injective (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    Injective (modelBall.{u} len ε k) := fun x x' h =>
  Subtype.ext (ballSphere_injOn hε hε' hlen (modelBase k) (closedCell_mem_ball x)
    (closedCell_mem_ball x') h)

/-- The inclusion of the handle model into the model space. -/
def handleInclusion (q : ClosedCell 2 × Icc (0 : ℝ) 1) : ModelSpace :=
  ((q.1 : ModelPlane), (q.2 : ℝ))

theorem handleInclusion_mem_zoneDomain (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    handleInclusion q ∈ zoneDomain := by
  have h1 : ‖(q.1 : ModelPlane)‖ ≤ 1 := q.1.2
  have h2 := q.2.2
  exact ⟨by simp only [handleInclusion]; linarith, by simp only [handleInclusion]; linarith [h2.1],
    by simp only [handleInclusion]; linarith [h2.2]⟩

theorem handleInclusion_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, ModelSpace) ∞ handleInclusion := by
  change ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, ModelPlane × ℝ) ∞ (Prod.map Subtype.val Subtype.val)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).contMDiff
      |>.prodMap (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

theorem handleInclusion_bijective (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, ModelSpace) handleInclusion q) := by
  change Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, ModelPlane × ℝ)
    (Prod.map Subtype.val Subtype.val) q)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hi :=
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).prodMap
      (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
    ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Prod.map Subtype.val Subtype.val) q
    (hi.isImmersion.isImmersionAt q) (by simp)

theorem modelHandle_eq (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    modelHandle.{u} len ε k = modelHandleChart.{u} hlen hε hε' k ∘ handleInclusion := by
  funext q
  simp only [Function.comp_apply, modelHandle, modelHandleChart_apply, handleInclusion]

theorem modelHandle_smooth (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (modelHandle.{u} len ε k) := by
  intro q
  set C := modelHandleChart.{u} hlen hε hε' k
  have hq : handleInclusion q ∈ C.source := by
    rw [modelHandleChart_source]
    exact handleInclusion_mem_zoneDomain q
  have hC := C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds hq)
  rw [modelHandle_eq hlen hε hε' k]
  exact hC.comp q (handleInclusion_smooth q)

theorem modelHandle_mfderiv (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) (modelHandle.{u} len ε k) q) := by
  set C := modelHandleChart.{u} hlen hε hε' k
  have hq : handleInclusion q ∈ C.source := by
    rw [modelHandleChart_source]
    exact handleInclusion_mem_zoneDomain q
  have hC := C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds hq)
  rw [modelHandle_eq hlen hε hε' k, mfderiv_comp q (hC.mdifferentiableAt (by simp))
    ((handleInclusion_smooth q).mdifferentiableAt (by simp))]
  have h1 := ((C.isLocalDiffeomorphAt _ _ _ hq).isInvertible_mfderiv (by simp)).bijective
  exact h1.comp (handleInclusion_bijective q)

theorem handleInclusion_injective : Injective handleInclusion := by
  rintro ⟨z, t⟩ ⟨z', t'⟩ h
  simp only [handleInclusion, Prod.mk.injEq] at h
  rw [Subtype.ext h.1, Subtype.ext h.2]

theorem modelHandle_injective (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) :
    Injective (modelHandle.{u} len ε k) := fun q q' h =>
  handleInclusion_injective (zoneSphere_injOn hε hε' hlen (modelBase k)
    (handleInclusion_mem_zoneDomain q) (handleInclusion_mem_zoneDomain q') h)

/-! ## Heights in `S³` -/

theorem modelSphere_eq_shift {len : ℕ} (hlen : 0 < len) {p p' : ModelSpace}
    (hp : ‖p.1‖ < 13 / 10) (hp' : ‖p'.1‖ < 13 / 10)
    (h : modelSphere.{u} len p = modelSphere.{u} len p') :
    p.1 = p'.1 ∧ ∃ m : ℤ, p'.2 = p.2 + 4 * len * m := by
  have h1 : ‖p.1‖ ^ 2 < 2 := by nlinarith [norm_nonneg p.1]
  have h2 : ‖p'.1‖ ^ 2 < 2 := by nlinarith [norm_nonneg p'.1]
  exact (modelSphere_eq_iff hlen h1 h2).mp h

theorem zoneChartMap_range (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {y : ModelSpace}
    (hy : y ∈ zoneDomain) :
    ‖(zoneChartMap ε c y).1‖ < 13 / 10 ∧ c + 3 / 10 < (zoneChartMap ε c y).2 ∧
      (zoneChartMap ε c y).2 < c + 37 / 10 := by
  have hU := zoneHeight_mem (norm_nonneg y.1) hy.1 hy.2.1 hy.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_zoneChartMap_fst hε hε' c hy]
    exact (zoneRadius_le hε hε' (norm_nonneg _) (by linarith [hy.1]) (by linarith [hU.1])
      (by linarith [hU.2])).trans_lt hy.1
  · rw [zoneChartMap_apply]
    simp only
    linarith [hU.1]
  · rw [zoneChartMap_apply]
    simp only
    linarith [hU.2]

theorem ballMap_range (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (x : ClosedCell 3) :
    ‖(ballMap ε c (x : EuclideanSpace ℝ (Fin 3))).1‖ ≤ 1 ∧
      c - 1 ≤ (ballMap ε c (x : EuclideanSpace ℝ (Fin 3))).2 ∧
      (ballMap ε c (x : EuclideanSpace ℝ (Fin 3))).2 ≤ c + 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  have hh := abs_le.mp ((abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3))).trans hx)
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_ballMap_fst hε hε']
    apply ballRadius_le_one hε hε' (norm_nonneg _)
    rw [norm_sq_ballCoord]
    nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin 3))]
  · rw [ballMap_snd]
    linarith
  · rw [ballMap_snd]
    linarith

theorem ballMap_add (ε c d : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ballMap ε (c + d) x = ((ballMap ε c x).1, (ballMap ε c x).2 + d) := by
  rw [ballMap_apply, ballMap_apply]
  simp only
  congr 1
  ring

theorem modelBase_finRotate {len : ℕ} (hlen : 0 < len) (k : Fin len) (x : ModelPlane) (v : ℝ) :
    modelSphere.{u} len (x, modelBase (finRotate len k) + v) =
      modelSphere.{u} len (x, modelBase k + 4 + v) := by
  obtain ⟨m, hm⟩ := finRotate_eq_add_one k
  have hm' : modelBase (finRotate len k) = modelBase k + 4 + 4 * len * m := by
    unfold modelBase
    have : (((finRotate len k : Fin len) : ℕ) : ℝ) = (k : ℕ) + 1 + len * m := by exact_mod_cast hm
    rw [this]
    ring
  rw [hm', show modelBase k + 4 + 4 * len * m + v = (modelBase k + 4 + v) + 4 * len * m by ring]
  exact modelSphere_add_period hlen (x, modelBase k + 4 + v) m

/-! ## The cap and end identities -/

theorem inner_capPole_false (x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x ((capPole false : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = -(ballCoord x).2 := by
  rw [ballCoord_snd, capPole]
  simp only [Bool.false_eq_true, ↓reduceIte, southPole_val]
  rw [inner_neg_right, real_inner_comm]
  rfl

theorem inner_capPole_true (x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x ((capPole true : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = (ballCoord x).2 := by
  rw [ballCoord_snd, real_inner_comm]
  rfl

theorem modelBall_cap (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) (b : Bool)
    (x : ClosedCell 3) (hx : x ∈ neckCapRegion ε b) :
    modelBall.{u} len ε (rimBall len k b) x =
      modelNeck.{u} hlen hε hε' k b (capMap b (x : EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨hR, hpole, hs⟩ := hx
  have hx1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  have hR' : 3 / 4 < ‖(x : EuclideanSpace ℝ (Fin 3))‖ := by linarith
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hR'
    linarith
  set ξ := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).1
  set h := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 with hh
  set R := ‖(x : EuclideanSpace ℝ (Fin 3))‖
  have hR2 : R ^ 2 = ‖ξ‖ ^ 2 + h ^ 2 := (norm_sq_ballCoord _).symm
  rw [modelNeck_apply]
  cases b
  · rw [inner_capPole_false] at hpole
    have hRh : 0 < R - h := by linarith
    have hcap := capMap_false_eq hx0 (by rw [← ballCoord_snd]; exact hRh.ne')
    have hsval : ‖(capMap false (x : EuclideanSpace ℝ (Fin 3))).1‖ = 2 * ‖ξ‖ / (R - h) := by
      rw [hcap, norm_smul, Real.norm_of_nonneg (by positivity)]
      ring
    have hcos := mul_capCos_south hR2 (norm_nonneg _) hRh
    have hq := (capCos_neck_bounds (s := 2 * ‖ξ‖ / (R - h)) (by positivity)
      (by rw [← hsval]; linarith)).1
    have hh4 : h ≤ -1 / 4 := by nlinarith
    rw [neckFlip_false, rimBall_false]
    unfold modelBall ballSphere zoneSphere
    rw [ballMap_eq_zoneChartMap_south hε hε' (modelBase k) hR' (by linarith) hh4
      (by rw [hsval]; rw [hsval] at hs; linarith)]
  · rw [inner_capPole_true] at hpole
    have hRh : 0 < R + h := by linarith
    have hcap := capMap_true_eq hx0 (by rw [← ballCoord_snd]; exact hRh.ne')
    have hsval : ‖(capMap true (x : EuclideanSpace ℝ (Fin 3))).1‖ = 2 * ‖ξ‖ / (R + h) := by
      rw [hcap, norm_smul, Real.norm_of_nonneg (by positivity)]
      ring
    have hR2' : R ^ 2 = ‖ξ‖ ^ 2 + (-h) ^ 2 := by rw [neg_sq]; exact hR2
    have hcos := mul_capCos_south hR2' (norm_nonneg _) (show 0 < R - -h by linarith)
    rw [sub_neg_eq_add, neg_neg] at hcos
    have hq := (capCos_neck_bounds (s := 2 * ‖ξ‖ / (R + h)) (by positivity)
      (by rw [← hsval]; linarith)).1
    have hh4 : 1 / 4 ≤ h := by nlinarith
    rw [neckFlip_true, rimBall_true]
    unfold modelBall ballSphere zoneSphere
    rw [← ballMap_eq_zoneChartMap_north hε hε' (modelBase k) hR' (by linarith) hh4
      (by rw [hsval]; rw [hsval] at hs; linarith)]
    rw [ballMap_apply, ballMap_apply]
    exact modelBase_finRotate hlen k _ _

theorem modelHandle_end (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len) (b : Bool)
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    modelHandle.{u} len ε k q = modelNeck.{u} hlen hε hε' k b (handleEnd b q) := by
  rw [modelNeck_apply]
  cases b
  · rfl
  · rw [neckFlip_true]
    simp only [handleEnd, endCoord, ↓reduceIte, sub_sub_cancel]
    rfl

/-! ## The rounded union in the necks -/

theorem modelNeck_fst_norm (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (b : Bool) {q : ModelSpace} (hq : q ∈ neckDomain ε) :
    ‖(zoneChartMap ε (modelBase k) (neckFlip b q)).1‖ = neckRadius ε ‖q.1‖ q.2 := by
  rw [zoneChartMap_neckFlip hε hε' _ b hq]
  exact norm_neckRatio_smul hε hε' hq.2

theorem modelNeck_mem_solidTorusSet_iff (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (k : Fin len) (b : Bool) {q : ModelSpace} (hq : q ∈ neckDomain ε) :
    modelNeck.{u} hlen hε hε' k b q ∈ solidTorusSet.{u} ↔ neckRounding ε q ≤ 0 := by
  have hz := (zoneChartMap_range hε hε' (modelBase k) (neckFlip_mapsTo hε hε' b hq)).1
  rw [modelNeck_apply, zoneSphere, modelSphere_mem_solidTorusSet_iff len
    (by nlinarith [norm_nonneg (zoneChartMap ε (modelBase k) (neckFlip b q)).1]),
    modelNeck_fst_norm hε hε' k b hq, neckRounding_nonpos_iff hε]

/-! ## Disjoint neck targets -/

/-- The height of the neck `(k, b)` above the base of the zone `k`. -/
theorem modelNeck_height (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (b : Bool) {q : ModelSpace}
    (hq : q ∈ neckDomain ε) :
    ∃ x : ℝ, (zoneChartMap ε c (neckFlip b q)).2 = c + x ∧
      (b = false → 8 / 25 < x ∧ x < 5 / 4) ∧ (b = true → 11 / 4 < x ∧ x < 92 / 25) := by
  have hm := neck_height_mem hε hε' hq
  rw [zoneChartMap_neckFlip hε hε' c b hq]
  cases b
  · exact ⟨(1 + q.2) * capCos ‖q.1‖, rfl, fun _ => hm, fun h => absurd h (by simp)⟩
  · refine ⟨4 - (1 + q.2) * capCos ‖q.1‖, by simp only [↓reduceIte]; ring,
      fun h => absurd h (by simp), fun _ => ⟨by linarith, by linarith⟩⟩

theorem modelNeck_disjoint (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (b : Bool) (k' : Fin len) (b' : Bool) (hne : (k, b) ≠ (k', b')) :
    Disjoint (modelNeck.{u} hlen hε hε' k b).target (modelNeck.{u} hlen hε hε' k' b').target := by
  rw [modelNeck_target, modelNeck_target, Set.disjoint_left]
  rintro p ⟨q, hq, rfl⟩ ⟨q', hq', hqq'⟩
  apply hne
  have hr := zoneChartMap_range hε hε' (modelBase k) (neckFlip_mapsTo hε hε' b hq)
  have hr' := zoneChartMap_range hε hε' (modelBase k') (neckFlip_mapsTo hε hε' b' hq')
  obtain ⟨-, m, hm⟩ := modelSphere_eq_shift hlen hr'.1 hr.1 hqq'
  obtain ⟨x, hx, hxf, hxt⟩ := modelNeck_height hε hε' (modelBase k) b hq
  obtain ⟨x', hx', hxf', hxt'⟩ := modelNeck_height hε hε' (modelBase k') b' hq'
  rw [hx, hx'] at hm
  have hxb : 8 / 25 < x ∧ x < 92 / 25 := by
    cases b
    · have := hxf rfl; constructor <;> linarith
    · have := hxt rfl; constructor <;> linarith
  have hxb' : 8 / 25 < x' ∧ x' < 92 / 25 := by
    cases b'
    · have := hxf' rfl; constructor <;> linarith
    · have := hxt' rfl; constructor <;> linarith
  unfold modelBase at hm
  have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ)) (b := ((k' : ℕ) : ℤ)) (m := m)
    (x := x) (y := x') (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
  have hkk : k = k' := fin_eq_of_int_eq hwin
  subst hkk
  have hm0 : m = 0 := by
    have : ((len : ℤ) * m) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst hm0
  have hxx : x = x' := by push_cast at hm; linarith
  subst hxx
  cases b <;> cases b'
  · rfl
  · have := hxf rfl; have := hxt' rfl; linarith
  · have := hxt rfl; have := hxf' rfl; linarith
  · rfl

end GC.GraphManifold.Assembly
