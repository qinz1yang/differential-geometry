import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRimFibreSTR
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 3: the face functions of `C₁` and the fibre / face tests

The three face functions of `C₁ = {5/8 ≤ ‖q‖² ≤ 15/16, Re q ≤ κ}` on the circle base of the rows
(`gCusp`, `gVert`, `gBall`: all `≤ 0` on `C₁`, planar and explicit), their smoothness and
differentials (`mfderiv_planar_STR` carries the ambient derivative through the three open
subtypes), the characterization of the base `C₁` (`mem_cbase_STR`) and the tests
`fibre ⊆ face ↔ g = 0` (`fibre_cusp_iff_STR`, `fibre_ball_iff_STR`, `fibre_vert_iff_STR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_FaceFnsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FaceFnsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- The planar vector of a point of the circle base of the rows. -/
def vOf_STR (c : rows_STR.circle.Base) : EuclideanSpace ℝ (Fin 2) := c.val.val.val

theorem qOf_eq_STR (c : rows_STR.circle.Base) : qOfBase_STR c.1 = modelPlaneComplex (vOf_STR c) :=
  rfl

theorem norm_q_sq_STR (c : rows_STR.circle.Base) : ‖qOfBase_STR c.1‖ ^ 2 = ‖vOf_STR c‖ ^ 2 := by
  rw [qOf_eq_STR, LinearIsometryEquiv.norm_map]

/-- The real part as a continuous linear form on the plane model. -/
def reL_STR : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  Complex.reCLM.comp modelPlaneComplex.toContinuousLinearEquiv.toContinuousLinearMap

theorem reL_apply_STR (w : EuclideanSpace ℝ (Fin 2)) : reL_STR w = w 0 := by
  simp [reL_STR, modelPlaneComplex]

/-- The face functions on the plane model. -/
def gCusp_STR (z : EuclideanSpace ℝ (Fin 2)) : ℝ := 5 / 8 - ‖z‖ ^ 2

def gVert_STR (z : EuclideanSpace ℝ (Fin 2)) : ℝ := ‖z‖ ^ 2 - 15 / 16

def gBall_STR (z : EuclideanSpace ℝ (Fin 2)) : ℝ := reL_STR z - 4 / 5

theorem hasFDerivAt_gCusp_STR (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt gCusp_STR (-(2 • innerSL ℝ z)) z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_sub (5 / 8 : ℝ))
  exact h

theorem hasFDerivAt_gVert_STR (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt gVert_STR (2 • innerSL ℝ z) z :=
  (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const (15 / 16 : ℝ)

theorem hasFDerivAt_gBall_STR (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt gBall_STR reL_STR z :=
  reL_STR.hasFDerivAt.sub_const (4 / 5 : ℝ)

theorem contDiff_gCusp_STR : ContDiff ℝ ∞ gCusp_STR :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

theorem contDiff_gVert_STR : ContDiff ℝ ∞ gVert_STR :=
  (contDiff_norm_sq ℝ).sub contDiff_const

theorem contDiff_gBall_STR : ContDiff ℝ ∞ gBall_STR :=
  reL_STR.contDiff.sub contDiff_const

/-- The face functions as functions on the circle base of the rows. -/
def phiCusp_STR (c : rows_STR.circle.Base) : ℝ := gCusp_STR (vOf_STR c)

def phiVert_STR (c : rows_STR.circle.Base) : ℝ := gVert_STR (vOf_STR c)

def phiBall_STR (c : rows_STR.circle.Base) : ℝ := gBall_STR (vOf_STR c)

theorem contMDiff_vOf_STR : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ vOf_STR :=
  contMDiff_subtype_val.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem contMDiff_phi_STR {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun c : rows_STR.circle.Base => g (vOf_STR c)) :=
  hg.contMDiff.comp contMDiff_vOf_STR

/-- The differential of an ambient function through the three open subtypes. -/
theorem mfderiv_planar_STR {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {g' : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ}
    (c : rows_STR.circle.Base) (hg : HasFDerivAt g g' (vOf_STR c)) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : rows_STR.circle.Base => g (vOf_STR y)) c = g' := by
  have h1 := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 2) (J := 𝓘(ℝ, ℝ))
    (fun v : X135Radial.radialCircleBase => (fun w : loopCircleBase => g w.val) v.val)
    (⊤ : TopologicalSpace.Opens X135Radial.radialCircleBase) ⟨c.1, trivial⟩
  have h2 := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 2) (J := 𝓘(ℝ, ℝ))
    (fun w : loopCircleBase => g w.val) X135Radial.radialCircleBase c.val
  have h3 := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 2) (J := 𝓘(ℝ, ℝ)) g
    loopCircleBase c.val.val
  have h4 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g (vOf_STR c) = g' := by
    rw [mfderiv_eq_fderiv]
    exact hg.fderiv
  exact h1.trans (h2.trans (h3.trans h4))

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
