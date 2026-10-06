import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFibreTestsSTR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankKernel74

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 5: the labelled local faces of `C₁`

The three labels of the faces of `C₁` (`labCusp_STR`, `labVert_STR`, `labBall_STR`), the face
function `phiL_STR` of a label, and `local_faces_STR` (the FDC03 corner model): at a frontier point
exactly the active faces are used, with the other faces strictly negative on the neighbourhood.
The corner points (both `labVert_STR` and `labBall_STR` active) keep the explicit label set
`{labVert_STR, labBall_STR}` (`localFaces_corner_STR`); there the two differentials are independent
because `Im q ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_LocalFacesSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_LocalFacesSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## Labels and face functions -/

/-- The labels of the faces of the circle base of the rows. -/
abbrev Lab_STR : Type := CircleFaceLabel rows_STR.slimPieces.ResidualFace
  rows_STR.edge.EdgeBaseComponent

def labBall_STR : Lab_STR := .horizontal ballRes_STR

def labCusp_STR : Lab_STR := .horizontal cuspRes_STR

def labVert_STR : Lab_STR := .vertical cbaseComp_STR

/-- The face function of a label (the new slim ends do not exist, so their value is arbitrary). -/
def phiL_STR : Lab_STR → rows_STR.circle.Base → ℝ
  | .horizontal (.inl ⟨.inl _, _⟩) => phiBall_STR
  | .horizontal (.inl ⟨.inr _, _⟩) => phiCusp_STR
  | .horizontal (.inr _) => phiBall_STR
  | .vertical _ => phiVert_STR

theorem phiL_ball_STR : phiL_STR labBall_STR = phiBall_STR := rfl

theorem phiL_cusp_STR : phiL_STR labCusp_STR = phiCusp_STR := rfl

theorem phiL_vert_STR : phiL_STR labVert_STR = phiVert_STR := rfl

theorem lab_cases_STR (f : Lab_STR) : f = labBall_STR ∨ f = labCusp_STR ∨ f = labVert_STR := by
  cases f with
  | horizontal F =>
    rcases res_cases_STR F with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | vertical C =>
    right
    right
    have := actualComponent_eq_STR C
    subst this
    rfl

theorem contMDiff_phiL_STR (f : Lab_STR) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (phiL_STR f) := by
  rcases lab_cases_STR f with rfl | rfl | rfl
  · rw [phiL_ball_STR]
    exact contMDiff_phi_STR contDiff_gBall_STR
  · rw [phiL_cusp_STR]
    exact contMDiff_phi_STR contDiff_gCusp_STR
  · rw [phiL_vert_STR]
    exact contMDiff_phi_STR contDiff_gVert_STR

theorem fibre_iff_STR {f : Lab_STR} {c : rows_STR.circle.Base}
    (hc : c ∈ rows_STR.circle.cbase) :
    rows_STR.circle.fibre c ⊆ circleFaceSet rows_STR.slimPieces rows_STR.edge f ↔
      phiL_STR f c = 0 := by
  rcases lab_cases_STR f with rfl | rfl | rfl
  · rw [phiL_ball_STR]
    exact fibre_ball_iff_STR
  · rw [phiL_cusp_STR]
    exact fibre_cusp_iff_STR
  · rw [phiL_vert_STR]
    exact fibre_vert_iff_STR hc cbaseComp_STR

/-! ## The differentials -/

theorem norm_v_pos_STR (c : rows_STR.circle.Base) : (1 / 2 : ℝ) < ‖vOf_STR c‖ ^ 2 := c.val.property

theorem mfderiv_phiCusp_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiCusp_STR c = -(2 • innerSL ℝ (vOf_STR c)) :=
  mfderiv_planar_STR c (hasFDerivAt_gCusp_STR _)

theorem mfderiv_phiVert_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiVert_STR c = 2 • innerSL ℝ (vOf_STR c) :=
  mfderiv_planar_STR c (hasFDerivAt_gVert_STR _)

theorem mfderiv_phiBall_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiBall_STR c = reL_STR :=
  mfderiv_planar_STR c (hasFDerivAt_gBall_STR _)

theorem inner_two_STR (v w : EuclideanSpace ℝ (Fin 2)) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem eval2_STR (v w : EuclideanSpace ℝ (Fin 2)) :
    ((2 : ℕ) • innerSL ℝ v) w = 2 * (v 0 * w 0 + v 1 * w 1) := by
  rw [two_nsmul, add_apply, innerSL_apply_apply, inner_two_STR]
  ring

theorem mfderiv_phiCusp_ne_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiCusp_STR c ≠ 0 := by
  rw [mfderiv_phiCusp_STR]
  intro h
  have h1 : (-((2 : ℕ) • innerSL ℝ (vOf_STR c))) (vOf_STR c) =
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (vOf_STR c) := DFunLike.congr_fun h (vOf_STR c)
  rw [neg_apply, zero_apply, eval2_STR] at h1
  have := norm_v_pos_STR c
  have hn : ‖vOf_STR c‖ ^ 2 = vOf_STR c 0 * vOf_STR c 0 + vOf_STR c 1 * vOf_STR c 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_two_STR]
  nlinarith

theorem mfderiv_phiVert_ne_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiVert_STR c ≠ 0 := by
  rw [mfderiv_phiVert_STR]
  intro h
  have h1 : ((2 : ℕ) • innerSL ℝ (vOf_STR c)) (vOf_STR c) =
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (vOf_STR c) := DFunLike.congr_fun h (vOf_STR c)
  rw [zero_apply, eval2_STR] at h1
  have := norm_v_pos_STR c
  have hn : ‖vOf_STR c‖ ^ 2 = vOf_STR c 0 * vOf_STR c 0 + vOf_STR c 1 * vOf_STR c 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_two_STR]
  nlinarith

theorem mfderiv_phiBall_ne_STR (c : rows_STR.circle.Base) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phiBall_STR c ≠ 0 := by
  rw [mfderiv_phiBall_STR]
  intro h
  have h1 : reL_STR (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) :=
    DFunLike.congr_fun h _
  rw [reL_apply_STR, zero_apply] at h1
  simp at h1

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
