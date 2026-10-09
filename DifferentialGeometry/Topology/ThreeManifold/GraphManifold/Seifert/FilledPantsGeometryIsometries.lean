import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsGeometry

/-!
# The isometries of the fold model used by the filled pants assembly

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §2).
In the log chart `(x, y, s) ↦ x + i eʸ` of `H² × ℝ` (`Seifert/PantsGeometry.lean`) the side
pairings, the cone screws and the fibre translations of the assembly are all of the form
`pairingDiffeo g t = mobiusLogMap g t`: a Möbius map `g ∈ GL₂⁺(ℝ)` in the base and a translation
by `t` in the fibre; they are isometries of `coordinateModelMetric .hyperbolicProduct`
(`pullbackMetric_pairingDiffeo`, from `mobiusLogMap_coordinateInner`) and compose by
`pairingDiffeo_trans`. The lift `(x, y, s) ↦ (-x, y, c - s)` of the wall-0 reflection is the
affine map `foldFlip c`, an involutive isometry (`pullbackMetric_foldFlip`). The other wall lifts
are `foldFlip` conjugated by Möbius maps and are introduced where they are used.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Geometry
open scoped Manifold ContDiff Topology

namespace GC.Seifert

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def pairingDiffeo (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (t : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := mobiusLogMap g t
  invFun := mobiusLogMap g⁻¹ (-t)
  left_inv p := by
    rw [mobiusLogMap_mobiusLogMap, inv_mul_cancel, add_neg_cancel, mobiusLogMap_one]
  right_inv p := by
    rw [mobiusLogMap_mobiusLogMap, mul_inv_cancel, neg_add_cancel, mobiusLogMap_one]
  contMDiff_toFun := (contDiff_mobiusLogMap hg t).contMDiff
  contMDiff_invFun := (contDiff_mobiusLogMap (by simpa using hg) (-t)).contMDiff

theorem pairingDiffeo_apply (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (t : ℝ)
    (p : ModelCoordinates) : pairingDiffeo g hg t p = mobiusLogMap g t p := rfl

theorem pairingDiffeo_trans (g h : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (hh : 0 < h.det.val)
    (s t : ℝ) (p : ModelCoordinates) :
    pairingDiffeo g hg s (pairingDiffeo h hh t p) =
      pairingDiffeo (g * h) (by rw [map_mul, Units.val_mul]; exact mul_pos hg hh) (t + s) p :=
  mobiusLogMap_mobiusLogMap g h s t p

theorem pullbackMetric_pairingDiffeo (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (t : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (pairingDiffeo g hg t) =
      coordinateModelMetric .hyperbolicProduct := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : ((pairingDiffeo g hg t : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates) :
      ModelCoordinates → ModelCoordinates) = mobiusLogMap g t := rfl
  rw [Diffeomorph.pullbackMetric_inner, hfun, mfderiv_eq_fderiv]
  exact (coordinateModelMetric_inner _ _ _ _).trans
    ((mobiusLogMap_coordinateInner hg t x v w).trans (coordinateModelMetric_inner _ _ _ _).symm)

def flipLinear : ModelCoordinates →ₗ[ℝ] ModelCoordinates where
  toFun p := !₂[-p 0, p 1, -p 2]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i
    fin_cases i <;> simp

def flipCLM : ModelCoordinates →L[ℝ] ModelCoordinates := LinearMap.toContinuousLinearMap flipLinear

theorem flipCLM_apply (p : ModelCoordinates) : flipCLM p = !₂[-p 0, p 1, -p 2] := rfl

def flipMap (c : ℝ) (p : ModelCoordinates) : ModelCoordinates := flipCLM p + !₂[0, 0, c]

theorem flipMap_zero (c : ℝ) (p : ModelCoordinates) : flipMap c p 0 = -p 0 := by
  simp [flipMap, flipCLM_apply]

theorem flipMap_one (c : ℝ) (p : ModelCoordinates) : flipMap c p 1 = p 1 := by
  simp [flipMap, flipCLM_apply]

theorem flipMap_two (c : ℝ) (p : ModelCoordinates) : flipMap c p 2 = c - p 2 := by
  simp [flipMap, flipCLM_apply]
  ring

theorem flipMap_flipMap (c : ℝ) (p : ModelCoordinates) : flipMap c (flipMap c p) = p := by
  ext i
  fin_cases i
  · simp [flipMap_zero]
  · simp [flipMap_one]
  · simp [flipMap_two]

theorem contDiff_flipMap (c : ℝ) : ContDiff ℝ ∞ (flipMap c) :=
  flipCLM.contDiff.add contDiff_const

theorem hasFDerivAt_flipMap (c : ℝ) (p : ModelCoordinates) :
    HasFDerivAt (flipMap c) flipCLM p :=
  flipCLM.hasFDerivAt.add_const _

def foldFlip (c : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := flipMap c
  invFun := flipMap c
  left_inv := flipMap_flipMap c
  right_inv := flipMap_flipMap c
  contMDiff_toFun := (contDiff_flipMap c).contMDiff
  contMDiff_invFun := (contDiff_flipMap c).contMDiff

theorem foldFlip_apply (c : ℝ) (p : ModelCoordinates) : foldFlip c p = flipMap c p := rfl

theorem coordinateInner_flipMap (c : ℝ) (p v w : ModelCoordinates) :
    coordinateInner .hyperbolicProduct (flipMap c p) (flipCLM v) (flipCLM w) =
      coordinateInner .hyperbolicProduct p v w := by
  simp only [coordinateInner, coordinateCoframe, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, flipMap_one,
    flipCLM_apply]
  simp

theorem pullbackMetric_foldFlip (c : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (foldFlip c) =
      coordinateModelMetric .hyperbolicProduct := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : ((foldFlip c : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates) :
      ModelCoordinates → ModelCoordinates) = flipMap c := rfl
  rw [Diffeomorph.pullbackMetric_inner, hfun, mfderiv_eq_fderiv, (hasFDerivAt_flipMap c x).fderiv]
  exact (coordinateModelMetric_inner _ _ _ _).trans
    ((coordinateInner_flipMap c x v w).trans (coordinateModelMetric_inner _ _ _ _).symm)

end GC.Seifert
