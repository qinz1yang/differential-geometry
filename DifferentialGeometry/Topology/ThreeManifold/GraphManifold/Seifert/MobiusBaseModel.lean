import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Elementary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances

/-!
# The model Möbius band base

Lane MD3, T5. The first `MobiusBase` of the tree, `mobiusBase`, built like `planarBase`. Its
surface `mobiusSurface` is the sublevel set `mobiusSet = {mobiusWidth ≤ 1}` of the width
`mobiusWidth [θ, y] = y²` in the lift `MobiusLift = ULift MobiusBand` of the open Möbius band of
`SaddleSlabModels.lean`, with the regular-sublevel atlas shifted by `shiftAtlas'` (`mobiusAtlas`;
the shift keeps every chart off `0`, so pieces can be immersed across their boundary). The
orientation double cover `mobiusBandCover (t, y) = [arg t, y]` of `Circle × ℝ` is smooth
(`contMDiff_mobiusCover`), and
`mobiusVec [θ, y] = y e^{iθ}` inverts it off the core (`mobiusBandCover_unitOf`). The collar
`mobiusCollar (e^{iθ}, s) = [θ, 1 - s / 8]` (`mobiusCollar_apply`) exhausts the boundary
`{y² = 1}` (`mobiusSet_boundary_eq`). The embedding `mobiusEmbed` into `ℝ³` is
`[θ, y] ↦ mobiusPoint (e^{iθ}) ((1 - y) / 2)` (`mobiusBase_embedding_apply`): it is injective
(`mobiusTriple_injOn`, through `mobiusVec` and `mobiusSq [θ, y] = e^{2iθ}`), an immersion
(`isImmersion_mobiusEmbed`, by the explicit differential `hasFDerivAt_mobiusTripleLift`), and its
range is `mobiusModel` (`range_mobiusEmbed_set`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

section Shift

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

def shiftAtlas' {K : Set M} (C : SmoothBoundaryAtlas I 2 K) : SmoothBoundaryAtlas I 2 K where
  ambientChart y := (C.ambientChart y).trans (SmoothBoundaryAtlas.affineDiffeomorph
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
    ((1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1)).toPartialDiffeomorph
  mem_source y := ⟨C.mem_source y, mem_univ _⟩
  mem_iff y z hz := by
    rw [C.mem_iff y z hz.1]
    change 0 ≤ C.ambientChart y z 0 ↔
      0 ≤ (C.ambientChart y z + (1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1 :
        EuclideanSpace ℝ (Fin 2)) 0
    simp

theorem shiftAtlas'_apply_self {K : Set M} (C : SmoothBoundaryAtlas I 2 K) (y : K) :
    (shiftAtlas' C).ambientChart y y.val 1 = 1 := by
  change (C.ambientChart y y.val + (1 - C.ambientChart y y.val 1) • EuclideanSpace.single 1 1 :
    EuclideanSpace ℝ (Fin 2)) 1 = 1
  simp

theorem shiftAtlas'_isBoundaryPoint_iff {K : Set M} (C : SmoothBoundaryAtlas I 2 K) (x : K) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (EuclideanSpace ℝ (Fin 2)) _ _ (EuclideanHalfSpace 2) _
      (𝓡∂ 2) K _ (shiftAtlas' C).toChartedSpace x ↔ C.ambientChart x x.val 0 = 0 := by
  rw [(shiftAtlas' C).isBoundaryPoint_iff]
  change (C.ambientChart x x.val + (1 - C.ambientChart x x.val 1) • EuclideanSpace.single 1 1 :
    EuclideanSpace ℝ (Fin 2)) 0 = 0 ↔ _
  simp

end Shift

section Width

def mobiusWidthLift (p : ℝ × ℝ) : ℝ := p.2 ^ 2

theorem mobiusWidthLift_smul (g : mobiusDeckGroup) (p : ℝ × ℝ) :
    mobiusWidthLift (g • p) = mobiusWidthLift p := by
  obtain ⟨n, rfl⟩ := mobiusZ_surjective g
  rw [mobiusZ_smul]
  simp only [mobiusWidthLift]
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num
  rw [mul_pow, hsq, one_mul]

def mobiusWidth : MobiusBand → ℝ :=
  Quotient.lift mobiusWidthLift fun a b hab => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg, mobiusWidthLift_smul]

theorem mobiusWidth_mk (p : ℝ × ℝ) : mobiusWidth (mobiusProj p) = p.2 ^ 2 := rfl

theorem contMDiff_mobiusWidth : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ mobiusWidth :=
  isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective
    (contDiff_snd.pow 2).contMDiff

theorem fderiv_mobiusWidthLift_eq_zero_iff (m : ℝ × ℝ) :
    fderiv ℝ mobiusWidthLift m = 0 ↔ m.2 = 0 := by
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) m :=
    hasFDerivAt_snd
  have hd : HasFDerivAt mobiusWidthLift ((2 * m.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) m := by
    have h := hs.pow 2
    refine h.congr_fderiv ?_
    have e : (2 • m.2 ^ (2 - 1) : ℝ) = 2 * m.2 := by simp [two_smul, two_mul]
    rw [e]
  rw [hd.fderiv]
  constructor
  · intro h
    have h2 : 2 * m.2 = 0 := by
      simpa using congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) h
    linarith
  · intro h
    rw [h, mul_zero, zero_smul]

theorem mfderiv_mobiusWidth_ne_zero {x : MobiusBand} (hx : mobiusWidth x = 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) mobiusWidth x ≠ 0 := by
  obtain ⟨m, rfl⟩ := mobiusProj_surjective x
  intro h
  have hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) mobiusWidth
      (mobiusProj m) := h
  rw [← isCriticalPointAt_comp_localDiffeomorph_iff (isLocalDiffeomorph_mobiusProj m)
    (contMDiff_mobiusWidth.mdifferentiableAt (by simp))] at hc
  have h2 : mobiusWidth ∘ mobiusProj = mobiusWidthLift := rfl
  rw [h2, DifferentialGeometry.Topology.Morse.IsCriticalPointAt, mfderiv_eq_fderiv] at hc
  have hc' : fderiv ℝ mobiusWidthLift m = 0 := hc
  rw [fderiv_mobiusWidthLift_eq_zero_iff] at hc'
  rw [mobiusWidth_mk, hc'] at hx
  norm_num at hx

end Width

section Cover

theorem mobiusProj_add_int_mul_two_pi (θ y : ℝ) (k : ℤ) :
    mobiusProj (θ + k * (2 * Real.pi), y) = mobiusProj (θ, y) := by
  have h := mobiusProj_smul (mobiusZ (2 * k)) (θ, y)
  rw [mobiusZ_smul] at h
  have h1 : ((-1 : ℝ) ^ (2 * k)) = 1 := by
    rw [zpow_mul]
    norm_num
  rw [h1, one_mul] at h
  have h2 : θ + ((2 * k : ℤ) : ℝ) * Real.pi = θ + k * (2 * Real.pi) := by
    push_cast
    ring
  rw [h2] at h
  exact h

theorem mobiusProj_add_pi (θ y : ℝ) : mobiusProj (θ + Real.pi, -y) = mobiusProj (θ, y) := by
  have h := mobiusProj_smul (mobiusZ 1) (θ, y)
  rw [mobiusZ_smul] at h
  simpa using h

def mobiusBandCover (p : Circle × ℝ) : MobiusBand := mobiusProj (Complex.arg p.1, p.2)

theorem mobiusProj_eq_of_exp_eq {θ θ' : ℝ} (h : Circle.exp θ = Circle.exp θ') (y : ℝ) :
    mobiusProj (θ, y) = mobiusProj (θ', y) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  rw [hm, mobiusProj_add_int_mul_two_pi]

theorem mobiusBandCover_exp (θ y : ℝ) : mobiusBandCover (Circle.exp θ, y) = mobiusProj (θ, y) := by
  apply mobiusProj_eq_of_exp_eq
  exact Circle.exp_arg _

theorem mobiusBandCover_eq_local (t₀ t : Circle) (y : ℝ) :
    mobiusBandCover (t, y) =
      mobiusProj (Complex.arg (t₀ : ℂ) + Complex.arg ((t * t₀⁻¹ : Circle) : ℂ), y) := by
  apply mobiusProj_eq_of_exp_eq
  rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg, Circle.exp_arg, mul_comm,
    inv_mul_cancel_right]

theorem contMDiffAt_arg_mul_inv' (w : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun z : Circle => Complex.arg ((z * w⁻¹ : Circle) : ℂ)) w := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have h1 : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => ((z * w⁻¹ : Circle) : ℂ)) w :=
    (hc.comp (contMDiff_mul_right (a := w⁻¹))).contMDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => Complex.arg z) ((w * w⁻¹ : Circle) : ℂ) := by
    rw [mul_inv_cancel, Circle.coe_one]
    have h3 : (fun z : ℂ => Complex.arg z) = fun z => (Complex.log z).im :=
      funext fun z => (Complex.log_im z).symm
    rw [h3]
    exact Complex.imCLM.contDiff.contDiffAt.comp _
      ((Complex.contDiffAt_log (by simp)).restrict_scalars ℝ)
  exact ContDiffAt.comp_contMDiffAt (x := w) (f := fun z : Circle => ((z * w⁻¹ : Circle) : ℂ))
    h2 h1

theorem contMDiff_mobiusCover :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusBandCover := by
  intro p
  have hproj : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusProj :=
    isLocalDiffeomorph_mobiusProj.contMDiff
  have hin : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : Circle × ℝ =>
        (Complex.arg (p.1 : ℂ) + Complex.arg ((q.1 * p.1⁻¹ : Circle) : ℂ), q.2)) p := by
    refine ContMDiffAt.prodMk_space ?_ contMDiffAt_snd
    exact contMDiffAt_const.add ((contMDiffAt_arg_mul_inv' p.1).comp p contMDiffAt_fst)
  have h := hproj.contMDiffAt.comp p hin
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  exact mobiusBandCover_eq_local p.1 q.1 q.2

end Cover

section Vec

theorem coe_circleExp_add_int_mul_pi (θ : ℝ) (n : ℤ) :
    ((Circle.exp (θ + n * Real.pi) : Circle) : ℂ) = (-1) ^ n * (Circle.exp θ : ℂ) := by
  rw [Circle.exp_add, Circle.coe_mul, mul_comm, Circle.coe_exp (n * Real.pi)]
  have h : ((n * Real.pi : ℝ) : ℂ) * Complex.I = n * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

def mobiusVecLift (p : ℝ × ℝ) : ℂ := p.2 • ((Circle.exp p.1 : Circle) : ℂ)

theorem mobiusVecLift_smul (g : mobiusDeckGroup) (p : ℝ × ℝ) :
    mobiusVecLift (g • p) = mobiusVecLift p := by
  obtain ⟨n, rfl⟩ := mobiusZ_surjective g
  rw [mobiusZ_smul]
  simp only [mobiusVecLift]
  rw [coe_circleExp_add_int_mul_pi, Complex.real_smul, Complex.real_smul]
  push_cast
  have h : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_zpow]
    norm_num
  calc (-1 : ℂ) ^ n * (p.2 : ℂ) * ((-1) ^ n * (Circle.exp p.1 : ℂ))
      = ((-1 : ℂ) ^ n * (-1) ^ n) * ((p.2 : ℂ) * (Circle.exp p.1 : ℂ)) := by ring
    _ = (p.2 : ℂ) * (Circle.exp p.1 : ℂ) := by rw [h, one_mul]

def mobiusVec : MobiusBand → ℂ :=
  Quotient.lift mobiusVecLift fun a b hab => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg, mobiusVecLift_smul]

theorem mobiusVec_mk (p : ℝ × ℝ) :
    mobiusVec (mobiusProj p) = p.2 • ((Circle.exp p.1 : Circle) : ℂ) := rfl

theorem contDiff_mobiusVecLift : ContDiff ℝ ∞ mobiusVecLift := by
  have h : mobiusVecLift = fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.exp (p.1 * Complex.I) := by
    funext p
    rw [mobiusVecLift, Complex.real_smul, Circle.coe_exp]
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp contDiff_snd).mul
    (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
      contDiff_const))

theorem contMDiff_mobiusVec : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞ mobiusVec :=
  isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective
    contDiff_mobiusVecLift.contMDiff

theorem mobiusVec_cover (t : Circle) (y : ℝ) :
    mobiusVec (mobiusBandCover (t, y)) = y • (t : ℂ) := by
  change (y : ℝ) • ((Circle.exp (Complex.arg (t : ℂ)) : Circle) : ℂ) = _
  rw [Circle.exp_arg]

theorem norm_mobiusVec_sq (x : MobiusBand) : ‖mobiusVec x‖ ^ 2 = mobiusWidth x := by
  obtain ⟨m, rfl⟩ := mobiusProj_surjective x
  rw [mobiusVec_mk, mobiusWidth_mk, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    sq_abs]

theorem mobiusVec_ne_zero_iff (x : MobiusBand) : mobiusVec x ≠ 0 ↔ mobiusWidth x ≠ 0 := by
  rw [← norm_mobiusVec_sq, ne_eq, ne_eq, pow_eq_zero_iff two_ne_zero, norm_eq_zero]

theorem mobiusBandCover_unitOf {x : MobiusBand} (hx : mobiusVec x ≠ 0) :
    mobiusBandCover (unitOf (mobiusVec x), ‖mobiusVec x‖) = x := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  rw [mobiusVec_mk] at hx ⊢
  have hy : y ≠ 0 := by
    intro h
    apply hx
    simp [h]
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have he : y • ((Circle.exp θ : Circle) : ℂ) =
        (-y) • ((Circle.exp (θ + Real.pi) : Circle) : ℂ) := by
      have h1 := coe_circleExp_add_int_mul_pi θ 1
      simp only [Int.cast_one, one_mul, zpow_one] at h1
      rw [h1, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [he, unitOf_smul (by linarith), norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith), mobiusBandCover_exp, mobiusProj_add_pi]
  · rw [unitOf_smul hpos, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
      abs_of_pos hpos, mobiusBandCover_exp]

theorem mobiusWidth_cover (t : Circle) (y : ℝ) : mobiusWidth (mobiusBandCover (t, y)) = y ^ 2 := rfl

end Vec

section Lift

abbrev MobiusLift : Type u := ULift.{u} MobiusBand

instance : ChartedSpace (ℝ × ℝ) MobiusLift.{u} := uliftChartedSpace _ _

instance : IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ MobiusLift.{u} := isManifold_ulift _ _

theorem contMDiff_mobiusLift_down :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (ULift.down : MobiusLift.{u} → MobiusBand) :=
  (uliftDiffeomorph 𝓘(ℝ, ℝ × ℝ) MobiusBand).symm.contMDiff

theorem contMDiff_mobiusLift_up :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (ULift.up : MobiusBand → MobiusLift.{u}) :=
  (uliftDiffeomorph 𝓘(ℝ, ℝ × ℝ) MobiusBand).contMDiff

def mobiusSet : Set MobiusLift.{u} := {w | mobiusWidth w.down ≤ 1}

theorem contMDiff_mobiusWidth_down :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun w : MobiusLift.{u} => mobiusWidth w.down) :=
  contMDiff_mobiusWidth.comp contMDiff_mobiusLift_down

theorem mobiusWidth_down_regular (w : MobiusLift.{u}) (hw : mobiusWidth w.down = 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (fun w : MobiusLift.{u} => mobiusWidth w.down) w ≠ 0 :=
  mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℝ × ℝ)) (s := ULift.up) (y := w.down)
    (contMDiff_mobiusWidth_down.mdifferentiableAt (by simp))
    (contMDiff_mobiusLift_up.mdifferentiableAt (by simp)) (mfderiv_mobiusWidth_ne_zero hw)

def mobiusSublevelAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℝ × ℝ) 2 mobiusSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℝ × ℝ) (n := 1) (by simp)
    contMDiff_mobiusWidth_down.{u} 1 mobiusWidth_down_regular

def mobiusAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℝ × ℝ) 2 mobiusSet.{u} :=
  shiftAtlas' mobiusSublevelAtlas

instance : ChartedSpace (EuclideanHalfSpace 2) mobiusSet.{u} := mobiusAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 2) ∞ mobiusSet.{u} := mobiusAtlas.isManifold

theorem mobiusSet_isBoundaryPoint_iff (x : mobiusSet.{u}) :
    (𝓡∂ 2).IsBoundaryPoint x ↔ mobiusWidth x.val.down = 1 :=
  (shiftAtlas'_isBoundaryPoint_iff mobiusSublevelAtlas x).trans
    (SmoothBoundaryAtlas.regularSublevel_ambientChart_eq_zero_iff 𝓘(ℝ, ℝ × ℝ) (n := 1)
      (by simp) contMDiff_mobiusWidth_down 1 mobiusWidth_down_regular x)

theorem mobiusSet_eq_image : mobiusSet.{u} =
    (fun p : ℝ × ℝ => (ULift.up (mobiusProj p) : MobiusLift.{u})) ''
      (Icc 0 Real.pi ×ˢ Icc (-1) 1) := by
  ext w
  constructor
  · intro hw
    obtain ⟨m, hm⟩ := mobiusProj_surjective w.down
    obtain ⟨n, hn⟩ := exists_rep_Ico m
    refine ⟨mobiusZ n • m, ⟨⟨hn.1, hn.2.le⟩, ?_⟩, ?_⟩
    · have h1 : mobiusWidth (mobiusProj (mobiusZ n • m)) ≤ 1 := by
        rw [mobiusProj_smul, hm]
        exact hw
      rw [mobiusWidth_mk, sq_le_one_iff_abs_le_one, abs_le] at h1
      exact h1
    · change ULift.up (mobiusProj (mobiusZ n • m)) = w
      rw [mobiusProj_smul, hm]
  · rintro ⟨p, ⟨-, hp⟩, rfl⟩
    change mobiusWidth (mobiusProj p) ≤ 1
    rw [mobiusWidth_mk]
    nlinarith [hp.1, hp.2]

theorem isCompact_mobiusSet : IsCompact mobiusSet.{u} := by
  rw [mobiusSet_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image
    (continuous_uliftUp.comp continuous_mobiusProj)

theorem isConnected_mobiusSet : IsConnected mobiusSet.{u} := by
  rw [mobiusSet_eq_image]
  exact (isConnected_Icc Real.pi_pos.le |>.prod (isConnected_Icc (by norm_num))).image _
    (continuous_uliftUp.comp continuous_mobiusProj).continuousOn

instance : CompactSpace mobiusSet.{u} := isCompact_iff_compactSpace.mp isCompact_mobiusSet

instance : SecondCountableTopology mobiusSet.{u} :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace 2) mobiusSet.{u}

def mobiusSurface : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := mobiusSet.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 2) mobiusSet.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 2) ∞ mobiusSet.{u})
  connected := isConnected_iff_connectedSpace.mp isConnected_mobiusSet

end Lift

section Collar

theorem halfSpaceOneLift_apply_zero (t : ℝ) :
    (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift t).val 0 = max t 0 := rfl

theorem halfSpaceOneLift_val_zero' (h : EuclideanHalfSpace 1) :
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change max (h.val 0) 0 = h.val 0
  exact max_eq_left h.2

theorem halfPoint_apply_zero (s : ℝ) (hs : 0 ≤ s) : (halfPoint s hs).val 0 = s := rfl

def mobiusCollarFun (q : Circle × EuclideanHalfSpace 1) : mobiusSet.{u} :=
  ⟨ULift.up (mobiusBandCover (q.1, 1 - min (q.2.val 0) 1 / 8)), by
    change mobiusWidth (mobiusBandCover _) ≤ 1
    rw [mobiusWidth_cover]
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    have h1 : min (q.2.val 0) 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ min (q.2.val 0) 1 := le_min h0 zero_le_one
    nlinarith⟩

def mobiusCollarInv (w : mobiusSet.{u}) : Circle × EuclideanHalfSpace 1 :=
  (unitOf (mobiusVec w.val.down),
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (8 * (1 - ‖mobiusVec w.val.down‖)))

theorem norm_mobiusVec_le_one (w : mobiusSet.{u}) : ‖mobiusVec w.val.down‖ ≤ 1 := by
  have h : ‖mobiusVec w.val.down‖ ^ 2 ≤ 1 := by
    rw [norm_mobiusVec_sq]
    exact w.2
  nlinarith [norm_nonneg (mobiusVec w.val.down)]

theorem seven_eighths_lt_norm {w : mobiusSet.{u}} (hw : 49 / 64 < mobiusWidth w.val.down) :
    7 / 8 < ‖mobiusVec w.val.down‖ := by
  rw [← norm_mobiusVec_sq] at hw
  nlinarith [norm_nonneg (mobiusVec w.val.down)]

theorem mobiusCollarFun_val {q : Circle × EuclideanHalfSpace 1} (hq : q ∈ circleCollarSource) :
    (mobiusCollarFun.{u} q).val.down = mobiusBandCover (q.1, 1 - q.2.val 0 / 8) := by
  have h : min (q.2.val 0) 1 = q.2.val 0 := min_eq_left (le_of_lt hq)
  change mobiusBandCover (q.1, 1 - min (q.2.val 0) 1 / 8) = _
  rw [h]

def mobiusCollar : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
    mobiusSet.{u} ∞ where
  toFun := mobiusCollarFun
  invFun := mobiusCollarInv
  source := circleCollarSource
  target := {w | 49 / 64 < mobiusWidth w.val.down}
  map_source' q hq := by
    change 49 / 64 < mobiusWidth (mobiusCollarFun.{u} q).val.down
    rw [mobiusCollarFun_val hq, mobiusWidth_cover]
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    have h1 : q.2.val 0 < 1 := hq
    nlinarith
  map_target' w hw := by
    change max (8 * (1 - ‖mobiusVec w.val.down‖)) 0 < 1
    have := seven_eighths_lt_norm hw
    refine max_lt ?_ one_pos
    linarith
  left_inv' q hq := by
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    have h1 : q.2.val 0 < 1 := hq
    have hy : 0 < 1 - q.2.val 0 / 8 := by linarith
    change (unitOf (mobiusVec (mobiusCollarFun.{u} q).val.down),
      DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
        (8 * (1 - ‖mobiusVec (mobiusCollarFun.{u} q).val.down‖))) = q
    rw [mobiusCollarFun_val hq, mobiusVec_cover, unitOf_smul hy, norm_smul, Circle.norm_coe,
      mul_one, Real.norm_eq_abs, abs_of_pos hy]
    have he : 8 * (1 - (1 - q.2.val 0 / 8)) = q.2.val 0 := by ring
    rw [he, halfSpaceOneLift_val_zero']
  right_inv' w hw := by
    have hn := seven_eighths_lt_norm hw
    have hle := norm_mobiusVec_le_one w
    have hne : mobiusVec w.val.down ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      norm_num at hn
    apply Subtype.ext
    apply ULift.ext
    change mobiusBandCover (unitOf (mobiusVec w.val.down),
      1 - min (max (8 * (1 - ‖mobiusVec w.val.down‖)) 0) 1 / 8) = w.val.down
    have h1 : max (8 * (1 - ‖mobiusVec w.val.down‖)) 0 = 8 * (1 - ‖mobiusVec w.val.down‖) :=
      max_eq_left (by linarith)
    have h2 : min (8 * (1 - ‖mobiusVec w.val.down‖)) 1 = 8 * (1 - ‖mobiusVec w.val.down‖) :=
      min_eq_left (by linarith)
    rw [h1, h2]
    have h3 : 1 - 8 * (1 - ‖mobiusVec w.val.down‖) / 8 = ‖mobiusVec w.val.down‖ := by ring
    rw [h3]
    exact mobiusBandCover_unitOf hne
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_lt continuous_const
    (contMDiff_mobiusWidth_down.continuous.comp continuous_subtype_val)
  contMDiffOn_toFun := by
    refine (mobiusAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
    have hg : ContMDiff circleCollarModel ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : Circle × EuclideanHalfSpace 1 => (q.1, 1 - q.2.val 0 / 8)) :=
      contMDiff_fst.prodMk ((contMDiff_const.sub
        (DifferentialGeometry.Topology.Manifold.contMDiff_halfSpaceOneCoordinate.div_const
          8)).comp contMDiff_snd)
    have h := (contMDiff_mobiusLift_up.comp (contMDiff_mobiusCover.comp hg)).contMDiffOn
      (s := circleCollarSource)
    refine h.congr fun q hq => ?_
    change ULift.up (mobiusCollarFun.{u} q).val.down = _
    rw [mobiusCollarFun_val hq]
    rfl
  contMDiffOn_invFun := by
    have hv : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun w : mobiusSet.{u} => mobiusVec w.val.down) :=
      contMDiff_mobiusVec.comp (contMDiff_mobiusLift_down.comp mobiusAtlas.contMDiff_subtype_val)
    have hne : ∀ w ∈ ({w | 49 / 64 < mobiusWidth w.val.down} : Set mobiusSet.{u}),
        mobiusVec w.val.down ≠ 0 := by
      intro w hw h
      have hn := seven_eighths_lt_norm hw
      rw [h, norm_zero] at hn
      norm_num at hn
    have h1 : ContMDiffOn (𝓡∂ 2) (𝓡 1) ∞ (fun w : mobiusSet.{u} => unitOf (mobiusVec w.val.down))
        {w | 49 / 64 < mobiusWidth w.val.down} :=
      contMDiffOn_unitOf.comp hv.contMDiffOn hne
    have hnorm : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
        (fun w : mobiusSet.{u} => ‖mobiusVec w.val.down‖)
        {w | 49 / 64 < mobiusWidth w.val.down} := by
      intro w hw
      exact ((contDiffAt_norm ℝ (hne w hw)).contMDiffAt.comp w hv.contMDiffAt).contMDiffWithinAt
    have h2 : ContMDiffOn (𝓡∂ 2) (𝓡∂ 1) ∞ (fun w : mobiusSet.{u} =>
        DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (8 * (1 - ‖mobiusVec w.val.down‖))) {w | 49 / 64 < mobiusWidth w.val.down} :=
      DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.comp
        ((contMDiff_const.mul (contMDiff_const.sub contMDiff_id)).comp_contMDiffOn hnorm)
        fun w _ => by
          have := norm_mobiusVec_le_one w
          change (0 : ℝ) ≤ 8 * (1 - ‖mobiusVec w.val.down‖)
          linarith
    exact h1.prodMk h2

theorem mobiusCollar_source : mobiusCollar.{u}.source = circleCollarSource := rfl

theorem mobiusCollar_apply (θ s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    (mobiusCollar.{u} (Circle.exp θ, halfPoint s hs)).val.down = mobiusProj (θ, 1 - s / 8) := by
  change (mobiusCollarFun.{u} (Circle.exp θ, halfPoint s hs)).val.down = _
  rw [mobiusCollarFun_val (show (Circle.exp θ, halfPoint s hs) ∈ circleCollarSource from hs1)]
  exact mobiusBandCover_exp θ _

theorem mobiusCollar_zero (t : Circle) :
    (mobiusCollar.{u} (t, halfZero)).val.down = mobiusBandCover (t, 1) := by
  change (mobiusCollarFun.{u} (t, halfZero)).val.down = _
  rw [mobiusCollarFun_val (show (t, halfZero) ∈ circleCollarSource from
    show (0 : ℝ) < 1 by norm_num)]
  norm_num [halfZero, halfPoint_apply_zero]

theorem mobiusSet_boundary_eq : (𝓡∂ 2).boundary mobiusSet.{u} =
    range fun t => mobiusCollar.{u} (t, halfZero) := by
  ext w
  change (𝓡∂ 2).IsBoundaryPoint w ↔ _
  rw [mobiusSet_isBoundaryPoint_iff]
  constructor
  · intro hw
    have hn : ‖mobiusVec w.val.down‖ = 1 := by
      have h := norm_mobiusVec_sq w.val.down
      rw [hw] at h
      nlinarith [norm_nonneg (mobiusVec w.val.down)]
    have hne : mobiusVec w.val.down ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      norm_num at hn
    refine ⟨unitOf (mobiusVec w.val.down), Subtype.ext (ULift.ext ?_)⟩
    change (mobiusCollar.{u} (unitOf (mobiusVec w.val.down), halfZero)).val.down = w.val.down
    rw [mobiusCollar_zero, ← hn]
    exact mobiusBandCover_unitOf hne
  · rintro ⟨t, rfl⟩
    rw [mobiusCollar_zero, mobiusWidth_cover]
    norm_num

end Collar

section Embedding

def mobiusSqLift (p : ℝ × ℝ) : ℂ := ((Circle.exp (2 * p.1) : Circle) : ℂ)

theorem mobiusSqLift_smul (g : mobiusDeckGroup) (p : ℝ × ℝ) :
    mobiusSqLift (g • p) = mobiusSqLift p := by
  obtain ⟨n, rfl⟩ := mobiusZ_surjective g
  rw [mobiusZ_smul]
  simp only [mobiusSqLift]
  have h : 2 * (p.1 + n * Real.pi) = 2 * p.1 + n * (2 * Real.pi) := by ring
  rw [h, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

def mobiusSq : MobiusBand → ℂ :=
  Quotient.lift mobiusSqLift fun a b hab => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg, mobiusSqLift_smul]

theorem mobiusSq_mk (p : ℝ × ℝ) :
    mobiusSq (mobiusProj p) = ((Circle.exp (2 * p.1) : Circle) : ℂ) := rfl

theorem contMDiff_mobiusSq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞ mobiusSq := by
  refine isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective ?_
  have h : mobiusSq ∘ mobiusProj = fun p : ℝ × ℝ => Complex.exp ((2 * p.1 : ℝ) * Complex.I) := by
    funext p
    rfl
  rw [h]
  exact (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_fst)).mul contDiff_const)).contMDiff

theorem circleExp_re (θ : ℝ) : ((Circle.exp θ : Circle) : ℂ).re = Real.cos θ := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

theorem circleExp_im (θ : ℝ) : ((Circle.exp θ : Circle) : ℂ).im = Real.sin θ := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

def mobiusTripleLift (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((2 - p.2 * Real.cos p.1) * Real.cos (2 * p.1), (2 - p.2 * Real.cos p.1) * Real.sin (2 * p.1),
    -(p.2 * Real.sin p.1))

def mobiusTriple (x : MobiusBand) : ℝ × ℝ × ℝ :=
  ((2 - (mobiusVec x).re) * (mobiusSq x).re, (2 - (mobiusVec x).re) * (mobiusSq x).im,
    -(mobiusVec x).im)

theorem mobiusVec_mk_re (p : ℝ × ℝ) : (mobiusVec (mobiusProj p)).re = p.2 * Real.cos p.1 := by
  rw [mobiusVec_mk, Complex.real_smul, Complex.re_ofReal_mul, circleExp_re]

theorem mobiusVec_mk_im (p : ℝ × ℝ) : (mobiusVec (mobiusProj p)).im = p.2 * Real.sin p.1 := by
  rw [mobiusVec_mk, Complex.real_smul, Complex.im_ofReal_mul, circleExp_im]

theorem mobiusTriple_comp : mobiusTriple ∘ mobiusProj = mobiusTripleLift := by
  funext p
  change ((2 - (mobiusVec (mobiusProj p)).re) * (mobiusSq (mobiusProj p)).re,
    (2 - (mobiusVec (mobiusProj p)).re) * (mobiusSq (mobiusProj p)).im,
    -(mobiusVec (mobiusProj p)).im) = _
  rw [mobiusVec_mk_re, mobiusVec_mk_im, mobiusSq_mk, circleExp_re, circleExp_im]
  rfl

theorem contDiff_mobiusTripleLift : ContDiff ℝ ∞ mobiusTripleLift := by
  unfold mobiusTripleLift
  fun_prop

theorem contMDiff_mobiusTriple : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ mobiusTriple := by
  refine isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective ?_
  rw [mobiusTriple_comp]
  exact contDiff_mobiusTripleLift.contMDiff

theorem hasFDerivAt_mobiusTripleLift (p : ℝ × ℝ) :
    HasFDerivAt mobiusTripleLift
      (((p.2 * Real.sin p.1 * Real.cos (2 * p.1) -
          2 * (2 - p.2 * Real.cos p.1) * Real.sin (2 * p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(Real.cos p.1 * Real.cos (2 * p.1))) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (((p.2 * Real.sin p.1 * Real.sin (2 * p.1) +
          2 * (2 - p.2 * Real.cos p.1) * Real.cos (2 * p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(Real.cos p.1 * Real.sin (2 * p.1))) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((-(p.2 * Real.cos p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-Real.sin p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ))) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hc := (Real.hasDerivAt_cos p.1).comp_hasFDerivAt p hf
  have hsn := (Real.hasDerivAt_sin p.1).comp_hasFDerivAt p hf
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => 2 * q.1) ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hf.const_mul 2
  have hc2 := (Real.hasDerivAt_cos (2 * p.1)).comp_hasFDerivAt p h2
  have hs2 := (Real.hasDerivAt_sin (2 * p.1)).comp_hasFDerivAt p h2
  have hA := (hs.mul hc).const_sub 2
  refine ((hA.mul hc2).prodMk ((hA.mul hs2).prodMk (hs.mul hsn).neg)).congr_fderiv ?_
  ext <;> simp <;> ring

theorem injective_fderiv_mobiusTripleLift {p : ℝ × ℝ} (hp : |p.2| < 2) :
    Injective (fderiv ℝ mobiusTripleLift p) := by
  rw [(hasFDerivAt_mobiusTripleLift p).fderiv]
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) hv
  have h3 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) hv
  simp only [ContinuousLinearMap.prod_apply, FunLike.coe_add, Pi.add_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at h1 h2 h3
  set c := Real.cos p.1
  set s := Real.sin p.1
  set C := Real.cos (2 * p.1)
  set S := Real.sin (2 * p.1)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq p.1
  have hCS : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * p.1)
  have hA : 0 < 2 - p.2 * c := by
    have hc1 : |c| ≤ 1 := Real.abs_cos_le_one p.1
    have : |p.2 * c| < 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg p.2, abs_nonneg c]
    linarith [le_abs_self (p.2 * c)]
  have ha : v.1 = 0 := by
    have key : 2 * (2 - p.2 * c) * v.1 = 0 := by
      linear_combination (-S) * h1 + C * h2 - 2 * (2 - p.2 * c) * v.1 * hCS
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact h
  rw [ha] at h1 h2 h3
  have hb : v.2 = 0 := by
    have k1 : c * v.2 = 0 := by linear_combination (-C) * h1 + (-S) * h2 - c * v.2 * hCS
    have k2 : s * v.2 = 0 := by linear_combination -h3
    have k3 : v.2 = 0 := by
      have : v.2 * (s ^ 2 + c ^ 2) = 0 := by linear_combination s * k2 + c * k1
      rw [hcs, mul_one] at this
      exact this
    exact k3
  exact Prod.ext ha hb

end Embedding

section Base

def euclidThree : (ℝ × ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => !₂[p.1, p.2.1, p.2.2]
      invFun := fun x => (x 0, x 1, x 2)
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp
      left_inv := fun p => by simp
      right_inv := fun x => by ext i; fin_cases i <;> simp }

theorem euclidThree_apply (p : ℝ × ℝ × ℝ) : euclidThree p = !₂[p.1, p.2.1, p.2.2] := rfl

def mobiusEmbed (x : MobiusBand) : EuclideanSpace ℝ (Fin 3) := euclidThree (mobiusTriple x)

theorem contMDiff_mobiusEmbed :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ mobiusEmbed :=
  euclidThree.contDiff.contMDiff.comp contMDiff_mobiusTriple

theorem circleExp_sq (θ : ℝ) :
    ((Circle.exp θ : Circle) : ℂ) ^ 2 = ((Circle.exp (2 * θ) : Circle) : ℂ) := by
  rw [two_mul, Circle.exp_add, Circle.coe_mul, sq]

theorem mobiusEmbed_mk (θ y : ℝ) (hy : y ^ 2 ≤ 1) :
    mobiusEmbed (mobiusProj (θ, y)) =
      mobiusPoint (Circle.exp θ) (Set.projIcc 0 1 zero_le_one ((1 - y) / 2)) := by
  have hy' := (sq_le_one_iff_abs_le_one y).mp hy
  rw [abs_le] at hy'
  have hm : (1 - y) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Set.projIcc_of_mem _ hm]
  have h1 := congrFun mobiusTriple_comp (θ, y)
  simp only [Function.comp_apply] at h1
  rw [mobiusEmbed, h1, euclidThree_apply, mobiusPoint, circleExp_sq, circleExp_re, circleExp_re,
    circleExp_im, circleExp_im]
  simp only [mobiusTripleLift]
  ext i
  fin_cases i <;> simp [-mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem mobiusVec_mobiusSq_injective {x x' : MobiusBand} (hv : mobiusVec x = mobiusVec x')
    (hs : mobiusSq x = mobiusSq x') : x = x' := by
  by_cases h0 : mobiusVec x = 0
  · obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
    obtain ⟨⟨θ', y'⟩, rfl⟩ := mobiusProj_surjective x'
    have hy : y = 0 := by
      have h := norm_mobiusVec_sq (mobiusProj (θ, y))
      rw [h0, norm_zero, mobiusWidth_mk] at h
      nlinarith
    have hy' : y' = 0 := by
      have h := norm_mobiusVec_sq (mobiusProj (θ', y'))
      rw [← hv, h0, norm_zero, mobiusWidth_mk] at h
      nlinarith
    rw [mobiusSq_mk, mobiusSq_mk] at hs
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.ext hs)
    have hθ : θ = θ' + m * Real.pi := by linarith
    subst hy hy'
    rw [hθ]
    have h := mobiusProj_smul (mobiusZ m) (θ', 0)
    rw [mobiusZ_smul, mul_zero] at h
    exact h
  · have h0' : mobiusVec x' ≠ 0 := hv ▸ h0
    rw [← mobiusBandCover_unitOf h0, ← mobiusBandCover_unitOf h0', hv]

theorem mobiusTriple_injOn {x x' : MobiusBand} (hx : mobiusWidth x ≤ 1) (hx' : mobiusWidth x' ≤ 1)
    (h : mobiusTriple x = mobiusTriple x') : x = x' := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  obtain ⟨⟨θ', y'⟩, rfl⟩ := mobiusProj_surjective x'
  rw [mobiusWidth_mk] at hx hx'
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) h
  have e3 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) h
  simp only [mobiusTriple, mobiusVec_mk_re, mobiusVec_mk_im, mobiusSq_mk, circleExp_re,
    circleExp_im] at e1 e2 e3
  have hc := Real.abs_cos_le_one θ
  have hc' := Real.abs_cos_le_one θ'
  have hy := (sq_le_one_iff_abs_le_one y).mp hx
  have hy' := (sq_le_one_iff_abs_le_one y').mp hx'
  have hA : 0 < 2 - y * Real.cos θ := by
    have : |y * Real.cos θ| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg y, abs_nonneg (Real.cos θ)]
    linarith [le_abs_self (y * Real.cos θ)]
  have hA' : 0 < 2 - y' * Real.cos θ' := by
    have : |y' * Real.cos θ'| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg y', abs_nonneg (Real.cos θ')]
    linarith [le_abs_self (y' * Real.cos θ')]
  have hS := Real.sin_sq_add_cos_sq (2 * θ)
  have hS' := Real.sin_sq_add_cos_sq (2 * θ')
  have hAA : (2 - y * Real.cos θ) ^ 2 = (2 - y' * Real.cos θ') ^ 2 := by
    have := congrArg (· ^ 2) e1
    have := congrArg (· ^ 2) e2
    nlinarith
  have hAe : 2 - y * Real.cos θ = 2 - y' * Real.cos θ' := by
    nlinarith [sq_nonneg (2 - y * Real.cos θ - (2 - y' * Real.cos θ'))]
  have hre : y * Real.cos θ = y' * Real.cos θ' := by linarith
  rw [hAe] at e1 e2
  have hC : Real.cos (2 * θ) = Real.cos (2 * θ') := mul_left_cancel₀ hA'.ne' e1
  have hSn : Real.sin (2 * θ) = Real.sin (2 * θ') := mul_left_cancel₀ hA'.ne' e2
  apply mobiusVec_mobiusSq_injective
  · apply Complex.ext
    · rw [mobiusVec_mk_re, mobiusVec_mk_re]
      exact hre
    · rw [mobiusVec_mk_im, mobiusVec_mk_im]
      linarith
  · rw [mobiusSq_mk, mobiusSq_mk]
    apply Complex.ext
    · rw [circleExp_re, circleExp_re]
      exact hC
    · rw [circleExp_im, circleExp_im]
      exact hSn

theorem injective_mfderiv_of_comp_localDiffeomorph {E F G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {H H' H'' : Type} [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace H''] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {K : ModelWithCorners ℝ G H''} {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
    {φ : M → N} {g : N → P} {x : M} (hφ : IsLocalDiffeomorphAt I J ∞ φ x)
    (hg : MDifferentiableAt J K g (φ x)) (h : Injective (mfderiv I K (g ∘ φ) x)) :
    Injective (mfderiv J K g (φ x)) := by
  rw [mfderiv_comp x hg (hφ.mdifferentiableAt (by simp))] at h
  set L := hφ.mfderivToContinuousLinearEquiv (by simp)
  have hL : mfderiv I J φ x = (L : TangentSpace I x →L[ℝ] TangentSpace J (φ x)) := rfl
  rw [hL] at h
  intro u u' huu
  have h1 : L.symm u = L.symm u' := by
    apply h
    change mfderiv J K g (φ x) (L (L.symm u)) = mfderiv J K g (φ x) (L (L.symm u'))
    rw [L.apply_symm_apply, L.apply_symm_apply, huu]
  simpa using congrArg L h1

theorem injective_mfderiv_comp_localDiffeomorph {E F G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {H H' H'' : Type} [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace H''] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {K : ModelWithCorners ℝ G H''} {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
    {φ : M → N} {g : N → P} {x : M} (hφ : IsLocalDiffeomorphAt I J ∞ φ x)
    (hg : MDifferentiableAt J K g (φ x)) (h : Injective (mfderiv J K g (φ x))) :
    Injective (mfderiv I K (g ∘ φ) x) := by
  rw [mfderiv_comp x hg (hφ.mdifferentiableAt (by simp))]
  set L := hφ.mfderivToContinuousLinearEquiv (by simp)
  have hL : mfderiv I J φ x = (L : TangentSpace I x →L[ℝ] TangentSpace J (φ x)) := rfl
  rw [hL]
  exact h.comp L.injective

theorem injective_mfderiv_mobiusEmbed (p : ℝ × ℝ) (hp : |p.2| < 2) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) mobiusEmbed (mobiusProj p)) := by
  refine injective_mfderiv_of_comp_localDiffeomorph (isLocalDiffeomorph_mobiusProj p)
    (contMDiff_mobiusEmbed.mdifferentiableAt (by simp)) ?_
  have hc : mobiusEmbed ∘ mobiusProj = euclidThree ∘ mobiusTripleLift := by
    rw [← mobiusTriple_comp]
    rfl
  rw [hc, mfderiv_eq_fderiv]
  have hd := euclidThree.hasFDerivAt.comp p (hasFDerivAt_mobiusTripleLift p)
  change Injective (fderiv ℝ (euclidThree ∘ mobiusTripleLift) p)
  rw [hd.fderiv]
  have hinj := injective_fderiv_mobiusTripleLift hp
  rw [(hasFDerivAt_mobiusTripleLift p).fderiv] at hinj
  exact euclidThree.injective.comp hinj

theorem contMDiff_mobiusEmbed_down :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun w : MobiusLift.{u} => mobiusEmbed w.down) :=
  contMDiff_mobiusEmbed.comp contMDiff_mobiusLift_down

theorem injective_mfderiv_mobiusEmbed_down (w : MobiusLift.{u}) (hw : mobiusWidth w.down ≤ 1) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (fun w : MobiusLift.{u} => mobiusEmbed w.down) w) := by
  obtain ⟨p, hp⟩ := mobiusProj_surjective w.down
  have hφ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (ULift.down : MobiusLift.{u} → _) w :=
    (uliftDiffeomorph 𝓘(ℝ, ℝ × ℝ) MobiusBand).symm.isLocalDiffeomorph w
  refine injective_mfderiv_comp_localDiffeomorph (g := mobiusEmbed) hφ
    (contMDiff_mobiusEmbed.mdifferentiableAt (by simp)) ?_
  rw [← hp]
  refine injective_mfderiv_mobiusEmbed p ?_
  rw [← hp, mobiusWidth_mk] at hw
  have := (sq_le_one_iff_abs_le_one p.2).mp hw
  linarith

theorem isImmersion_mobiusEmbed :
    Manifold.IsImmersion (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun w : mobiusSet.{u} => mobiusEmbed w.val.down) := by
  apply DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt
  intro x
  have hf0 := mobiusAtlas.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt x
  have hg0 := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp) contMDiff_mobiusEmbed_down x.val (injective_mfderiv_mobiusEmbed_down x.val x.2)
  have : FiniteDimensional ℝ hf0.complement :=
    FiniteDimensional.of_injective (hf0.equiv.toLinearMap.comp (LinearMap.inr ℝ _ _))
      (hf0.equiv.injective.comp LinearMap.inr_injective)
  have : FiniteDimensional ℝ hg0.complement :=
    FiniteDimensional.of_injective (hg0.equiv.toLinearMap.comp (LinearMap.inr ℝ _ _))
      (hg0.equiv.injective.comp LinearMap.inr_injective)
  have : CompleteSpace hf0.complement := FiniteDimensional.complete ℝ _
  have : CompleteSpace hg0.complement := FiniteDimensional.complete ℝ _
  exact (hf0.isImmersionAtOfComplement_complement.comp_of_isInteriorPoint_map
    hg0.isImmersionAtOfComplement_complement (by simp)
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, ℝ × ℝ)))).isImmersionAt

theorem injective_mobiusEmbed_set :
    Injective (fun w : mobiusSet.{u} => mobiusEmbed w.val.down) := by
  intro w w' h
  apply Subtype.ext
  apply ULift.ext
  exact mobiusTriple_injOn w.2 w'.2 (euclidThree.injective h)

theorem isSmoothEmbedding_mobiusEmbed :
    Manifold.IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun w : mobiusSet.{u} => mobiusEmbed w.val.down) :=
  ⟨isImmersion_mobiusEmbed, (Continuous.isClosedEmbedding
    (contMDiff_mobiusEmbed_down.continuous.comp continuous_subtype_val)
    injective_mobiusEmbed_set).isEmbedding⟩

theorem range_mobiusEmbed_set :
    range (fun w : mobiusSet.{u} => mobiusEmbed w.val.down) = mobiusModel := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨θ, y⟩, hp⟩ := mobiusProj_surjective w.val.down
    have hw : y ^ 2 ≤ 1 := by
      have := w.2
      change mobiusWidth w.val.down ≤ 1 at this
      rwa [← hp, mobiusWidth_mk] at this
    refine ⟨(Circle.exp θ, Set.projIcc 0 1 zero_le_one ((1 - y) / 2)), ?_⟩
    change mobiusPoint _ _ = mobiusEmbed w.val.down
    rw [← hp, mobiusEmbed_mk θ y hw]
  · rintro ⟨⟨z, t⟩, rfl⟩
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hmem : (ULift.up (mobiusProj (Complex.arg (z : ℂ), 1 - 2 * t)) : MobiusLift.{u}) ∈
        mobiusSet.{u} := by
      change mobiusWidth (mobiusProj _) ≤ 1
      rw [mobiusWidth_mk]
      nlinarith
    refine ⟨⟨_, hmem⟩, ?_⟩
    change mobiusEmbed (mobiusProj (Complex.arg (z : ℂ), 1 - 2 * t)) = mobiusPoint z t
    rw [mobiusEmbed_mk _ _ (by nlinarith), Circle.exp_arg]
    have h : (1 - (1 - 2 * (t : ℝ))) / 2 = t := by ring
    rw [h, Set.projIcc_val]

def mobiusBase : MobiusBase.{u} where
  surface := mobiusSurface
  collar := mobiusCollar
  source_eq := rfl
  boundary_exhausted := mobiusSet_boundary_eq
  embedding w := mobiusEmbed w.val.down
  isSmoothEmbedding := isSmoothEmbedding_mobiusEmbed
  range_embedding := range_mobiusEmbed_set
  embedding_collar t := by
    change mobiusEmbed (mobiusCollar.{u} (t, halfZero)).val.down = mobiusPoint t 0
    rw [mobiusCollar_zero]
    change mobiusEmbed (mobiusProj (Complex.arg (t : ℂ), 1)) = _
    rw [mobiusEmbed_mk _ _ (by norm_num), Circle.exp_arg]
    norm_num

theorem mobiusBase_collar : mobiusBase.{u}.collar = mobiusCollar.{u} := rfl

theorem mobiusBase_embedding_apply (θ y : ℝ) (h : ULift.up (mobiusProj (θ, y)) ∈ mobiusSet.{u}) :
    mobiusBase.{u}.embedding ⟨ULift.up (mobiusProj (θ, y)), h⟩ =
      mobiusPoint (Circle.exp θ) (Set.projIcc 0 1 zero_le_one ((1 - y) / 2)) := by
  have hy : y ^ 2 ≤ 1 := h
  exact mobiusEmbed_mk θ y hy

end Base

end GC.Seifert
