import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBaseModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.OneSidedPants
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecomposition

/-!
# The split of the one-sided model slab

Lane MD3, T5. The one-sided model slab `K = slabSet mobiusHeight 0 2` (connected lower and upper
level, one saddle) is the blow-up of the round annulus `1 ≤ |W| ≤ √3` at `W₀ = i√2`:
`mobiusBlowDown [θ, y] = (y - √2 sin θ) e^{iθ} + i√2` satisfies `mobiusHeight = |β|² - 1`
(`mobiusHeight_eq_norm_blowDown`) and is inverted off the core by `mobiusBlowUp`
(`mobiusBlowUp_blowDown`, `mobiusBlowDown_blowUp`). The fibrewise affine diffeomorphism
`mobiusShear [θ, y] = [θ, 7/5 sin θ + R(θ) y]` carries `{y² ≤ 1}` onto the preimage of the disc
`|W - 7i/5| ≤ 1/5` (`ospF_blowDown_shear`), so `mobiusBase` embeds as the Möbius piece
(`mobiusPieceMap`), and the slab of `ospFun` (the round pants of `OneSidedPants.lean`) embeds as the
pants piece through `mobiusBlowUp` (`ospPantsMap`). Both pieces meet the boundary of the other
inside `K`; they are immersions there by `isImmersionAt_of_ambient` (a piece that is the restriction
of an ambient partial diffeomorphism is immersed at every point, its source charts being shifted off
`0` by `shiftAtlas'`). The cut `mobiusCut (t, s) = Φ [arg t, 1 - s/8]` is the common bicollar.
`exists_mobiusSlab_split` assembles the decomposition: the boundary circle `jc` of the pants
model that goes to the hole is found by connectedness (`exists_jc`), the pants collars are replaced
by halves of the cut (`pantsCutCollar`) and of the given level collars (`pantsCollarOf`), matched by
circle diffeomorphisms (`exists_cut_match`, `exists_level_match`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

section BlowDown

def mobiusBlowDown (x : MobiusBand) : ℂ :=
  mobiusVec x + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I * (mobiusSq x + 1)

theorem contMDiff_mobiusBlowDown : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞ mobiusBlowDown := by
  have h : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I *
      (p.2 + 1)) := by fun_prop
  exact h.contMDiff.comp (contMDiff_mobiusVec.prodMk_space contMDiff_mobiusSq)

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem mobiusBlowDown_cover (t : Circle) (y : ℝ) :
    mobiusBlowDown (mobiusBandCover (t, y)) =
      (y - Real.sqrt 2 * (t : ℂ).im) • (t : ℂ) + ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective t
  rw [mobiusBandCover_exp, mobiusBlowDown, mobiusVec_mk, mobiusSq_mk]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.mul_im,
      Complex.one_re, Complex.one_im, circleExp_re, circleExp_im, Complex.add_im]
    rw [Real.sin_two_mul]
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.mul_re,
      Complex.one_re, Complex.one_im, circleExp_re, circleExp_im, Complex.add_re]
    rw [Real.cos_two_mul, Real.cos_sq']
    ring

theorem mobiusBlowDown_mk (θ y : ℝ) :
    mobiusBlowDown (mobiusProj (θ, y)) =
      (y - Real.sqrt 2 * Real.sin θ) • ((Circle.exp θ : Circle) : ℂ) +
        ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
  rw [← mobiusBandCover_exp, mobiusBlowDown_cover, circleExp_im]

theorem mobiusHeight_eq_norm_blowDown (x : MobiusBand) :
    mobiusHeight x = ‖mobiusBlowDown x‖ ^ 2 - 1 := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  rw [mobiusHeight_mk, mobiusHeightLift, mobiusBlowDown_mk, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im,
    Complex.mul_im, circleExp_re, circleExp_im]
  have hs := Real.sin_sq_add_cos_sq θ
  rw [Real.cos_two_mul]
  linear_combination (-(y - Real.sqrt 2 * Real.sin θ) ^ 2) * hs +
    (-(Real.cos θ) ^ 2) * sqrt_two_sq + Real.sqrt 2 ^ 2 * hs

def mobiusPole : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I

def mobiusBlowUp (w : ℂ) : MobiusBand :=
  mobiusBandCover (unitOf (w - mobiusPole),
    ‖w - mobiusPole‖ + Real.sqrt 2 * (unitOf (w - mobiusPole) : ℂ).im)

theorem mobiusBlowDown_blowUp (w : ℂ) :
    mobiusBlowDown (mobiusBlowUp w) = w := by
  rw [mobiusBlowUp, mobiusBlowDown_cover]
  have h : (‖w - mobiusPole‖ + Real.sqrt 2 * (unitOf (w - mobiusPole) : ℂ).im -
      Real.sqrt 2 * (unitOf (w - mobiusPole) : ℂ).im) = ‖w - mobiusPole‖ := by ring
  rw [h, norm_smul_unitOf]
  change w - mobiusPole + mobiusPole = w
  ring

theorem mobiusBlowUp_blowDown {x : MobiusBand} (hx : mobiusBlowDown x ≠ mobiusPole) :
    mobiusBlowUp (mobiusBlowDown x) = x := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  have hv : mobiusBlowDown (mobiusProj (θ, y)) - mobiusPole =
      (y - Real.sqrt 2 * Real.sin θ) • ((Circle.exp θ : Circle) : ℂ) := by
    rw [mobiusBlowDown_mk, mobiusPole]
    ring
  have hne : y - Real.sqrt 2 * Real.sin θ ≠ 0 := by
    intro h
    apply hx
    rw [mobiusBlowDown_mk, h, zero_smul, zero_add, mobiusPole]
  rw [mobiusBlowUp, hv]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have he : (y - Real.sqrt 2 * Real.sin θ) • ((Circle.exp θ : Circle) : ℂ) =
        (-(y - Real.sqrt 2 * Real.sin θ)) • ((Circle.exp (θ + Real.pi) : Circle) : ℂ) := by
      have h1 := coe_circleExp_add_int_mul_pi θ 1
      simp only [Int.cast_one, one_mul, zpow_one] at h1
      rw [h1, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [he, unitOf_smul (by linarith), norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      Circle.norm_coe, mul_one, circleExp_im, Real.sin_add_pi, mobiusBandCover_exp]
    have h2 : -(y - Real.sqrt 2 * Real.sin θ) + Real.sqrt 2 * -Real.sin θ = -y := by ring
    rw [h2, mobiusProj_add_pi]
  · rw [unitOf_smul hpos, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, Circle.norm_coe,
      mul_one, circleExp_im, mobiusBandCover_exp]
    have h2 : y - Real.sqrt 2 * Real.sin θ + Real.sqrt 2 * Real.sin θ = y := by ring
    rw [h2]

theorem contMDiffOn_mobiusBlowUp :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusBlowUp {w | w ≠ mobiusPole} := by
  have hsub : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun w : ℂ => w - mobiusPole) :=
    contMDiff_id.sub contMDiff_const
  have hmaps : MapsTo (fun w : ℂ => w - mobiusPole) {w | w ≠ mobiusPole} {z | z ≠ 0} :=
    fun w hw => sub_ne_zero.mpr hw
  have hu : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun w : ℂ => unitOf (w - mobiusPole))
      {w | w ≠ mobiusPole} := contMDiffOn_unitOf.comp hsub.contMDiffOn hmaps
  have hn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : ℂ => ‖w - mobiusPole‖)
      {w | w ≠ mobiusPole} := fun w hw =>
    ((contDiffAt_norm ℝ (sub_ne_zero.mpr hw)).comp w
      (contDiffAt_id.sub contDiffAt_const)).contMDiffAt.contMDiffWithinAt
  have him : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun w : ℂ => Real.sqrt 2 * (unitOf (w - mobiusPole) : ℂ).im) {w | w ≠ mobiusPole} :=
    (contMDiff_const.mul (Complex.imCLM.contDiff.contMDiff.comp
      contMDiff_circle_coe)).comp_contMDiffOn hu
  exact contMDiff_mobiusCover.comp_contMDiffOn (hu.prodMk (hn.add him))

end BlowDown

section Shear

theorem sqrt_two_gt : 7 / 5 < Real.sqrt 2 := by
  rw [show (7 / 5 : ℝ) = Real.sqrt ((7 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt_two_lt : Real.sqrt 2 < 71 / 50 := by
  rw [show (71 / 50 : ℝ) = Real.sqrt ((71 / 50) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

def ospD : ℝ := Real.sqrt 2 - 7 / 5

theorem ospD_pos : 0 < ospD := by
  unfold ospD
  linarith [sqrt_two_gt]

theorem ospD_lt : ospD < 1 / 50 := by
  unfold ospD
  linarith [sqrt_two_lt]

def ospK2 : ℝ := 1 / 25 - ospD ^ 2

theorem ospK2_pos : 0 < ospK2 := by
  unfold ospK2
  nlinarith [ospD_pos, ospD_lt]

def mobiusR (θ : ℝ) : ℝ := Real.sqrt (ospD ^ 2 * Real.sin θ ^ 2 + ospK2)

theorem mobiusR_arg_pos (θ : ℝ) : 0 < ospD ^ 2 * Real.sin θ ^ 2 + ospK2 := by
  have := ospK2_pos
  positivity

theorem mobiusR_pos (θ : ℝ) : 0 < mobiusR θ := Real.sqrt_pos.mpr (mobiusR_arg_pos θ)

theorem mobiusR_sq (θ : ℝ) : mobiusR θ ^ 2 = ospD ^ 2 * Real.sin θ ^ 2 + ospK2 :=
  Real.sq_sqrt (mobiusR_arg_pos θ).le

theorem mobiusR_sq_le (θ : ℝ) : mobiusR θ ^ 2 ≤ 1 / 25 := by
  rw [mobiusR_sq]
  unfold ospK2
  nlinarith [Real.sin_sq_le_one θ, sq_nonneg ospD]

theorem contDiff_mobiusR : ContDiff ℝ ∞ mobiusR := by
  have h : ContDiff ℝ ∞ (fun θ : ℝ => ospD ^ 2 * Real.sin θ ^ 2 + ospK2) := by fun_prop
  exact h.sqrt fun θ => (mobiusR_arg_pos θ).ne'

theorem mobiusR_add_int_mul_pi (θ : ℝ) (n : ℤ) : mobiusR (θ + n * Real.pi) = mobiusR θ := by
  unfold mobiusR
  rw [Real.sin_add_int_mul_pi, mul_pow]
  have h : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num
  rw [h, one_mul]

def mobiusShearLift (p : ℝ × ℝ) : ℝ × ℝ := (p.1, 7 / 5 * Real.sin p.1 + mobiusR p.1 * p.2)

def mobiusShearInvLift (p : ℝ × ℝ) : ℝ × ℝ := (p.1, (p.2 - 7 / 5 * Real.sin p.1) / mobiusR p.1)

theorem mobiusShearLift_smul (g : mobiusDeckGroup) (p : ℝ × ℝ) :
    mobiusShearLift (g • p) = g • mobiusShearLift p := by
  obtain ⟨n, rfl⟩ := mobiusZ_surjective g
  rw [mobiusZ_smul, mobiusZ_smul]
  simp only [mobiusShearLift, Real.sin_add_int_mul_pi, mobiusR_add_int_mul_pi]
  ext
  · rfl
  · simp only
    ring

theorem mobiusShearInvLift_smul (g : mobiusDeckGroup) (p : ℝ × ℝ) :
    mobiusShearInvLift (g • p) = g • mobiusShearInvLift p := by
  obtain ⟨n, rfl⟩ := mobiusZ_surjective g
  rw [mobiusZ_smul, mobiusZ_smul]
  simp only [mobiusShearInvLift, Real.sin_add_int_mul_pi, mobiusR_add_int_mul_pi]
  ext
  · rfl
  · simp only
    ring

def mobiusShear : MobiusBand → MobiusBand :=
  Quotient.lift (fun p => mobiusProj (mobiusShearLift p)) fun a b hab => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg, mobiusShearLift_smul, mobiusProj_smul]

def mobiusShearInv : MobiusBand → MobiusBand :=
  Quotient.lift (fun p => mobiusProj (mobiusShearInvLift p)) fun a b hab => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg, mobiusShearInvLift_smul, mobiusProj_smul]

theorem mobiusShear_mk (p : ℝ × ℝ) : mobiusShear (mobiusProj p) = mobiusProj (mobiusShearLift p) :=
  rfl

theorem mobiusShearInv_mk (p : ℝ × ℝ) :
    mobiusShearInv (mobiusProj p) = mobiusProj (mobiusShearInvLift p) := rfl

theorem mobiusShearInv_shear (x : MobiusBand) : mobiusShearInv (mobiusShear x) = x := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  rw [mobiusShear_mk, mobiusShearInv_mk]
  congr 1
  simp only [mobiusShearLift, mobiusShearInvLift]
  ext
  · rfl
  · simp only
    field_simp [(mobiusR_pos θ).ne']
    ring

theorem mobiusShear_shearInv (x : MobiusBand) : mobiusShear (mobiusShearInv x) = x := by
  obtain ⟨⟨θ, y⟩, rfl⟩ := mobiusProj_surjective x
  rw [mobiusShearInv_mk, mobiusShear_mk]
  congr 1
  simp only [mobiusShearLift, mobiusShearInvLift]
  ext
  · rfl
  · simp only
    field_simp [(mobiusR_pos θ).ne']
    ring

theorem contMDiff_mobiusShear : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusShear := by
  refine isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective ?_
  have h : ContDiff ℝ ∞ mobiusShearLift := by
    have := contDiff_mobiusR
    unfold mobiusShearLift
    fun_prop
  exact isLocalDiffeomorph_mobiusProj.contMDiff.comp h.contMDiff

theorem contMDiff_mobiusShearInv : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ mobiusShearInv := by
  refine isLocalDiffeomorph_mobiusProj.contMDiff_of_comp_of_surjective mobiusProj_surjective ?_
  have h : ContDiff ℝ ∞ mobiusShearInvLift := by
    have hR := contDiff_mobiusR
    unfold mobiusShearInvLift
    refine contDiff_fst.prodMk ?_
    exact ((contDiff_snd.sub (contDiff_const.mul (Real.contDiff_sin.comp contDiff_fst))).div
      (hR.comp contDiff_fst) fun p => (mobiusR_pos p.1).ne')
  exact isLocalDiffeomorph_mobiusProj.contMDiff.comp h.contMDiff

def mobiusShearDiffeo : MobiusBand ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ MobiusBand where
  toFun := mobiusShear
  invFun := mobiusShearInv
  left_inv := mobiusShearInv_shear
  right_inv := mobiusShear_shearInv
  contMDiff_toFun := contMDiff_mobiusShear
  contMDiff_invFun := contMDiff_mobiusShearInv

theorem ospF_blowDown_shear (θ y : ℝ) :
    ospF (mobiusBlowDown (mobiusShear (mobiusProj (θ, y)))) = mobiusR θ ^ 2 * (y ^ 2 - 1) := by
  rw [mobiusShear_mk, mobiusShearLift, mobiusBlowDown_mk]
  simp only [ospF, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
    circleExp_re, circleExp_im]
  have hs := Real.sin_sq_add_cos_sq θ
  have hR := mobiusR_sq θ
  unfold ospK2 ospD at hR
  linear_combination hR + (mobiusR θ * y - (Real.sqrt 2 - 7 / 5) * Real.sin θ) ^ 2 * hs

end Shear

section AmbientImmersion

variable {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']

variable [IsManifold I ∞ M] [IsManifold I' ∞ M'] {X : Set M} {Y : Set M'}

open Classical in
def ambientYChart (C' : SmoothBoundaryAtlas I' 2 Y) (P : PartialDiffeomorph I I' M M' ∞)
    (hPY : P.target ⊆ Y)
    (A : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞)
    (y₀ : Y) :
    letI := C'.toChartedSpace
    PartialDiffeomorph (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Y (EuclideanSpace ℝ (Fin 2)) ∞ :=
  letI := C'.toChartedSpace
  letI := C'.isManifold
  have hmem : ∀ v ∈ A.target ∩ A.symm ⁻¹' P.source, P (A.symm v) ∈ Y := fun v hv =>
    hPY (P.map_source hv.2)
  have hval : ∀ v ∈ A.target ∩ A.symm ⁻¹' P.source,
      (if h : P (A.symm v) ∈ Y then (⟨P (A.symm v), h⟩ : Y) else y₀).val = P (A.symm v) :=
    fun v hv => by rw [dite_eq_left (hmem v hv)]
  { toFun := fun y => A (P.symm y.val)
    invFun := fun v => if h : P (A.symm v) ∈ Y then ⟨P (A.symm v), h⟩ else y₀
    source := {y | y.val ∈ P.target ∧ P.symm y.val ∈ A.source}
    target := A.target ∩ A.symm ⁻¹' P.source
    map_source' := fun y hy => by
      refine ⟨A.map_source hy.2, ?_⟩
      change A.symm (A (P.symm y.val)) ∈ P.source
      erw [A.left_inv hy.2]
      exact P.map_target hy.1
    map_target' := fun v hv => by
      refine ⟨?_, ?_⟩
      · change (if h : P (A.symm v) ∈ Y then (⟨P (A.symm v), h⟩ : Y) else y₀).val ∈ P.target
        rw [hval v hv]
        exact P.map_source hv.2
      · change P.symm (if h : P (A.symm v) ∈ Y then (⟨P (A.symm v), h⟩ : Y) else y₀).val ∈
          A.source
        rw [hval v hv]
        erw [P.left_inv hv.2]
        exact A.map_target hv.1
    left_inv' := fun y hy => by
      have hv : A (P.symm y.val) ∈ A.target ∩ A.symm ⁻¹' P.source := by
        refine ⟨A.map_source hy.2, ?_⟩
        change A.symm (A (P.symm y.val)) ∈ P.source
        erw [A.left_inv hy.2]
        exact P.map_target hy.1
      apply Subtype.ext
      change (if h : P (A.symm (A (P.symm y.val))) ∈ Y then
        (⟨P (A.symm (A (P.symm y.val))), h⟩ : Y) else y₀).val = y.val
      rw [hval _ hv]
      erw [A.left_inv hy.2, P.right_inv hy.1]
    right_inv' := fun v hv => by
      change A (P.symm (if h : P (A.symm v) ∈ Y then
        (⟨P (A.symm v), h⟩ : Y) else y₀).val) = v
      rw [hval v hv]
      erw [P.left_inv hv.2, A.right_inv hv.1]
    open_source := by
      have h := P.toOpenPartialHomeomorph.isOpen_inter_preimage_symm A.open_source
      exact h.preimage continuous_subtype_val
    open_target := A.toOpenPartialHomeomorph.isOpen_inter_preimage_symm P.open_source
    contMDiffOn_toFun := by
      refine A.contMDiffOn.comp (P.symm.contMDiffOn.comp C'.contMDiff_subtype_val.contMDiffOn
        fun y hy => hy.1) fun y hy => hy.2
    contMDiffOn_invFun := by
      refine (C'.contMDiffOn_iff_subtype_val _ _).mpr ?_
      refine (P.contMDiffOn.comp (A.symm.contMDiffOn.mono fun v hv => hv.1)
        fun v hv => hv.2).congr fun v hv => ?_
      exact hval v hv }


omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem isImmersionAt_of_ambient (C : SmoothBoundaryAtlas I 2 X)
    (C' : SmoothBoundaryAtlas I' 2 Y) (ι : X → Y) (hιc : Continuous ι)
    (P : PartialDiffeomorph I I' M M' ∞) (hPY : P.target ⊆ Y)
    (hι : ∀ y : X, y.val ∈ P.source → (ι y).val = P y.val) (x : X) (hx : x.val ∈ P.source) :
    letI := (shiftAtlas' C).toChartedSpace
    letI := C'.toChartedSpace
    Manifold.IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞ ι x := by
  let Cs := shiftAtlas' C
  let inst : ChartedSpace (EuclideanHalfSpace 2) X := Cs.toChartedSpace
  have instM : IsManifold (𝓡∂ 2) ∞ X := Cs.isManifold
  let instY : ChartedSpace (EuclideanHalfSpace 2) Y := C'.toChartedSpace
  have instMY : IsManifold (𝓡∂ 2) ∞ Y := C'.isManifold
  let A := Cs.ambientChart x
  have hAx : A x.val ≠ 0 := by
    intro h
    have h1 : A x.val 1 = 1 := shiftAtlas'_apply_self C x
    rw [h] at h1
    exact zero_ne_one h1
  obtain ⟨w, hw, hw0⟩ := CoreDecomposition.exists_interior_halfSpace_ne_zero
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℝ) hAx hw0
  let bb := ((ambientYChart C' P hPY A (ι x)).trans L.toDiffeomorph.toPartialDiffeomorph).trans
    CoreDecomposition.halfInteriorInverse
  have hιx : (ι x).val = P x.val := hι x hx
  have hPx : P.symm (ι x).val = x.val := by
    rw [hιx]
    exact P.left_inv hx
  have hbx : ι x ∈ bb.source := by
    refine ⟨⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
    · rw [hιx]
      exact P.map_source hx
    · change P.symm (ι x).val ∈ A.source
      rw [hPx]
      exact Cs.mem_source x
    · change L (A (P.symm (ι x).val)) ∈ interior (range (𝓡∂ 2))
      rw [hPx, hL]
      exact hw
  have hbmax : bb.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ Y :=
    bb.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      bb.contMDiffOn_toFun bb.contMDiffOn_invFun
  let s : Set X := ι ⁻¹' bb.source ∩ {y | y.val ∈ P.source}
  have hs : IsOpen s :=
    (bb.open_source.preimage hιc).inter (P.open_source.preimage continuous_subtype_val)
  let d := (Cs.chart x).restr s
  have hdsource : d.source = (Cs.chart x).source ∩ s := by
    rw [OpenPartialHomeomorph.restr_source, hs.interior_eq]
  have hdmax : d ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ X :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) (IsManifold.chart_mem_maximalAtlas x) hs
  have hformula (y : X) (hy : y ∈ (Cs.chart x).source) (hyb : y ∈ s) :
      bb.toOpenPartialHomeomorph.extend (𝓡∂ 2) (ι y) = L ((Cs.chart x).extend (𝓡∂ 2) y) := by
    have hyP : P.symm (ι y).val = y.val := by
      rw [hι y hyb.2]
      exact P.left_inv hyb.2
    have hyb' : L (A (P.symm (ι y).val)) ∈ interior (range (𝓡∂ 2)) := hyb.1.2
    change (𝓡∂ 2) ((𝓡∂ 2).symm (L (A (P.symm (ι y).val)))) = L ((Cs.chart x y).val)
    rw [(𝓡∂ 2).right_inv (interior_subset hyb'), hyP]
    exact congrArg L (OpenPartialHomeomorph.restrictSubtypes_apply
      (Cs.ambientChart x).toOpenPartialHomeomorph X
      {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 0} x (0 : EuclideanHalfSpace 2)
      (Cs.mem_iff x) y hy).symm
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) PUnit.{1}).trans L)
    d bb.toOpenPartialHomeomorph (by rw [hdsource]; exact ⟨Cs.mem_source x, hbx, hx⟩) hbx hdmax
    hbmax (fun y hy => by rw [hdsource] at hy; exact hy.2.1) ?_
  intro u hu
  let y := (d.extend (𝓡∂ 2)).symm u
  have hy : y ∈ d.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (d.extend (𝓡∂ 2)).map_target hu
  rw [hdsource] at hy
  change bb.toOpenPartialHomeomorph.extend (𝓡∂ 2) (ι y) = L u
  rw [hformula y hy.1 hy.2]
  exact congrArg L ((d.extend (𝓡∂ 2)).right_inv hu)

end AmbientImmersion

section MobiusPiece

abbrev mobiusSlabAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℝ × ℝ) 2 (slabSet mobiusHeight 0 2) :=
  slabAtlas (show Module.finrank ℝ (ℝ × ℝ) = 2 by simp) contMDiff_mobiusHeight
    (show (0 : ℝ) < 2 by norm_num) mobiusHeight_regular_endpoints

theorem mem_mobiusSlab_iff (x : MobiusBand) :
    x ∈ slabSet mobiusHeight 0 2 ↔ 0 ≤ mobiusHeight x ∧ mobiusHeight x ≤ 2 :=
  mem_slabSet_iff (by norm_num) x

theorem mobiusHeight_eq_ospU (x : MobiusBand) : mobiusHeight x = ospU (mobiusBlowDown x) := by
  rw [mobiusHeight_eq_norm_blowDown, ospU_eq]

theorem ospU_bounds_of_ospF_lt {z : ℂ} (h : ospF z < 17 / 1600) :
    1 / 4 < ospU z ∧ ospU z < 7 / 4 := by
  unfold ospF at h
  unfold ospU
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 7 / 5), sq_nonneg (z.im - 47 / 40),
    sq_nonneg (z.im - 13 / 8)]

theorem exists_ospF_blowDown_eq (x : MobiusBand) : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 25 ∧
    ospF (mobiusBlowDown x) = r * (mobiusWidth (mobiusShearInv x) - 1) := by
  obtain ⟨⟨θ, y⟩, hp⟩ := mobiusProj_surjective (mobiusShearInv x)
  have hx : x = mobiusShear (mobiusProj (θ, y)) := by rw [hp, mobiusShear_shearInv]
  refine ⟨mobiusR θ ^ 2, pow_pos (mobiusR_pos θ) 2, mobiusR_sq_le θ, ?_⟩
  rw [← hp, hx, ospF_blowDown_shear, mobiusWidth_mk]

theorem ospF_blowDown_lt {x : MobiusBand} (hx : mobiusWidth (mobiusShearInv x) < 81 / 64) :
    ospF (mobiusBlowDown x) < 17 / 1600 := by
  obtain ⟨r, hr0, hr1, he⟩ := exists_ospF_blowDown_eq x
  rw [he]
  rcases le_or_gt (mobiusWidth (mobiusShearInv x)) 1 with h | h
  · nlinarith
  · nlinarith

theorem mobiusHeight_bounds_of_width {x : MobiusBand}
    (hx : mobiusWidth (mobiusShearInv x) < 81 / 64) :
    1 / 4 < mobiusHeight x ∧ mobiusHeight x < 7 / 4 := by
  rw [mobiusHeight_eq_ospU]
  exact ospU_bounds_of_ospF_lt (ospF_blowDown_lt hx)

theorem mem_mobiusSlab_of_width {x : MobiusBand} (hx : mobiusWidth (mobiusShearInv x) < 81 / 64) :
    x ∈ slabSet mobiusHeight 0 2 := by
  have h := mobiusHeight_bounds_of_width hx
  rw [mem_mobiusSlab_iff]
  constructor <;> linarith [h.1, h.2]

def mobiusPieceMap (w : mobiusSet.{u}) : slabSet mobiusHeight 0 2 :=
  ⟨mobiusShear w.val.down, mem_mobiusSlab_of_width (by
    rw [mobiusShearInv_shear]
    have := w.2
    change mobiusWidth w.val.down ≤ 1 at this
    linarith)⟩

def mobiusPieceAmbient :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) MobiusLift.{u} MobiusBand ∞ where
  toFun w := mobiusShear w.down
  invFun x := ULift.up (mobiusShearInv x)
  source := {w | mobiusWidth w.down < 81 / 64}
  target := {x | mobiusWidth (mobiusShearInv x) < 81 / 64}
  map_source' w hw := by
    change mobiusWidth (mobiusShearInv (mobiusShear w.down)) < 81 / 64
    rw [mobiusShearInv_shear]
    exact hw
  map_target' x hx := hx
  left_inv' w hw := by
    change ULift.up (mobiusShearInv (mobiusShear w.down)) = w
    rw [mobiusShearInv_shear]
  right_inv' x hx := mobiusShear_shearInv x
  open_source := isOpen_lt contMDiff_mobiusWidth_down.continuous continuous_const
  open_target := isOpen_lt (contMDiff_mobiusWidth.continuous.comp
    contMDiff_mobiusShearInv.continuous) continuous_const
  contMDiffOn_toFun := (contMDiff_mobiusShear.comp contMDiff_mobiusLift_down).contMDiffOn
  contMDiffOn_invFun := (contMDiff_mobiusLift_up.comp contMDiff_mobiusShearInv).contMDiffOn

theorem contMDiff_mobiusPieceMap :
    letI := mobiusSlabAtlas.toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ mobiusPieceMap.{u} := by
  let := mobiusSlabAtlas.toChartedSpace
  refine (mobiusSlabAtlas.contMDiff_iff_subtype_val _).mpr ?_
  exact contMDiff_mobiusShear.comp (contMDiff_mobiusLift_down.comp
    mobiusAtlas.contMDiff_subtype_val)

theorem injective_mobiusPieceMap : Injective mobiusPieceMap.{u} := by
  intro w w' h
  have h1 : mobiusShear w.val.down = mobiusShear w'.val.down := congrArg Subtype.val h
  have h2 := congrArg mobiusShearInv h1
  rw [mobiusShearInv_shear, mobiusShearInv_shear] at h2
  exact Subtype.ext (ULift.ext h2)

theorem isSmoothEmbedding_mobiusPieceMap' :
    letI := mobiusSlabAtlas.toChartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ mobiusPieceMap.{u} := by
  let := mobiusSlabAtlas.toChartedSpace
  have hc : Continuous mobiusPieceMap.{u} := contMDiff_mobiusPieceMap.continuous
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun x => ?_,
    (hc.isClosedEmbedding injective_mobiusPieceMap).isEmbedding⟩
  refine isImmersionAt_of_ambient mobiusSublevelAtlas mobiusSlabAtlas mobiusPieceMap hc
    mobiusPieceAmbient (fun z hz => mem_mobiusSlab_of_width hz) (fun y hy => rfl) x ?_
  change mobiusWidth x.val.down < 81 / 64
  have := x.2
  change mobiusWidth x.val.down ≤ 1 at this
  linarith

theorem isSmoothEmbedding_mobiusPieceMap :
    letI := mobiusSlabAtlas.toChartedSpace
    Manifold.IsSmoothEmbedding (SurfaceModel.model mobiusBase.{u}.surface.kind) (𝓡∂ 2) ∞
      (fun x : mobiusBase.{u}.surface.Carrier => mobiusPieceMap.{u} x) :=
  isSmoothEmbedding_mobiusPieceMap'

end MobiusPiece

section Cut

theorem ospF_blowDown_le {x : MobiusBand} (hx : mobiusWidth (mobiusShearInv x) ≤ 81 / 64) :
    ospF (mobiusBlowDown x) ≤ 17 / 1600 := by
  obtain ⟨r, hr0, hr1, he⟩ := exists_ospF_blowDown_eq x
  rw [he]
  rcases le_or_gt (mobiusWidth (mobiusShearInv x)) 1 with h | h
  · nlinarith
  · nlinarith

theorem ospU_bounds_of_ospF_le {z : ℂ} (h : ospF z ≤ 17 / 1600) :
    1 / 4 < ospU z ∧ ospU z < 7 / 4 := by
  unfold ospF at h
  unfold ospU
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 7 / 5), sq_nonneg (z.im - 47 / 40),
    sq_nonneg (z.im - 13 / 8)]

theorem mobiusHeight_bounds_of_width_le {x : MobiusBand}
    (hx : mobiusWidth (mobiusShearInv x) ≤ 81 / 64) :
    1 / 4 < mobiusHeight x ∧ mobiusHeight x < 7 / 4 := by
  rw [mobiusHeight_eq_ospU]
  exact ospU_bounds_of_ospF_le (ospF_blowDown_le hx)

theorem mem_mobiusSlab_of_width_le {x : MobiusBand}
    (hx : mobiusWidth (mobiusShearInv x) ≤ 81 / 64) : x ∈ slabSet mobiusHeight 0 2 := by
  have h := mobiusHeight_bounds_of_width_le hx
  rw [mem_mobiusSlab_iff]
  constructor <;> linarith [h.1, h.2]

def cutClamp (s : ℝ) : ℝ := max (-1) (min s 1)

theorem cutClamp_of_mem {s : ℝ} (h1 : -1 < s) (h2 : s < 1) : cutClamp s = s := by
  unfold cutClamp
  rw [min_eq_left h2.le, max_eq_right h1.le]

theorem cutClamp_bounds (s : ℝ) : -1 ≤ cutClamp s ∧ cutClamp s ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

def mobiusCutFun (q : Circle × ℝ) : slabSet mobiusHeight 0 2 :=
  ⟨mobiusShear (mobiusBandCover (q.1, 1 - cutClamp q.2 / 8)), mem_mobiusSlab_of_width_le (by
    rw [mobiusShearInv_shear, mobiusWidth_cover]
    have h := cutClamp_bounds q.2
    nlinarith [h.1, h.2])⟩

def mobiusCutInv (x : slabSet mobiusHeight 0 2) : Circle × ℝ :=
  (unitOf (mobiusVec (mobiusShearInv x.val)), 8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖))

theorem mobiusCutFun_val {q : Circle × ℝ} (hq : -1 < q.2 ∧ q.2 < 1) :
    (mobiusCutFun q).val = mobiusShear (mobiusBandCover (q.1, 1 - q.2 / 8)) := by
  change mobiusShear (mobiusBandCover (q.1, 1 - cutClamp q.2 / 8)) = _
  rw [cutClamp_of_mem hq.1 hq.2]

theorem norm_mobiusVec_bounds {x : MobiusBand} (h1 : 49 / 64 < mobiusWidth x)
    (h2 : mobiusWidth x < 81 / 64) : 7 / 8 < ‖mobiusVec x‖ ∧ ‖mobiusVec x‖ < 9 / 8 := by
  rw [← norm_mobiusVec_sq] at h1 h2
  constructor <;> nlinarith [norm_nonneg (mobiusVec x)]

def mobiusCut :
    letI := mobiusSlabAtlas.toChartedSpace
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ)
      (slabSet mobiusHeight 0 2) ∞ :=
  letI := mobiusSlabAtlas.toChartedSpace
  { toFun := mobiusCutFun
    invFun := mobiusCutInv
    source := {p | -1 < p.2 ∧ p.2 < 1}
    target := {x | 49 / 64 < mobiusWidth (mobiusShearInv x.val) ∧
      mobiusWidth (mobiusShearInv x.val) < 81 / 64}
    map_source' := fun q hq => by
      change 49 / 64 < mobiusWidth (mobiusShearInv (mobiusCutFun q).val) ∧
        mobiusWidth (mobiusShearInv (mobiusCutFun q).val) < 81 / 64
      rw [mobiusCutFun_val hq, mobiusShearInv_shear, mobiusWidth_cover]
      obtain ⟨h1, h2⟩ := hq
      constructor <;> nlinarith
    map_target' := fun x hx => by
      have hn := norm_mobiusVec_bounds hx.1 hx.2
      change -1 < 8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) ∧
        8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) < 1
      constructor <;> linarith [hn.1, hn.2]
    left_inv' := fun q hq => by
      obtain ⟨h1, h2⟩ := hq
      have hy : 0 < 1 - q.2 / 8 := by linarith
      change (unitOf (mobiusVec (mobiusShearInv (mobiusCutFun q).val)),
        8 * (1 - ‖mobiusVec (mobiusShearInv (mobiusCutFun q).val)‖)) = q
      rw [mobiusCutFun_val ⟨h1, h2⟩, mobiusShearInv_shear, mobiusVec_cover, unitOf_smul hy,
        norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos hy]
      ext
      · rfl
      · simp only
        ring
    right_inv' := fun x hx => by
      have hn := norm_mobiusVec_bounds hx.1 hx.2
      have hne : mobiusVec (mobiusShearInv x.val) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hn
        norm_num at hn
      apply Subtype.ext
      have hq : -1 < 8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) ∧
          8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) < 1 := by
        constructor <;> linarith [hn.1, hn.2]
      change (mobiusCutFun (mobiusCutInv x)).val = x.val
      rw [mobiusCutFun_val hq]
      have h3 : 1 - 8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) / 8 =
          ‖mobiusVec (mobiusShearInv x.val)‖ := by ring
      change mobiusShear (mobiusBandCover (unitOf (mobiusVec (mobiusShearInv x.val)),
        1 - 8 * (1 - ‖mobiusVec (mobiusShearInv x.val)‖) / 8)) = x.val
      rw [h3, mobiusBandCover_unitOf hne, mobiusShear_shearInv]
    open_source := (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
    open_target := by
      have hc : Continuous fun x : slabSet mobiusHeight 0 2 =>
          mobiusWidth (mobiusShearInv x.val) :=
        contMDiff_mobiusWidth.continuous.comp (contMDiff_mobiusShearInv.continuous.comp
          continuous_subtype_val)
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    contMDiffOn_toFun := by
      refine (mobiusSlabAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
      have hg : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : Circle × ℝ => (q.1, 1 - q.2 / 8)) :=
        contMDiff_fst.prodMk ((contMDiff_const.sub (contMDiff_id.div_const 8)).comp contMDiff_snd)
      refine (contMDiff_mobiusShear.comp (contMDiff_mobiusCover.comp hg)).contMDiffOn.congr
        fun q hq => ?_
      exact mobiusCutFun_val hq
    contMDiffOn_invFun := by
      have hv : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
          (fun x : slabSet mobiusHeight 0 2 => mobiusVec (mobiusShearInv x.val)) :=
        contMDiff_mobiusVec.comp (contMDiff_mobiusShearInv.comp
          mobiusSlabAtlas.contMDiff_subtype_val)
      have hne : ∀ x ∈ ({x | 49 / 64 < mobiusWidth (mobiusShearInv x.val) ∧
          mobiusWidth (mobiusShearInv x.val) < 81 / 64} : Set (slabSet mobiusHeight 0 2)),
          mobiusVec (mobiusShearInv x.val) ≠ 0 := by
        intro x hx h
        have hn := norm_mobiusVec_bounds hx.1 hx.2
        rw [h, norm_zero] at hn
        norm_num at hn
      have h1 := contMDiffOn_unitOf.comp hv.contMDiffOn hne
      have hnorm : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
          (fun x : slabSet mobiusHeight 0 2 => ‖mobiusVec (mobiusShearInv x.val)‖)
          {x | 49 / 64 < mobiusWidth (mobiusShearInv x.val) ∧
            mobiusWidth (mobiusShearInv x.val) < 81 / 64} := fun x hx =>
        ((contDiffAt_norm ℝ (hne x hx)).contMDiffAt.comp x hv.contMDiffAt).contMDiffWithinAt
      exact h1.prodMk ((contMDiff_const.mul (contMDiff_const.sub contMDiff_id)).comp_contMDiffOn
        hnorm) }

theorem mobiusCut_source :
    letI := mobiusSlabAtlas.toChartedSpace
    mobiusCut.source = {p : Circle × ℝ | -1 < p.2 ∧ p.2 < 1} := rfl

theorem mobiusCut_apply_val {t : Circle} {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    letI := mobiusSlabAtlas.toChartedSpace
    (mobiusCut (t, s)).val = mobiusShear (mobiusBandCover (t, 1 - s / 8)) :=
  mobiusCutFun_val (q := (t, s)) ⟨h1, h2⟩

theorem mobiusPieceMap_collar (t : Circle) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    letI := mobiusSlabAtlas.toChartedSpace
    mobiusPieceMap.{u} (mobiusBase.{u}.collar (t, halfPoint s hs)) = mobiusCut (t, s) := by
  apply Subtype.ext
  rw [mobiusCut_apply_val (by linarith) hs1]
  change mobiusShear (mobiusCollarFun.{u} (t, halfPoint s hs)).val.down = _
  rw [mobiusCollarFun_val (show (t, halfPoint s hs) ∈ circleCollarSource from hs1)]
  rfl

theorem mobiusHeight_bounds_of_mem_cutTarget {x : slabSet mobiusHeight 0 2}
    (hx : letI := mobiusSlabAtlas.toChartedSpace; x ∈ mobiusCut.target) :
    1 / 4 ≤ mobiusHeight x.val ∧ mobiusHeight x.val ≤ 7 / 4 := by
  have h := mobiusHeight_bounds_of_width hx.2
  exact ⟨h.1.le, h.2.le⟩

theorem mobiusHeight_bounds_of_mem_range {w : mobiusSet.{u}} :
    1 / 4 ≤ mobiusHeight (mobiusPieceMap w).val ∧ mobiusHeight (mobiusPieceMap w).val ≤ 7 / 4 := by
  have hw : mobiusWidth (mobiusShearInv (mobiusPieceMap w).val) < 81 / 64 := by
    change mobiusWidth (mobiusShearInv (mobiusShear w.val.down)) < 81 / 64
    rw [mobiusShearInv_shear]
    have := w.2
    change mobiusWidth w.val.down ≤ 1 at this
    linarith
  have h := mobiusHeight_bounds_of_width hw
  exact ⟨h.1.le, h.2.le⟩

end Cut

section PantsPiece

theorem mem_ospSlab_of_mem (z : slabSet ospFun 0 1) : z.val.val ∈ ospSlab :=
  (ospHeight_mem_Icc_iff z.val.2).mp ((mem_slabSet_iff zero_le_one z.val).mp z.2)

theorem ospF_pole_lt : ospF mobiusPole < -(1 / 50) := by
  have h1 := ospD_pos
  have h2 := ospD_lt
  unfold ospD at h1 h2
  simp only [ospF, mobiusPole, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.mul_im]
  nlinarith

theorem ne_pole_of_ospF {z : ℂ} (h : -(1 / 50) < ospF z) : z ≠ mobiusPole := by
  rintro rfl
  linarith [ospF_pole_lt]

theorem im_lt_of_ospF_le {z : ℂ} (h : ospF z ≤ 17 / 1600) : z.im < 123 / 70 := by
  unfold ospF at h
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 7 / 5)]

theorem mobiusHeight_blowUp {z : ℂ} : mobiusHeight (mobiusBlowUp z) = ospU z := by
  rw [mobiusHeight_eq_ospU, mobiusBlowDown_blowUp]

theorem mem_mobiusSlab_blowUp {z : ℂ} (hz : z ∈ ospSlab) :
    mobiusBlowUp z ∈ slabSet mobiusHeight 0 2 := by
  rw [mem_mobiusSlab_iff, mobiusHeight_blowUp]
  exact ⟨hz.1, hz.2.1⟩

def ospPantsMap (z : slabSet ospFun 0 1) : slabSet mobiusHeight 0 2 :=
  ⟨mobiusBlowUp z.val.val, mem_mobiusSlab_blowUp (mem_ospSlab_of_mem z)⟩

abbrev ospShiftAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (slabSet ospFun 0 1) :=
  shiftAtlas' ospSlabAtlas

theorem contMDiff_slab_val :
    letI := ospShiftAtlas.toChartedSpace
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun z : slabSet ospFun 0 1 => z.val.val) := by
  let := ospShiftAtlas.toChartedSpace
  exact (contMDiff_subtype_val (U := ospDom)).comp ospShiftAtlas.contMDiff_subtype_val

theorem contMDiff_ospPantsMap :
    letI := ospShiftAtlas.toChartedSpace
    letI := mobiusSlabAtlas.toChartedSpace
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ ospPantsMap := by
  let := ospShiftAtlas.toChartedSpace
  let := mobiusSlabAtlas.toChartedSpace
  refine (mobiusSlabAtlas.contMDiff_iff_subtype_val _).mpr ?_
  refine contMDiffOn_univ.mp ?_
  refine contMDiffOn_mobiusBlowUp.comp contMDiff_slab_val.contMDiffOn fun z _ => ?_
  exact ne_pole_of_ospF (by linarith [(mem_ospSlab_of_mem z).2.2])

theorem injective_ospPantsMap : Injective ospPantsMap := by
  intro z z' h
  have h1 : mobiusBlowUp z.val.val = mobiusBlowUp z'.val.val := congrArg Subtype.val h
  have h2 := congrArg mobiusBlowDown h1
  rw [mobiusBlowDown_blowUp, mobiusBlowDown_blowUp] at h2
  exact Subtype.ext (Subtype.ext h2)

open Classical in
def ospPantsAmbient : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ospDom MobiusBand ∞ where
  toFun z := mobiusBlowUp z.val
  invFun x := if h : (mobiusBlowDown x).im < 123 / 70 then ⟨mobiusBlowDown x, h⟩ else ospSaddlePt
  source := {z | -(1 / 50) < ospF z.val ∧ ospF z.val < 17 / 1600}
  target := {x | -(1 / 50) < ospF (mobiusBlowDown x) ∧ ospF (mobiusBlowDown x) < 17 / 1600}
  map_source' z hz := by
    change -(1 / 50) < ospF (mobiusBlowDown (mobiusBlowUp z.val)) ∧
      ospF (mobiusBlowDown (mobiusBlowUp z.val)) < 17 / 1600
    rw [mobiusBlowDown_blowUp]
    exact hz
  map_target' x hx := by
    have him := im_lt_of_ospF_le hx.2.le
    change -(1 / 50) < ospF (if h : (mobiusBlowDown x).im < 123 / 70 then
      (⟨mobiusBlowDown x, h⟩ : ospDom) else ospSaddlePt).val ∧ _
    rw [dite_eq_left him]
    exact hx
  left_inv' z hz := by
    have h1 : mobiusBlowDown (mobiusBlowUp z.val) = z.val := mobiusBlowDown_blowUp z.val
    have him : (mobiusBlowDown (mobiusBlowUp z.val)).im < 123 / 70 := by rw [h1]; exact z.2
    change (if h : (mobiusBlowDown (mobiusBlowUp z.val)).im < 123 / 70 then
      (⟨mobiusBlowDown (mobiusBlowUp z.val), h⟩ : ospDom) else ospSaddlePt) = z
    rw [dite_eq_left him]
    exact Subtype.ext h1
  right_inv' x hx := by
    have him := im_lt_of_ospF_le hx.2.le
    change mobiusBlowUp (if h : (mobiusBlowDown x).im < 123 / 70 then
      (⟨mobiusBlowDown x, h⟩ : ospDom) else ospSaddlePt).val = x
    rw [dite_eq_left him]
    exact mobiusBlowUp_blowDown (ne_pole_of_ospF hx.1)
  open_source := by
    have hc : Continuous fun z : ospDom => ospF z.val :=
      contDiff_ospF.continuous.comp continuous_subtype_val
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  open_target := by
    have hc : Continuous fun x : MobiusBand => ospF (mobiusBlowDown x) :=
      contDiff_ospF.continuous.comp contMDiff_mobiusBlowDown.continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  contMDiffOn_toFun := contMDiffOn_mobiusBlowUp.comp
    (contMDiff_subtype_val (U := ospDom)).contMDiffOn fun z hz => ne_pole_of_ospF hz.1
  contMDiffOn_invFun := by
    rw [← DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff]
    refine contMDiff_mobiusBlowDown.contMDiffOn.congr fun x hx => ?_
    change (if h : (mobiusBlowDown x).im < 123 / 70 then
      (⟨mobiusBlowDown x, h⟩ : ospDom) else ospSaddlePt).val = mobiusBlowDown x
    rw [dite_eq_left (im_lt_of_ospF_le hx.2.le)]

theorem slab_mem_of_ospSlab {w : ℂ} (hw : w ∈ ospSlab) :
    (⟨w, ospSlab_subset_ospDom hw⟩ : ospDom) ∈ slabSet ospFun 0 1 :=
  (mem_slabSet_iff zero_le_one _).mpr ((ospHeight_mem_Icc_iff (ospSlab_subset_ospDom hw)).mpr hw)

def ospSlabBase : slabSet ospFun 0 1 :=
  ⟨ospSaddlePt, slab_mem_of_ospSlab ospSaddle_mem_ospSlab⟩

open Classical in
def ospSlabPoint (x : MobiusBand) : slabSet ospFun 0 1 :=
  if h : mobiusBlowDown x ∈ ospSlab then ⟨⟨_, ospSlab_subset_ospDom h⟩, slab_mem_of_ospSlab h⟩
  else ospSlabBase

theorem ospSlabPoint_val {x : MobiusBand} (h : mobiusBlowDown x ∈ ospSlab) :
    (ospSlabPoint x).val.val = mobiusBlowDown x := by
  rw [ospSlabPoint, dite_eq_left h]

theorem mem_ospSlab_of_mobiusSlab {y : slabSet mobiusHeight 0 2}
    (hy : 0 ≤ ospF (mobiusBlowDown y.val)) : mobiusBlowDown y.val ∈ ospSlab := by
  have h := (mem_mobiusSlab_iff y.val).mp y.2
  rw [mobiusHeight_eq_ospU] at h
  exact ⟨h.1, h.2, hy⟩

theorem ospSlabPoint_pantsMap (z : slabSet ospFun 0 1) :
    ospSlabPoint (ospPantsMap z).val = z := by
  have h1 : mobiusBlowDown (ospPantsMap z).val = z.val.val := mobiusBlowDown_blowUp _
  have h2 : mobiusBlowDown (ospPantsMap z).val ∈ ospSlab := by
    rw [h1]
    exact mem_ospSlab_of_mem z
  apply Subtype.ext
  apply Subtype.ext
  rw [ospSlabPoint_val h2, h1]

theorem pantsMap_ospSlabPoint {y : slabSet mobiusHeight 0 2}
    (hy : 0 ≤ ospF (mobiusBlowDown y.val)) : ospPantsMap (ospSlabPoint y.val) = y := by
  apply Subtype.ext
  change mobiusBlowUp (ospSlabPoint y.val).val.val = y.val
  rw [ospSlabPoint_val (mem_ospSlab_of_mobiusSlab hy)]
  exact mobiusBlowUp_blowDown (ne_pole_of_ospF (by linarith))

theorem contMDiffOn_ospSlabPoint :
    letI := ospShiftAtlas.toChartedSpace
    letI := mobiusSlabAtlas.toChartedSpace
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (fun y : slabSet mobiusHeight 0 2 => ospSlabPoint y.val)
      {y | 0 < ospF (mobiusBlowDown y.val)} := by
  let := ospShiftAtlas.toChartedSpace
  let := mobiusSlabAtlas.toChartedSpace
  refine (ospShiftAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
  rw [← DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff]
  refine (contMDiff_mobiusBlowDown.comp mobiusSlabAtlas.contMDiff_subtype_val).contMDiffOn.congr
    fun y hy => ?_
  exact ospSlabPoint_val (mem_ospSlab_of_mobiusSlab (le_of_lt hy))

theorem isSmoothEmbedding_ospPantsMap :
    letI := ospShiftAtlas.toChartedSpace
    letI := mobiusSlabAtlas.toChartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ ospPantsMap := by
  let := ospShiftAtlas.toChartedSpace
  have := ospShiftAtlas.isManifold
  let := mobiusSlabAtlas.toChartedSpace
  have := mobiusSlabAtlas.isManifold
  have hc : Continuous ospPantsMap := contMDiff_ospPantsMap.continuous
  have hcpt : CompactSpace (slabSet ospFun 0 1) := by
    rw [← isCompact_iff_compactSpace, slabSet_eq zero_le_one]
    exact isCompact_ospFun_preimage_Icc
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun x => ?_,
    (hc.isClosedEmbedding injective_ospPantsMap).isEmbedding⟩
  by_cases hx : ospF x.val.val < 17 / 1600
  · refine isImmersionAt_of_ambient ospSlabAtlas mobiusSlabAtlas ospPantsMap hc ospPantsAmbient
      (fun w hw => ?_) (fun y hy => rfl) x ⟨?_, hx⟩
    · have h := ospU_bounds_of_ospF_le hw.2.le
      rw [mem_mobiusSlab_iff, mobiusHeight_eq_ospU]
      constructor <;> linarith [h.1, h.2]
    · linarith [(mem_ospSlab_of_mem x).2.2]
  · refine CoreDecomposition.isImmersionAtOfComplement_of_localInverse ospPantsMap
      contMDiff_ospPantsMap injective_ospPantsMap x (U := {y | 0 < ospF (mobiusBlowDown y.val)})
      (isOpen_lt continuous_const (contDiff_ospF.continuous.comp
        (contMDiff_mobiusBlowDown.continuous.comp continuous_subtype_val))) ?_
      contMDiffOn_ospSlabPoint (fun y hy => pantsMap_ospSlabPoint (le_of_lt hy))
    change 0 < ospF (mobiusBlowDown (mobiusBlowUp x.val.val))
    rw [mobiusBlowDown_blowUp]
    linarith

end PantsPiece

section PantsCircles

local instance instSlabCharted : ChartedSpace (EuclideanHalfSpace 2) (slabSet ospFun 0 1) :=
  ospShiftAtlas.toChartedSpace

local instance instSlabManifold : IsManifold (𝓡∂ 2) ∞ (slabSet ospFun 0 1) :=
  ospShiftAtlas.isManifold

local instance instKCharted : ChartedSpace (EuclideanHalfSpace 2) (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.toChartedSpace

local instance instKManifold : IsManifold (𝓡∂ 2) ∞ (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.isManifold

theorem exists_ospPants_shift :
    ∃ e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1,
      ∀ j t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
        if j.val = 0 then 1 else 0 := by
  obtain ⟨e, he⟩ := exists_ospPants.{u}
  exact ⟨@Diffeomorph.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ospSlabAtlas.toChartedSpace _ _ ospShiftAtlas.toChartedSpace _ e
    (ospSlabAtlas.diffeomorphOfAmbient ospShiftAtlas (Diffeomorph.refl 𝓘(ℝ, ℂ) ospDom ∞)
      (fun z => Iff.rfl)), he⟩

theorem slab_isBoundaryPoint_iff' (z : slabSet ospFun 0 1) :
    (𝓡∂ 2).IsBoundaryPoint z ↔ ospFun z.val = 0 ∨ ospFun z.val = 1 := by
  rw [shiftAtlas'_isBoundaryPoint_iff, ← ospSlabAtlas.isBoundaryPoint_iff]
  exact slab_isBoundaryPoint z

theorem exists_collar_of_boundary (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (z : slabSet ospFun 0 1) (hz : ospFun z.val = 0 ∨ ospFun z.val = 1) :
    ∃ j t, e (pantsPlanarBase.{u}.collar j (t, halfZero)) = z := by
  have hb : (𝓡∂ 2).IsBoundaryPoint z := (slab_isBoundaryPoint_iff' z).mpr hz
  have himg := e.image_boundary (by simp)
  have hmem : z ∈ (𝓡∂ 2).boundary (slabSet ospFun 0 1) := hb
  have hbe : (𝓡∂ 2).boundary (planarSet.{u} 3) =
      ⋃ j, range fun t => pantsPlanarBase.{u}.collar j (t, halfZero) :=
    pantsPlanarBase.{u}.boundary_exhausted
  rw [← himg, hbe] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hp
  exact ⟨j, t, rfl⟩

theorem continuous_pantsZero (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (j : Fin 3) : Continuous fun t : Circle => e (pantsPlanarBase.{u}.collar j (t, halfZero)) := by
  have hcol : Continuous fun t : Circle => pantsPlanarBase.{u}.collar j (t, halfZero) := by
    refine (pantsPlanarBase.{u}.collar j).contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun t => ?_
    rw [pantsPlanarBase.{u}.source_eq j]
    exact halfZero_mem_circleCollarSource t
  exact e.continuous.comp hcol

theorem pants_zero_dichotomy (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (j : Fin 3) (hj : ∀ t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) = 0) :
    (∀ t, ospF (e (pantsPlanarBase.{u}.collar j (t, halfZero))).val.val = 0) ∨
      (∀ t, ospU (e (pantsPlanarBase.{u}.collar j (t, halfZero))).val.val = 0) := by
  set z := fun t : Circle => e (pantsPlanarBase.{u}.collar j (t, halfZero))
  have hcases : ∀ t, ospU (z t).val.val = 0 ∨ ospF (z t).val.val = 0 := fun t =>
    (ospHeight_eq_zero_iff (z t).val.2).mp (hj t)
  have hcont : Continuous fun t => ospF (z t).val.val :=
    contDiff_ospF.continuous.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_pantsZero e j)))
  by_cases hall : ∀ t, ospF (z t).val.val = 0
  · exact Or.inl hall
  · right
    obtain ⟨t₁, ht₁⟩ := not_forall.mp hall
    intro t
    rcases hcases t with h | h
    · exact h
    · exfalso
      have hpos : 0 < ospF (z t₁).val.val := by
        rcases hcases t₁ with h' | h'
        · exact ospF_pos_of_ospU_nonpos h'.le
        · exact absurd h' ht₁
      have hpos' : 3 / 25 ≤ ospF (z t₁).val.val := by
        rcases hcases t₁ with h' | h'
        · simp only [ospU] at h'
          simp only [ospF]
          nlinarith [sq_nonneg (z t₁).val.val.re, sq_nonneg (z t₁).val.val.im]
        · exact absurd h' ht₁
      have hiv := intermediate_value_univ t t₁ hcont
      rw [h] at hiv
      obtain ⟨t₂, ht₂⟩ := hiv ⟨by norm_num, by linarith⟩ (a := 1 / 20)
      rcases hcases t₂ with h'' | h''
      · have : 3 / 25 ≤ ospF (z t₂).val.val := by
          simp only [ospU] at h''
          simp only [ospF]
          nlinarith [sq_nonneg (z t₂).val.val.re, sq_nonneg (z t₂).val.val.im]
        simp only at ht₂
        linarith
      · simp only at ht₂
        rw [h''] at ht₂
        norm_num at ht₂

theorem slabPt_hole_mem : ((6 / 5 : ℝ) * Complex.I : ℂ) ∈ ospSlab := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ospU, ospF]

theorem slabPt_inner_mem : (-Complex.I : ℂ) ∈ ospSlab := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ospU, ospF]

theorem exists_jc (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (he : ∀ j t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
      if j.val = 0 then 1 else 0) :
    ∃ jc : Fin 3, jc ≠ 0 ∧
      (∀ t, ospF (e (pantsPlanarBase.{u}.collar jc (t, halfZero))).val.val = 0) ∧
      ∀ j, j ≠ 0 → j ≠ jc → ∀ t,
        ospU (e (pantsPlanarBase.{u}.collar j (t, halfZero))).val.val = 0 := by
  have hz0 : ∀ j : Fin 3, j ≠ 0 → ∀ t,
      ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) = 0 := by
    intro j hj t
    have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    rw [he j t]
    simp [hv]
  have hne0 : ∀ (j : Fin 3) (t : Circle),
      ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) = 0 → j ≠ 0 := by
    intro j t h hj
    rw [he j t, hj] at h
    norm_num at h
  let ph : slabSet ospFun 0 1 := ⟨_, slab_mem_of_ospSlab slabPt_hole_mem⟩
  let pi : slabSet ospFun 0 1 := ⟨_, slab_mem_of_ospSlab slabPt_inner_mem⟩
  have hph : ospFun ph.val = 0 := by
    change ospHeight _ = 0
    rw [ospHeight_eq_zero_iff (ospSlab_subset_ospDom slabPt_hole_mem)]
    right
    norm_num [ospF]
  have hpi : ospFun pi.val = 0 := by
    change ospHeight _ = 0
    rw [ospHeight_eq_zero_iff (ospSlab_subset_ospDom slabPt_inner_mem)]
    left
    norm_num [ospU]
  obtain ⟨j₁, t₁, h₁⟩ := exists_collar_of_boundary e ph (Or.inl hph)
  obtain ⟨j₂, t₂, h₂⟩ := exists_collar_of_boundary e pi (Or.inl hpi)
  have hj₁ : j₁ ≠ 0 := hne0 j₁ t₁ (by rw [h₁]; exact hph)
  have hj₂ : j₂ ≠ 0 := hne0 j₂ t₂ (by rw [h₂]; exact hpi)
  have hF₁ : ∀ t, ospF (e (pantsPlanarBase.{u}.collar j₁ (t, halfZero))).val.val = 0 := by
    rcases pants_zero_dichotomy e j₁ (hz0 j₁ hj₁) with h | h
    · exact h
    · exfalso
      have := h t₁
      rw [h₁] at this
      norm_num [ospU, ph] at this
  have hU₂ : ∀ t, ospU (e (pantsPlanarBase.{u}.collar j₂ (t, halfZero))).val.val = 0 := by
    rcases pants_zero_dichotomy e j₂ (hz0 j₂ hj₂) with h | h
    · exfalso
      have := h t₂
      rw [h₂] at this
      norm_num [ospF, pi] at this
    · exact h
  have hj12 : j₁ ≠ j₂ := by
    rintro rfl
    have := hF₁ t₂
    rw [h₂] at this
    norm_num [ospF, pi] at this
  refine ⟨j₁, hj₁, hF₁, fun j hj hj' => ?_⟩
  have hj2 : j = j₂ := by
    revert hj hj' hj₁ hj₂ hj12
    fin_cases j <;> fin_cases j₁ <;> fin_cases j₂ <;> simp
  rw [hj2]
  exact hU₂

end PantsCircles

section PantsCollars

local instance instSlabCharted' : ChartedSpace (EuclideanHalfSpace 2) (slabSet ospFun 0 1) :=
  ospShiftAtlas.toChartedSpace

local instance instSlabManifold' : IsManifold (𝓡∂ 2) ∞ (slabSet ospFun 0 1) :=
  ospShiftAtlas.isManifold

local instance instKCharted' : ChartedSpace (EuclideanHalfSpace 2) (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.toChartedSpace

local instance instKManifold' : IsManifold (𝓡∂ 2) ∞ (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.isManifold

theorem one_le_width_of_ospF {x : MobiusBand} (h : 0 ≤ ospF (mobiusBlowDown x)) :
    1 ≤ mobiusWidth (mobiusShearInv x) := by
  obtain ⟨r, hr0, -, he⟩ := exists_ospF_blowDown_eq x
  rw [he] at h
  by_contra hc
  have : r * (mobiusWidth (mobiusShearInv x) - 1) < 0 :=
    mul_neg_of_pos_of_neg hr0 (by linarith [lt_of_not_ge hc])
  linarith

theorem cut_snd_nonpos {y : slabSet mobiusHeight 0 2}
    (hF : 0 ≤ ospF (mobiusBlowDown y.val)) : (mobiusCut.symm y).2 ≤ 0 := by
  have hw := one_le_width_of_ospF hF
  have hn : 1 ≤ ‖mobiusVec (mobiusShearInv y.val)‖ := by
    rw [← norm_mobiusVec_sq] at hw
    nlinarith [norm_nonneg (mobiusVec (mobiusShearInv y.val))]
  change 8 * (1 - ‖mobiusVec (mobiusShearInv y.val)‖) ≤ 0
  linarith

theorem ospF_cut_nonneg {t : Circle} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ ospF (mobiusBlowDown (mobiusCut (t, -s)).val) := by
  rw [mobiusCut_apply_val (by linarith) (by linarith)]
  obtain ⟨r, hr0, -, he⟩ := exists_ospF_blowDown_eq (mobiusShear (mobiusBandCover (t, 1 - -s / 8)))
  rw [he, mobiusShearInv_shear, mobiusWidth_cover]
  apply mul_nonneg hr0.le
  nlinarith

theorem cut_target_of_snd {q : Circle × ℝ} (h1 : -1 < q.2) (h2 : q.2 < 1) :
    mobiusCut q ∈ mobiusCut.target := mobiusCut.map_source ⟨h1, h2⟩

open CoreDecomposition in
def pantsCutCollar (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 3) ∞ :=
  have hval : ∀ q ∈ circleCollarSource, 0 ≤ ospF (mobiusBlowDown
      (mobiusCut (σ q.1, -collarClamp q)).val) := fun q hq =>
    ospF_cut_nonneg (collarClamp_nonneg q) (collarClamp_lt_one q)
  have hside : ∀ p : planarSet.{u} 3, ospPantsMap (e p) ∈ mobiusCut.target →
      (mobiusCut.symm (ospPantsMap (e p))).2 ≤ 0 := fun p hp => cut_snd_nonpos (by
    rw [show mobiusBlowDown (ospPantsMap (e p)).val = (e p).val.val from
      mobiusBlowDown_blowUp _]
    exact (mem_ospSlab_of_mem (e p)).2.2)
  { toFun := fun q => e.symm (ospSlabPoint (mobiusCut (σ q.1, -collarClamp q)).val)
    invFun := fun p => (σ.symm (mobiusCut.symm (ospPantsMap (e p))).1,
      DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
        (-(mobiusCut.symm (ospPantsMap (e p))).2))
    source := circleCollarSource
    target := {p | ospPantsMap (e p) ∈ mobiusCut.target}
    map_source' := fun q hq => by
      change ospPantsMap (e (e.symm (ospSlabPoint (mobiusCut (σ q.1, -collarClamp q)).val))) ∈
        mobiusCut.target
      rw [e.apply_symm_apply, pantsMap_ospSlabPoint (hval q hq)]
      exact cut_target_of_snd (by linarith [collarClamp_lt_one q])
        (by linarith [collarClamp_nonneg q])
    map_target' := fun p hp => by
      have h1 : -1 < (mobiusCut.symm (ospPantsMap (e p))).2 ∧
          (mobiusCut.symm (ospPantsMap (e p))).2 < 1 := mobiusCut.map_target hp
      have h2 := hside p hp
      change max (-(mobiusCut.symm (ospPantsMap (e p))).2) 0 < 1
      rw [max_eq_left (by linarith)]
      linarith [h1.1]
    left_inv' := fun q hq => by
      have hm : (σ q.1, -collarClamp q) ∈ mobiusCut.source :=
        ⟨by linarith [collarClamp_lt_one q], by linarith [collarClamp_nonneg q]⟩
      change (σ.symm (mobiusCut.symm (ospPantsMap (e (e.symm (ospSlabPoint
        (mobiusCut (σ q.1, -collarClamp q)).val))))).1,
        DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (-(mobiusCut.symm (ospPantsMap (e (e.symm (ospSlabPoint
            (mobiusCut (σ q.1, -collarClamp q)).val))))).2)) = q
      have hl : mobiusCut.symm (mobiusCut (σ q.1, -collarClamp q)) = (σ q.1, -collarClamp q) :=
        mobiusCut.left_inv hm
      rw [e.apply_symm_apply, pantsMap_ospSlabPoint (hval q hq), hl]
      simp only [Diffeomorph.symm_apply_apply, neg_neg]
      rw [collarClamp_of_mem hq, halfSpaceOneLift_val_zero']
    right_inv' := fun p hp => by
      have h1 : -1 < (mobiusCut.symm (ospPantsMap (e p))).2 ∧
          (mobiusCut.symm (ospPantsMap (e p))).2 < 1 := mobiusCut.map_target hp
      have h2 := hside p hp
      have hc : collarClamp (σ.symm (mobiusCut.symm (ospPantsMap (e p))).1,
          DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
            (-(mobiusCut.symm (ospPantsMap (e p))).2)) =
          -(mobiusCut.symm (ospPantsMap (e p))).2 := by
        have hmem : (σ.symm (mobiusCut.symm (ospPantsMap (e p))).1,
            DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
              (-(mobiusCut.symm (ospPantsMap (e p))).2)) ∈ circleCollarSource := by
          change max (-(mobiusCut.symm (ospPantsMap (e p))).2) 0 < 1
          rw [max_eq_left (by linarith)]
          linarith [h1.1]
        rw [collarClamp_of_mem hmem]
        change max (-(mobiusCut.symm (ospPantsMap (e p))).2) 0 = _
        rw [max_eq_left (by linarith)]
      change e.symm (ospSlabPoint (mobiusCut (σ (σ.symm (mobiusCut.symm (ospPantsMap (e p))).1),
        -collarClamp (σ.symm (mobiusCut.symm (ospPantsMap (e p))).1,
          DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
            (-(mobiusCut.symm (ospPantsMap (e p))).2)))).val) = p
      rw [hc, neg_neg, Diffeomorph.apply_symm_apply]
      change e.symm (ospSlabPoint (mobiusCut (mobiusCut.symm (ospPantsMap (e p)))).val) = p
      have hr : mobiusCut (mobiusCut.symm (ospPantsMap (e p))) = ospPantsMap (e p) :=
        mobiusCut.right_inv hp
      rw [hr, ospSlabPoint_pantsMap, e.symm_apply_apply]
    open_source := isOpen_lt
      ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
      continuous_const
    open_target := mobiusCut.open_target.preimage
      (contMDiff_ospPantsMap.continuous.comp e.continuous)
    contMDiffOn_toFun := by
      refine e.symm.contMDiff.comp_contMDiffOn ?_
      refine (ospShiftAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
      rw [← DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff]
      have hg : ContMDiff circleCollarModel ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : Circle × EuclideanHalfSpace 1 => (σ q.1, -q.2.val 0)) :=
        (σ.contMDiff.comp contMDiff_fst).prodMk
          (DifferentialGeometry.Topology.Manifold.contMDiff_halfSpaceOneCoordinate.neg.comp
            contMDiff_snd)
      have hc := contMDiff_mobiusBlowDown.comp_contMDiffOn
        (mobiusSlabAtlas.contMDiff_subtype_val.comp_contMDiffOn
          (mobiusCut.contMDiffOn.comp hg.contMDiffOn (s := circleCollarSource) fun q hq =>
            ⟨by linarith [(show q.2.val 0 < 1 from hq)], by linarith [q.2.2]⟩))
      refine hc.congr fun q hq => ?_
      have hv := hval q hq
      rw [collarClamp_of_mem hq] at hv
      change (ospSlabPoint (mobiusCut (σ q.1, -collarClamp q)).val).val.val = _
      rw [collarClamp_of_mem hq, ospSlabPoint_val (mem_ospSlab_of_mobiusSlab hv)]
      rfl
    contMDiffOn_invFun := by
      have hι : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fun p : planarSet.{u} 3 => ospPantsMap (e p)) :=
        contMDiff_ospPantsMap.comp e.contMDiff
      have hs : ContMDiffOn (𝓡∂ 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun p : planarSet.{u} 3 => mobiusCut.symm (ospPantsMap (e p)))
          {p | ospPantsMap (e p) ∈ mobiusCut.target} :=
        mobiusCut.symm.contMDiffOn.comp hι.contMDiffOn fun p hp => hp
      refine ContMDiffOn.prodMk (σ.symm.contMDiff.comp_contMDiffOn
        (contMDiff_fst.comp_contMDiffOn hs)) ?_
      refine DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.comp
        (contMDiff_snd.neg.comp_contMDiffOn hs) fun p hp => ?_
      change (0 : ℝ) ≤ -(mobiusCut.symm (ospPantsMap (e p))).2
      linarith [hside p hp] }

def pantsCollarOf (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞)
    (hF : ∀ y ∈ κ.target, 0 < ospF (mobiusBlowDown y.val)) :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 3) ∞ where
  toFun q := e.symm (ospSlabPoint (κ q).val)
  invFun p := κ.symm (ospPantsMap (e p))
  source := κ.source
  target := {p | ospPantsMap (e p) ∈ κ.target}
  map_source' q hq := by
    change ospPantsMap (e (e.symm (ospSlabPoint (κ q).val))) ∈ κ.target
    rw [e.apply_symm_apply, pantsMap_ospSlabPoint (hF _ (κ.map_source hq)).le]
    exact κ.map_source hq
  map_target' p hp := κ.map_target hp
  left_inv' q hq := by
    have hl : κ.symm (κ q) = q := κ.left_inv hq
    change κ.symm (ospPantsMap (e (e.symm (ospSlabPoint (κ q).val)))) = q
    rw [e.apply_symm_apply, pantsMap_ospSlabPoint (hF _ (κ.map_source hq)).le, hl]
  right_inv' p hp := by
    have hr : κ (κ.symm (ospPantsMap (e p))) = ospPantsMap (e p) := κ.right_inv hp
    change e.symm (ospSlabPoint (κ (κ.symm (ospPantsMap (e p)))).val) = p
    rw [hr, ospSlabPoint_pantsMap, e.symm_apply_apply]
  open_source := κ.open_source
  open_target := κ.open_target.preimage (contMDiff_ospPantsMap.continuous.comp e.continuous)
  contMDiffOn_toFun := by
    refine e.symm.contMDiff.comp_contMDiffOn ?_
    exact contMDiffOn_ospSlabPoint.comp κ.contMDiffOn fun q hq => hF _ (κ.map_source hq)
  contMDiffOn_invFun :=
    κ.symm.contMDiffOn.comp (contMDiff_ospPantsMap.comp e.contMDiff).contMDiffOn fun p hp => hp

theorem pantsCollarOf_apply (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞)
    (hF : ∀ y ∈ κ.target, 0 < ospF (mobiusBlowDown y.val)) {q : Circle × EuclideanHalfSpace 1}
    (hq : q ∈ κ.source) : ospPantsMap (e (pantsCollarOf e κ hF q)) = κ q := by
  change ospPantsMap (e (e.symm (ospSlabPoint (κ q).val))) = κ q
  rw [e.apply_symm_apply, pantsMap_ospSlabPoint (hF _ (κ.map_source hq)).le]

theorem pantsCutCollar_apply (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (t : Circle) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    ospPantsMap (e (pantsCutCollar e σ (t, halfPoint s hs))) = mobiusCut (σ t, -s) := by
  have hq : (t, halfPoint s hs) ∈ circleCollarSource := hs1
  have hc : CoreDecomposition.collarClamp (t, halfPoint s hs) = s := by
    rw [CoreDecomposition.collarClamp_of_mem hq]
    rfl
  change ospPantsMap (e (e.symm (ospSlabPoint (mobiusCut (σ t,
    -CoreDecomposition.collarClamp (t, halfPoint s hs))).val))) = _
  rw [hc, e.apply_symm_apply, pantsMap_ospSlabPoint (ospF_cut_nonneg hs hs1)]

theorem width_eq_one_of_ospF {x : MobiusBand} (h : ospF (mobiusBlowDown x) = 0) :
    mobiusWidth (mobiusShearInv x) = 1 := by
  obtain ⟨r, hr0, -, he⟩ := exists_ospF_blowDown_eq x
  rw [h] at he
  have := (mul_eq_zero.mp he.symm).resolve_left hr0.ne'
  linarith

theorem mem_cutTarget_of_ospF {y : slabSet mobiusHeight 0 2}
    (h : ospF (mobiusBlowDown y.val) = 0) : y ∈ mobiusCut.target := by
  have hw := width_eq_one_of_ospF h
  change 49 / 64 < mobiusWidth (mobiusShearInv y.val) ∧ mobiusWidth (mobiusShearInv y.val) < 81 / 64
  rw [hw]
  norm_num

theorem cut_symm_snd_of_ospF {y : slabSet mobiusHeight 0 2}
    (h : ospF (mobiusBlowDown y.val) = 0) : (mobiusCut.symm y).2 = 0 := by
  have hw := width_eq_one_of_ospF h
  have hn : ‖mobiusVec (mobiusShearInv y.val)‖ = 1 := by
    have h2 := norm_mobiusVec_sq (mobiusShearInv y.val)
    rw [hw] at h2
    nlinarith [norm_nonneg (mobiusVec (mobiusShearInv y.val))]
  change 8 * (1 - ‖mobiusVec (mobiusShearInv y.val)‖) = 0
  rw [hn]
  norm_num

theorem mobiusCut_symm_fst_of_ospF {y : slabSet mobiusHeight 0 2}
    (h : ospF (mobiusBlowDown y.val) = 0) : mobiusCut ((mobiusCut.symm y).1, 0) = y := by
  have hr : mobiusCut (mobiusCut.symm y) = y := mobiusCut.right_inv (mem_cutTarget_of_ospF h)
  have he : ((mobiusCut.symm y).1, (0 : ℝ)) = mobiusCut.symm y :=
    Prod.ext rfl (cut_symm_snd_of_ospF h).symm
  rw [he, hr]

theorem ospF_mobiusCut_zero (t : Circle) : ospF (mobiusBlowDown (mobiusCut (t, 0)).val) = 0 := by
  rw [mobiusCut_apply_val (by norm_num) (by norm_num)]
  obtain ⟨r, -, -, he⟩ := exists_ospF_blowDown_eq (mobiusShear (mobiusBandCover (t, 1 - 0 / 8)))
  rw [he, mobiusShearInv_shear, mobiusWidth_cover]
  norm_num

theorem contMDiff_pantsZero (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (j : Fin 3) : ContMDiff (𝓡 1) (𝓡∂ 2) ∞
      (fun t : Circle => ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero)))) := by
  have h1 : ContMDiff (𝓡 1) circleCollarModel ∞ (fun t : Circle => (t, halfZero)) :=
    contMDiff_id.prodMk contMDiff_const
  have h2 : ContMDiff (𝓡 1) (SurfaceModel.model pantsPlanarBase.{u}.surface.kind) ∞
      (fun t : Circle => pantsPlanarBase.{u}.collar j (t, halfZero)) :=
    (pantsPlanarBase.{u}.collar j).contMDiffOn.comp_contMDiff h1 fun t => by
      rw [pantsPlanarBase.{u}.source_eq j]
      exact halfZero_mem_circleCollarSource t
  exact contMDiff_ospPantsMap.comp (e.contMDiff.comp h2)

theorem collar_zero_mem_target (j : Fin 3) (t : Circle) :
    pantsPlanarBase.{u}.collar j (t, halfZero) ∈ (pantsPlanarBase.{u}.collar j).target :=
  (pantsPlanarBase.{u}.collar j).map_source (by
    rw [pantsPlanarBase.{u}.source_eq j]
    exact halfZero_mem_circleCollarSource t)

theorem collar_symm_zero (j : Fin 3) (t : Circle) :
    (pantsPlanarBase.{u}.collar j).symm (pantsPlanarBase.{u}.collar j (t, halfZero)) =
      (t, halfZero) :=
  (pantsPlanarBase.{u}.collar j).left_inv (by
    rw [pantsPlanarBase.{u}.source_eq j]
    exact halfZero_mem_circleCollarSource t)

theorem exists_cut_match (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1) (jc : Fin 3)
    (hF : ∀ t, ospF (e (pantsPlanarBase.{u}.collar jc (t, halfZero))).val.val = 0)
    (hR : ∀ y : slabSet mobiusHeight 0 2, ospF (mobiusBlowDown y.val) = 0 →
      ∃ t, ospPantsMap (e (pantsPlanarBase.{u}.collar jc (t, halfZero))) = y) :
    ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t,
      mobiusCut (σ t, 0) = ospPantsMap (e (pantsPlanarBase.{u}.collar jc (t, halfZero))) := by
  set α := fun t : Circle => ospPantsMap (e (pantsPlanarBase.{u}.collar jc (t, halfZero)))
  have hαF : ∀ t, ospF (mobiusBlowDown (α t).val) = 0 := fun t => by
    change ospF (mobiusBlowDown (mobiusBlowUp _)) = 0
    rw [mobiusBlowDown_blowUp]
    exact hF t
  have hgF : ∀ t', 0 ≤ ospF (mobiusBlowDown (mobiusCut (t', 0)).val) := fun t' =>
    (ospF_mobiusCut_zero t').ge
  have hgmem : ∀ t', e.symm (ospSlabPoint (mobiusCut (t', 0)).val) =
      pantsPlanarBase.{u}.collar jc
        (((pantsPlanarBase.{u}.collar jc).symm (e.symm (ospSlabPoint (mobiusCut (t', 0)).val))).1,
          halfZero) := by
    intro t'
    obtain ⟨t₁, ht₁⟩ := hR _ (ospF_mobiusCut_zero t')
    rw [← ht₁, ospSlabPoint_pantsMap]
    erw [e.symm_apply_apply, collar_symm_zero]
  refine ⟨{ toFun := fun t => (mobiusCut.symm (α t)).1
            invFun := fun t' => ((pantsPlanarBase.{u}.collar jc).symm
              (e.symm (ospSlabPoint (mobiusCut (t', 0)).val))).1
            left_inv := fun t => ?_
            right_inv := fun t' => ?_
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }, fun t => ?_⟩
  · change ((pantsPlanarBase.{u}.collar jc).symm
      (e.symm (ospSlabPoint (mobiusCut ((mobiusCut.symm (α t)).1, 0)).val))).1 = t
    rw [mobiusCut_symm_fst_of_ospF (hαF t)]
    change ((pantsPlanarBase.{u}.collar jc).symm (e.symm (ospSlabPoint
      (ospPantsMap (e (pantsPlanarBase.{u}.collar jc (t, halfZero)))).val))).1 = t
    rw [ospSlabPoint_pantsMap]
    erw [e.symm_apply_apply, collar_symm_zero]
  · have h1 := hgmem t'
    change (mobiusCut.symm (ospPantsMap (e (pantsPlanarBase.{u}.collar jc
      (((pantsPlanarBase.{u}.collar jc).symm (e.symm (ospSlabPoint (mobiusCut (t', 0)).val))).1,
        halfZero))))).1 = t'
    rw [← h1]
    erw [e.apply_symm_apply]
    rw [pantsMap_ospSlabPoint (hgF t')]
    have hl : mobiusCut.symm (mobiusCut (t', 0)) = (t', 0) :=
      mobiusCut.left_inv ⟨by norm_num, by norm_num⟩
    rw [hl]
  · refine (contMDiff_fst (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))).comp ?_
    exact mobiusCut.symm.contMDiffOn.comp_contMDiff (contMDiff_pantsZero e jc) fun t =>
      mem_cutTarget_of_ospF (hαF t)
  · refine (contMDiff_fst (I := 𝓡 1) (J := 𝓡∂ 1)).comp ?_
    have hs : ContMDiff (𝓡 1) (𝓡∂ 2) ∞
        (fun t' : Circle => ospSlabPoint (mobiusCut (t', 0)).val) := by
      refine (ospShiftAtlas.contMDiff_iff_subtype_val _).mpr ?_
      rw [← DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff]
      have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
          (fun t' : Circle => mobiusBlowDown (mobiusCut (t', 0)).val) :=
        contMDiff_mobiusBlowDown.comp (mobiusSlabAtlas.contMDiff_subtype_val.comp
          (mobiusCut.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
            fun t' => ⟨by norm_num, by norm_num⟩))
      refine hc.congr fun t' => ?_
      exact ospSlabPoint_val (mem_ospSlab_of_mobiusSlab (hgF t'))
    exact (pantsPlanarBase.{u}.collar jc).symm.contMDiffOn.comp_contMDiff
      (e.symm.contMDiff.comp hs) fun t' => by
        change e.symm (ospSlabPoint (mobiusCut (t', 0)).val) ∈
          (pantsPlanarBase.{u}.collar jc).target
        rw [hgmem t']
        exact collar_zero_mem_target jc _
  · exact mobiusCut_symm_fst_of_ospF (hαF t)

theorem exists_level_match (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1) (j : Fin 3)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞)
    (hsrc : κ.source = circleCollarSource)
    (hF : ∀ y ∈ κ.target, 0 < ospF (mobiusBlowDown y.val))
    (hR1 : ∀ t, ∃ t', κ (t', halfZero) = ospPantsMap (e (pantsPlanarBase.{u}.collar j
      (t, halfZero))))
    (hR2 : ∀ t', ∃ t, ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
      κ (t', halfZero)) :
    ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t,
      κ (σ t, halfZero) = ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))) := by
  set α := fun t : Circle => ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero)))
  have hsrc0 : ∀ t', (t', halfZero) ∈ κ.source := fun t' => by
    rw [hsrc]
    exact halfZero_mem_circleCollarSource t'
  have hl : ∀ t', κ.symm (κ (t', halfZero)) = (t', halfZero) := fun t' => κ.left_inv (hsrc0 t')
  have hαt : ∀ t, α t ∈ κ.target := fun t => by
    obtain ⟨t', ht'⟩ := hR1 t
    change ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))) ∈ κ.target
    rw [← ht']
    exact κ.map_source (hsrc0 t')
  have hαe : ∀ t, κ ((κ.symm (α t)).1, halfZero) = α t := fun t => by
    obtain ⟨t', ht'⟩ := hR1 t
    change κ ((κ.symm (ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))))).1,
      halfZero) = ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero)))
    rw [← ht', hl]
  have hgF : ∀ t', 0 ≤ ospF (mobiusBlowDown (κ (t', halfZero)).val) := fun t' =>
    (hF _ (κ.map_source (hsrc0 t'))).le
  have hgmem : ∀ t', e.symm (ospSlabPoint (κ (t', halfZero)).val) =
      pantsPlanarBase.{u}.collar j
        (((pantsPlanarBase.{u}.collar j).symm (e.symm (ospSlabPoint (κ (t', halfZero)).val))).1,
          halfZero) := by
    intro t'
    obtain ⟨t₁, ht₁⟩ := hR2 t'
    rw [← ht₁, ospSlabPoint_pantsMap]
    erw [e.symm_apply_apply, collar_symm_zero]
  refine ⟨{ toFun := fun t => (κ.symm (α t)).1
            invFun := fun t' => ((pantsPlanarBase.{u}.collar j).symm
              (e.symm (ospSlabPoint (κ (t', halfZero)).val))).1
            left_inv := fun t => ?_
            right_inv := fun t' => ?_
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }, fun t => hαe t⟩
  · change ((pantsPlanarBase.{u}.collar j).symm
      (e.symm (ospSlabPoint (κ ((κ.symm (α t)).1, halfZero)).val))).1 = t
    rw [hαe t]
    change ((pantsPlanarBase.{u}.collar j).symm (e.symm (ospSlabPoint
      (ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero)))).val))).1 = t
    rw [ospSlabPoint_pantsMap]
    erw [e.symm_apply_apply, collar_symm_zero]
  · have h1 := hgmem t'
    change (κ.symm (ospPantsMap (e (pantsPlanarBase.{u}.collar j
      (((pantsPlanarBase.{u}.collar j).symm (e.symm (ospSlabPoint (κ (t', halfZero)).val))).1,
        halfZero))))).1 = t'
    rw [← h1]
    erw [e.apply_symm_apply]
    rw [pantsMap_ospSlabPoint (hgF t'), hl]
  · refine (contMDiff_fst (I := 𝓡 1) (J := 𝓡∂ 1)).comp ?_
    exact κ.symm.contMDiffOn.comp_contMDiff (contMDiff_pantsZero e j) hαt
  · refine (contMDiff_fst (I := 𝓡 1) (J := 𝓡∂ 1)).comp ?_
    have hκ0 : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ (fun t' : Circle => κ (t', halfZero)) :=
      κ.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) hsrc0
    have hs : ContMDiff (𝓡 1) (𝓡∂ 2) ∞
        (fun t' : Circle => ospSlabPoint (κ (t', halfZero)).val) := fun t' =>
      (contMDiffOn_ospSlabPoint.contMDiffAt (IsOpen.mem_nhds (isOpen_lt continuous_const
        (contDiff_ospF.continuous.comp (contMDiff_mobiusBlowDown.continuous.comp
          continuous_subtype_val))) (hF _ (κ.map_source (hsrc0 t'))))).comp t' hκ0.contMDiffAt
    exact (pantsPlanarBase.{u}.collar j).symm.contMDiffOn.comp_contMDiff
      (e.symm.contMDiff.comp hs) fun t' => by
        change e.symm (ospSlabPoint (κ (t', halfZero)).val) ∈ (pantsPlanarBase.{u}.collar j).target
        rw [hgmem t']
        exact collar_zero_mem_target j _

theorem ospF_pos_of_height {y : slabSet mobiusHeight 0 2}
    (h : mobiusHeight y.val < 1 / 4 ∨ 7 / 4 < mobiusHeight y.val) :
    0 < ospF (mobiusBlowDown y.val) := by
  by_contra hc
  have hle : ospF (mobiusBlowDown y.val) ≤ 17 / 1600 := by linarith [le_of_not_gt hc]
  have hb := ospU_bounds_of_ospF_le hle
  rw [← mobiusHeight_eq_ospU] at hb
  rcases h with h | h <;> linarith [hb.1, hb.2]

theorem pantsMap_height (z : slabSet ospFun 0 1) :
    mobiusHeight (ospPantsMap z).val = ospU z.val.val :=
  mobiusHeight_blowUp

theorem ospFun_slabPoint {y : slabSet mobiusHeight 0 2} (hF : 0 ≤ ospF (mobiusBlowDown y.val)) :
    ospFun (ospSlabPoint y.val).val = ospHeight (mobiusBlowDown y.val) := by
  change ospHeight (ospSlabPoint y.val).val.val = _
  rw [ospSlabPoint_val (mem_ospSlab_of_mobiusSlab hF)]

theorem exists_pants_of_hole (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (he : ∀ j t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
      if j.val = 0 then 1 else 0) (jc : Fin 3)
    (hU : ∀ j, j ≠ 0 → j ≠ jc → ∀ t,
      ospU (e (pantsPlanarBase.{u}.collar j (t, halfZero))).val.val = 0)
    (y : slabSet mobiusHeight 0 2) (hy : ospF (mobiusBlowDown y.val) = 0) :
    ∃ t, ospPantsMap (e (pantsPlanarBase.{u}.collar jc (t, halfZero))) = y := by
  have hdom : (mobiusBlowDown y.val).im < 123 / 70 := im_lt_of_ospF_le (by rw [hy]; norm_num)
  have hfun : ospFun (ospSlabPoint y.val).val = 0 := by
    rw [ospFun_slabPoint hy.ge, ospHeight_eq_zero_iff hdom]
    exact Or.inr hy
  obtain ⟨j, t, hjt⟩ := exists_collar_of_boundary e _ (Or.inl hfun)
  have hj0 : j ≠ 0 := by
    intro h0
    have := he j t
    rw [hjt, hfun, h0] at this
    norm_num at this
  have hjc : j = jc := by
    by_contra hne
    have h1 := hU j hj0 hne t
    rw [hjt, ospSlabPoint_val (mem_ospSlab_of_mobiusSlab hy.ge)] at h1
    have hb := mobiusHeight_bounds_of_width (x := y.val) (by
      rw [width_eq_one_of_ospF hy]; norm_num)
    rw [mobiusHeight_eq_ospU, h1] at hb
    linarith [hb.1]
  subst hjc
  exact ⟨t, by rw [hjt, pantsMap_ospSlabPoint hy.ge]⟩


theorem exists_pants_of_level (e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1)
    (he : ∀ j t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
      if j.val = 0 then 1 else 0) (jc : Fin 3) (hjc0 : jc ≠ 0)
    (hF : ∀ t, ospF (e (pantsPlanarBase.{u}.collar jc (t, halfZero))).val.val = 0)
    (j : Fin 3) (hj : j ≠ jc) (y : slabSet mobiusHeight 0 2)
    (hy : mobiusHeight y.val = if j = 0 then 2 else 0) :
    ∃ t, ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))) = y := by
  have hFy : 0 < ospF (mobiusBlowDown y.val) := by
    apply ospF_pos_of_height
    split_ifs at hy <;> rw [hy] <;> norm_num
  have hUy : ospU (mobiusBlowDown y.val) = if j = 0 then 2 else 0 := by
    rw [← mobiusHeight_eq_ospU, hy]
  have hdom : (mobiusBlowDown y.val).im < 123 / 70 :=
    ospSlab_subset_ospDom (mem_ospSlab_of_mobiusSlab hFy.le)
  have hfun : ospFun (ospSlabPoint y.val).val = if j = 0 then 1 else 0 := by
    rw [ospFun_slabPoint hFy.le]
    by_cases hj0 : j = 0
    · simp only [hj0, ↓reduceIte] at hUy ⊢
      exact (ospHeight_eq_one_iff hdom).mpr hUy
    · simp only [hj0, ↓reduceIte] at hUy ⊢
      exact (ospHeight_eq_zero_iff hdom).mpr (Or.inl hUy)
  obtain ⟨j', t, hjt⟩ := exists_collar_of_boundary e _ (by
    rw [hfun]; split_ifs <;> simp)
  have hj' : j' = j := by
    have h1 := he j' t
    rw [hjt, hfun] at h1
    by_cases hj0 : j = 0
    · subst hj0
      simp only [↓reduceIte] at h1
      by_contra hne
      have : j'.val ≠ 0 := fun h => hne (Fin.ext h)
      simp only [this, ↓reduceIte] at h1
      norm_num at h1
    · simp only [hj0, ↓reduceIte] at h1
      have hj'0 : j' ≠ 0 := by
        intro h0
        rw [h0] at h1
        norm_num at h1
      have hj'c : j' ≠ jc := by
        intro hc
        have := hF t
        rw [← hc, hjt, ospSlabPoint_val (mem_ospSlab_of_mobiusSlab hFy.le)] at this
        linarith
      revert hj0 hj'0 hj'c hj hjc0
      fin_cases j <;> fin_cases j' <;> fin_cases jc <;> simp
  subst hj'
  exact ⟨t, by rw [hjt, pantsMap_ospSlabPoint hFy.le]⟩

theorem isPreconnected_circleCollarSource : IsPreconnected circleCollarSource := by
  have h : {h : EuclideanHalfSpace 1 | h.val 0 < 1} =
      DifferentialGeometry.Topology.Manifold.halfSpaceOneLift '' Ico 0 1 := by
    ext h
    constructor
    · intro hh
      exact ⟨h.val 0, ⟨h.2, hh⟩, halfSpaceOneLift_val_zero' h⟩
    · rintro ⟨t, ht, rfl⟩
      change max t 0 < 1
      rw [max_eq_left ht.1]
      exact ht.2
  have hc : IsPreconnected {h : EuclideanHalfSpace 1 | h.val 0 < 1} := by
    rw [h]
    exact isPreconnected_Ico.image _
      (DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.continuousOn.mono
        fun t ht => ht.1)
  have he : circleCollarSource =
      (univ : Set Circle) ×ˢ {h : EuclideanHalfSpace 1 | h.val 0 < 1} := by
    ext q
    simp [circleCollarSource]
  rw [he]
  exact isPreconnected_univ.prod hc

theorem col_target_side
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞) (hsrc : κ.source = circleCollarSource)
    (hη : ∀ x ∈ κ.target, mobiusHeight x.val < 1 / 4 ∨ 2 - 1 / 4 < mobiusHeight x.val) (b : Bool)
    (hlev : ∀ t, mobiusHeight (κ (t, halfZero)).val = if b then 2 else 0) :
    ∀ x ∈ κ.target, if b then 7 / 4 < mobiusHeight x.val else mobiusHeight x.val < 1 / 4 := by
  have hpc : IsPreconnected κ.target := by
    rw [← κ.toPartialEquiv.image_source_eq_target, hsrc]
    exact isPreconnected_circleCollarSource.image _
      (by rw [← hsrc]; exact κ.contMDiffOn.continuousOn)
  have hcont : Continuous fun x : slabSet mobiusHeight 0 2 => mobiusHeight x.val :=
    contMDiff_mobiusHeight.continuous.comp continuous_subtype_val
  have hsub : κ.target ⊆ {x | mobiusHeight x.val < 1 / 4} ∪ {x | 7 / 4 < mobiusHeight x.val} :=
    fun x hx => by
      rcases hη x hx with h | h
      · exact Or.inl h
      · right
        change 7 / 4 < mobiusHeight x.val
        linarith
  have hdisj : Disjoint {x : slabSet mobiusHeight 0 2 | mobiusHeight x.val < 1 / 4}
      {x | 7 / 4 < mobiusHeight x.val} := by
    rw [Set.disjoint_left]
    intro x h1 h2
    change mobiusHeight x.val < 1 / 4 at h1
    change 7 / 4 < mobiusHeight x.val at h2
    linarith
  obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
  have h0 : κ (t₀, halfZero) ∈ κ.target :=
    κ.map_source (by rw [hsrc]; exact halfZero_mem_circleCollarSource t₀)
  rcases hpc.subset_or_subset (isOpen_lt hcont continuous_const)
    (isOpen_lt continuous_const hcont) hdisj hsub with h | h
  · cases b
    · intro x hx
      exact h hx
    · exfalso
      have := h h0
      change mobiusHeight (κ (t₀, halfZero)).val < 1 / 4 at this
      rw [hlev] at this
      norm_num at this
  · cases b
    · exfalso
      have := h h0
      change 7 / 4 < mobiusHeight (κ (t₀, halfZero)).val at this
      rw [hlev] at this
      norm_num at this
    · intro x hx
      exact h hx

def levelKappa (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞) :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞ :=
  (σ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans κ

theorem levelKappa_apply (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞) (q : Circle × EuclideanHalfSpace 1) :
    levelKappa σ κ q = κ (σ q.1, q.2) := rfl

theorem levelKappa_source (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞) (hsrc : κ.source = circleCollarSource) :
    (levelKappa σ κ).source = circleCollarSource := by
  ext q
  constructor
  · rintro ⟨-, h⟩
    have h' : (σ q.1, q.2) ∈ κ.source := h
    rw [hsrc] at h'
    exact h'
  · intro h
    refine ⟨mem_univ _, ?_⟩
    change (σ q.1, q.2) ∈ κ.source
    rw [hsrc]
    exact h

theorem levelKappa_target_subset (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞) : (levelKappa σ κ).target ⊆ κ.target :=
  fun y (hy : y ∈ (levelKappa σ κ).target) => hy.1

end PantsCollars

section Split

local instance instSlabCharted'' : ChartedSpace (EuclideanHalfSpace 2) (slabSet ospFun 0 1) :=
  ospShiftAtlas.toChartedSpace

local instance instSlabManifold'' : IsManifold (𝓡∂ 2) ∞ (slabSet ospFun 0 1) :=
  ospShiftAtlas.isManifold

local instance instKCharted'' : ChartedSpace (EuclideanHalfSpace 2) (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.toChartedSpace

local instance instKManifold'' : IsManifold (𝓡∂ 2) ∞ (slabSet mobiusHeight 0 2) :=
  mobiusSlabAtlas.isManifold

open CoreDecomposition in
theorem mobiusSlab_split_quarter :
    letI := mobiusSlabAtlas.toChartedSpace
    ∀ (col : Bool → PartialDiffeomorph circleCollarModel (𝓡∂ 2)
        (Circle × EuclideanHalfSpace 1) (slabSet mobiusHeight 0 2) ∞),
      (∀ b, (col b).source = circleCollarSource) →
      (∀ b t, mobiusHeight (col b (t, halfZero)) = if b then 2 else 0) →
      (∀ b, ∀ x ∈ (col b).target, mobiusHeight x < 1 / 4 ∨ 2 - 1 / 4 < mobiusHeight x) →
      (∀ b (x : slabSet mobiusHeight 0 2), mobiusHeight x = (if b then 2 else 0) →
        ∃ t, col b (t, halfZero) = x) →
      ∃ (ιM : mobiusBase.{u}.surface.Carrier → slabSet mobiusHeight 0 2) (Q : PlanarBase.{u} 3)
        (ιQ : Q.surface.Carrier → slabSet mobiusHeight 0 2)
        (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ)
          (slabSet mobiusHeight 0 2) ∞) (jc : Fin 3) (lv : Fin 3 → Bool),
        Q.surface.kind = .withBoundary ∧
        Manifold.IsSmoothEmbedding (SurfaceModel.model mobiusBase.{u}.surface.kind) (𝓡∂ 2) ∞ ιM ∧
        Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind) (𝓡∂ 2) ∞ ιQ ∧
        c.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
        (∀ x, x ∈ c.target ∨ x ∈ range ιM → 1 / 4 ≤ mobiusHeight x ∧ mobiusHeight x ≤ 2 - 1 / 4) ∧
        range ιM ∪ range ιQ = univ ∧ (∀ x x', ιM x = ιQ x' → ∃ t, ιM x = c (t, 0)) ∧
        (∀ t s (hs : 0 ≤ s), s < 1 →
          ιM (mobiusBase.{u}.collar (t, halfPoint s hs)) = c (t, s)) ∧
        (∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
          ιQ (Q.collar jc (t, halfPoint s hs)) = c (σ t, -s)) ∧
        (∀ j, j ≠ jc → ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
          ιQ (Q.collar j (t, halfPoint s hs)) = col (lv j) (σ t, halfPoint s hs)) ∧
        (∀ j j', j ≠ jc → j' ≠ jc → lv j = lv j' → j = j') ∧
        (∀ x, mobiusHeight (ιQ x) = 0 ∨ mobiusHeight (ιQ x) = 2 →
          ∃ j t, j ≠ jc ∧ x = Q.collar j (t, halfZero)) ∧
        ∃ W : Set (slabSet mobiusHeight 0 2), IsOpen W ∧
          (∀ x, mobiusHeight (ιQ x) = 0 ∨ mobiusHeight (ιQ x) = 2 → ιQ x ∈ W) ∧
          ∃ ψ : slabSet mobiusHeight 0 2 → Q.surface.Carrier,
            ContMDiffOn (𝓡∂ 2) (SurfaceModel.model Q.surface.kind) ∞ ψ W ∧
            ∀ y ∈ W, ιQ (ψ y) = y := by
  let := mobiusSlabAtlas.toChartedSpace
  intro col hsrc hlev htgt hcov
  obtain ⟨e, he⟩ := exists_ospPants_shift.{u}
  obtain ⟨jc, hjc0, hFjc, hUo⟩ := exists_jc e he
  have hside : ∀ b, ∀ x ∈ (col b).target,
      if b then 7 / 4 < mobiusHeight x.val else mobiusHeight x.val < 1 / 4 := fun b =>
    col_target_side (col b) (hsrc b) (htgt b) b (hlev b)
  have hFcol : ∀ b, ∀ y ∈ (col b).target, 0 < ospF (mobiusBlowDown y.val) := fun b y hy => by
    apply ospF_pos_of_height
    have := hside b y hy
    cases b
    · exact Or.inl this
    · exact Or.inr this
  have hlevz : ∀ j, j ≠ jc → ∀ t, mobiusHeight
      (ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero)))).val =
        if decide (j = 0) then 2 else 0 := by
    intro j hj t
    rw [pantsMap_height]
    by_cases hj0 : j = 0
    · simp only [hj0, decide_true, ↓reduceIte]
      have h1 := he 0 t
      simp only [Fin.isValue, Fin.val_zero, ↓reduceIte] at h1
      rw [← hj0] at h1 ⊢
      exact (ospHeight_eq_one_iff (e (pantsPlanarBase.{u}.collar j (t, halfZero))).val.2).mp h1
    · simp only [hj0, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hUo j hj0 hj t
  have hmatch : ∀ j, j ≠ jc → ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t,
      col (decide (j = 0)) (σ t, halfZero) =
        ospPantsMap (e (pantsPlanarBase.{u}.collar j (t, halfZero))) := by
    intro j hj
    refine exists_level_match e j (col (decide (j = 0))) (hsrc _) (hFcol _) (fun t => ?_)
      (fun t' => ?_)
    · obtain ⟨t', ht'⟩ := hcov (decide (j = 0)) _ (hlevz j hj t)
      exact ⟨t', ht'⟩
    · refine exists_pants_of_level e he jc hjc0 hFjc j hj _ ?_
      rw [hlev]
      by_cases hj0 : j = 0 <;> simp [hj0]
  choose σL hσL using hmatch
  obtain ⟨σc, hσc⟩ := exists_cut_match e jc hFjc
    (exists_pants_of_hole e he jc hUo)
  have hFlev : ∀ j (hj : j ≠ jc), ∀ y ∈ (levelKappa (σL j hj) (col (decide (j = 0)))).target,
      0 < ospF (mobiusBlowDown y.val) := fun j hj y hy =>
    hFcol _ y (levelKappa_target_subset _ _ hy)
  let newcol : Fin 3 → PartialDiffeomorph circleCollarModel (𝓡∂ 2)
      (Circle × EuclideanHalfSpace 1) (planarSet.{u} 3) ∞ := fun j =>
    if hj : j = jc then pantsCutCollar e σc
    else pantsCollarOf e (levelKappa (σL j hj) (col (decide (j = 0)))) (hFlev j hj)
  have hnewc : newcol jc = pantsCutCollar e σc := by simp [newcol]
  have hnewl : ∀ j (hj : j ≠ jc), newcol j =
      pantsCollarOf e (levelKappa (σL j hj) (col (decide (j = 0)))) (hFlev j hj) := by
    intro j hj
    simp [newcol, hj]
  have hsrc' : ∀ j, (newcol j).source = circleCollarSource := by
    intro j
    by_cases hj : j = jc
    · rw [hj, hnewc]
      rfl
    · rw [hnewl j hj]
      exact levelKappa_source _ _ (hsrc _)
  have hzero : ∀ j t, newcol j (t, halfZero) = pantsPlanarBase.{u}.collar j (t, halfZero) := by
    intro j t
    by_cases hj : j = jc
    · subst hj
      rw [hnewc]
      have hq : (t, halfZero) ∈ circleCollarSource := halfZero_mem_circleCollarSource t
      have hc0 : collarClamp (t, halfZero) = 0 := by
        rw [collarClamp_of_mem hq]
        rfl
      change e.symm (ospSlabPoint (mobiusCut (σc t, -collarClamp (t, halfZero))).val) = _
      rw [hc0, neg_zero, hσc t, ospSlabPoint_pantsMap]
      exact e.symm_apply_apply _
    · rw [hnewl j hj]
      change e.symm (ospSlabPoint (levelKappa (σL j hj) (col (decide (j = 0)))
        (t, halfZero)).val) = _
      rw [levelKappa_apply, hσL j hj t, ospSlabPoint_pantsMap]
      exact e.symm_apply_apply _
  have htgt' : ∀ j, ∀ p ∈ (newcol j).target, ∃ y, y = ospPantsMap (e p) ∧
      ((j = jc ∧ y ∈ mobiusCut.target) ∨ (j ≠ jc ∧ y ∈ (col (decide (j = 0))).target)) := by
    intro j p hp
    refine ⟨_, rfl, ?_⟩
    by_cases hj : j = jc
    · rw [hj, hnewc] at hp
      exact Or.inl ⟨hj, hp⟩
    · rw [hnewl j hj] at hp
      exact Or.inr ⟨hj, levelKappa_target_subset _ _ hp⟩
  have hdisj : Pairwise fun i j => Disjoint (newcol i).target (newcol j).target := by
    intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    obtain ⟨y, rfl, hi⟩ := htgt' i p hpi
    obtain ⟨y', rfl, hj⟩ := htgt' j p hpj
    have hcut : ∀ y : slabSet mobiusHeight 0 2, y ∈ mobiusCut.target →
        1 / 4 < mobiusHeight y.val ∧ mobiusHeight y.val < 7 / 4 := fun y hy =>
      mobiusHeight_bounds_of_width hy.2
    rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
    · exact hij (hi1.trans hj1.symm)
    · have h1 := hcut _ hi2
      have h2 := hside _ _ hj2
      split_ifs at h2 <;> linarith [h1.1, h1.2]
    · have h1 := hcut _ hj2
      have h2 := hside _ _ hi2
      split_ifs at h2 <;> linarith [h1.1, h1.2]
    · have h1 := hside _ _ hi2
      have h2 := hside _ _ hj2
      have hne : decide (i = 0) ≠ decide (j = 0) := by
        intro hdec
        apply hij
        revert hi1 hj1 hjc0 hdec
        fin_cases i <;> fin_cases j <;> fin_cases jc <;> simp
      cases hdi : decide (i = 0) <;> cases hdj : decide (j = 0) <;> rw [hdi] at h1 <;>
        rw [hdj] at h2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 <;>
        first | exact absurd (hdi.trans hdj.symm) hne | linarith
  let Q := recollarBase pantsPlanarBase.{u} newcol hsrc' hzero hdisj
  have hQc : ∀ j, Q.collar j = newcol j := fun j => rfl
  have hιQ : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind) (𝓡∂ 2) ∞
      (fun p : Q.surface.Carrier => ospPantsMap (e p)) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp ospPantsMap
      isSmoothEmbedding_ospPantsMap e
  refine ⟨fun x => mobiusPieceMap.{u} x, Q, fun p => ospPantsMap (e p), mobiusCut, jc,
    fun j => decide (j = 0), rfl, isSmoothEmbedding_mobiusPieceMap, hιQ, rfl, ?_, ?_, ?_,
    fun t s hs hs1 => mobiusPieceMap_collar t s hs hs1, ⟨σc, fun t s hs hs1 => ?_⟩, ?_, ?_, ?_,
    ⟨{y | 0 < ospF (mobiusBlowDown y.val)}, isOpen_lt continuous_const
      (contDiff_ospF.continuous.comp (contMDiff_mobiusBlowDown.continuous.comp
        continuous_subtype_val)), fun x hx => ospF_pos_of_height (by
          rcases hx with h | h
          · left; rw [h]; norm_num
          · right; rw [h]; norm_num),
      fun y => e.symm (ospSlabPoint y.val),
      e.symm.contMDiff.comp_contMDiffOn contMDiffOn_ospSlabPoint, fun y hy => ?_⟩⟩
  · rintro x (hx | ⟨w, rfl⟩)
    · have h := mobiusHeight_bounds_of_mem_cutTarget hx
      exact ⟨h.1, by linarith [h.2]⟩
    · have h := mobiusHeight_bounds_of_mem_range (w := w)
      exact ⟨h.1, by linarith [h.2]⟩
  · refine Set.eq_univ_of_forall fun y => ?_
    by_cases hF : ospF (mobiusBlowDown y.val) ≤ 0
    · left
      obtain ⟨r, hr0, -, hr⟩ := exists_ospF_blowDown_eq y.val
      rw [hr] at hF
      have hw : mobiusWidth (mobiusShearInv y.val) ≤ 1 := by
        by_contra hc
        have : 0 < r * (mobiusWidth (mobiusShearInv y.val) - 1) :=
          mul_pos hr0 (by linarith [lt_of_not_ge hc])
        linarith
      refine ⟨⟨ULift.up (mobiusShearInv y.val), hw⟩, Subtype.ext ?_⟩
      exact mobiusShear_shearInv y.val
    · right
      have hF' : 0 ≤ ospF (mobiusBlowDown y.val) := le_of_lt (lt_of_not_ge hF)
      refine ⟨e.symm (ospSlabPoint y.val), ?_⟩
      change ospPantsMap (e (e.symm (ospSlabPoint y.val))) = y
      rw [e.apply_symm_apply, pantsMap_ospSlabPoint hF']
  · intro x x' hxx
    have hle : ospF (mobiusBlowDown (mobiusPieceMap.{u} x).val) ≤ 0 := by
      obtain ⟨r, hr0, -, hr⟩ := exists_ospF_blowDown_eq (mobiusPieceMap.{u} x).val
      rw [hr]
      have hw : mobiusWidth (mobiusShearInv (mobiusPieceMap.{u} x).val) ≤ 1 := by
        change mobiusWidth (mobiusShearInv (mobiusShear x.val.down)) ≤ 1
        rw [mobiusShearInv_shear]
        exact x.2
      nlinarith
    have hge : 0 ≤ ospF (mobiusBlowDown (mobiusPieceMap.{u} x).val) := by
      rw [show (mobiusPieceMap.{u} x) = ospPantsMap (e x') from hxx]
      rw [show mobiusBlowDown (ospPantsMap (e x')).val = (e x').val.val from
        mobiusBlowDown_blowUp _]
      exact (mem_ospSlab_of_mem (e x')).2.2
    have h0 : ospF (mobiusBlowDown (mobiusPieceMap.{u} x).val) = 0 := le_antisymm hle hge
    exact ⟨_, (mobiusCut_symm_fst_of_ospF h0).symm⟩
  · change ospPantsMap (e (newcol jc (t, halfPoint s hs))) = mobiusCut (σc t, -s)
    rw [hnewc]
    exact pantsCutCollar_apply e σc t s hs hs1
  · intro j hj
    refine ⟨σL j hj, fun t s hs hs1 => ?_⟩
    change ospPantsMap (e (newcol j (t, halfPoint s hs))) = _
    rw [hnewl j hj, pantsCollarOf_apply e _ (hFlev j hj)
      (by rw [levelKappa_source _ _ (hsrc _)]; exact hs1), levelKappa_apply]
  · intro j j' hj hj' hlv
    revert hj hj' hjc0 hlv
    fin_cases j <;> fin_cases j' <;> fin_cases jc <;> simp
  · intro x hx
    have hU : ospU (e x).val.val = 0 ∨ ospU (e x).val.val = 2 := by
      rw [← pantsMap_height]
      exact hx
    have hfun : ospFun (e x).val = 0 ∨ ospFun (e x).val = 1 := by
      rcases hU with h | h
      · left
        exact (ospHeight_eq_zero_iff (e x).val.2).mpr (Or.inl h)
      · right
        exact (ospHeight_eq_one_iff (e x).val.2).mpr h
    obtain ⟨j, t, hjt⟩ := exists_collar_of_boundary e (e x) hfun
    have hx' : x = pantsPlanarBase.{u}.collar j (t, halfZero) := (e.injective hjt).symm
    have hjc : j ≠ jc := by
      rintro rfl
      have hF0 := hFjc t
      rw [hjt] at hF0
      have hb := mobiusHeight_bounds_of_width (x := (ospPantsMap (e x)).val) (by
        rw [width_eq_one_of_ospF (show ospF (mobiusBlowDown (ospPantsMap (e x)).val) = 0 by
          rw [show mobiusBlowDown (ospPantsMap (e x)).val = (e x).val.val from
            mobiusBlowDown_blowUp _]
          exact hF0)]
        norm_num)
      rcases hx with h | h <;> linarith [hb.1, hb.2]
    refine ⟨j, t, hjc, ?_⟩
    rw [hQc, hzero]
    exact hx'
  · change ospPantsMap (e (e.symm (ospSlabPoint y.val))) = y
    rw [e.apply_symm_apply, pantsMap_ospSlabPoint (le_of_lt hy)]


open CoreDecomposition in
theorem exists_mobiusSlab_split :
    letI := mobiusSlabAtlas.toChartedSpace
    ∃ η : ℝ, 0 < η ∧ ∀ (col : Bool → PartialDiffeomorph circleCollarModel (𝓡∂ 2)
        (Circle × EuclideanHalfSpace 1) (slabSet mobiusHeight 0 2) ∞),
      (∀ b, (col b).source = circleCollarSource) →
      (∀ b t, mobiusHeight (col b (t, halfZero)) = if b then 2 else 0) →
      (∀ b, ∀ x ∈ (col b).target, mobiusHeight x < η ∨ 2 - η < mobiusHeight x) →
      (∀ b (x : slabSet mobiusHeight 0 2), mobiusHeight x = (if b then 2 else 0) →
        ∃ t, col b (t, halfZero) = x) →
      ∃ (ιM : mobiusBase.{u}.surface.Carrier → slabSet mobiusHeight 0 2) (Q : PlanarBase.{u} 3)
        (ιQ : Q.surface.Carrier → slabSet mobiusHeight 0 2)
        (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ)
          (slabSet mobiusHeight 0 2) ∞) (jc : Fin 3) (lv : Fin 3 → Bool),
        Q.surface.kind = .withBoundary ∧
        Manifold.IsSmoothEmbedding (SurfaceModel.model mobiusBase.{u}.surface.kind) (𝓡∂ 2) ∞ ιM ∧
        Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind) (𝓡∂ 2) ∞ ιQ ∧
        c.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
        (∀ x, x ∈ c.target ∨ x ∈ range ιM → η ≤ mobiusHeight x ∧ mobiusHeight x ≤ 2 - η) ∧
        range ιM ∪ range ιQ = univ ∧ (∀ x x', ιM x = ιQ x' → ∃ t, ιM x = c (t, 0)) ∧
        (∀ t s (hs : 0 ≤ s), s < 1 →
          ιM (mobiusBase.{u}.collar (t, halfPoint s hs)) = c (t, s)) ∧
        (∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
          ιQ (Q.collar jc (t, halfPoint s hs)) = c (σ t, -s)) ∧
        (∀ j, j ≠ jc → ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
          ιQ (Q.collar j (t, halfPoint s hs)) = col (lv j) (σ t, halfPoint s hs)) ∧
        (∀ j j', j ≠ jc → j' ≠ jc → lv j = lv j' → j = j') ∧
        (∀ x, mobiusHeight (ιQ x) = 0 ∨ mobiusHeight (ιQ x) = 2 →
          ∃ j t, j ≠ jc ∧ x = Q.collar j (t, halfZero)) ∧
        ∃ W : Set (slabSet mobiusHeight 0 2), IsOpen W ∧
          (∀ x, mobiusHeight (ιQ x) = 0 ∨ mobiusHeight (ιQ x) = 2 → ιQ x ∈ W) ∧
          ∃ ψ : slabSet mobiusHeight 0 2 → Q.surface.Carrier,
            ContMDiffOn (𝓡∂ 2) (SurfaceModel.model Q.surface.kind) ∞ ψ W ∧
            ∀ y ∈ W, ιQ (ψ y) = y := by
  exact ⟨1 / 4, by norm_num, mobiusSlab_split_quarter⟩

end Split


end GC.Seifert
