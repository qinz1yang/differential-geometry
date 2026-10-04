import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProduct
import DifferentialGeometry.Topology.Diffeomorph.CompactLocalIsotopy
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
/-!
# A height-zero boundary permutation of the round pants
A circle inversion exchanges the outer circle with the first hole. A compact smooth
isotopy restores the remaining disk inside the annulus between the retained circles.
Explicit Möbius isotopies remove all boundary parameters by disjoint supported twists.
The resulting whole product diffeomorphism swaps ports 0/1 with identity collar germs.
-/
set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ComplexConjugate
universe u

namespace GC.Seifert

def pantsInversion (z : ℂ) : ℂ := (9 / 7 : ℂ) + (60 / 49 : ℂ) / (z - 9 / 7)

theorem pantsInversion_ne {z : ℂ} (hz : z ≠ 9 / 7) : pantsInversion z ≠ 9 / 7 := by
  unfold pantsInversion
  have hw : z - (9 / 7 : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  simpa only [add_ne_left] using div_ne_zero (by norm_num : (60 / 49 : ℂ) ≠ 0) hw

theorem pantsInversion_involutive (z : ℂ) :
    pantsInversion (pantsInversion z) = z := by
  rw [pantsInversion, pantsInversion, add_sub_cancel_left, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ (by norm_num : (60 / 49 : ℂ) ≠ 0)]
  ring

theorem pantsInversion_circle_identity (z : ℂ) (hz : z ≠ 9 / 7) (a r : ℝ) :
    (‖pantsInversion z - (a : ℂ)‖ ^ 2 - r ^ 2) * ‖z - 9 / 7‖ ^ 2 =
      ‖((9 / 7 - a : ℝ) : ℂ) * (z - 9 / 7) + 60 / 49‖ ^ 2 -
        r ^ 2 * ‖z - 9 / 7‖ ^ 2 := by
  have hw : z - (9 / 7 : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have he : (pantsInversion z - (a : ℂ)) * (z - 9 / 7) =
      ((9 / 7 - a : ℝ) : ℂ) * (z - 9 / 7) + 60 / 49 := by
    unfold pantsInversion
    push_cast
    rw [sub_mul, add_mul, div_mul_cancel₀ _ hw]
    ring
  calc
    _ = ‖(pantsInversion z - (a : ℂ)) * (z - 9 / 7)‖ ^ 2 -
        r ^ 2 * ‖z - 9 / 7‖ ^ 2 := by rw [norm_mul]; ring
    _ = _ := by rw [he]

theorem pantsInversion_outer_identity (z : ℂ) (hz : z ≠ 9 / 7) :
    (‖pantsInversion z‖ ^ 2 - 9) * ‖z - 9 / 7‖ ^ 2 =
      -(360 / 49) * (‖z - 3 / 2‖ ^ 2 - 1 / 4) := by
  have h := pantsInversion_circle_identity z hz 0 3
  norm_num at h
  rw [h]
  norm_num [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem pantsInversion_inner_identity (z : ℂ) (hz : z ≠ 9 / 7) :
    (‖pantsInversion z - 3 / 2‖ ^ 2 - 1 / 4) * ‖z - 9 / 7‖ ^ 2 =
      -(10 / 49) * (‖z‖ ^ 2 - 9) := by
  have h := pantsInversion_circle_identity z hz (3 / 2) (1 / 2)
  norm_num at h
  rw [h]
  norm_num [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem pantsInversion_other_identity (z : ℂ) (hz : z ≠ 9 / 7) :
    (‖pantsInversion z - 153 / 184‖ ^ 2 - (15 / 184) ^ 2) * ‖z - 9 / 7‖ ^ 2 =
      (225 / 1127) * (‖z + 3 / 2‖ ^ 2 - 1 / 4) := by
  have h := pantsInversion_circle_identity z hz (153 / 184) (15 / 184)
  norm_num at h ⊢
  rw [h]
  norm_num [Complex.sq_norm, Complex.normSq_apply]
  ring

def pantsInversionRegion : Set ℂ :=
  {z | ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖ ∧ 15 / 184 ≤ ‖z - 153 / 184‖}

theorem pantsInversion_mem_iff (z : ℂ) (hz : z ≠ 9 / 7) :
    pantsInversion z ∈ pantsInversionRegion ↔ z ∈ planarModel 3 := by
  have hd : 0 < ‖z - (9 / 7 : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have ho : ‖pantsInversion z‖ ^ 2 - 9 ≤ 0 ↔ 0 ≤ ‖z - 3 / 2‖ ^ 2 - 1 / 4 := by
    calc
      _ ↔ (‖pantsInversion z‖ ^ 2 - 9) * ‖z - 9 / 7‖ ^ 2 ≤ 0 := by
        simp [mul_nonpos_iff, hd.le, not_le.mpr hd]
      _ ↔ _ := by rw [pantsInversion_outer_identity z hz]; constructor <;> intro h <;> linarith
  have hi : 0 ≤ ‖pantsInversion z - 3 / 2‖ ^ 2 - 1 / 4 ↔ ‖z‖ ^ 2 - 9 ≤ 0 := by
    calc
      _ ↔ 0 ≤ (‖pantsInversion z - 3 / 2‖ ^ 2 - 1 / 4) * ‖z - 9 / 7‖ ^ 2 :=
        (mul_nonneg_iff_of_pos_right hd).symm
      _ ↔ _ := by rw [pantsInversion_inner_identity z hz]; constructor <;> intro h <;> linarith
  have ht : 0 ≤ ‖pantsInversion z - 153 / 184‖ ^ 2 - (15 / 184) ^ 2 ↔
      0 ≤ ‖z + 3 / 2‖ ^ 2 - 1 / 4 := by
    calc
      _ ↔ 0 ≤ (‖pantsInversion z - 153 / 184‖ ^ 2 - (15 / 184) ^ 2) *
          ‖z - 9 / 7‖ ^ 2 := (mul_nonneg_iff_of_pos_right hd).symm
      _ ↔ _ := by
        rw [pantsInversion_other_identity z hz]
        constructor <;> intro h <;> linarith
  rw [mem_planarModel_three]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, sub_neg_eq_add]
  change (‖pantsInversion z‖ ≤ 3 ∧ 1 / 2 ≤ ‖pantsInversion z - 3 / 2‖ ∧
    15 / 184 ≤ ‖pantsInversion z - 153 / 184‖) ↔ _
  have hs₀ : ‖pantsInversion z‖ ≤ 3 ↔ ‖pantsInversion z‖ ^ 2 - 9 ≤ 0 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg (pantsInversion z)]
  have hs₁ : 1 / 2 ≤ ‖pantsInversion z - 3 / 2‖ ↔
      0 ≤ ‖pantsInversion z - 3 / 2‖ ^ 2 - 1 / 4 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg (pantsInversion z - 3 / 2)]
  have hs₂ : 15 / 184 ≤ ‖pantsInversion z - 153 / 184‖ ↔
      0 ≤ ‖pantsInversion z - 153 / 184‖ ^ 2 - (15 / 184) ^ 2 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg (pantsInversion z - 153 / 184)]
  rw [hs₀, hs₁, hs₂, ho, hi, ht]
  constructor
  · rintro ⟨h₁, h₀, h₂⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [norm_nonneg z, norm_nonneg (z - 3 / 2), norm_nonneg (z + 3 / 2)]
  · rintro ⟨h₀, h₁, h₂⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [norm_nonneg z, norm_nonneg (z - 3 / 2), norm_nonneg (z + 3 / 2)]

def pantsDiskMotionCenter (t : ℝ) : ℝ :=
  153 / 184 + (-3 / 2 - 153 / 184) * Real.smoothTransition t

def pantsDiskMotionScale (t : ℝ) : ℝ :=
  1 + (92 / 15 - 1) * Real.smoothTransition t

theorem pantsDiskMotionScale_pos (t : ℝ) : 0 < pantsDiskMotionScale t := by
  have h := Real.smoothTransition.nonneg t
  unfold pantsDiskMotionScale
  linarith

def pantsDiskMotion (t : ℝ) : ℂ ≃ₘ[ℝ] ℂ where
  toFun z := (pantsDiskMotionCenter t : ℂ) +
    (pantsDiskMotionScale t : ℂ) * (z - 153 / 184)
  invFun z := (153 / 184 : ℂ) +
    (z - (pantsDiskMotionCenter t : ℂ)) / (pantsDiskMotionScale t : ℂ)
  left_inv z := by
    dsimp only
    have hs : (pantsDiskMotionScale t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pantsDiskMotionScale_pos t).ne'
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hs]
    ring
  right_inv z := by
    dsimp only
    have hs : (pantsDiskMotionScale t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pantsDiskMotionScale_pos t).ne'
    rw [add_sub_cancel_left, mul_div_cancel₀ _ hs]
    ring
  contMDiff_toFun := (contDiff_const.add (contDiff_const.mul
    (contDiff_id.sub contDiff_const))).contMDiff
  contMDiff_invFun := (contDiff_const.add
    ((contDiff_id.sub contDiff_const).div_const _)).contMDiff

theorem contDiff_pantsDiskMotionCenter : ContDiff ℝ ∞ pantsDiskMotionCenter :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem contDiff_pantsDiskMotionScale : ContDiff ℝ ∞ pantsDiskMotionScale :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem contDiff_pantsDiskMotion :
    ContDiff ℝ ∞ (fun q : ℝ × ℂ => pantsDiskMotion q.1 q.2) :=
  (Complex.ofRealCLM.contDiff.comp
    (contDiff_pantsDiskMotionCenter.comp contDiff_fst)).add
      ((Complex.ofRealCLM.contDiff.comp
        (contDiff_pantsDiskMotionScale.comp contDiff_fst)).mul
          (contDiff_snd.sub contDiff_const))

theorem contDiff_pantsDiskMotion_symm :
    ContDiff ℝ ∞ (fun q : ℝ × ℂ => (pantsDiskMotion q.1).symm q.2) := by
  change ContDiff ℝ ∞ (fun q : ℝ × ℂ => (153 / 184 : ℂ) +
    (q.2 - (pantsDiskMotionCenter q.1 : ℂ)) * (pantsDiskMotionScale q.1 : ℂ)⁻¹)
  exact contDiff_const.add
    ((contDiff_snd.sub (Complex.ofRealCLM.contDiff.comp
      (contDiff_pantsDiskMotionCenter.comp contDiff_fst))).mul
        ((Complex.ofRealCLM.contDiff.comp
          (contDiff_pantsDiskMotionScale.comp contDiff_fst)).inv
            (fun q => Complex.ofReal_ne_zero.mpr (pantsDiskMotionScale_pos q.1).ne')))

theorem pantsDiskMotion_zero : pantsDiskMotion 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ := by
  apply Diffeomorph.ext
  intro z
  change (pantsDiskMotionCenter 0 : ℂ) + (pantsDiskMotionScale 0 : ℂ) *
    (z - 153 / 184) = z
  norm_num [pantsDiskMotionCenter, pantsDiskMotionScale, Real.smoothTransition.zero]

theorem pantsDiskMotion_one_norm (z : ℂ) :
    ‖pantsDiskMotion 1 z + 3 / 2‖ = (92 / 15) * ‖z - 153 / 184‖ := by
  have he : pantsDiskMotion 1 z + 3 / 2 = (92 / 15 : ℂ) * (z - 153 / 184) := by
    change (pantsDiskMotionCenter 1 : ℂ) + (pantsDiskMotionScale 1 : ℂ) *
      (z - 153 / 184) + 3 / 2 = _
    norm_num [pantsDiskMotionCenter, pantsDiskMotionScale, Real.smoothTransition.one]
  rw [he, norm_mul]
  norm_num

def pantsPermutationAnnulus : Set ℂ := {z | ‖z‖ < 3 ∧ 1 / 2 < ‖z - 3 / 2‖}

theorem isOpen_pantsPermutationAnnulus : IsOpen pantsPermutationAnnulus :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))

theorem pantsDiskMotion_bounds (t : ℝ) :
    |pantsDiskMotionCenter t| ≤ 3 / 2 ∧
      pantsDiskMotionScale t * (15 / 184) ≤ 1 / 2 ∧
      pantsDiskMotionCenter t + pantsDiskMotionScale t * (15 / 184) ≤ 21 / 23 := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  unfold pantsDiskMotionCenter pantsDiskMotionScale
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem pantsDiskMotion_trace (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (153 / 184 : ℂ) (15 / 184)) :
    pantsDiskMotion t z ∈ pantsPermutationAnnulus := by
  have hz' : ‖z - (153 / 184 : ℂ)‖ ≤ 15 / 184 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  obtain ⟨hc, hs, hright⟩ := pantsDiskMotion_bounds t
  have hscale := pantsDiskMotionScale_pos t
  have hnorm : ‖pantsDiskMotion t z‖ ≤ 2 := by
    calc
      _ ≤ ‖(pantsDiskMotionCenter t : ℂ)‖ +
          ‖(pantsDiskMotionScale t : ℂ) * (z - 153 / 184)‖ := norm_add_le _ _
      _ = |pantsDiskMotionCenter t| +
          pantsDiskMotionScale t * ‖z - 153 / 184‖ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_of_nonneg hscale.le]
      _ ≤ 2 := by nlinarith
  have hre : (pantsDiskMotion t z).re ≤ 21 / 23 := by
    have hzr : z.re - 153 / 184 ≤ ‖z - (153 / 184 : ℂ)‖ := by
      simpa using (Complex.re_le_norm (z - (153 / 184 : ℂ)))
    have he : (pantsDiskMotion t z).re = pantsDiskMotionCenter t +
        pantsDiskMotionScale t * (z.re - 153 / 184) := by
      change ((pantsDiskMotionCenter t : ℂ) +
        (pantsDiskMotionScale t : ℂ) * (z - 153 / 184)).re = _
      simp
    rw [he]
    nlinarith
  have hr : 3 / 2 - (pantsDiskMotion t z).re ≤ ‖pantsDiskMotion t z - 3 / 2‖ := by
    calc
      _ = -(pantsDiskMotion t z - 3 / 2).re := by simp
      _ ≤ |(pantsDiskMotion t z - 3 / 2).re| := neg_le_abs _
      _ ≤ _ := Complex.abs_re_le_norm _
  exact ⟨by linarith, by linarith⟩

theorem pantsDiskMotion_image :
    pantsDiskMotion 1 '' closedBall (153 / 184 : ℂ) (15 / 184) =
      closedBall (-3 / 2 : ℂ) (1 / 2) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : ‖z - (153 / 184 : ℂ)‖ ≤ 15 / 184 := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    rw [mem_closedBall, dist_eq_norm]
    have he : pantsDiskMotion 1 z - (-3 / 2 : ℂ) = pantsDiskMotion 1 z + 3 / 2 := by ring
    rw [he, pantsDiskMotion_one_norm]
    linarith
  · intro hy
    refine ⟨(pantsDiskMotion 1).symm y, ?_, (pantsDiskMotion 1).apply_symm_apply y⟩
    rw [mem_closedBall, dist_eq_norm]
    have he := pantsDiskMotion_one_norm ((pantsDiskMotion 1).symm y)
    rw [(pantsDiskMotion 1).apply_symm_apply] at he
    have hy' : ‖y + (3 / 2 : ℂ)‖ ≤ 1 / 2 := by
      simpa only [mem_closedBall, dist_eq_norm, sub_neg_eq_add, neg_div] using hy
    linarith

theorem exists_pantsDiskRestoration :
    ∃ R : ℂ ≃ₘ[ℝ] ℂ,
      EqOn R (pantsDiskMotion 1) (closedBall (153 / 184 : ℂ) (15 / 184)) ∧
      EqOn R id pantsPermutationAnnulusᶜ ∧ EqOn R.symm id pantsPermutationAnnulusᶜ ∧
      R '' closedBall (153 / 184 : ℂ) (15 / 184) = closedBall (-3 / 2 : ℂ) (1 / 2) := by
  obtain ⟨V, hV, hKV, Φ, hΦ, hΦi, hΦ0, htrack, hfixed, hlinear, S, hS, hSO, hsupport⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_preserving_linear_map
      pantsDiskMotion contDiff_pantsDiskMotion contDiff_pantsDiskMotion_symm
      (0 : ℂ →L[ℝ] ℂ) (fun t z => rfl) (A := ∅)
      (fun t z hz => hz.elim) (a := 0) (b := 1)
      (isCompact_closedBall (153 / 184 : ℂ) (15 / 184)) isOpen_pantsPermutationAnnulus
      (fun t ht z hz => pantsDiskMotion_trace t z hz)
  have hagree : EqOn (Φ 1) (pantsDiskMotion 1)
      (closedBall (153 / 184 : ℂ) (15 / 184)) := by
    intro z hz
    have h := htrack 1 (by norm_num) z (hKV hz)
    simpa only [pantsDiskMotion_zero, Diffeomorph.coe_refl, id_eq] using h
  refine ⟨Φ 1, hagree, ?_, ?_, ?_⟩
  · intro z hz
    exact (hsupport 1).1 (fun hzS => hz (hSO hzS))
  · intro z hz
    exact (hsupport 1).2 (fun hzS => hz (hSO hzS))
  · rw [image_congr hagree, pantsDiskMotion_image]

def pantsDiskRestoration : ℂ ≃ₘ[ℝ] ℂ := Classical.choose exists_pantsDiskRestoration

theorem pantsDiskRestoration_agree :
    EqOn pantsDiskRestoration (pantsDiskMotion 1)
      (closedBall (153 / 184 : ℂ) (15 / 184)) :=
  (Classical.choose_spec exists_pantsDiskRestoration).1

theorem pantsDiskRestoration_fixed : EqOn pantsDiskRestoration id pantsPermutationAnnulusᶜ :=
  (Classical.choose_spec exists_pantsDiskRestoration).2.1

theorem pantsDiskRestoration_symm_fixed :
    EqOn pantsDiskRestoration.symm id pantsPermutationAnnulusᶜ :=
  (Classical.choose_spec exists_pantsDiskRestoration).2.2.1

theorem pantsDiskRestoration_image :
    pantsDiskRestoration '' closedBall (153 / 184 : ℂ) (15 / 184) =
      closedBall (-3 / 2 : ℂ) (1 / 2) :=
  (Classical.choose_spec exists_pantsDiskRestoration).2.2.2

theorem pantsDiskRestoration_ball_image :
    pantsDiskRestoration '' ball (153 / 184 : ℂ) (15 / 184) =
      ball (-3 / 2 : ℂ) (1 / 2) := by
  rw [← interior_closedBall' (153 / 184 : ℂ) (15 / 184),
    ← Diffeomorph.coe_toHomeomorph pantsDiskRestoration,
    pantsDiskRestoration.toHomeomorph.image_interior,
    Diffeomorph.coe_toHomeomorph, pantsDiskRestoration_image, interior_closedBall']

theorem pantsDiskRestoration_sphere_image :
    pantsDiskRestoration '' sphere (153 / 184 : ℂ) (15 / 184) =
      sphere (-3 / 2 : ℂ) (1 / 2) := by
  rw [← frontier_closedBall (153 / 184 : ℂ) (by norm_num : (15 / 184 : ℝ) ≠ 0),
    ← Diffeomorph.coe_toHomeomorph pantsDiskRestoration,
    pantsDiskRestoration.toHomeomorph.image_frontier,
    Diffeomorph.coe_toHomeomorph, pantsDiskRestoration_image,
    frontier_closedBall (-3 / 2 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem pantsAnnulus_fixed_mapsTo (R : ℂ ≃ₘ[ℝ] ℂ)
    (hf : EqOn R id pantsPermutationAnnulusᶜ)
    (hi : EqOn R.symm id pantsPermutationAnnulusᶜ) :
    MapsTo R {z | ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖}
      {z | ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖} := by
  intro z hz
  by_cases h : z ∈ pantsPermutationAnnulus
  · have hr : R z ∈ pantsPermutationAnnulus := by
      by_contra hn
      have he : R.symm (R z) = R z := hi hn
      rw [R.symm_apply_apply] at he
      exact hn (he ▸ h)
    exact ⟨hr.1.le, hr.2.le⟩
  · rw [hf h]
    exact hz

theorem pantsDiskRestoration_mem_iff (z : ℂ) :
    pantsDiskRestoration z ∈ planarModel 3 ↔ z ∈ pantsInversionRegion := by
  have hs : (‖pantsDiskRestoration z‖ ≤ 3 ∧ 1 / 2 ≤
      ‖pantsDiskRestoration z - 3 / 2‖) ↔ (‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖) := by
    constructor
    · intro hz
      have h := pantsAnnulus_fixed_mapsTo pantsDiskRestoration.symm
        pantsDiskRestoration_symm_fixed pantsDiskRestoration_fixed hz
      rwa [pantsDiskRestoration.symm_apply_apply] at h
    · exact fun hz => pantsAnnulus_fixed_mapsTo pantsDiskRestoration
        pantsDiskRestoration_fixed pantsDiskRestoration_symm_fixed hz
  have hb : pantsDiskRestoration z ∈ ball (-3 / 2 : ℂ) (1 / 2) ↔
      z ∈ ball (153 / 184 : ℂ) (15 / 184) := by
    rw [← pantsDiskRestoration_ball_image]
    constructor
    · rintro ⟨w, hw, he⟩
      exact pantsDiskRestoration.injective he ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hn : 1 / 2 ≤ ‖pantsDiskRestoration z + 3 / 2‖ ↔
      15 / 184 ≤ ‖z - 153 / 184‖ := by
    have h := not_congr hb
    simpa only [mem_ball, dist_eq_norm, sub_neg_eq_add, neg_div, not_lt] using h
  rw [mem_planarModel_three]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, sub_neg_eq_add]
  change (‖pantsDiskRestoration z‖ ≤ 3 ∧
    1 / 2 ≤ ‖pantsDiskRestoration z - 3 / 2‖ ∧
    1 / 2 ≤ ‖pantsDiskRestoration z + 3 / 2‖) ↔
    (‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖ ∧ 15 / 184 ≤ ‖z - 153 / 184‖)
  rw [← and_assoc, hs, and_assoc, hn]

theorem pants_ne_inversionCenter {z : ℂ} (hz : z ∈ planarModel 3) : z ≠ 9 / 7 := by
  intro he
  have h := (mem_planarModel_three z).mp hz
  rw [he] at h
  norm_num at h

theorem pantsInversionRegion_ne {z : ℂ} (hz : z ∈ pantsInversionRegion) : z ≠ 9 / 7 := by
  intro he
  have h := hz.2.1
  rw [he] at h
  norm_num at h

def pantsOuterHoleMap (x : planarSet.{u} 3) : planarSet.{u} 3 :=
  ⟨ULift.up (pantsDiskRestoration (pantsInversion x.val.down)),
    (mem_planarSet_iff (Or.inr rfl) _).mpr
      ((pantsDiskRestoration_mem_iff _).mpr
        ((pantsInversion_mem_iff _ (pants_ne_inversionCenter
          ((mem_planarSet_iff (Or.inr rfl) _).mp x.property))).mpr
            ((mem_planarSet_iff (Or.inr rfl) _).mp x.property)))⟩

def pantsOuterHoleInverse (x : planarSet.{u} 3) : planarSet.{u} 3 := by
  have hx := (mem_planarSet_iff (Or.inr rfl) x.val).mp x.property
  have hy : pantsDiskRestoration.symm x.val.down ∈ pantsInversionRegion :=
    (pantsDiskRestoration_mem_iff _).mp (by rw [pantsDiskRestoration.apply_symm_apply]; exact hx)
  have hn := pantsInversionRegion_ne hy
  refine ⟨ULift.up (pantsInversion (pantsDiskRestoration.symm x.val.down)),
    (mem_planarSet_iff (Or.inr rfl) _).mpr ?_⟩
  have he := pantsInversion_mem_iff (pantsInversion (pantsDiskRestoration.symm x.val.down))
    (pantsInversion_ne hn)
  rw [pantsInversion_involutive] at he
  exact he.mp hy

theorem contMDiffAt_pantsInversion {z : ℂ} (hz : z ≠ 9 / 7) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ pantsInversion z := by
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    (fun w : ℂ => (9 / 7 : ℂ) + (60 / 49 : ℂ) * (w - 9 / 7)⁻¹) z
  exact (contDiffAt_const.add (contDiffAt_const.mul
    ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hz)))).contMDiffAt

theorem contMDiff_pantsOuterHoleMap :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ pantsOuterHoleMap.{u} := by
  refine ((planarAtlas 3).contMDiff_iff_subtype_val _).mpr fun x => ?_
  have hI := (contMDiffAt_pantsInversion (pants_ne_inversionCenter
    ((mem_planarSet_iff (Or.inr rfl) _).mp x.property))).comp x
      (contMDiff_planarSet_down 3 x)
  have hR := pantsDiskRestoration.contMDiff.contMDiffAt.comp x hI
  exact contMDiff_planeLift_up.contMDiffAt.comp x hR

theorem contMDiff_pantsOuterHoleInverse :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ pantsOuterHoleInverse.{u} := by
  refine ((planarAtlas 3).contMDiff_iff_subtype_val _).mpr fun x => ?_
  have hy : pantsDiskRestoration.symm x.val.down ∈ pantsInversionRegion :=
    (pantsDiskRestoration_mem_iff _).mp (by
      rw [pantsDiskRestoration.apply_symm_apply]
      exact (mem_planarSet_iff (Or.inr rfl) _).mp x.property)
  have hR := pantsDiskRestoration.symm.contMDiff.contMDiffAt.comp x
    (contMDiff_planarSet_down 3 x)
  have hI := (contMDiffAt_pantsInversion (pantsInversionRegion_ne hy)).comp x hR
  exact contMDiff_planeLift_up.contMDiffAt.comp x hI

def pantsOuterHoleDiffeomorph : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ planarSet.{u} 3 where
  toFun := pantsOuterHoleMap
  invFun := pantsOuterHoleInverse
  left_inv x := by
    apply Subtype.ext
    apply ULift.ext
    change pantsInversion (pantsDiskRestoration.symm
      (pantsDiskRestoration (pantsInversion x.val.down))) = x.val.down
    rw [pantsDiskRestoration.symm_apply_apply, pantsInversion_involutive]
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    change pantsDiskRestoration (pantsInversion
      (pantsInversion (pantsDiskRestoration.symm x.val.down))) = x.val.down
    rw [pantsInversion_involutive, pantsDiskRestoration.apply_symm_apply]
  contMDiff_toFun := contMDiff_pantsOuterHoleMap
  contMDiff_invFun := contMDiff_pantsOuterHoleInverse

theorem pantsInversion_outer_boundary (z : ℂ) (hz : z ≠ 9 / 7) (hn : ‖z‖ = 3) :
    ‖pantsInversion z - 3 / 2‖ = 1 / 2 := by
  have hd : 0 < ‖z - (9 / 7 : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have hm : (‖pantsInversion z - 3 / 2‖ ^ 2 - 1 / 4) * ‖z - 9 / 7‖ ^ 2 = 0 := by
    rw [pantsInversion_inner_identity z hz, hn]
    norm_num
  have he := (mul_eq_zero.mp hm).resolve_right hd.ne'
  nlinarith [norm_nonneg (pantsInversion z - 3 / 2)]

theorem pantsInversion_inner_boundary (z : ℂ) (hz : z ≠ 9 / 7)
    (hn : ‖z - 3 / 2‖ = 1 / 2) : ‖pantsInversion z‖ = 3 := by
  have hd : 0 < ‖z - (9 / 7 : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have hm : (‖pantsInversion z‖ ^ 2 - 9) * ‖z - 9 / 7‖ ^ 2 = 0 := by
    rw [pantsInversion_outer_identity z hz, hn]
    norm_num
  have he := (mul_eq_zero.mp hm).resolve_right hd.ne'
  nlinarith [norm_nonneg (pantsInversion z)]

theorem pantsInversion_other_boundary (z : ℂ) (hz : z ≠ 9 / 7)
    (hn : ‖z + 3 / 2‖ = 1 / 2) : ‖pantsInversion z - 153 / 184‖ = 15 / 184 := by
  have hd : 0 < ‖z - (9 / 7 : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have hm : (‖pantsInversion z - 153 / 184‖ ^ 2 - (15 / 184) ^ 2) *
      ‖z - 9 / 7‖ ^ 2 = 0 := by
    rw [pantsInversion_other_identity z hz, hn]
    norm_num
  have he := (mul_eq_zero.mp hm).resolve_right hd.ne'
  nlinarith [norm_nonneg (pantsInversion z - 153 / 184)]

theorem pantsOuterHoleDiffeomorph_boundary_norm (j : Fin 3) (t : Circle) :
    ‖(pantsOuterHoleDiffeomorph.{u} (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero))).val.down -
      planarCenter 3 (Equiv.swap 0 1 j)‖ = planarRadius (Equiv.swap 0 1 j) := by
  have hval := planarCollar_zero_val.{u} (Or.inr rfl) j t
  change (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)).val.down = planarCircleMap 3 j t at hval
  change ‖pantsDiskRestoration
    (pantsInversion (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)).val.down) -
      planarCenter 3 (Equiv.swap 0 1 j)‖ = planarRadius (Equiv.swap 0 1 j)
  rw [hval]
  have hne := pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) j t)
  have hnorm := norm_planarCircleMap_sub 3 j t
  fin_cases j
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsDiskRestoration (pantsInversion (planarCircleMap 3 0 t)) - 3 / 2‖ = 1 / 2
    have hz : ‖planarCircleMap 3 0 t‖ = 3 := by
      simpa [planarCenter, planarRadius] using hnorm
    have he : ‖pantsInversion (planarCircleMap 3 0 t) - 3 / 2‖ = 1 / 2 :=
      pantsInversion_outer_boundary _ hne hz
    have hfix : pantsInversion (planarCircleMap 3 0 t) ∉ pantsPermutationAnnulus := by
      intro h
      change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
      rw [he] at h
      exact lt_irrefl _ h.2
    rw [pantsDiskRestoration_fixed hfix]
    exact he
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsDiskRestoration (pantsInversion (planarCircleMap 3 1 t))‖ = 3
    have hz : ‖planarCircleMap 3 1 t - 3 / 2‖ = 1 / 2 := by
      simpa [planarCenter, planarRadius] using hnorm
    have he : ‖pantsInversion (planarCircleMap 3 1 t)‖ = 3 :=
      pantsInversion_inner_boundary _ hne hz
    have hfix : pantsInversion (planarCircleMap 3 1 t) ∉ pantsPermutationAnnulus := by
      intro h
      change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
      rw [he] at h
      exact lt_irrefl _ h.1
    rw [pantsDiskRestoration_fixed hfix]
    exact he
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsDiskRestoration (pantsInversion (planarCircleMap 3 2 t)) +
      (3 / 2 : ℂ)‖ = 1 / 2
    have hz : ‖planarCircleMap 3 2 t + 3 / 2‖ = 1 / 2 := by
      simpa [planarCenter, planarRadius] using hnorm
    have he : ‖pantsInversion (planarCircleMap 3 2 t) - 153 / 184‖ = 15 / 184 :=
      pantsInversion_other_boundary _ hne hz
    have hm : pantsDiskRestoration (pantsInversion (planarCircleMap 3 2 t)) ∈
        sphere (-3 / 2 : ℂ) (1 / 2) := by
      rw [← pantsDiskRestoration_sphere_image]
      exact ⟨_, by simpa only [mem_sphere, dist_eq_norm] using he, rfl⟩
    simpa only [mem_sphere, dist_eq_norm, neg_div, sub_neg_eq_add] using hm

def planarBoundaryParameter (j : Fin 3) (z : ℂ) : Circle :=
  if j.val = 0 then unitOf (z - planarCenter 3 j) else (unitOf (z - planarCenter 3 j))⁻¹

theorem planarBoundaryParameter_circle (j : Fin 3) (t : Circle) :
    planarBoundaryParameter j (planarCircleMap 3 j t) = t := by
  by_cases hj : j.val = 0
  · simp only [planarBoundaryParameter, hj, ite_true, planarCircleMap, add_sub_cancel_left,
      planarRadius]
    change unitOf ((3 : ℝ) • (t : ℂ)) = t
    exact unitOf_smul (by norm_num) t
  · simp only [planarBoundaryParameter, hj, ite_false, planarCircleMap, add_sub_cancel_left,
      planarRadius]
    rw [← Circle.coe_inv_eq_conj]
    change (unitOf ((1 / 2 : ℝ) • (t⁻¹ : Circle)))⁻¹ = t
    rw [unitOf_smul (by norm_num), inv_inv]

theorem planarCircleMap_parameter (j : Fin 3) (z : ℂ)
    (hz : ‖z - planarCenter 3 j‖ = planarRadius j) :
    planarCircleMap 3 j (planarBoundaryParameter j z) = z := by
  have he : ((‖z - planarCenter 3 j‖ : ℝ) : ℂ) *
      (unitOf (z - planarCenter 3 j) : ℂ) = z - planarCenter 3 j := by
    simpa only [Complex.real_smul] using norm_smul_unitOf (z - planarCenter 3 j)
  rw [hz] at he
  by_cases hj : j.val = 0
  · simp only [planarCircleMap, planarBoundaryParameter, hj, ite_true]
    rw [he]
    ring
  · simp only [planarCircleMap, planarBoundaryParameter, hj, ite_false]
    rw [← Circle.coe_inv_eq_conj, inv_inv, he]
    ring

theorem pantsInversion_other_boundary_inverse (z : ℂ) (hz : z ≠ 9 / 7)
    (hn : ‖z - 153 / 184‖ = 15 / 184) : ‖pantsInversion z + 3 / 2‖ = 1 / 2 := by
  have h := pantsInversion_other_identity (pantsInversion z) (pantsInversion_ne hz)
  rw [pantsInversion_involutive, hn] at h
  norm_num at h
  nlinarith [norm_nonneg (pantsInversion z + 3 / 2)]

theorem pantsOuterHoleDiffeomorph_symm_boundary_norm (j : Fin 3) (t : Circle) :
    ‖(pantsOuterHoleDiffeomorph.{u}.symm
      (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero))).val.down -
      planarCenter 3 (Equiv.swap 0 1 j)‖ = planarRadius (Equiv.swap 0 1 j) := by
  have hval := planarCollar_zero_val.{u} (Or.inr rfl) j t
  change (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)).val.down = planarCircleMap 3 j t at hval
  change ‖pantsInversion
    (pantsDiskRestoration.symm (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)).val.down) -
      planarCenter 3 (Equiv.swap 0 1 j)‖ = planarRadius (Equiv.swap 0 1 j)
  rw [hval]
  have hne := pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) j t)
  have hnorm := norm_planarCircleMap_sub 3 j t
  fin_cases j
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsInversion (pantsDiskRestoration.symm (planarCircleMap 3 0 t)) - 3 / 2‖ = 1 / 2
    have hz : ‖planarCircleMap 3 0 t‖ = 3 := by
      simpa [planarCenter, planarRadius] using hnorm
    have hfix : planarCircleMap 3 0 t ∉ pantsPermutationAnnulus := by
      intro h
      change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
      rw [hz] at h
      exact lt_irrefl _ h.1
    rw [pantsDiskRestoration_symm_fixed hfix]
    exact pantsInversion_outer_boundary _ hne hz
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsInversion (pantsDiskRestoration.symm (planarCircleMap 3 1 t))‖ = 3
    have hz : ‖planarCircleMap 3 1 t - 3 / 2‖ = 1 / 2 := by
      simpa [planarCenter, planarRadius] using hnorm
    have hfix : planarCircleMap 3 1 t ∉ pantsPermutationAnnulus := by
      intro h
      change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
      rw [hz] at h
      exact lt_irrefl _ h.2
    rw [pantsDiskRestoration_symm_fixed hfix]
    exact pantsInversion_inner_boundary _ hne hz
  · norm_num [Equiv.swap_apply_def, planarCenter, planarRadius]
    change ‖pantsInversion (pantsDiskRestoration.symm (planarCircleMap 3 2 t)) +
      (3 / 2 : ℂ)‖ = 1 / 2
    have hz : ‖planarCircleMap 3 2 t + 3 / 2‖ = 1 / 2 := by
      simpa [planarCenter, planarRadius] using hnorm
    have hm : planarCircleMap 3 2 t ∈ sphere (-3 / 2 : ℂ) (1 / 2) := by
      simpa only [mem_sphere, dist_eq_norm, sub_neg_eq_add, neg_div] using hz
    rw [← pantsDiskRestoration_sphere_image] at hm
    obtain ⟨z, hz', he⟩ := hm
    have he' : pantsDiskRestoration.symm (planarCircleMap 3 2 t) = z := by
      rw [← he, pantsDiskRestoration.symm_apply_apply]
    rw [he']
    have hzn : z ≠ 9 / 7 := by
      have hy := (pantsDiskRestoration_mem_iff z).mp
        (he.symm ▸ planarCircleMap_mem_planarModel (by decide) 2 t)
      exact pantsInversionRegion_ne hy
    have hzr : ‖z - (153 / 184 : ℂ)‖ = 15 / 184 := by
      simpa only [mem_sphere, dist_eq_norm] using hz'
    simpa only [sub_neg_eq_add] using pantsInversion_other_boundary_inverse z hzn hzr

theorem contMDiffAt_planarBoundaryParameter (j : Fin 3) {z : ℂ}
    (hz : z - planarCenter 3 j ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (planarBoundaryParameter j) z := by
  have h := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hz)).comp z
    (contMDiffAt_id.sub contMDiffAt_const)
  by_cases hj : j.val = 0
  · have he : planarBoundaryParameter j = fun w => unitOf (w - planarCenter 3 j) := by
      funext w
      simp only [planarBoundaryParameter, hj, ite_true]
    rw [he]
    exact h
  · have he : planarBoundaryParameter j = fun w => (unitOf (w - planarCenter 3 j))⁻¹ := by
      funext w
      simp only [planarBoundaryParameter, hj, ite_false]
    rw [he]
    exact h.inv

theorem contMDiff_planarBoundaryPoint (j : Fin 3) :
    ContMDiff (𝓡 1) (𝓡∂ 2) ∞
      (fun t : Circle => planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)) := by
  intro t
  have ht : (t, halfZero) ∈ (planarCollar.{u} 3 (Or.inr rfl) j).source := by
    exact halfZero_mem_circleCollarSource t
  exact (((planarCollar.{u} 3 (Or.inr rfl) j).contMDiffOn_toFun (t, halfZero) ht).contMDiffAt
    ((planarCollar.{u} 3 (Or.inr rfl) j).open_source.mem_nhds ht)).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)

def pantsOuterHoleBoundaryMap (j : Fin 3) (t : Circle) : Circle :=
  planarBoundaryParameter (Equiv.swap 0 1 j)
    (pantsOuterHoleDiffeomorph.{u} (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero))).val.down

def pantsOuterHoleBoundaryInverse (j : Fin 3) (t : Circle) : Circle :=
  planarBoundaryParameter j (pantsOuterHoleDiffeomorph.{u}.symm
    (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j) (t, halfZero))).val.down

theorem pantsOuterHole_boundary_point (j : Fin 3) (t : Circle) :
    pantsOuterHoleDiffeomorph.{u} (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero)) =
      planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
        (pantsOuterHoleBoundaryMap.{u} j t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  rw [planarCollar_zero_val]
  exact (planarCircleMap_parameter _ _ (pantsOuterHoleDiffeomorph_boundary_norm.{u} j t)).symm

theorem pantsOuterHole_symm_boundary_point (j : Fin 3) (t : Circle) :
    pantsOuterHoleDiffeomorph.{u}.symm
      (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j) (t, halfZero)) =
      planarCollar.{u} 3 (Or.inr rfl) j (pantsOuterHoleBoundaryInverse.{u} j t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  rw [planarCollar_zero_val]
  have h := pantsOuterHoleDiffeomorph_symm_boundary_norm.{u} (Equiv.swap 0 1 j) t
  rw [Equiv.swap_apply_self] at h
  exact (planarCircleMap_parameter j _ h).symm

theorem contMDiff_pantsOuterHoleBoundaryMap (j : Fin 3) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (pantsOuterHoleBoundaryMap.{u} j) := by
  have ham := (contMDiff_planarSet_down.{u} 3).comp
    (pantsOuterHoleDiffeomorph.{u}.contMDiff.comp (contMDiff_planarBoundaryPoint.{u} j))
  intro t
  have hn := pantsOuterHoleDiffeomorph_boundary_norm.{u} j t
  have hp : 0 < planarRadius (Equiv.swap 0 1 j) := by unfold planarRadius; split_ifs <;> norm_num
  have hne : (pantsOuterHoleDiffeomorph.{u}
      (planarCollar.{u} 3 (Or.inr rfl) j (t, halfZero))).val.down -
      planarCenter 3 (Equiv.swap 0 1 j) ≠ 0 :=
    norm_pos_iff.mp (hn.symm ▸ hp)
  exact (contMDiffAt_planarBoundaryParameter _ hne).comp t (ham t)

theorem contMDiff_pantsOuterHoleBoundaryInverse (j : Fin 3) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (pantsOuterHoleBoundaryInverse.{u} j) := by
  have ham := (contMDiff_planarSet_down.{u} 3).comp
    (pantsOuterHoleDiffeomorph.{u}.symm.contMDiff.comp
      (contMDiff_planarBoundaryPoint.{u} (Equiv.swap 0 1 j)))
  intro t
  have hn := pantsOuterHoleDiffeomorph_symm_boundary_norm.{u} (Equiv.swap 0 1 j) t
  rw [Equiv.swap_apply_self] at hn
  have hp : 0 < planarRadius j := by unfold planarRadius; split_ifs <;> norm_num
  have hne : (pantsOuterHoleDiffeomorph.{u}.symm
      (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j) (t, halfZero))).val.down -
      planarCenter 3 j ≠ 0 :=
    norm_pos_iff.mp (hn.symm ▸ hp)
  exact (contMDiffAt_planarBoundaryParameter j hne).comp t (ham t)

def pantsOuterHoleBoundaryParameter (j : Fin 3) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun := pantsOuterHoleBoundaryMap.{u} j
  invFun := pantsOuterHoleBoundaryInverse.{u} j
  left_inv t := by
    change planarBoundaryParameter j (pantsOuterHoleDiffeomorph.{u}.symm
      (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
        (pantsOuterHoleBoundaryMap.{u} j t, halfZero))).val.down = t
    rw [← pantsOuterHole_boundary_point.{u}, pantsOuterHoleDiffeomorph.{u}.symm_apply_apply,
      planarCollar_zero_val, planarBoundaryParameter_circle]
  right_inv t := by
    change planarBoundaryParameter (Equiv.swap 0 1 j) (pantsOuterHoleDiffeomorph.{u}
      (planarCollar.{u} 3 (Or.inr rfl) j
        (pantsOuterHoleBoundaryInverse.{u} j t, halfZero))).val.down = t
    rw [← pantsOuterHole_symm_boundary_point.{u}, pantsOuterHoleDiffeomorph.{u}.apply_symm_apply,
      planarCollar_zero_val, planarBoundaryParameter_circle]
  contMDiff_toFun := contMDiff_pantsOuterHoleBoundaryMap.{u} j
  contMDiff_invFun := contMDiff_pantsOuterHoleBoundaryInverse.{u} j

theorem exists_pantsOuterHolePermutation :
    ∃ P : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ planarSet.{u} 3,
      ∃ ψ : Fin 3 → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle),
        ∀ j t, P (pantsPlanarBase.collar j (t, halfZero)) =
          pantsPlanarBase.collar (Equiv.swap 0 1 j) (ψ j t, halfZero) :=
  ⟨pantsOuterHoleDiffeomorph.{u}, pantsOuterHoleBoundaryParameter.{u},
    pantsOuterHole_boundary_point.{u}⟩

def pantsOuterHoleProductTrivialization :
    (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (⊤ : TopologicalSpace.Opens (productSet.{u} 3)) :=
  (pantsOuterHoleDiffeomorph.{u}.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (productTrivialization.{u} 3)

def pantsOuterHoleTorusParameter (j : Fin 3) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (pantsOuterHoleBoundaryParameter.{u} j).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)

theorem pantsOuterHoleProductTrivialization_zero (j : Fin 3) (t : Torus) :
    (productPresentation.{u} 3 (Or.inr rfl)).pieceCollar ⟨0, Nat.one_pos⟩
      (productPort.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j))
      (pantsOuterHoleTorusParameter.{u} j t, halfZero) =
        pantsOuterHoleProductTrivialization.{u}
          (planarCollar.{u} 3 (Or.inr rfl) j (t.1, halfZero), t.2) := by
  have h := (productFibredPiece.{u} 3 (Or.inr rfl)).collar_eq (Equiv.swap 0 1 j)
    (pantsOuterHoleTorusParameter.{u} j t, halfZero)
    (zero_mem_halfCollarSource (pantsOuterHoleTorusParameter.{u} j t))
  refine h.trans ?_
  change productTrivialization.{u} 3
      (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
        (pantsOuterHoleBoundaryParameter.{u} j t.1, halfZero), t.2) =
    productTrivialization.{u} 3
      (pantsOuterHoleDiffeomorph.{u} (planarCollar.{u} 3 (Or.inr rfl) j (t.1, halfZero)), t.2)
  rw [pantsOuterHole_boundary_point.{u}]
  rfl

theorem exists_pantsOuterHoleGermPermutation :
    ∃ δ > (0 : ℝ), ∃ P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle), ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
        P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
          (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
            (pantsOuterHoleBoundaryParameter.{u} j p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, Θ, hΘ⟩ :=
    (productPresentation.{u} 3 (Or.inr rfl)).exists_germ_trivialization ⟨0, Nat.one_pos⟩
      pantsPlanarBase.{u} ((Equiv.swap 0 1).trans (productPort.{u} 3 (Or.inr rfl)))
      pantsOuterHoleTorusParameter.{u} pantsOuterHoleProductTrivialization.{u}
      pantsOuterHoleProductTrivialization_zero.{u}
  refine ⟨δ, hδ, Θ.trans (productTrivialization.{u} 3).symm, fun j p hp hlt => ?_⟩
  have h := hΘ j p hp hlt
  have hc := (productFibredPiece.{u} 3 (Or.inr rfl)).collar_eq (Equiv.swap 0 1 j)
    (pantsOuterHoleTorusParameter.{u} j p.1, p.2) ?_
  · have he : Θ (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        productTrivialization.{u} 3
          (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
            (pantsOuterHoleBoundaryParameter.{u} j p.1.1, p.2), p.1.2) := h.symm.trans hc
    exact (congrArg (productTrivialization.{u} 3).symm he).trans
      ((productTrivialization.{u} 3).symm_apply_apply _)
  · simpa only [halfCollarSource, Set.mem_ofPred_eq] using hp

local instance : ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
local instance : ContMDiffInv₀ 𝓘(ℝ, ℂ) ∞ ℂ where
  contMDiffAt_inv₀ _x hx := (contDiffAt_inv ℝ hx).contMDiffAt

theorem contMDiff_circleMoebius (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (Complex.diskAutomorphismCircle a η ha hη) := by
  have he : (Complex.diskAutomorphismCircle a η ha hη : Circle → Circle) =
      fun t : Circle => unitOf (η * Complex.diskMoebius a t) := by
    funext t
    have h := unitOf_smul (r := 1) one_pos (Complex.diskAutomorphismCircle a η ha hη t)
    simpa only [one_smul, Complex.coe_diskAutomorphismCircle_apply] using h.symm
  rw [he]
  intro t
  have hd := Complex.diskMoebius_denominator_ne_zero ha (Circle.norm_coe t).le
  have hg : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle =>
      η * Complex.diskMoebius a t) t :=
    contMDiffAt_const.mul ((contMDiff_circle_coe.contMDiffAt.sub contMDiffAt_const).div₀
      (contMDiffAt_const.sub (contMDiffAt_const.mul contMDiff_circle_coe.contMDiffAt)) hd)
  have hn : η * Complex.diskMoebius a t ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_mul, hη, Complex.norm_diskMoebius_eq_one ha (Circle.norm_coe t)]
    norm_num
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hn)).comp t hg

def circleMoebiusDiffeomorph (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toEquiv := (Complex.diskAutomorphismCircle a η ha hη).toEquiv
  contMDiff_toFun := contMDiff_circleMoebius a η ha hη
  contMDiff_invFun := by
    have he : ((Complex.diskAutomorphismCircle a η ha hη).symm : Circle → Circle) =
        fun t : Circle => unitOf (Complex.diskMoebius (-a) (conj η * t)) := by
      funext t
      have h := unitOf_smul (r := 1) one_pos
        ((Complex.diskAutomorphismCircle a η ha hη).symm t)
      rw [one_smul] at h
      exact h.symm
    refine ContMDiff.congr
      (f := fun t : Circle => unitOf (Complex.diskMoebius (-a) (conj η * t))) ?_
      (fun t => congrFun he t)
    intro t
    have ht : ‖conj η * (t : ℂ)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hη, Circle.norm_coe, one_mul]
    have hd := Complex.diskMoebius_denominator_ne_zero (a := -a) (by simpa using ha) ht.le
    have hg : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle => conj η * t) t :=
      contMDiffAt_const.mul contMDiff_circle_coe.contMDiffAt
    have hr : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle =>
        Complex.diskMoebius (-a) (conj η * t)) t :=
      (hg.sub contMDiffAt_const).div₀
        (contMDiffAt_const.sub (contMDiffAt_const.mul hg)) hd
    have hn : Complex.diskMoebius (-a) (conj η * t) ≠ 0 := by
      apply norm_pos_iff.mp
      rw [Complex.norm_diskMoebius_eq_one (by simpa using ha) ht]
      norm_num
    exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hn)).comp t hr

theorem contMDiff_circleMoebius_family (a : ℝ → ℂ) (η : ℝ → Circle)
    (ha : ∀ s, ‖a s‖ < 1) (hη : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ η)
    (haSmooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ a) :
    ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞ (fun q : ℝ × Circle =>
      circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _) q.2) := by
  have he : (fun q : ℝ × Circle =>
      circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _) q.2) =
      fun q : ℝ × Circle => unitOf ((η q.1 : ℂ) * Complex.diskMoebius (a q.1) q.2) := by
    funext q
    have h := unitOf_smul (r := 1) one_pos
      (circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _) q.2)
    rw [one_smul] at h
    exact h.symm
  rw [he]
  intro q
  have hd := Complex.diskMoebius_denominator_ne_zero (ha q.1) (Circle.norm_coe q.2).le
  have ht : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => (q.2 : ℂ)) q :=
    (contMDiff_circle_coe.comp contMDiff_snd).contMDiffAt
  have hA : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => a q.1) q := (haSmooth.comp contMDiff_fst).contMDiffAt
  have hE : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => (η q.1 : ℂ)) q :=
    (contMDiff_circle_coe.comp (hη.comp contMDiff_fst)).contMDiffAt
  have hconj := Complex.conjCLE.contDiff.contMDiff.contMDiffAt.comp q hA
  have hg : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ (fun q : ℝ × Circle =>
      (η q.1 : ℂ) * Complex.diskMoebius (a q.1) q.2) q :=
    hE.mul ((ht.sub hA).div₀ (contMDiffAt_const.sub (hconj.mul ht)) hd)
  have hn : (η q.1 : ℂ) * Complex.diskMoebius (a q.1) q.2 ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_mul, Circle.norm_coe, Complex.norm_diskMoebius_eq_one (ha q.1)
      (Circle.norm_coe q.2)]
    norm_num
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hn)).comp q hg

theorem contMDiff_circleMoebius_symm_family (a : ℝ → ℂ) (η : ℝ → Circle)
    (ha : ∀ s, ‖a s‖ < 1) (hη : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ η)
    (haSmooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ a) :
    ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞ (fun q : ℝ × Circle =>
      (circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _)).symm q.2) := by
  have he : (fun q : ℝ × Circle =>
      (circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _)).symm q.2) =
      fun q : ℝ × Circle => unitOf
        (Complex.diskMoebius (-a q.1) (conj (η q.1 : ℂ) * q.2)) := by
    funext q
    have h := unitOf_smul (r := 1) one_pos
      ((circleMoebiusDiffeomorph (a q.1) (η q.1) (ha q.1) (Circle.norm_coe _)).symm q.2)
    rw [one_smul] at h
    exact h.symm
  rw [he]
  intro q
  have hnorm : ‖conj (η q.1 : ℂ) * (q.2 : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, Circle.norm_coe, one_mul]
  have hd := Complex.diskMoebius_denominator_ne_zero (a := -a q.1)
    (by simpa using ha q.1) hnorm.le
  have ht : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => (q.2 : ℂ)) q :=
    (contMDiff_circle_coe.comp contMDiff_snd).contMDiffAt
  have hA : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => -a q.1) q := (haSmooth.comp contMDiff_fst).contMDiffAt.neg
  have hE : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × Circle => (η q.1 : ℂ)) q :=
    (contMDiff_circle_coe.comp (hη.comp contMDiff_fst)).contMDiffAt
  have hconj := Complex.conjCLE.contDiff.contMDiff.contMDiffAt.comp q hA
  have hr := (Complex.conjCLE.contDiff.contMDiff.contMDiffAt.comp q hE).mul ht
  have hg : ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ (fun q : ℝ × Circle =>
      Complex.diskMoebius (-a q.1) (conj (η q.1 : ℂ) * q.2)) q :=
    (hr.sub hA).div₀ (contMDiffAt_const.sub (hconj.mul hr)) hd
  have hn : Complex.diskMoebius (-a q.1) (conj (η q.1 : ℂ) * q.2) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [Complex.norm_diskMoebius_eq_one (by simpa using ha q.1) hnorm]
    norm_num
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hn)).comp q hg

theorem circleMoebiusDiffeomorph_isotopic (a : ℂ) (θ : ℝ) (ha : ‖a‖ < 1) :
    IsotopicDiffeomorph (circleMoebiusDiffeomorph a (Circle.exp θ) ha (Circle.norm_coe _))
      (Diffeomorph.refl (𝓡 1) Circle ∞) := by
  let A : ℝ → ℂ := fun s => a * ((1 - Real.smoothTransition s : ℝ) : ℂ)
  let E : ℝ → Circle := fun s => Circle.exp (θ * (1 - Real.smoothTransition s))
  have hA : ∀ s, ‖A s‖ < 1 := by
    intro s
    have hb := Real.smoothTransition.nonneg s
    have hc := Real.smoothTransition.le_one s
    change ‖a * ((1 - Real.smoothTransition s : ℝ) : ℂ)‖ < 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) (by linarith)) ha
  have hASmooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ A :=
    contMDiff_const.mul (Complex.ofRealCLM.contDiff.contMDiff.comp
      (contMDiff_const.sub Real.smoothTransition.contDiff.contMDiff))
  have hESmooth : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ E :=
    (contMDiff_circleExp (m := ∞)).comp
      (contMDiff_const.mul (contMDiff_const.sub Real.smoothTransition.contDiff.contMDiff))
  refine ⟨fun s => circleMoebiusDiffeomorph (A s) (E s) (hA s) (Circle.norm_coe _),
    contMDiff_circleMoebius_family A E hA hESmooth hASmooth,
    contMDiff_circleMoebius_symm_family A E hA hESmooth hASmooth, ?_, ?_⟩
  · ext t
    change (E 0 : ℂ) * Complex.diskMoebius (A 0) t =
      (Circle.exp θ : ℂ) * Complex.diskMoebius a t
    simp [A, E, Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
  · ext t
    change (E 1 : ℂ) * Complex.diskMoebius (A 1) t = (t : ℂ)
    simp [A, E, Real.smoothTransition.one_of_one_le (le_refl (1 : ℝ)), Complex.diskMoebius]
theorem pantsOuterHoleBoundaryParameter_zero (t : Circle) :
    (pantsOuterHoleBoundaryParameter.{u} 0 t : ℂ) = Complex.diskMoebius (3 / 7) t := by
  have hn := pantsInversion_outer_boundary (planarCircleMap 3 0 t)
    (pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 0 t))
    (by simpa [planarCenter, planarRadius] using norm_planarCircleMap_sub 3 0 t)
  have hf : pantsInversion (planarCircleMap 3 0 t) ∉ pantsPermutationAnnulus := by
    intro h
    change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
    rw [hn] at h
    exact lt_irrefl _ h.2
  change (planarBoundaryParameter (Equiv.swap (0 : Fin 3) 1 0)
    (pantsDiskRestoration (pantsInversion
      (planarCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero)).val.down)) : ℂ) = _
  rw [planarCollar_zero_val, pantsDiskRestoration_fixed hf, Equiv.swap_apply_left]
  norm_num [planarBoundaryParameter, planarCenter]
  change (((unitOf (pantsInversion (planarCircleMap 3 0 t) - 3 / 2))⁻¹ : Circle) : ℂ) = _
  rw [Circle.coe_inv, coe_unitOf (norm_pos_iff.mp (by rw [hn]; norm_num)), hn]
  have hz : (3 : ℂ) * t - 9 / 7 ≠ 0 := by
    have h := pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 0 t)
    simpa [planarCircleMap, planarCenter, planarRadius] using sub_ne_zero.mpr h
  have ht : (t : ℂ) - 3 / 7 ≠ 0 := by
    intro h
    have hn := Circle.norm_coe t
    rw [sub_eq_zero.mp h] at hn
    norm_num at hn
  have hz' : -(9 : ℂ) + (t : ℂ) * 21 ≠ 0 := by
    rw [show -(9 : ℂ) + (t : ℂ) * 21 = (3 * t - 9 / 7) * 7 by ring]
    exact mul_ne_zero hz (by norm_num)
  have ht' : -(3 : ℂ) + (t : ℂ) * 7 ≠ 0 := by
    rw [show -(3 : ℂ) + (t : ℂ) * 7 = (t - 3 / 7) * 7 by ring]
    exact mul_ne_zero ht (by norm_num)
  apply inv_injective
  rw [inv_inv, Complex.diskMoebius, inv_div]
  simp [Complex.real_smul, planarCircleMap, planarCenter, planarRadius, pantsInversion]
  simp only [map_ofNat]
  field_simp [hz, ht]
  apply mul_right_cancel₀ (mul_ne_zero hz' ht')
  have hZI := inv_mul_cancel₀ hz'
  have hTI := inv_mul_cancel₀ ht'
  linear_combination (5880 * (-(3 : ℂ) + (t : ℂ) * 7)) * hZI +
    ((1029 * (t : ℂ) - 2401) * (-(9 : ℂ) + (t : ℂ) * 21)) * hTI
theorem pantsOuterHoleBoundaryParameter_one (t : Circle) :
    (pantsOuterHoleBoundaryParameter.{u} 1 t : ℂ) = Complex.diskMoebius (-(3 / 7)) t := by
  have hn := pantsInversion_inner_boundary (planarCircleMap 3 1 t)
    (pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 1 t))
    (by simpa [planarCenter, planarRadius] using norm_planarCircleMap_sub 3 1 t)
  have hf : pantsInversion (planarCircleMap 3 1 t) ∉ pantsPermutationAnnulus := by
    intro h
    change ‖_‖ < 3 ∧ 1 / 2 < ‖_ - 3 / 2‖ at h
    rw [hn] at h
    exact lt_irrefl _ h.1
  change (planarBoundaryParameter (Equiv.swap (0 : Fin 3) 1 1)
    (pantsDiskRestoration (pantsInversion
      (planarCollar.{u} 3 (Or.inr rfl) 1 (t, halfZero)).val.down)) : ℂ) = _
  rw [planarCollar_zero_val, pantsDiskRestoration_fixed hf, Equiv.swap_apply_right]
  norm_num [planarBoundaryParameter, planarCenter]
  rw [coe_unitOf (norm_pos_iff.mp (by rw [hn]; norm_num)), hn]
  have hz : (3 / 2 : ℂ) + (1 / 2) * (t : ℂ)⁻¹ - 9 / 7 ≠ 0 := by
    have h := pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 1 t)
    simpa [planarCircleMap, planarCenter, planarRadius, ← Circle.coe_inv_eq_conj,
      Circle.coe_inv] using sub_ne_zero.mpr h
  have hd := Complex.diskMoebius_denominator_ne_zero
    (a := (-(3 / 7) : ℂ)) (by norm_num) (Circle.norm_coe t).le
  have hd' : (7 : ℂ) + (t : ℂ) * 3 ≠ 0 := by
    intro h
    have he : (t : ℂ) = -(7 / 3) := by linear_combination (1 / 3 : ℂ) * h
    have hn := Circle.norm_coe t
    rw [he] at hn
    norm_num at hn
  simp [Complex.real_smul, planarCircleMap, planarCenter, planarRadius,
    pantsInversion, Complex.diskMoebius, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  simp only [map_ofNat]
  field_simp [hz, hd, Circle.coe_ne_zero t]
  apply mul_right_cancel₀ hd'
  have hi := inv_mul_cancel₀ hd'
  linear_combination (-1323 * (t : ℂ) - 3087) * hi
theorem pantsOuterHoleBoundaryParameter_two (t : Circle) :
    (pantsOuterHoleBoundaryParameter.{u} 2 t : ℂ) =
      -Complex.diskMoebius (7 / 39) t := by
  have hi := pantsInversion_other_boundary (planarCircleMap 3 2 t)
    (pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 2 t))
    (by simpa [planarCenter, planarRadius] using norm_planarCircleMap_sub 3 2 t)
  have hK : pantsInversion (planarCircleMap 3 2 t) ∈
      closedBall (153 / 184 : ℂ) (15 / 184) := by
    simpa only [mem_closedBall, dist_eq_norm] using hi.le
  have hR := pantsDiskRestoration_agree hK
  have hn : ‖pantsDiskRestoration (pantsInversion (planarCircleMap 3 2 t)) + 3 / 2‖ =
      1 / 2 := by
    rw [hR, pantsDiskMotion_one_norm, hi]
    norm_num
  change (planarBoundaryParameter (Equiv.swap (0 : Fin 3) 1 2)
    (pantsDiskRestoration (pantsInversion
      (planarCollar.{u} 3 (Or.inr rfl) 2 (t, halfZero)).val.down)) : ℂ) = _
  rw [planarCollar_zero_val]
  norm_num [planarBoundaryParameter, planarCenter, Equiv.swap_apply_def]
  rw [coe_unitOf (norm_pos_iff.mp (by rw [hn]; norm_num)), hn, hR]
  have hz : -(3 / 2 : ℂ) + (1 / 2) * (t : ℂ)⁻¹ - 9 / 7 ≠ 0 := by
    have h := pants_ne_inversionCenter (planarCircleMap_mem_planarModel (by decide) 2 t)
    simpa [planarCircleMap, planarCenter, planarRadius, ← Circle.coe_inv_eq_conj,
      Circle.coe_inv] using sub_ne_zero.mpr h
  have ht : (t : ℂ) - 7 / 39 ≠ 0 := by
    intro h
    have hn := Circle.norm_coe t
    rw [sub_eq_zero.mp h] at hn
    norm_num at hn
  have hH (w : ℂ) : pantsDiskMotion 1 w =
      -(3 / 2) + (92 / 15) * (w - 153 / 184) := by
    change pantsDiskMotionCenter 1 + (pantsDiskMotionScale 1 : ℂ) * (w - 153 / 184) = _
    norm_num [pantsDiskMotionCenter, pantsDiskMotionScale, Real.smoothTransition.one]
  rw [hH]
  apply inv_injective
  rw [inv_inv, inv_neg, Complex.diskMoebius, inv_div]
  have hd : (7 : ℂ) - (t : ℂ) * 39 ≠ 0 := by
    rw [show (7 : ℂ) - (t : ℂ) * 39 = -(t - 7 / 39) * 39 by ring]
    exact mul_ne_zero (neg_ne_zero.mpr ht) (by norm_num)
  simp [Complex.real_smul, planarCircleMap, planarCenter,
    planarRadius, pantsInversion, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  simp only [map_ofNat]
  field_simp [hz, ht, Circle.coe_ne_zero t]
  ring_nf
  rw [show -(7 : ℂ) + (t : ℂ) * 39 = -(7 - (t : ℂ) * 39) by ring, inv_neg]
  apply mul_right_cancel₀ hd
  have hDI := inv_mul_cancel₀ hd
  linear_combination (205700040 * (t : ℂ) - 36920520) * hDI
theorem pantsOuterHoleBoundaryParameter_isotopic (j : Fin 3) :
    IsotopicDiffeomorph (pantsOuterHoleBoundaryParameter.{u} j)
      (Diffeomorph.refl (𝓡 1) Circle ∞) := by
  fin_cases j
  · have he : pantsOuterHoleBoundaryParameter.{u} 0 =
        circleMoebiusDiffeomorph (3 / 7) (Circle.exp 0) (by norm_num) (Circle.norm_coe _) := by
      ext t
      change (pantsOuterHoleBoundaryParameter.{u} 0 t : ℂ) =
        (Circle.exp 0 : ℂ) * Complex.diskMoebius (3 / 7) t
      rw [pantsOuterHoleBoundaryParameter_zero]
      simp
    change IsotopicDiffeomorph (pantsOuterHoleBoundaryParameter.{u} 0) _
    rw [he]
    exact circleMoebiusDiffeomorph_isotopic (3 / 7) 0 (by norm_num)
  · have he : pantsOuterHoleBoundaryParameter.{u} 1 =
        circleMoebiusDiffeomorph (-(3 / 7)) (Circle.exp 0) (by norm_num)
          (Circle.norm_coe _) := by
      ext t
      change (pantsOuterHoleBoundaryParameter.{u} 1 t : ℂ) =
        (Circle.exp 0 : ℂ) * Complex.diskMoebius (-(3 / 7)) t
      rw [pantsOuterHoleBoundaryParameter_one]
      simp
    change IsotopicDiffeomorph (pantsOuterHoleBoundaryParameter.{u} 1) _
    rw [he]
    exact circleMoebiusDiffeomorph_isotopic (-(3 / 7)) 0 (by norm_num)
  · have he : pantsOuterHoleBoundaryParameter.{u} 2 =
        circleMoebiusDiffeomorph (7 / 39) (Circle.exp Real.pi) (by norm_num)
          (Circle.norm_coe _) := by
      ext t
      change (pantsOuterHoleBoundaryParameter.{u} 2 t : ℂ) =
        (Circle.exp Real.pi : ℂ) * Complex.diskMoebius (7 / 39) t
      rw [pantsOuterHoleBoundaryParameter_two, Circle.coe_exp, Complex.exp_pi_mul_I,
        neg_one_mul]
    change IsotopicDiffeomorph (pantsOuterHoleBoundaryParameter.{u} 2) _
    rw [he]
    exact circleMoebiusDiffeomorph_isotopic (7 / 39) Real.pi (by norm_num)

open DifferentialGeometry.Topology.Manifold ElementaryPresentation

private theorem permutationHalfLift_coordinate (s : EuclideanHalfSpace 1) :
    halfSpaceOneLift (s.val 0) = s := by
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  change max (s.val 0) 0 = s.val 0
  exact max_eq_left s.property

theorem exists_boundaryMultiExtension_of_isotopic_identity {C : CompactCarrier} {k : ℕ}
    (b : BoundaryTori C k) (f : Fin k → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : ∀ j, IsotopicDiffeomorph (f j) (Diffeomorph.refl torusModel Torus ∞)) :
    ∃ Θ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier,
      ∀ j t s, s.val 0 ≤ 1 / 4 → Θ (b.collar j (t, s)) = b.collar j (f j t, s) := by
  classical
  choose F hF hFi hF0 hF1 using hf
  let G (j : Fin k) : ℝ → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
    fun s => F j (seamCut s)
  have hG (j : Fin k) : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => G j q.1 q.2) :=
    (hF j).comp ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hGi (j : Fin k) : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => (G j q.1).symm q.2) :=
    (hFi j).comp ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  let D (j : Fin k) := sliceDiffeomorph (G j) (hG j) (hGi j)
    (fun s : EuclideanHalfSpace 1 => s.val 0) contMDiff_halfSpaceOneCoordinate
  let K : Set (Torus × EuclideanHalfSpace 1) :=
    univ ×ˢ (halfSpaceOneLift '' Icc (0 : ℝ) (1 / 2))
  have hLift : Continuous halfSpaceOneLift := by
    rw [funext halfSpaceOneLift_eq]
    exact halfSpaceOneHomeomorph.symm.continuous.comp
      ((continuous_const.max continuous_id).subtype_mk fun s => le_max_left 0 s)
  have hK : IsCompact K := isCompact_univ.prod (isCompact_Icc.image hLift)
  have hKs : K ⊆ halfCollarSource := by
    rintro ⟨t, s⟩ ⟨ht, a, ha, rfl⟩
    change max a 0 < 1
    rw [max_eq_left ha.1]
    linarith [ha.2]
  have hfix : ∀ j z, z ∉ K → D j z = z := by
    intro j z hz
    have hle : 1 / 2 ≤ z.2.val 0 := by
      by_contra h
      apply hz
      exact ⟨mem_univ z.1, z.2.val 0,
        ⟨z.2.property, (not_le.mp h).le⟩, permutationHalfLift_coordinate z.2⟩
    change (F j (seamCut (z.2.val 0)) z.1, z.2) = z
    rw [seamCut_of_ge hle, hF1 j]
    rfl
  have hS : ∀ j z, z ∈ halfCollarSource → D j z ∈ halfCollarSource := by
    intro j z hz
    exact hz
  obtain ⟨Θ, hΘ⟩ := exists_multiTwist b.collar b.source_eq b.disjoint D hK hKs hfix hS
  refine ⟨Θ, fun j t s hs => ?_⟩
  have hsrc : (t, s) ∈ halfCollarSource := by
    change s.val 0 < 1
    linarith
  rw [hΘ j (t, s) hsrc]
  change b.collar j (F j (seamCut (s.val 0)) t, s) = b.collar j (f j t, s)
  rw [seamCut_of_le hs, hF0 j]

theorem pantsOuterHoleTorusParameter_symm_isotopic (j : Fin 3) :
    IsotopicDiffeomorph (pantsOuterHoleTorusParameter.{u} j).symm
      (Diffeomorph.refl torusModel Torus ∞) := by
  obtain ⟨F, hF, hFi, hF0, hF1⟩ := pantsOuterHoleBoundaryParameter_isotopic.{u} j
  refine ⟨fun s => (F s).symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞), ?_, ?_, ?_, ?_⟩
  · exact (hFi.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  · exact (hF.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  · dsimp only
    rw [hF0]
    rfl
  · dsimp only
    rw [hF1]
    rfl

theorem exists_pantsOuterHoleIdentityGermPermutation :
    ∃ δ > (0 : ℝ), ∃ P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle), ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
        P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
          (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j) (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, P, hP⟩ := exists_pantsOuterHoleGermPermutation.{u}
  obtain ⟨Θ, hΘ⟩ := exists_boundaryMultiExtension_of_isotopic_identity
    (productBoundaryTori.{u} 3 (Or.inr rfl))
    (fun j => (pantsOuterHoleTorusParameter.{u} (Equiv.swap 0 1 j)).symm)
    (fun j => pantsOuterHoleTorusParameter_symm_isotopic.{u} (Equiv.swap 0 1 j))
  let Q := (productDiffeomorph.{u} 3).trans (Θ.trans (productDiffeomorph.{u} 3).symm)
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), P.trans Q, fun j p hp hlt => ?_⟩
  change Q (P _) = _
  rw [hP j p hp (lt_of_lt_of_le hlt (min_le_left _ _))]
  have h := hΘ (Equiv.swap 0 1 j) (pantsOuterHoleTorusParameter.{u} j p.1) p.2
    (le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _)))
  rw [Equiv.swap_apply_self, Diffeomorph.symm_apply_apply] at h
  have he : Θ (productDiffeomorph.{u} 3
      (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j)
        (pantsOuterHoleBoundaryParameter.{u} j p.1.1, p.2), p.1.2)) =
      productDiffeomorph.{u} 3
        (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 0 1 j) (p.1.1, p.2), p.1.2) := h
  exact (congrArg (productDiffeomorph.{u} 3).symm he).trans
    ((productDiffeomorph.{u} 3).symm_apply_apply _)

open ElementaryPresentation

def PantsIdentityGerm (ρ : Fin 3 ≃ Fin 3) : Prop :=
  ∃ δ > (0 : ℝ), ∃ P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
    (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle), ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        (planarCollar.{u} 3 (Or.inr rfl) (ρ j) (p.1.1, p.2), p.1.2)

theorem PantsIdentityGerm.refl : PantsIdentityGerm.{u} (Equiv.refl (Fin 3)) :=
  ⟨1, by norm_num, Diffeomorph.refl _ _ ∞, fun _ _ _ _ => rfl⟩

theorem PantsIdentityGerm.trans {ρ σ : Fin 3 ≃ Fin 3}
    (hρ : PantsIdentityGerm.{u} ρ) (hσ : PantsIdentityGerm.{u} σ) :
    PantsIdentityGerm.{u} (ρ.trans σ) := by
  obtain ⟨δ, hδ, P, hP⟩ := hρ
  obtain ⟨η, hη, Q, hQ⟩ := hσ
  refine ⟨min δ η, lt_min hδ hη, P.trans Q, fun j p hp hlt => ?_⟩
  change Q (P _) = _
  rw [hP j p hp (lt_of_lt_of_le hlt (min_le_left _ _)),
    hQ (ρ j) p hp (lt_of_lt_of_le hlt (min_le_right _ _))]
  rfl

theorem cappingPantsNeg_collar (j : Fin 3) (p : Circle × EuclideanHalfSpace 1) :
    cappingPantsNegDiffeomorph (planarCollar.{u} 3 (Or.inr rfl) j p) =
      planarCollar 3 (Or.inr rfl) (Equiv.swap 1 2 j) (cappingCircleNeg p.1, p.2) := by
  fin_cases j
  · have he : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    change cappingPantsNegDiffeomorph (planarCollar.{u} 3 (Or.inr rfl) 0 p) =
      planarCollar 3 (Or.inr rfl) (Equiv.swap 1 2 0) (cappingCircleNeg p.1, p.2)
    rw [he]
    exact cappingPantsNeg_collar_outer.{u} p
  · simpa using cappingPantsNeg_collar_one.{u} p
  · simpa using cappingPantsNeg_collar_two.{u} p

theorem pantsIdentityGerm_swap_zero_two : PantsIdentityGerm.{u} (Equiv.swap 0 2) := by
  obtain ⟨δ, hδ, P, hP⟩ := exists_pantsOuterHoleIdentityGermPermutation.{u}
  let N := cappingPantsNegDiffeomorph.{u}.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  have hN (j : Fin 3) (p : Torus × EuclideanHalfSpace 1) :
      N (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        (planarCollar.{u} 3 (Or.inr rfl) (Equiv.swap 1 2 j)
          (cappingCircleNeg p.1.1, p.2), p.1.2) := by
    exact Prod.ext (cappingPantsNeg_collar.{u} j (p.1.1, p.2)) rfl
  refine ⟨δ, hδ, N.trans (P.trans N), fun j p hp hlt => ?_⟩
  change N (P (N _)) = _
  rw [hN j p]
  have hpn : ((cappingCircleNeg p.1.1, p.1.2), p.2) ∈ halfCollarSource := hp
  rw [hP (Equiv.swap 1 2 j) _ hpn hlt, hN]
  have he : Equiv.swap (1 : Fin 3) 2 (Equiv.swap 0 1 (Equiv.swap 1 2 j)) =
      Equiv.swap 0 2 j := by fin_cases j <;> decide
  have hn : cappingCircleNeg (cappingCircleNeg p.1.1) = p.1.1 :=
    cappingCircleNegDiffeomorph.symm_apply_apply p.1.1
  rw [he, hn]

theorem exists_pantsIdentityGermPermutation (ρ : Fin 3 ≃ Fin 3) :
    PantsIdentityGerm.{u} ρ := by
  have h01 : PantsIdentityGerm.{u} (Equiv.swap 0 1) :=
    exists_pantsOuterHoleIdentityGermPermutation.{u}
  have h02 : PantsIdentityGerm.{u} (Equiv.swap 0 2) := pantsIdentityGerm_swap_zero_two.{u}
  have hcases : ∀ ρ : Fin 3 ≃ Fin 3,
      ρ = Equiv.refl (Fin 3) ∨ ρ = Equiv.swap 0 1 ∨ ρ = Equiv.swap 0 2 ∨
      ρ = (Equiv.swap 0 1).trans (Equiv.swap 0 2) ∨
      ρ = (Equiv.swap 0 2).trans (Equiv.swap 0 1) ∨
      ρ = (Equiv.swap 0 1).trans ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) := by decide
  rcases hcases ρ with h | h | h | h | h | h <;> subst ρ
  · exact PantsIdentityGerm.refl
  · exact h01
  · exact h02
  · exact h01.trans h02
  · exact h02.trans h01
  · exact h01.trans (h02.trans h01)

end GC.Seifert
