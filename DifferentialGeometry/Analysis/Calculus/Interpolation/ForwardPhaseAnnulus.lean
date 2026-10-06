import DifferentialGeometry.Topology.LoopSpace.RadialLoopExtension
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis.ForwardPhaseAnnulus

/-- The forward angular interpolation becomes the identity strictly before `b`. -/
def cutoff (r b τ : ℝ) : ℝ :=
  1 - Real.smoothTransition ((τ - r) / ((r + b) / 2 - r))

theorem contDiff_cutoff (r b : ℝ) : ContDiff ℝ ∞ (cutoff r b) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem cutoff_mem_Icc (r b τ : ℝ) : cutoff r b τ ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg ((τ - r) / ((r + b) / 2 - r))
  have h1 := Real.smoothTransition.le_one ((τ - r) / ((r + b) / 2 - r))
  constructor <;> dsimp [cutoff] <;> linarith

theorem cutoff_eq_one {r b τ : ℝ} (hrb : r < b) (hτ : τ ≤ r) :
    cutoff r b τ = 1 := by
  have hd : 0 < (r + b) / 2 - r := by linarith
  rw [cutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ) hd.le), sub_zero]

theorem cutoff_lt_one {r b τ : ℝ} (hrb : r < b) (hτ : r < τ) :
    cutoff r b τ < 1 := by
  have hd : 0 < (r + b) / 2 - r := by linarith
  have hp := Real.smoothTransition.pos_of_pos (div_pos (sub_pos.mpr hτ) hd)
  dsimp [cutoff]
  linarith

theorem cutoff_eq_zero {r b τ : ℝ} (hrb : r < b) (hτ : (r + b) / 2 ≤ τ) :
    cutoff r b τ = 0 := by
  have hd : 0 < (r + b) / 2 - r := by linarith
  rw [cutoff, Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hd).mpr (by linarith))]
  ring

/-- A real lift; no inverse phase and no positive derivative are built into it. -/
def phaseLift (r b : ℝ) (φ : ℝ → ℝ) (τ t : ℝ) : ℝ :=
  (1 - cutoff r b τ) * t + cutoff r b τ * φ t

theorem phaseLift_add_one (r b : ℝ) {φ : ℝ → ℝ}
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (τ t : ℝ) :
    phaseLift r b φ τ (t + 1) = phaseLift r b φ τ t + 1 := by
  dsimp [phaseLift]
  rw [hp]
  ring

private theorem displacement_periodic {φ : ℝ → ℝ}
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    Periodic (fun t : ℝ => φ t - t) 1 := by
  intro t
  change φ (t + 1) - (t + 1) = φ t - t
  rw [hp]
  ring

/-- The literal displacement of the supplied real lift, not a newly chosen lift. -/
def displacement {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) : C(loopCircle, ℝ) :=
  periodicLoop (fun t : ℝ => φ t - t) (displacement_periodic hp)
    (hφ.continuous.sub continuous_id)

@[simp] theorem displacement_coe {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (t : ℝ) :
    displacement hφ hp (t : loopCircle) = φ t - t := rfl

private theorem slitPlane_pos_smul (τ : ℝ) (hτ : 0 < τ) (z : ℂ) :
    τ • z ∈ Complex.slitPlane ↔ z ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  constructor
  · rintro (hre | him)
    · exact Or.inl ((mul_pos_iff_of_pos_left hτ).mp hre)
    · exact Or.inr (fun hz => him (by rw [hz, mul_zero]))
  · rintro (hre | him)
    · exact Or.inl (mul_pos hτ hre)
    · exact Or.inr (mul_ne_zero hτ.ne' him)

private theorem radialLoopExtension_pos_smul (γ : C(loopCircle, ℝ))
    {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    radialLoopExtension γ (τ • z) = radialLoopExtension γ z := by
  classical
  have hslit := slitPlane_pos_smul τ hτ z
  by_cases hs : z ∈ Complex.slitPlane
  · rw [radialLoopExtension_eq₀ γ (hslit.mpr hs), radialLoopExtension_eq₀ γ hs]
    unfold radialLoopExtension₀
    rw [Complex.real_smul, Complex.arg_real_mul z hτ]
  · by_cases hz : z = 0
    · simp only [hz, smul_zero]
    · have hsτ : τ • z ∉ Complex.slitPlane := fun h => hs (hslit.mp h)
      have hzτ : τ • z ≠ 0 := smul_ne_zero hτ.ne' hz
      rw [radialLoopExtension, ite_eq_right hsτ, ite_eq_right hzτ,
        radialLoopExtension, ite_eq_right hs, ite_eq_right hz]
      unfold radialLoopExtension₁
      rw [← smul_neg, Complex.real_smul, Complex.arg_real_mul (-z) hτ]

/-- The actual planar map. Its angular displacement may be degenerate at `r`. -/
def map (r b : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (z : ℂ) : ℂ :=
  z * Complex.exp (((2 * Real.pi * cutoff r b ‖z‖ *
    radialLoopExtension (displacement hφ hp) z : ℝ) : ℂ) * Complex.I)

@[simp] theorem map_zero (r b : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) : map r b hφ hp 0 = 0 := by
  simp [map]

@[simp] theorem norm_map (r b : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (z : ℂ) :
    ‖map r b hφ hp z‖ = ‖z‖ := by
  simp [map, Complex.norm_exp, Complex.mul_re]

theorem map_eq_self {r b : ℝ} (hrb : r < b) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    {z : ℂ} (hz : (r + b) / 2 ≤ ‖z‖) : map r b hφ hp z = z := by
  simp [map, cutoff_eq_zero hrb hz]

/-- The literal lift identity, with the originally supplied phase. -/
theorem map_pos_smul_toCircle (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    map r b hφ hp (τ • (AddCircle.toCircle (t : loopCircle) : ℂ)) =
      τ • (AddCircle.toCircle (phaseLift r b φ τ t : loopCircle) : ℂ) := by
  have hd : radialLoopExtension (displacement hφ hp)
      (τ • (AddCircle.toCircle (t : loopCircle) : ℂ)) = φ t - t := by
    rw [radialLoopExtension_pos_smul _ hτ]
    change radialLoopExtension (displacement hφ hp) (diskBoundary (t : loopCircle) : ℂ) = _
    rw [radialLoopExtension_diskBoundary, displacement_coe]
  rw [map, hd]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, Circle.norm_coe, mul_one]
  have he (s : ℝ) : (AddCircle.toCircle (s : loopCircle) : ℂ) =
      Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]
  rw [he, he, Complex.real_smul, Complex.real_smul, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  dsimp [phaseLift]
  push_cast
  ring

theorem contDiffAt_map (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ ∞ (map r b hφ hp) z := by
  have hd : ContDiffAt ℝ ∞ (radialLoopExtension (displacement hφ hp)) z := by
    apply ContMDiffAt.contDiffAt
    apply (contMDiffOn_radialLoopExtension (displacement hφ hp) ?_).contMDiffAt
      (isOpen_ne_zero.mem_nhds hz)
    rw [contMDiff_iff_contDiff]
    change ContDiff ℝ ∞ (fun t : ℝ => φ t - t)
    exact hφ.sub contDiff_id
  have hχ := (contDiff_cutoff r b).contDiffAt.comp z (contDiffAt_norm ℝ hz)
  have ha : ContDiffAt ℝ ∞ (fun w : ℂ =>
      ((2 * Real.pi * cutoff r b ‖w‖ *
        radialLoopExtension (displacement hφ hp) w : ℝ) : ℂ) * Complex.I) z :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul hχ).mul hd)).mul contDiffAt_const)
  exact contDiffAt_id.mul ha.cexp

theorem contDiffOn_map (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    ContDiffOn ℝ ∞ (map r b hφ hp) {z : ℂ | z ≠ 0} :=
  fun _ hz => (contDiffAt_map r b hφ hp hz).contDiffWithinAt

/-- A compact annulus receives a finite forward bound even if the inverse
angular derivative is unbounded toward its inner boundary. -/
theorem exists_lipschitzOnWith_map {r b : ℝ} (hr : 0 < r)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (map r b hφ hp)
      {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b} := by
  have hcompact : IsCompact {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b} := by
    have he : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b} =
        Metric.closedBall (0 : ℂ) b ∩ {z : ℂ | r ≤ ‖z‖} := by
      ext z
      simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) b).inter_right
      (isClosed_le continuous_const continuous_norm)
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact
  intro z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hz.1)
  obtain ⟨K, t, ht, hKt⟩ :=
    ((contDiffAt_map r b hφ hp hz0).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hKt⟩

private theorem phaseLift_strictMono (r b τ : ℝ) {φ : ℝ → ℝ}
    (hm : StrictMono φ) : StrictMono (phaseLift r b φ τ) := by
  intro x y hxy
  have hα := cutoff_mem_Icc r b τ
  have hp := hm hxy
  dsimp [phaseLift]
  by_cases h1 : cutoff r b τ = 1
  · simpa [h1] using hp
  · have hlt : cutoff r b τ < 1 := lt_of_le_of_ne hα.2 h1
    have hpos := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hxy)
    have hnon := mul_nonneg hα.1 (sub_nonneg.mpr hp.le)
    nlinarith

private theorem phaseLift_surjective (r b τ : ℝ) (φ : ℝ ≃ₜ ℝ)
    (hm : StrictMono φ) : Surjective (phaseLift r b φ τ) := by
  intro y
  have hc : Continuous (phaseLift r b φ τ) :=
    (continuous_const.mul continuous_id).add (continuous_const.mul φ.continuous)
  have hα := cutoff_mem_Icc r b τ
  apply mem_range_of_exists_le_of_exists_ge hc
  · refine ⟨min y (φ.symm y), ?_⟩
    have h1 := min_le_left y (φ.symm y)
    have h2 : φ (min y (φ.symm y)) ≤ y := by
      simpa only [φ.apply_symm_apply] using hm.monotone (min_le_right y (φ.symm y))
    have ha := mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr h1)
    have hb := mul_nonneg hα.1 (sub_nonneg.mpr h2)
    dsimp [phaseLift]
    nlinarith
  · refine ⟨max y (φ.symm y), ?_⟩
    have h1 := le_max_left y (φ.symm y)
    have h2 : y ≤ φ (max y (φ.symm y)) := by
      simpa only [φ.apply_symm_apply] using hm.monotone (le_max_right y (φ.symm y))
    have ha := mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr h1)
    have hb := mul_nonneg hα.1 (sub_nonneg.mpr h2)
    dsimp [phaseLift]
    nlinarith

private def phaseHomeomorph (r b τ : ℝ) (φ : ℝ ≃ₜ ℝ)
    (hm : StrictMono φ) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (phaseLift r b φ τ)
    (phaseLift_strictMono r b τ hm) (phaseLift_surjective r b τ φ hm)).toHomeomorph

private def phaseCircle (r b τ : ℝ) (φ : ℝ ≃ₜ ℝ) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) : loopCircle ≃ₜ loopCircle :=
  affineCircleHomeomorph (phaseHomeomorph r b τ φ hm) (phaseLift_add_one r b hp τ)

private theorem phaseCircle_coe (r b τ : ℝ) (φ : ℝ ≃ₜ ℝ) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (t : ℝ) :
    phaseCircle r b τ φ hm hp (t : loopCircle) =
      (phaseLift r b φ τ t : loopCircle) := rfl

private def angle (z : ℂ) : loopCircle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z)

private theorem norm_smul_angle (z : ℂ) :
    ‖z‖ • (AddCircle.toCircle (angle z) : ℂ) = z := by
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp only [angle, Homeomorph.apply_symm_apply]
  exact radialDirection_reconstruct z

private theorem map_circle (r b : ℝ) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t)) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) {τ : ℝ} (hτ : 0 < τ)
    (θ : loopCircle) :
    map r b hφ hp (τ • (AddCircle.toCircle θ : ℂ)) =
      τ • (AddCircle.toCircle (phaseCircle r b τ φ hm hp θ) : ℂ) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [phaseCircle_coe]
  exact map_pos_smul_toCircle r b hφ hp hτ t

/-- Radial interpolation of an increasing circle homeomorphism is bijective,
including when the boundary phase has zero derivative. -/
theorem bijective_map (r b : ℝ) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t)) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) : Bijective (map r b hφ hp) := by
  constructor
  · intro z w hzw
    have hnorm : ‖z‖ = ‖w‖ := by simpa only [norm_map] using congrArg norm hzw
    by_cases hz : z = 0
    · have hw : w = 0 := norm_eq_zero.mp (by simpa [hz] using hnorm.symm)
      simp [hz, hw]
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ‖z‖ • (AddCircle.toCircle (phaseCircle r b ‖z‖ φ hm hp (angle z)) : ℂ) =
        ‖z‖ • (AddCircle.toCircle (phaseCircle r b ‖z‖ φ hm hp (angle w)) : ℂ) := by
      rw [← map_circle r b φ hφ hm hp hr, ← map_circle r b φ hφ hm hp hr,
        norm_smul_angle z, hnorm, norm_smul_angle w]
      exact hzw
    have hec : (AddCircle.toCircle (phaseCircle r b ‖z‖ φ hm hp (angle z)) : ℂ) =
        (AddCircle.toCircle (phaseCircle r b ‖z‖ φ hm hp (angle w)) : ℂ) := by
      apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
      simpa only [Complex.real_smul] using he
    have heθ : phaseCircle r b ‖z‖ φ hm hp (angle z) =
        phaseCircle r b ‖z‖ φ hm hp (angle w) := by
      apply (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective
      rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
      apply Subtype.ext
      exact hec
    have ha := (phaseCircle r b ‖z‖ φ hm hp).injective heθ
    calc
      z = ‖z‖ • (AddCircle.toCircle (angle z) : ℂ) := (norm_smul_angle z).symm
      _ = ‖w‖ • (AddCircle.toCircle (angle w) : ℂ) := by rw [hnorm, ha]
      _ = w := norm_smul_angle w
  · intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨‖w‖ • (AddCircle.toCircle
      ((phaseCircle r b ‖w‖ φ hm hp).symm (angle w)) : ℂ), ?_⟩
    rw [map_circle r b φ hφ hm hp hr, Homeomorph.apply_symm_apply, norm_smul_angle]

/-- Every radial set is preserved pointwise in radius and bijectively in angle. -/
theorem bijOn_map_radial (r b : ℝ) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t)) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) (S : Set ℝ) :
    BijOn (map r b hφ hp) {z : ℂ | ‖z‖ ∈ S} {z : ℂ | ‖z‖ ∈ S} := by
  refine ⟨fun z hz => ?_, (bijective_map r b φ hφ hm hp).injective.injOn, ?_⟩
  · simpa only [mem_ofPred_eq, norm_map] using hz
  · intro w hw
    obtain ⟨z, hz⟩ := (bijective_map r b φ hφ hm hp).surjective w
    refine ⟨z, ?_, hz⟩
    have he : ‖z‖ = ‖w‖ := by simpa only [norm_map] using congrArg norm hz
    simpa only [mem_ofPred_eq, he] using hw

theorem exists_annulus_homeomorph {r b : ℝ} (hr : 0 < r)
    (φ : ℝ ≃ₜ ℝ) (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t)) (hm : StrictMono φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    ∃ e : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b} ≃ₜ {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b},
      ∀ z, (e z : ℂ) = map r b hφ hp z := by
  let A : Set ℂ := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ b}
  have hA : IsCompact A := by
    have he : A = Metric.closedBall (0 : ℂ) b ∩ {z : ℂ | r ≤ ‖z‖} := by
      ext z
      simp only [A, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) b).inter_right
      (isClosed_le continuous_const continuous_norm)
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hb := bijOn_map_radial r b φ hφ hm hp (Icc r b)
  let f : A → A := fun z => ⟨map r b hφ hp z, hb.mapsTo z.property⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro z
    exact (contDiffAt_map r b hφ hp
      (norm_pos_iff.mp (hr.trans_le z.property.1))).continuousAt.comp
        continuous_subtype_val.continuousAt
  have hfb : Bijective f := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      exact hb.injOn z.property w.property (congrArg Subtype.val hzw)
    · intro w
      obtain ⟨z, hz, hzw⟩ := hb.surjOn w.property
      exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩
  exact ⟨IsHomeomorph.homeomorph f
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hfc, hfb⟩), fun _ => rfl⟩

private def coordinates (r b : ℝ) (φ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, phaseLift r b φ p.1 p.2)

private theorem contDiff_coordinates (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (coordinates r b φ) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cutoff r b p.1) :=
    (contDiff_cutoff r b).comp contDiff_fst
  exact contDiff_fst.prodMk (((contDiff_const.sub hc).mul contDiff_snd).add
    (hc.mul (hφ.comp contDiff_snd)))

private theorem fderiv_coordinates_apply (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p v : ℝ × ℝ) :
    fderiv ℝ (coordinates r b φ) p v =
      (v.1, deriv (cutoff r b) p.1 * (φ p.2 - p.2) * v.1 +
        (1 - cutoff r b p.1 + cutoff r b p.1 * deriv φ p.2) * v.2) := by
  have hc := ((contDiff_cutoff r b).differentiable (by simp) p.1).hasDerivAt.comp_hasFDerivAt
    p (hasFDerivAt_fst (𝕜 := ℝ))
  have hf := (hφ.differentiable (by simp) p.2).hasDerivAt.comp_hasFDerivAt
    p (hasFDerivAt_snd (𝕜 := ℝ))
  have hd := (((hasFDerivAt_const (1 : ℝ) p).sub hc).mul
    (hasFDerivAt_snd (𝕜 := ℝ))).add (hc.mul hf)
  have hdcoords := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hd
  change HasFDerivAt (𝕜 := ℝ) (coordinates r b φ) _ p at hdcoords
  rw [hdcoords.fderiv]
  ext <;> simp
  ring

private theorem bijective_fderiv_coordinates (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p : ℝ × ℝ)
    (hB : 1 - cutoff r b p.1 + cutoff r b p.1 * deriv φ p.2 ≠ 0) :
    Bijective (fderiv ℝ (coordinates r b φ) p) := by
  let A := deriv (cutoff r b) p.1 * (φ p.2 - p.2)
  let B := 1 - cutoff r b p.1 + cutoff r b p.1 * deriv φ p.2
  have hv (v : ℝ × ℝ) : fderiv ℝ (coordinates r b φ) p v =
      (v.1, A * v.1 + B * v.2) := fderiv_coordinates_apply r b hφ p v
  constructor
  · intro v w h
    rw [hv, hv] at h
    have h1 := congrArg (fun u : ℝ × ℝ => u.1) h
    have h2 := congrArg (fun u : ℝ × ℝ => u.2) h
    change v.1 = w.1 at h1
    change A * v.1 + B * v.2 = A * w.1 + B * w.2 at h2
    apply Prod.ext
    · exact h1
    · apply mul_left_cancel₀ hB
      change B * v.2 = B * w.2
      rw [h1] at h2
      linarith
  · intro w
    refine ⟨(w.1, (w.2 - A * w.1) / B), ?_⟩
    rw [hv]
    apply Prod.ext
    · rfl
    · change A * w.1 + B * ((w.2 - A * w.1) / B) = w.2
      have hb : B ≠ 0 := hB
      field_simp [hb]
      ring

private def polarScale : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ ℝ)

private def polar (p : ℝ × ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm (polarCoord.symm (polarScale p))

private theorem polar_apply (p : ℝ × ℝ) :
    polar p = p.1 • (AddCircle.toCircle (p.2 : loopCircle) : ℂ) := by
  change Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2) = _
  rw [Complex.polarCoord_symm_apply, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one,
    Complex.exp_mul_I, Complex.real_smul]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

private theorem norm_polar (p : ℝ × ℝ) : ‖polar p‖ = |p.1| := by
  rw [polar_apply, norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one]

private theorem hasFDerivAt_polar (p : ℝ × ℝ) :
    HasFDerivAt polar
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
        ((fderivPolarCoordSymm (polarScale p)).comp polarScale)) p :=
  Complex.equivRealProdCLM.symm.hasFDerivAt.comp p
    ((hasFDerivAt_polarCoord_symm (polarScale p)).comp p polarScale.hasFDerivAt)

private theorem bijective_fderiv_polar (p : ℝ × ℝ) (hp : 0 < p.1) :
    Bijective (fderiv ℝ polar p) := by
  have hs : Bijective polarScale := by
    constructor
    · intro x y h
      have h1 := congrArg (fun u : ℝ × ℝ => u.1) h
      have h2 := congrArg (fun u : ℝ × ℝ => u.2) h
      change x.1 = y.1 at h1
      change (2 * Real.pi) * x.2 = (2 * Real.pi) * y.2 at h2
      exact Prod.ext h1 (mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0) h2)
    · intro y
      refine ⟨(y.1, y.2 / (2 * Real.pi)), ?_⟩
      apply Prod.ext
      · rfl
      · change (2 * Real.pi) * (y.2 / (2 * Real.pi)) = y.2
        field_simp
  have hd : (fderivPolarCoordSymm (polarScale p)).toLinearMap.det ≠ 0 := by
    change (fderivPolarCoordSymm (polarScale p)).det ≠ 0
    rw [det_fderivPolarCoordSymm]
    exact hp.ne'
  have hb : Bijective (fderivPolarCoordSymm (polarScale p)) :=
    ((fderivPolarCoordSymm (polarScale p)).toLinearMap.equivOfDetNeZero hd).bijective
  rw [(hasFDerivAt_polar p).fderiv]
  exact Complex.equivRealProdCLM.symm.bijective.comp (hb.comp hs)

private theorem map_polar (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    {p : ℝ × ℝ} (hp0 : 0 < p.1) :
    map r b hφ hp (polar p) = polar (coordinates r b φ p) := by
  simpa only [polar_apply, coordinates] using
    map_pos_smul_toCircle r b hφ hp hp0 p.2

private theorem bijective_fderiv_map_polar (r b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    {p : ℝ × ℝ} (hp0 : 0 < p.1)
    (hangular : 0 < 1 - cutoff r b p.1 + cutoff r b p.1 * deriv φ p.2) :
    Bijective (fderiv ℝ (map r b hφ hp) (polar p)) := by
  have hpz : polar p ≠ 0 := by
    intro h
    have hn := congrArg norm h
    rw [norm_polar, norm_zero, abs_of_pos hp0] at hn
    exact hp0.ne' hn
  have hH := (contDiffAt_map r b hφ hp hpz).differentiableAt (by simp)
  have hP := (hasFDerivAt_polar p).differentiableAt
  have hQ := (hasFDerivAt_polar (coordinates r b φ p)).differentiableAt
  have hG := (contDiff_coordinates r b hφ).differentiable (by simp) p
  have he : (map r b hφ hp ∘ polar) =ᶠ[𝓝 p] (polar ∘ coordinates r b φ) := by
    filter_upwards [(continuous_fst.tendsto p) (Ioi_mem_nhds hp0)] with q hq
    exact map_polar r b hφ hp hq
  have heD : (fderiv ℝ (map r b hφ hp) (polar p)).comp (fderiv ℝ polar p) =
      (fderiv ℝ polar (coordinates r b φ p)).comp (fderiv ℝ (coordinates r b φ) p) := by
    rw [← fderiv_comp p hH hP, he.fderiv_eq, fderiv_comp p hQ hG]
  have hcomp : Bijective
      ((fderiv ℝ (map r b hφ hp) (polar p)) ∘ (fderiv ℝ polar p)) := by
    change Bijective ((fderiv ℝ (map r b hφ hp) (polar p)).comp (fderiv ℝ polar p))
    rw [heD]
    exact (bijective_fderiv_polar (coordinates r b φ p) hp0).comp
      (bijective_fderiv_coordinates r b hφ p hangular.ne')
  exact (Function.Bijective.of_comp_iff _ (bijective_fderiv_polar p hp0)).mp hcomp

/-- On the open side of the inner circle the identity term supplies all missing
angular rank; no lower bound on the original phase derivative is assumed. -/
theorem bijective_fderiv_map_of_radius_gt {r b : ℝ} (hr : 0 < r) (hrb : r < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) {z : ℂ} (hz : r < ‖z‖) :
    Bijective (fderiv ℝ (map r b hφ hp) z) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (angle z)
  have he : polar (‖z‖, t) = z := by rw [polar_apply, ht, norm_smul_angle]
  rw [← he]
  apply bijective_fderiv_map_polar r b hφ hp (hr.trans hz)
  have hc := cutoff_lt_one hrb hz
  have hn := mul_nonneg (cutoff_mem_Icc r b ‖z‖).1 (hm.deriv_nonneg (x := t))
  change 0 < 1 - cutoff r b ‖z‖ + cutoff r b ‖z‖ * deriv φ t
  linarith

/-- The actual inner seam is nonsingular at every point with positive phase
speed, even when the phase speed vanishes elsewhere on the same circle. -/
theorem bijective_fderiv_map_at_inner {r b : ℝ} (hr : 0 < r) (hrb : r < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) {t : ℝ} (ht : 0 < deriv φ t) :
    Bijective (fderiv ℝ (map r b hφ hp)
      (r • (AddCircle.toCircle (t : loopCircle) : ℂ))) := by
  rw [← polar_apply (r, t)]
  apply bijective_fderiv_map_polar r b hφ hp hr
  simpa only [cutoff_eq_one hrb le_rfl, sub_self, zero_add, one_mul] using ht

end DifferentialGeometry.Analysis.ForwardPhaseAnnulus
