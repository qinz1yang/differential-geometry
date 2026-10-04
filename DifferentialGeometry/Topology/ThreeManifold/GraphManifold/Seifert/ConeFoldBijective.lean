import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldTopology

/-!
# Bijectivity of the cone fold from local data

Lane A4Q (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §8 and erratum
item 8). For a `ConeShape` `σ` the target is `basePlus = {‖u‖ < 3, 0 ≤ Im u}`, with the hole
`‖u + 3/2‖ > 1/2` removed when `v₂` is the cusp `0` (`θ₂ = 0`). `bijOn_of_local` turns the local
facts of the concrete fold (smoothness on an open set containing the closed triangle, positive
Jacobian off the vertices, real values exactly on the walls, injectivity, the one-sided wall
images, the vertex values and the cusp limits) into `Set.BijOn f σ.triangle σ.basePlus` by
K16f's open–closed argument: `f` of the open triangle is open (inverse function theorem), hence
lies in `{Im > 0}`; it is closed in the preconnected open upper target because the cusp limits
confine the preimage of a neighbourhood to the compact truncation `{Im z ≤ Y, δ ≤ ‖z‖}` of the
triangle and the walls have real image (`isPreconnected_upperDisc`, `isCompact_truncation`,
`closure_image_inter_subset`); the real segments are reached by the intermediate value theorem
along the three walls (`exists_wallOne_eq`, `exists_wallZero_eq`, `exists_wallTwo_eq`). No apex
germ and no monotonicity along the walls is needed; the vertices lie on the walls and never
enter the interior argument. `im_eq_zero_of_wall_identities` derives the wall reality from the
frozen reflection identities.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def upperDisc (S : Set ℂ) : Set ℂ := {u | ‖u‖ < 3 ∧ 0 < u.im ∧ ∀ c ∈ S, 1 / 2 < ‖u - c‖}

private def arcSet : Set ℂ :=
  (fun θ : ℝ => ((5 / 2 : ℝ) : ℂ) * exp (θ * I)) '' Set.Ioo 0 Real.pi

private theorem isPreconnected_arcSet : IsPreconnected arcSet :=
  isPreconnected_Ioo.image _ (by fun_prop)

private theorem mem_arcSet {v : ℂ} (hv : ‖v‖ = 5 / 2) (him : 0 < v.im) : v ∈ arcSet := by
  refine ⟨Complex.arg v, ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him.le) fun h => by
    have := Complex.arg_eq_zero_iff.1 h.symm
    linarith [this.2], ?_⟩, ?_⟩
  · exact lt_of_le_of_ne (Complex.arg_le_pi v) fun h => by
      have := Complex.arg_eq_pi_iff.1 h
      linarith [this.2]
  · change ((5 / 2 : ℝ) : ℂ) * exp ((Complex.arg v : ℂ) * I) = v
    rw [← hv]
    exact Complex.norm_mul_exp_arg_mul_I v

private theorem arcSet_subset {S : Set ℂ} (hS : ∀ c ∈ S, c.im = 0 ∧ ‖c‖ ≤ 3 / 2) :
    arcSet ⊆ upperDisc S := by
  rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
  have hn : ‖((5 / 2 : ℝ) : ℂ) * exp (θ * I)‖ = 5 / 2 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real]
    norm_num
  refine ⟨by rw [hn]; norm_num, ?_, fun c hc => ?_⟩
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have := Real.sin_pos_of_pos_of_lt_pi h0 h1
    positivity
  · have h2 := norm_sub_norm_le (((5 / 2 : ℝ) : ℂ) * exp (θ * I)) c
    rw [hn] at h2
    linarith [(hS c hc).2]

theorem isPreconnected_upperDisc {S : Set ℂ} (hS : ∀ c ∈ S, c.im = 0 ∧ ‖c‖ ≤ 3 / 2) :
    IsPreconnected (upperDisc S) := by
  have hbase : ((5 / 2 : ℝ) : ℂ) * exp ((Real.pi / 2 : ℝ) * I) ∈ arcSet :=
    ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩
  refine isPreconnected_of_forall (((5 / 2 : ℝ) : ℂ) * exp ((Real.pi / 2 : ℝ) * I))
    fun u hu => ?_
  obtain ⟨hn3, him, hholes⟩ := hu
  have hu0 : 0 < ‖u‖ := by
    rw [norm_pos_iff]
    rintro rfl
    simp at him
  rcases le_or_gt (5 / 2) ‖u‖ with hbig | hsmall
  · let seg := (fun t : ℝ => (t : ℂ) * u) '' Set.Icc ((5 / 2) / ‖u‖) 1
    have hk : (5 / 2) / ‖u‖ ≤ 1 := (div_le_one hu0).2 hbig
    refine ⟨seg ∪ arcSet, ?_, Or.inr hbase, Or.inl ⟨1, ⟨hk, le_rfl⟩, by simp⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ ⟨(5 / 2) / ‖u‖, ⟨le_rfl, hk⟩, rfl⟩
        (mem_arcSet ?_ ?_) isPreconnected_arcSet⟩
    · rintro w (⟨t, ⟨ht1, ht2⟩, rfl⟩ | hw)
      · have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
        have hnt : ‖(t : ℂ) * u‖ = t * ‖u‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        have hlo : 5 / 2 ≤ t * ‖u‖ := by rwa [div_le_iff₀ hu0] at ht1
        have hhi : t * ‖u‖ ≤ ‖u‖ := by nlinarith
        refine ⟨by rw [hnt]; linarith, ?_, fun c hc => ?_⟩
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          positivity
        · have h2 := norm_sub_norm_le ((t : ℂ) * u) c
          rw [hnt] at h2
          linarith [(hS c hc).2]
      · exact arcSet_subset hS hw
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      positivity
  · have hre : |u.re| < 5 / 2 := by
      have := Complex.abs_re_le_norm u
      linarith
    have hq : 0 < 25 / 4 - u.re ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 hre).1 (abs_lt.1 hre).2
      nlinarith
    set T := Real.sqrt (25 / 4 - u.re ^ 2)
    have hT2 : T ^ 2 = 25 / 4 - u.re ^ 2 := Real.sq_sqrt hq.le
    have hT0 : 0 < T := Real.sqrt_pos.2 hq
    have hnu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hiT : u.im < T := by nlinarith
    let seg := (fun t : ℝ => (u.re : ℂ) + (t : ℂ) * I) '' Set.Icc u.im T
    have hend : (u.re : ℂ) + (T : ℂ) * I ∈ arcSet := by
      apply mem_arcSet
      · have : ‖(u.re : ℂ) + (T : ℂ) * I‖ ^ 2 = (5 / 2) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          nlinarith
        exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1 this
      · simpa using hT0
    refine ⟨seg ∪ arcSet, ?_, Or.inr hbase, Or.inl ⟨u.im, ⟨le_rfl, hiT.le⟩, ?_⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ ⟨T, ⟨hiT.le, le_rfl⟩, rfl⟩ hend
        isPreconnected_arcSet⟩
    · rintro w (⟨t, ⟨ht1, ht2⟩, rfl⟩ | hw)
      · have hw2 : ∀ c : ℂ, ‖(u.re : ℂ) + (t : ℂ) * I - c‖ ^ 2 =
            (u.re - c.re) ^ 2 + (t - c.im) ^ 2 := by
          intro c
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        have hu2 : ∀ c : ℂ, ‖u - c‖ ^ 2 = (u.re - c.re) ^ 2 + (u.im - c.im) ^ 2 := by
          intro c
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        refine ⟨?_, ?_, fun c hc => ?_⟩
        · have h0 := hw2 0
          simp only [Complex.zero_re, Complex.zero_im, sub_zero] at h0
          have : ‖(u.re : ℂ) + (t : ℂ) * I‖ ^ 2 < 3 ^ 2 := by nlinarith
          exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).1 this
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
          linarith
        · obtain ⟨hci, -⟩ := hS c hc
          have h0 := hw2 c
          have h1 := hu2 c
          have h3 := hholes c hc
          have h3' : (1 / 2) ^ 2 < ‖u - c‖ ^ 2 := by nlinarith [norm_nonneg (u - c)]
          rw [hci] at h0 h1
          have : (1 / 2) ^ 2 < ‖(u.re : ℂ) + (t : ℂ) * I - c‖ ^ 2 := by nlinarith
          exact (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).1 this
      · exact arcSet_subset hS hw
    · exact Complex.re_add_im u

theorem norm_of_im_eq_zero {u : ℂ} (h : u.im = 0) : ‖u‖ = |u.re| := by
  have e : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [h])
  calc ‖u‖ = ‖(u.re : ℂ)‖ := by rw [← e]
    _ = |u.re| := by rw [Complex.norm_real, Real.norm_eq_abs]

theorem norm_add_three_halves_of_im_eq_zero {u : ℂ} (h : u.im = 0) :
    ‖u + 3 / 2‖ = |u.re + 3 / 2| := by
  have e : u + 3 / 2 = ((u.re + 3 / 2 : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [e, Complex.norm_real, Real.norm_eq_abs]

def wallZeroPt (y : ℝ) : ℂ := (y : ℂ) * I

@[simp] theorem wallZeroPt_re (y : ℝ) : (wallZeroPt y).re = 0 := by
  simp [wallZeroPt]

@[simp] theorem wallZeroPt_im (y : ℝ) : (wallZeroPt y).im = y := by
  simp [wallZeroPt]

theorem continuous_wallZeroPt : Continuous wallZeroPt := by
  unfold wallZeroPt
  fun_prop

theorem norm_wallZeroPt {y : ℝ} (hy : 0 ≤ y) : ‖wallZeroPt y‖ = y := by
  rw [wallZeroPt, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hy]

namespace ConeShape

variable (σ : ConeShape)

def openTarget : Set ℂ := {u | ‖u‖ < 3 ∧ 0 < u.im ∧ (σ.θ₂ = 0 → 1 / 2 < ‖u + 3 / 2‖)}

def triangleInterior : Set ℂ := {z | 0 < z.im ∧ ∀ i, 0 < σ.wallSide i z}

theorem continuous_wallSide (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact Complex.continuous_re
  · exact continuous_const.sub Complex.continuous_re
  · change Continuous fun z : ℂ => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16
    fun_prop

theorem isOpen_triangleInterior : IsOpen σ.triangleInterior := by
  have : σ.triangleInterior = {z | 0 < z.im} ∩ ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp [triangleInterior]
  rw [this]
  exact (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (σ.continuous_wallSide i))

theorem triangleInterior_subset : σ.triangleInterior ⊆ σ.triangle :=
  fun _ hz => ⟨hz.1, fun i => (hz.2 i).le⟩

theorem exists_wall_of_not_mem_interior {z : ℂ} (hz : z ∈ σ.triangle)
    (hz' : z ∉ σ.triangleInterior) : ∃ i, σ.wallSide i z = 0 := by
  by_contra hc
  push Not at hc
  exact hz' ⟨hz.1, fun i => lt_of_le_of_ne (hz.2 i) (Ne.symm (hc i))⟩

theorem vertexOne_not_mem_triangleInterior : σ.vertexOne ∉ σ.triangleInterior := fun h => by
  have := h.2 1
  change 0 < σ.width - σ.vertexOne.re at this
  rw [vertexOne_re] at this
  linarith

theorem vertexTwo_not_mem_triangleInterior : σ.vertexTwo ∉ σ.triangleInterior := fun h => by
  have := h.2 0
  change 0 < σ.vertexTwo.re at this
  rw [vertexTwo_re] at this
  linarith

theorem centre_mem_triangleInterior : (⟨σ.width / 2, 1⟩ : ℂ) ∈ σ.triangleInterior := by
  have hW := σ.width_pos
  refine ⟨by change (0 : ℝ) < 1; norm_num, fun i => ?_⟩
  fin_cases i
  · change 0 < σ.width / 2
    positivity
  · change 0 < σ.width - σ.width / 2
    linarith
  · change 0 < (σ.width / 2 - σ.centre) ^ 2 + (1 : ℝ) ^ 2 - 1 / 16
    nlinarith [sq_nonneg (σ.width / 2 - σ.centre)]

theorem isOpen_openTarget : IsOpen σ.openTarget := by
  have : σ.openTarget = ({u | ‖u‖ < 3} ∩ {u | 0 < u.im}) ∩
      {u | σ.θ₂ = 0 → 1 / 2 < ‖u + 3 / 2‖} := by
    ext u
    simp [openTarget, and_assoc]
  rw [this]
  refine ((isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter ?_
  by_cases h : σ.θ₂ = 0
  · simp only [h, true_implies]
    exact isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)
  · have e : {u : ℂ | σ.θ₂ = 0 → 1 / 2 < ‖u + 3 / 2‖} = Set.univ := by
      ext u
      simp [h]
    rw [e]
    exact isOpen_univ

theorem isPreconnected_openTarget : IsPreconnected σ.openTarget := by
  have : σ.openTarget = upperDisc {c | σ.θ₂ = 0 ∧ c = -(3 / 2)} := by
    ext u
    simp only [openTarget, upperDisc, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h3, h2⟩
      refine ⟨h1, h3, ?_⟩
      rintro c ⟨hc, rfl⟩
      rw [sub_neg_eq_add]
      exact h2 hc
    · rintro ⟨h1, h3, h2⟩
      refine ⟨h1, h3, fun hc => ?_⟩
      have := h2 (-(3 / 2)) ⟨hc, rfl⟩
      rwa [sub_neg_eq_add] at this
  rw [this]
  refine isPreconnected_upperDisc ?_
  rintro c ⟨-, rfl⟩
  constructor
  · simp
  · rw [norm_neg]
    norm_num

theorem cos_θ₁_lt_one' : Real.cos σ.θ₁ < 1 := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [σ.θ₁_le, Real.pi_pos])
    σ.θ₁_pos
  rwa [Real.cos_zero] at this

theorem cos_θ₂_lt_one (h : 0 < σ.θ₂) : Real.cos σ.θ₂ < 1 := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [σ.θ₂_le, Real.pi_pos]) h
  rwa [Real.cos_zero] at this

theorem width_sub_centre : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by
  unfold width centre
  ring

theorem centre_le_quarter : σ.centre ≤ 1 / 4 := by
  unfold centre
  linarith [Real.cos_le_one σ.θ₂]

theorem centre_nonneg : 0 ≤ σ.centre := by
  unfold centre
  linarith [σ.cos_θ₂_nonneg]

theorem im_pos_of_truncation {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ z.im)
    (hw : ∀ i, 0 ≤ σ.wallSide i z) (hn : δ ≤ ‖z‖) : 0 < z.im := by
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  have h0' := hw 0
  have h1' := hw 1
  have h2' := hw 2
  change 0 ≤ z.re at h0'
  change 0 ≤ σ.width - z.re at h1'
  change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at h2'
  rw [← h] at h2'
  have hc1 := σ.cos_θ₁_lt_one'
  have hW := σ.width_sub_centre
  have hcq := σ.centre_le_quarter
  have hs1 : z.re - σ.centre < 1 / 4 := by linarith
  have hs2 : -(1 / 4) ≤ z.re - σ.centre := by linarith
  have hsq : (z.re - σ.centre) ^ 2 ≤ 1 / 16 := by nlinarith
  have hprod : (z.re - σ.centre - 1 / 4) * (z.re - σ.centre + 1 / 4) = 0 := by nlinarith
  rcases mul_eq_zero.1 hprod with hp | hp
  · linarith
  have hx : z.re = 0 := by linarith
  have hz : z = 0 := Complex.ext hx (by simpa using h.symm)
  rw [hz, norm_zero] at hn
  linarith

theorem isCompact_truncation (Y δ : ℝ) (hδ : 0 < δ) :
    IsCompact {z ∈ σ.triangle | z.im ≤ Y ∧ δ ≤ ‖z‖} := by
  have heq : {z ∈ σ.triangle | z.im ≤ Y ∧ δ ≤ ‖z‖} =
      ({z : ℂ | 0 ≤ z.im} ∩ ⋂ i, {z | 0 ≤ σ.wallSide i z}) ∩
        ({z | z.im ≤ Y} ∩ {z | δ ≤ ‖z‖}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, triangle]
    constructor
    · rintro ⟨⟨h0, hw⟩, hY, hn⟩
      exact ⟨⟨h0.le, hw⟩, hY, hn⟩
    · rintro ⟨⟨h0, hw⟩, hY, hn⟩
      exact ⟨⟨σ.im_pos_of_truncation hδ h0 hw hn, hw⟩, hY, hn⟩
  rw [heq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_iInter fun i => isClosed_le continuous_const (σ.continuous_wallSide i))).inter
      ((isClosed_le Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const continuous_norm))
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨σ.width + |Y|, ?_⟩
    rintro z ⟨⟨h0, hw⟩, hY, -⟩
    have h0' := Set.mem_iInter.1 hw 0
    have h1' := Set.mem_iInter.1 hw 1
    change 0 ≤ z.re at h0'
    change 0 ≤ σ.width - z.re at h1'
    change 0 ≤ z.im at h0
    change z.im ≤ Y at hY
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ σ.width + |Y| := by
        rw [abs_of_nonneg h0', abs_of_nonneg h0]
        have := le_abs_self Y
        gcongr
        · linarith
        · linarith

theorem sin_θ₂_div_four_le_norm {z : ℂ} (hz : z ∈ σ.triangle) : Real.sin σ.θ₂ / 4 ≤ ‖z‖ := by
  have h0 := hz.2 0
  have h2 := hz.2 2
  change 0 ≤ z.re at h0
  change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at h2
  have hc := σ.centre_nonneg
  have hcen : σ.centre = Real.cos σ.θ₂ / 4 := rfl
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hs := Real.sin_sq_add_cos_sq σ.θ₂
  have hsq : (Real.sin σ.θ₂ / 4) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hn]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by linarith [σ.sin_θ₂_nonneg]) (norm_nonneg _) (by norm_num)).1 hsq

theorem im_eq_zero_of_wall_identities {f : ℂ → ℂ}
    (hwall : ∀ i : Fin 3, ∃ V : Set ℂ, σ.foldWall i ⊆ V ∧
      ∀ z ∈ V, f (σ.refl i z) = conj (f z)) :
    ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0 := by
  intro i z hz hw
  obtain ⟨V, hV, hV'⟩ := hwall i
  have := hV' z (hV ⟨hz, hw⟩)
  rw [σ.refl_of_wallSide_eq_zero hz.1 hw] at this
  exact Complex.conj_eq_iff_im.1 this.symm

section Local

variable {σ}
variable {U : Set ℂ} {f : ℂ → ℂ}

theorem isOpen_image_triangleInterior (hU : IsOpen U) (hTU : σ.triangle ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ f z).det ≠ 0) :
    IsOpen (f '' σ.triangleInterior) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hzU := hTU (σ.triangleInterior_subset hz)
  exact image_mem_nhds_of_det_ne_zero (σ.isOpen_triangleInterior.mem_nhds hz)
    (hf.contDiffAt (hU.mem_nhds hzU))
    (hdet z hzU (fun h => σ.vertexOne_not_mem_triangleInterior (h ▸ hz))
      (fun h => σ.vertexTwo_not_mem_triangleInterior (h ▸ hz)))

theorem mapsTo_triangleInterior_openTarget (hopen : IsOpen (f '' σ.triangleInterior))
    (hmaps : Set.MapsTo f σ.triangle σ.basePlus) :
    Set.MapsTo f σ.triangleInterior σ.openTarget := by
  intro z hz
  have hfz := hmaps (σ.triangleInterior_subset hz)
  refine ⟨hfz.1, lt_of_le_of_ne hfz.2.1 fun h0 => ?_, hfz.2.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen (f z) ⟨z, hz, rfl⟩
  have hmem : f z - ((r / 2 : ℝ) : ℂ) * I ∈ Metric.ball (f z) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨w, hw, hfw⟩ := hball hmem
  have := (hmaps (σ.triangleInterior_subset hw)).2.1
  rw [hfw] at this
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at this
  linarith

theorem closure_image_inter_subset (hTU : σ.triangle ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hinf : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ σ.triangle, Y < z.im → 3 - ε < ‖f z‖)
    (hzero : σ.θ₂ = 0 → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ →
      ‖f z + 3 / 2‖ < 1 / 2 + ε) :
    closure (f '' σ.triangleInterior) ∩ σ.openTarget ⊆ f '' σ.triangleInterior := by
  rintro v ⟨hvc, hv3, hvim, hvh⟩
  obtain ⟨Y, hY⟩ := hinf ((3 - ‖v‖) / 2) (by linarith)
  set s := (‖v + 3 / 2‖ + 1 / 2) / 2 with hs
  set N := {w : ℂ | ‖w‖ < (‖v‖ + 3) / 2 ∧ (σ.θ₂ = 0 → s < ‖w + 3 / 2‖)} with hN
  have hNo : IsOpen N := by
    refine (isOpen_lt continuous_norm continuous_const).inter ?_
    by_cases h : σ.θ₂ = 0
    · simp only [h, true_implies]
      exact isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)
    · have e : {w : ℂ | σ.θ₂ = 0 → s < ‖w + 3 / 2‖} = Set.univ := by
        ext w
        simp [h]
      change IsOpen {w : ℂ | σ.θ₂ = 0 → s < ‖w + 3 / 2‖}
      rw [e]
      exact isOpen_univ
  have hvN : v ∈ N := ⟨by linarith, fun h => by have := hvh h; linarith⟩
  have hδ : ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ → f z ∉ N := by
    by_cases h : σ.θ₂ = 0
    · obtain ⟨δ, hδ0, hδ⟩ := hzero h (s - 1 / 2) (by have := hvh h; linarith)
      refine ⟨δ, hδ0, fun z hz hzn hfN => ?_⟩
      have h1 := hδ z hz hzn
      have h2 := hfN.2 h
      linarith
    · have hθ : 0 < σ.θ₂ := lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm h)
      refine ⟨Real.sin σ.θ₂ / 4, ?_, fun z hz hzn _ => ?_⟩
      · have := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
        positivity
      · exact absurd hzn (not_lt.2 (σ.sin_θ₂_div_four_le_norm hz))
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  set K := {z ∈ σ.triangle | z.im ≤ Y ∧ δ ≤ ‖z‖} with hK
  have hKmem : ∀ z ∈ σ.triangle, f z ∈ N → z ∈ K := by
    intro z hz hfN
    refine ⟨hz, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have := hY z hz hc
      linarith [hfN.1]
    · by_contra hc
      push Not at hc
      exact hδ z hz hc hfN
  have hcomp : IsCompact (f '' K) :=
    (σ.isCompact_truncation Y δ hδ0).image_of_continuousOn
      (hf.continuousOn.mono fun z hz => hTU hz.1)
  have hv1 : v ∈ closure (N ∩ f '' σ.triangleInterior) := hNo.inter_closure ⟨hvN, hvc⟩
  have hv2 : v ∈ f '' K := by
    refine hcomp.isClosed.closure_subset (closure_mono ?_ hv1)
    rintro _ ⟨hwN, z, hz, rfl⟩
    exact ⟨z, hKmem z (σ.triangleInterior_subset hz) hwN, rfl⟩
  obtain ⟨z, hzK, rfl⟩ := hv2
  by_cases hzI : z ∈ σ.triangleInterior
  · exact ⟨z, hzI, rfl⟩
  · obtain ⟨i, hi⟩ := σ.exists_wall_of_not_mem_interior hzK.1 hzI
    have := hreal i z hzK.1 hi
    linarith

theorem openTarget_subset_image (hU : IsOpen U) (hTU : σ.triangle ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ f z).det ≠ 0)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hmaps : Set.MapsTo f σ.triangle σ.basePlus)
    (hinf : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ σ.triangle, Y < z.im → 3 - ε < ‖f z‖)
    (hzero : σ.θ₂ = 0 → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ →
      ‖f z + 3 / 2‖ < 1 / 2 + ε) :
    σ.openTarget ⊆ f '' σ.triangleInterior := by
  have hopen := isOpen_image_triangleInterior hU hTU hf hdet
  have hne : (σ.openTarget ∩ f '' σ.triangleInterior).Nonempty :=
    ⟨_, mapsTo_triangleInterior_openTarget hopen hmaps σ.centre_mem_triangleInterior,
      _, σ.centre_mem_triangleInterior, rfl⟩
  exact σ.isPreconnected_openTarget.subset_of_closure_inter_subset hopen hne
    (closure_image_inter_subset hTU hf hreal hinf hzero)

end Local

def wallOnePt (y : ℝ) : ℂ := (σ.width : ℂ) + (y : ℂ) * I

def arcPt (x : ℝ) : ℂ := (x : ℂ) + (Real.sqrt (1 / 16 - (x - σ.centre) ^ 2) : ℂ) * I

@[simp] theorem wallOnePt_re (y : ℝ) : (σ.wallOnePt y).re = σ.width := by
  simp [wallOnePt]

@[simp] theorem wallOnePt_im (y : ℝ) : (σ.wallOnePt y).im = y := by
  simp [wallOnePt]

@[simp] theorem arcPt_re (x : ℝ) : (σ.arcPt x).re = x := by
  simp [arcPt]

@[simp] theorem arcPt_im (x : ℝ) : (σ.arcPt x).im = Real.sqrt (1 / 16 - (x - σ.centre) ^ 2) := by
  simp [arcPt]

theorem continuous_wallOnePt : Continuous σ.wallOnePt := by
  unfold wallOnePt
  fun_prop

theorem continuous_arcPt : Continuous σ.arcPt := by
  unfold arcPt
  fun_prop

theorem wallOnePt_vertex : σ.wallOnePt (Real.sin σ.θ₁ / 4) = σ.vertexOne :=
  Complex.ext (by simp [vertexOne]) (by simp [vertexOne])

theorem wallZeroPt_vertex : wallZeroPt (Real.sin σ.θ₂ / 4) = σ.vertexTwo :=
  Complex.ext (by simp [vertexTwo]) (by simp [vertexTwo])

theorem wallOnePt_mem {y : ℝ} (hy : Real.sin σ.θ₁ / 4 ≤ y) :
    σ.wallOnePt y ∈ σ.triangle ∧ σ.wallSide 1 (σ.wallOnePt y) = 0 := by
  have hs := σ.sin_θ₁_pos
  have hW := σ.width_sub_centre
  have hsc := Real.sin_sq_add_cos_sq σ.θ₁
  refine ⟨⟨by rw [wallOnePt_im]; linarith, fun i => ?_⟩, ?_⟩
  · fin_cases i
    · change 0 ≤ (σ.wallOnePt y).re
      rw [wallOnePt_re]
      exact σ.width_pos.le
    · change 0 ≤ σ.width - (σ.wallOnePt y).re
      rw [wallOnePt_re, sub_self]
    · change 0 ≤ ((σ.wallOnePt y).re - σ.centre) ^ 2 + (σ.wallOnePt y).im ^ 2 - 1 / 16
      rw [wallOnePt_re, wallOnePt_im, hW]
      nlinarith
  · change σ.width - (σ.wallOnePt y).re = 0
    rw [wallOnePt_re, sub_self]

theorem wallZeroPt_mem {y : ℝ} (hy : Real.sin σ.θ₂ / 4 ≤ y) (hy0 : 0 < y) :
    wallZeroPt y ∈ σ.triangle ∧ σ.wallSide 0 (wallZeroPt y) = 0 := by
  have hsc := Real.sin_sq_add_cos_sq σ.θ₂
  have hcen : σ.centre = Real.cos σ.θ₂ / 4 := rfl
  have hs := σ.sin_θ₂_nonneg
  refine ⟨⟨by rw [wallZeroPt_im]; exact hy0, fun i => ?_⟩, ?_⟩
  · fin_cases i
    · change 0 ≤ (wallZeroPt y).re
      rw [wallZeroPt_re]
    · change 0 ≤ σ.width - (wallZeroPt y).re
      rw [wallZeroPt_re, sub_zero]
      exact σ.width_pos.le
    · change 0 ≤ ((wallZeroPt y).re - σ.centre) ^ 2 + (wallZeroPt y).im ^ 2 - 1 / 16
      rw [wallZeroPt_re, wallZeroPt_im, hcen]
      nlinarith
  · change (wallZeroPt y).re = 0
    rw [wallZeroPt_re]

theorem arcPt_sq_lt {x : ℝ} (hx0 : 0 ≤ x) (hxW : x ≤ σ.width) (hpos : 0 < x ∨ 0 < σ.θ₂) :
    (x - σ.centre) ^ 2 < 1 / 16 := by
  have hW := σ.width_sub_centre
  have hc1 := σ.cos_θ₁_lt_one'
  have hcq := σ.centre_le_quarter
  have hcn := σ.centre_nonneg
  have h1 : x - σ.centre < 1 / 4 := by linarith
  have h2 : -(1 / 4) < x - σ.centre := by
    rcases hpos with h | h
    · linarith
    · have := σ.cos_θ₂_lt_one h
      have hcen : σ.centre = Real.cos σ.θ₂ / 4 := rfl
      linarith
  nlinarith

theorem arcPt_mem {x : ℝ} (hx0 : 0 ≤ x) (hxW : x ≤ σ.width) (hpos : 0 < x ∨ 0 < σ.θ₂) :
    σ.arcPt x ∈ σ.triangle ∧ σ.wallSide 2 (σ.arcPt x) = 0 := by
  have hlt := σ.arcPt_sq_lt hx0 hxW hpos
  have hq : 0 < 1 / 16 - (x - σ.centre) ^ 2 := by linarith
  have hsq := Real.sq_sqrt hq.le
  refine ⟨⟨by rw [arcPt_im]; exact Real.sqrt_pos.2 hq, fun i => ?_⟩, ?_⟩
  · fin_cases i
    · change 0 ≤ (σ.arcPt x).re
      rw [arcPt_re]
      exact hx0
    · change 0 ≤ σ.width - (σ.arcPt x).re
      rw [arcPt_re]
      linarith
    · change 0 ≤ ((σ.arcPt x).re - σ.centre) ^ 2 + (σ.arcPt x).im ^ 2 - 1 / 16
      rw [arcPt_re, arcPt_im, hsq]
      linarith
  · change ((σ.arcPt x).re - σ.centre) ^ 2 + (σ.arcPt x).im ^ 2 - 1 / 16 = 0
    rw [arcPt_re, arcPt_im, hsq]
    ring

theorem arcPt_width : σ.arcPt σ.width = σ.vertexOne := by
  have hW := σ.width_sub_centre
  have hsc := Real.sin_sq_add_cos_sq σ.θ₁
  have hs := σ.sin_θ₁_pos
  refine Complex.ext (by simp [vertexOne]) ?_
  rw [arcPt_im, vertexOne_im, hW]
  rw [show 1 / 16 - (Real.cos σ.θ₁ / 4) ^ 2 = (Real.sin σ.θ₁ / 4) ^ 2 by nlinarith]
  exact Real.sqrt_sq (by positivity)

theorem arcPt_zero : σ.arcPt 0 = σ.vertexTwo := by
  have hsc := Real.sin_sq_add_cos_sq σ.θ₂
  have hs := σ.sin_θ₂_nonneg
  have hcen : σ.centre = Real.cos σ.θ₂ / 4 := rfl
  refine Complex.ext (by simp [vertexTwo]) ?_
  rw [arcPt_im, vertexTwo_im, zero_sub, neg_sq, hcen]
  rw [show 1 / 16 - (Real.cos σ.θ₂ / 4) ^ 2 = (Real.sin σ.θ₂ / 4) ^ 2 by nlinarith]
  exact Real.sqrt_sq (by positivity)

theorem norm_arcPt_sq_cusp (h : σ.θ₂ = 0) {x : ℝ} (hx0 : 0 ≤ x) (hxW : x ≤ σ.width) :
    ‖σ.arcPt x‖ ^ 2 = x / 2 := by
  have hc := σ.cusp_centre h
  have hq : 0 ≤ 1 / 16 - (x - σ.centre) ^ 2 := by
    rcases hx0.lt_or_eq with hx | hx
    · linarith [σ.arcPt_sq_lt hx0 hxW (Or.inl hx)]
    · rw [← hx, hc]
      norm_num
  rw [Complex.sq_norm, Complex.normSq_apply, arcPt_re, arcPt_im, Real.mul_self_sqrt hq, hc]
  ring

section Walls

variable {σ}
variable {f : ℂ → ℂ}

theorem re_lt_three_of_mem_basePlus {u : ℂ} (hu : u ∈ σ.basePlus) (h : u.im = 0) :
    |u.re| < 3 := by
  have := hu.1
  rwa [norm_of_im_eq_zero h] at this

theorem exists_wallOne_eq (hfc : ∀ z ∈ σ.triangle, ContinuousAt f z)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hw1 : ∀ z ∈ σ.triangle, σ.wallSide 1 z = 0 → 3 / 2 ≤ (f z).re)
    (hv1 : f σ.vertexOne = 3 / 2)
    (hinf : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ σ.triangle, Y < z.im → 3 - ε < ‖f z‖)
    {t : ℝ} (ht1 : 3 / 2 ≤ t) (ht2 : t < 3) : ∃ z ∈ σ.triangle, f z = t := by
  obtain ⟨Y, hY⟩ := hinf (3 - t) (by linarith)
  set y₁ := Real.sin σ.θ₁ / 4 with hy₁
  set Y' := max (Y + 1) y₁ with hY'
  have hY'1 : Y < Y' := by linarith [le_max_left (Y + 1) y₁]
  have hY'2 : y₁ ≤ Y' := le_max_right _ _
  set g : ℝ → ℝ := fun y => (f (σ.wallOnePt y)).re with hg
  have hgc : ContinuousOn g (Set.Icc y₁ Y') := by
    intro y hy
    exact (Complex.continuous_re.continuousAt.comp
      ((hfc _ (σ.wallOnePt_mem hy.1).1).comp
        σ.continuous_wallOnePt.continuousAt)).continuousWithinAt
  have hga : g y₁ = 3 / 2 := by
    simp only [hg, hy₁]
    rw [σ.wallOnePt_vertex, hv1]
    norm_num
  have hgb : t < g Y' := by
    obtain ⟨hz, hw⟩ := σ.wallOnePt_mem hY'2
    have h1 := hY _ hz (by rw [wallOnePt_im]; exact hY'1)
    have h2 := hw1 _ hz hw
    rw [norm_of_im_eq_zero (hreal 1 _ hz hw), abs_of_nonneg (by linarith)] at h1
    simp only [hg]
    linarith
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc hY'2 hgc ⟨by rw [hga]; exact ht1, hgb.le⟩
  obtain ⟨hz, hw⟩ := σ.wallOnePt_mem hy.1
  refine ⟨_, hz, Complex.ext ?_ ?_⟩
  · simpa using hgy
  · rw [hreal 1 _ hz hw]
    simp

theorem exists_wallZero_eq (hfc : ∀ z ∈ σ.triangle, ContinuousAt f z)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hw0 : ∀ z ∈ σ.triangle, σ.wallSide 0 z = 0 → (f z).re ≤ -(3 / 2))
    (hv2 : 0 < σ.θ₂ → f σ.vertexTwo = -(3 / 2))
    (hinf : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ σ.triangle, Y < z.im → 3 - ε < ‖f z‖)
    (hzero : σ.θ₂ = 0 → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ →
      ‖f z + 3 / 2‖ < 1 / 2 + ε)
    {t : ℝ} (ht1 : -3 < t) (ht2 : t ≤ -(3 / 2)) (ht3 : σ.θ₂ = 0 → t < -2) :
    ∃ z ∈ σ.triangle, f z = t := by
  obtain ⟨Y, hY⟩ := hinf (t + 3) (by linarith)
  set Y' := max (Y + 1) 1 with hY'
  have hY'1 : Y < Y' := by linarith [le_max_left (Y + 1) 1]
  have hY'2 : 1 ≤ Y' := le_max_right _ _
  have hsin : Real.sin σ.θ₂ / 4 ≤ 1 := by linarith [Real.sin_le_one σ.θ₂]
  set g : ℝ → ℝ := fun y => (f (wallZeroPt y)).re with hg
  have hgc : ∀ y₀, 0 < y₀ → Real.sin σ.θ₂ / 4 ≤ y₀ → ContinuousOn g (Set.Icc y₀ Y') := by
    intro y₀ hy₀ hy₀' y hy
    exact (Complex.continuous_re.continuousAt.comp
      ((hfc _ (σ.wallZeroPt_mem (le_trans hy₀' hy.1) (lt_of_lt_of_le hy₀ hy.1)).1).comp
        continuous_wallZeroPt.continuousAt)).continuousWithinAt
  have hgb : g Y' < t := by
    obtain ⟨hz, hw⟩ := σ.wallZeroPt_mem (le_trans hsin hY'2) (by linarith)
    have h1 := hY _ hz (by rw [wallZeroPt_im]; exact hY'1)
    have h2 := hw0 _ hz hw
    rw [norm_of_im_eq_zero (hreal 0 _ hz hw), abs_of_neg (by linarith)] at h1
    simp only [hg]
    linarith
  have key : ∀ y₀, 0 < y₀ → Real.sin σ.θ₂ / 4 ≤ y₀ → y₀ ≤ Y' → t ≤ g y₀ →
      ∃ z ∈ σ.triangle, f z = t := by
    intro y₀ hy₀ hy₀' hy₀Y hgy₀
    obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc' hy₀Y (hgc y₀ hy₀ hy₀') ⟨hgb.le, hgy₀⟩
    obtain ⟨hz, hw⟩ := σ.wallZeroPt_mem (le_trans hy₀' hy.1) (lt_of_lt_of_le hy₀ hy.1)
    refine ⟨_, hz, Complex.ext ?_ ?_⟩
    · simpa using hgy
    · rw [hreal 0 _ hz hw]
      simp
  by_cases h : σ.θ₂ = 0
  · obtain ⟨δ, hδ0, hδ⟩ := hzero h (-2 - t) (by linarith [ht3 h])
    set y₀ := min (δ / 2) 1 with hy₀
    have hy₀0 : 0 < y₀ := lt_min (by positivity) one_pos
    have hy₀δ : y₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hy₀1 : y₀ ≤ 1 := min_le_right _ _
    refine key y₀ hy₀0 (by rw [h, Real.sin_zero]; linarith) (le_trans hy₀1 hY'2) ?_
    obtain ⟨hz, hw⟩ := σ.wallZeroPt_mem (by rw [h, Real.sin_zero]; linarith) hy₀0
    have h1 := hδ _ hz (by rw [norm_wallZeroPt hy₀0.le]; exact hy₀δ)
    have h2 := hw0 _ hz hw
    rw [norm_add_three_halves_of_im_eq_zero (hreal 0 _ hz hw), abs_of_nonpos (by linarith)] at h1
    simp only [hg]
    linarith
  · have hθ : 0 < σ.θ₂ := lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm h)
    have hs : 0 < Real.sin σ.θ₂ :=
      Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
    refine key (Real.sin σ.θ₂ / 4) (by positivity) le_rfl (le_trans hsin hY'2) ?_
    simp only [hg]
    rw [σ.wallZeroPt_vertex, hv2 hθ]
    norm_num
    exact ht2

theorem exists_wallTwo_eq (hfc : ∀ z ∈ σ.triangle, ContinuousAt f z)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hw2 : ∀ z ∈ σ.triangle, σ.wallSide 2 z = 0 → -(3 / 2) ≤ (f z).re ∧ (f z).re ≤ 3 / 2)
    (hv1 : f σ.vertexOne = 3 / 2) (hv2 : 0 < σ.θ₂ → f σ.vertexTwo = -(3 / 2))
    (hzero : σ.θ₂ = 0 → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ →
      ‖f z + 3 / 2‖ < 1 / 2 + ε)
    {t : ℝ} (ht1 : -(3 / 2) ≤ t) (ht2 : t ≤ 3 / 2) (ht3 : σ.θ₂ = 0 → -1 < t) :
    ∃ z ∈ σ.triangle, f z = t := by
  have hW := σ.width_pos
  set g : ℝ → ℝ := fun x => (f (σ.arcPt x)).re with hg
  have hgW : g σ.width = 3 / 2 := by
    simp only [hg]
    rw [σ.arcPt_width, hv1]
    norm_num
  have key : ∀ x₀, 0 ≤ x₀ → x₀ ≤ σ.width → (0 < x₀ ∨ 0 < σ.θ₂) → g x₀ ≤ t →
      ∃ z ∈ σ.triangle, f z = t := by
    intro x₀ hx₀ hx₀W hpos hgx₀
    have hgc : ContinuousOn g (Set.Icc x₀ σ.width) := by
      intro x hx
      have hmem := σ.arcPt_mem (le_trans hx₀ hx.1) hx.2
        (hpos.imp (fun h => lt_of_lt_of_le h hx.1) id)
      exact (Complex.continuous_re.continuousAt.comp
        ((hfc _ hmem.1).comp σ.continuous_arcPt.continuousAt)).continuousWithinAt
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc hx₀W hgc ⟨hgx₀, by rw [hgW]; exact ht2⟩
    obtain ⟨hz, hw⟩ := σ.arcPt_mem (le_trans hx₀ hx.1) hx.2
      (hpos.imp (fun h => lt_of_lt_of_le h hx.1) id)
    refine ⟨_, hz, Complex.ext ?_ ?_⟩
    · simpa using hgx
    · rw [hreal 2 _ hz hw]
      simp
  by_cases h : σ.θ₂ = 0
  · obtain ⟨δ, hδ0, hδ⟩ := hzero h (t + 1) (by linarith [ht3 h])
    set x₀ := min (δ ^ 2) σ.width with hx₀
    have hx₀0 : 0 < x₀ := lt_min (by positivity) hW
    have hx₀W : x₀ ≤ σ.width := min_le_right _ _
    have hx₀δ : x₀ ≤ δ ^ 2 := min_le_left _ _
    refine key x₀ hx₀0.le hx₀W (Or.inl hx₀0) ?_
    obtain ⟨hz, hw⟩ := σ.arcPt_mem hx₀0.le hx₀W (Or.inl hx₀0)
    have hn : ‖σ.arcPt x₀‖ < δ := by
      have h1 := σ.norm_arcPt_sq_cusp h hx₀0.le hx₀W
      have h2 : ‖σ.arcPt x₀‖ ^ 2 < δ ^ 2 := by rw [h1]; linarith
      exact (sq_lt_sq₀ (norm_nonneg _) hδ0.le).1 h2
    have h1 := hδ _ hz hn
    have h2 := hw2 _ hz hw
    rw [norm_add_three_halves_of_im_eq_zero (hreal 2 _ hz hw), abs_of_nonneg (by linarith)] at h1
    simp only [hg]
    linarith
  · have hθ : 0 < σ.θ₂ := lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm h)
    refine key 0 le_rfl hW.le (Or.inr hθ) ?_
    simp only [hg]
    rw [σ.arcPt_zero, hv2 hθ]
    norm_num
    exact ht1

end Walls

theorem bijOn_of_local {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ f z).det ≠ 0)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hinj : Set.InjOn f σ.triangle) (hmaps : Set.MapsTo f σ.triangle σ.basePlus)
    (hw0 : ∀ z ∈ σ.triangle, σ.wallSide 0 z = 0 → (f z).re ≤ -(3 / 2))
    (hw1 : ∀ z ∈ σ.triangle, σ.wallSide 1 z = 0 → 3 / 2 ≤ (f z).re)
    (hw2 : ∀ z ∈ σ.triangle, σ.wallSide 2 z = 0 → -(3 / 2) ≤ (f z).re ∧ (f z).re ≤ 3 / 2)
    (hv1 : f σ.vertexOne = 3 / 2) (hv2 : 0 < σ.θ₂ → f σ.vertexTwo = -(3 / 2))
    (hinf : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ σ.triangle, Y < z.im → 3 - ε < ‖f z‖)
    (hzero : σ.θ₂ = 0 → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ →
      ‖f z + 3 / 2‖ < 1 / 2 + ε) :
    Set.BijOn f σ.triangle σ.basePlus := by
  refine ⟨hmaps, hinj, fun u hu => ?_⟩
  have hfc : ∀ z ∈ σ.triangle, ContinuousAt f z := fun z hz =>
    hf.continuousOn.continuousAt (hU.mem_nhds (hTU hz))
  rcases hu.2.1.lt_or_eq with him | him
  · obtain ⟨z, hz, hzu⟩ := openTarget_subset_image hU hTU hf hdet hreal hmaps hinf hzero
      ⟨hu.1, him, hu.2.2⟩
    exact ⟨z, σ.triangleInterior_subset hz, hzu⟩
  · have him' : u.im = 0 := him.symm
    have hu3 := re_lt_three_of_mem_basePlus hu him'
    have hue : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [him'])
    have hhole : σ.θ₂ = 0 → 1 / 2 < |u.re + 3 / 2| := fun h => by
      have := hu.2.2 h
      rwa [norm_add_three_halves_of_im_eq_zero him'] at this
    obtain ⟨a1, a2⟩ := abs_lt.1 hu3
    rw [hue]
    rcases le_or_gt (3 / 2) u.re with h1 | h1
    · exact exists_wallOne_eq hfc hreal hw1 hv1 hinf h1 a2
    rcases le_or_gt u.re (-(3 / 2)) with h2 | h2
    · refine exists_wallZero_eq hfc hreal hw0 hv2 hinf hzero a1 h2 fun h => ?_
      have := hhole h
      rw [abs_of_nonpos (by linarith)] at this
      linarith
    · refine exists_wallTwo_eq hfc hreal hw2 hv1 hv2 hzero h2.le h1.le fun h => ?_
      have := hhole h
      rw [abs_of_nonneg (by linarith)] at this
      linarith

theorem exists_wall_of_im_eq_zero {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hTU : σ.triangle ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ f z).det ≠ 0)
    (hmaps : Set.MapsTo f σ.triangle σ.basePlus) {z : ℂ} (hz : z ∈ σ.triangle)
    (him : (f z).im = 0) : ∃ i, σ.wallSide i z = 0 := by
  refine σ.exists_wall_of_not_mem_interior hz fun hzI => ?_
  have := (mapsTo_triangleInterior_openTarget (isOpen_image_triangleInterior hU hTU hf hdet)
    hmaps hzI).2.1
  linarith

theorem tendsto_outerProfile_atTop {K Y₁ Y₂ : ℝ} (hK : 0 < K) (hY : Y₁ < Y₂) :
    Filter.Tendsto (outerProfile K Y₁ Y₂) Filter.atTop (𝓝 3) := by
  have h0 : Filter.Tendsto (fun y : ℝ => (Real.sqrt K - Y₂) * (1 + Y₂) / (1 + y)) Filter.atTop
      (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id)
  have h1 : Filter.Tendsto (outerTarget K Y₂) Filter.atTop (𝓝 (Real.sqrt K)) := by
    have := (tendsto_const_nhds (x := Real.sqrt K)).sub h0
    rwa [sub_zero] at this
  have h2 : Filter.Tendsto (outerReparam K Y₁ Y₂) Filter.atTop (𝓝 (Real.sqrt K)) := by
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop Y₂] with y hy
    rw [outerReparam, coneStep_eq_one hY hy]
    ring
  have h3 := ((contDiff_coneProfile hK).continuous.tendsto (Real.sqrt K)).comp h2
  rw [coneProfile_sqrt hK] at h3
  have h4 := h3.const_add (3 / 2)
  rw [show (3 / 2 : ℝ) + 3 / 2 = 3 by norm_num] at h4
  exact h4

theorem exists_outerProfile_gt {K Y₁ Y₂ : ℝ} (hK : 0 < K) (hY : Y₁ < Y₂) {ε : ℝ}
    (hε : 0 < ε) : ∃ Y : ℝ, ∀ y, Y < y → 3 - ε < outerProfile K Y₁ Y₂ y := by
  obtain ⟨Y, hY'⟩ := Metric.tendsto_atTop.1 (tendsto_outerProfile_atTop hK hY) ε hε
  refine ⟨Y, fun y hy => ?_⟩
  have := hY' y hy.le
  rw [Real.dist_eq] at this
  linarith [(abs_lt.1 this).1]

theorem cuspZeroHeight_lt_of_norm_lt (h : σ.θ₂ = 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z ∈ σ.triangle, ‖z‖ < δ → cuspZeroHeight z < η := by
  refine ⟨min (1 / 4) (η / 2), lt_min (by norm_num) (by positivity), fun z hz hzn => ?_⟩
  have hc := σ.cusp_centre h
  have hy := hz.1
  have h2 := hz.2 2
  change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at h2
  rw [hc] at h2
  have h0 := hz.2 0
  change 0 ≤ z.re at h0
  have hx : z.re < min (1 / 4) (η / 2) :=
    lt_of_le_of_lt (le_trans (le_abs_self _) (Complex.abs_re_le_norm z)) hzn
  have hyl : z.im < min (1 / 4) (η / 2) :=
    lt_of_le_of_lt (le_trans (le_abs_self _) (Complex.abs_im_le_norm z)) hzn
  have hx4 : z.re < 1 / 4 := lt_of_lt_of_le hx (min_le_left _ _)
  have hy4 : z.im < 1 / 4 := lt_of_lt_of_le hyl (min_le_left _ _)
  have hyη : z.im < η / 2 := lt_of_lt_of_le hyl (min_le_right _ _)
  have hxx : z.re * z.re ≤ z.re / 4 := by nlinarith [mul_nonneg h0 (by linarith : 0 ≤ 1 / 4 - z.re)]
  have hxy : z.re ≤ 4 * z.im ^ 2 := by nlinarith
  have hx2 : z.re * z.re ≤ (4 * z.im ^ 2) * (4 * z.im ^ 2) := mul_le_mul hxy hxy h0 (by positivity)
  have hy2 : z.im ^ 2 ≤ 1 / 16 := by nlinarith
  have hy4' : (4 * z.im ^ 2) * (4 * z.im ^ 2) ≤ z.im * z.im := by nlinarith
  rw [cuspZeroHeight, Complex.normSq_apply, div_lt_iff₀ hy]
  nlinarith

theorem bijOn_of_local' {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ f z).det ≠ 0)
    (hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (f z).im = 0)
    (hinj : Set.InjOn f σ.triangle) (hmaps : Set.MapsTo f σ.triangle σ.basePlus)
    (hw0 : ∀ z ∈ σ.triangle, σ.wallSide 0 z = 0 → (f z).re ≤ -(3 / 2))
    (hw1 : ∀ z ∈ σ.triangle, σ.wallSide 1 z = 0 → 3 / 2 ≤ (f z).re)
    (hw2 : ∀ z ∈ σ.triangle, σ.wallSide 2 z = 0 → -(3 / 2) ≤ (f z).re ∧ (f z).re ≤ 3 / 2)
    (hv1 : f σ.vertexOne = 3 / 2) (hv2 : 0 < σ.θ₂ → f σ.vertexTwo = -(3 / 2))
    {Y₁ Y₂ H : ℝ} (hY : Y₁ < Y₂)
    (hinf : ∀ z ∈ σ.triangle, H < z.im → ‖f z‖ = outerProfile σ.constK Y₁ Y₂ z.im)
    {B : ℝ} (hB : 0 < B)
    (hzero : σ.θ₂ = 0 → ∀ z ∈ σ.triangle, cuspZeroHeight z < B →
      ‖f z + 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z)) :
    Set.BijOn f σ.triangle σ.basePlus := by
  have hK := σ.constK_pos
  refine σ.bijOn_of_local hU hTU hf hdet hreal hinj hmaps hw0 hw1 hw2 hv1 hv2 ?_ ?_
  · intro ε hε
    obtain ⟨Y, hY'⟩ := exists_outerProfile_gt hK hY hε
    refine ⟨max Y H, fun z hz hz' => ?_⟩
    rw [hinf z hz (lt_of_le_of_lt (le_max_right _ _) hz')]
    exact hY' _ (lt_of_le_of_lt (le_max_left _ _) hz')
  · intro h ε hε
    obtain ⟨η, hη, hηε⟩ := Metric.continuousAt_iff.1
      ((contDiff_coneProfile hK).continuous.continuousAt (x := 0)) ε hε
    obtain ⟨δ, hδ, hδ'⟩ := σ.cuspZeroHeight_lt_of_norm_lt h (lt_min hη hB)
    refine ⟨δ, hδ, fun z hz hzn => ?_⟩
    have hlt := hδ' z hz hzn
    rw [hzero h z hz (lt_of_lt_of_le hlt (min_le_right _ _))]
    have hnn : 0 ≤ cuspZeroHeight z := div_nonneg (normSq_nonneg _) hz.1.le
    have := hηε (x := cuspZeroHeight z) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
      exact lt_of_lt_of_le hlt (min_le_left _ _))
    have h0 : coneProfile σ.constK 0 = 1 / 2 := by simp [coneProfile]
    rw [Real.dist_eq, h0] at this
    linarith [(abs_lt.1 this).2]

end ConeShape

end GC.Seifert
