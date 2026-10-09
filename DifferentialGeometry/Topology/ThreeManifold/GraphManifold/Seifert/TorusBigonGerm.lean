import DifferentialGeometry.Topology.Manifold.CompactLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The boundary germ of a bigon

Model lens `X = {0 ≤ u ≤ 1 - v²}` in coordinates `z = (u, v)`, `u` the height. Its parabolic
side is swept by the radial family `lensRad (τ, w) = (1 - w) • (1 - τ², τ)`, which preserves the
straight side `u = 0` (the lines `τ = ±1`) and has the explicit inverse `lensPar` away from the
ray `{v = 0, u ≤ 0}`.

A bigon in the `(x, y)` plane is normalised to corners `(∓1, 0)` at parameters `∓1` of a curve
`γ` that lies above the axis on `(-1, 1)`, crosses it transversally at `∓1` and lies below it
just outside. The germ `bigonGerm` matches the model to the bigon: along the parabola it is the
tube `(τ, w) ↦ γ τ + w • N τ` read through `lensPar`, with a transverse field `N` that is
horizontal near the corners; near the middle of the straight side it is the swap
`(u, v) ↦ (v, u)`; in between the two are blended. Both agree on the straight side, so the
derivative there has the triangular shape of a fixed core with a positive normal coefficient.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def lensRad (p : ℝ × ℝ) : ℝ × ℝ := ((1 - p.2) * (1 - p.1 ^ 2), (1 - p.2) * p.1)

def lensRho (z : ℝ × ℝ) : ℝ := (z.1 + √(z.1 ^ 2 + 4 * z.2 ^ 2)) / 2

def lensPar (z : ℝ × ℝ) : ℝ × ℝ := (z.2 / lensRho z, 1 - lensRho z)

def lensGood : Set (ℝ × ℝ) := {z | z.2 ≠ 0 ∨ 0 < z.1}

theorem isOpen_lensGood : IsOpen lensGood :=
  (isOpen_ne_fun continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_fst)

theorem lensRho_pos {z : ℝ × ℝ} (hz : z ∈ lensGood) : 0 < lensRho z := by
  unfold lensRho
  have hs : |z.1| ≤ √(z.1 ^ 2 + 4 * z.2 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z.2])
  rcases hz with hz | hz
  · have hlt : |z.1| < √(z.1 ^ 2 + 4 * z.2 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [sq_pos_of_ne_zero hz])
    have := neg_abs_le z.1
    linarith
  · have := abs_nonneg z.1
    linarith

theorem lensRho_sq (z : ℝ × ℝ) : lensRho z ^ 2 = z.1 * lensRho z + z.2 ^ 2 := by
  unfold lensRho
  have hs := Real.sq_sqrt (show 0 ≤ z.1 ^ 2 + 4 * z.2 ^ 2 by positivity)
  nlinarith [hs]

theorem lensRad_lensPar {z : ℝ × ℝ} (hz : z ∈ lensGood) : lensRad (lensPar z) = z := by
  have hρ := lensRho_pos hz
  have hsq := lensRho_sq z
  unfold lensRad lensPar
  simp only [sub_sub_cancel]
  refine Prod.ext ?_ ?_
  · change lensRho z * (1 - (z.2 / lensRho z) ^ 2) = z.1
    field_simp
    nlinarith [hsq]
  · change lensRho z * (z.2 / lensRho z) = z.2
    field_simp

theorem lensRho_lensRad {p : ℝ × ℝ} (hp : p.2 < 1) : lensRho (lensRad p) = 1 - p.2 := by
  unfold lensRho lensRad
  have h1 : 0 < 1 - p.2 := by linarith
  have h : ((1 - p.2) * (1 - p.1 ^ 2)) ^ 2 + 4 * ((1 - p.2) * p.1) ^ 2 =
      ((1 - p.2) * (1 + p.1 ^ 2)) ^ 2 := by ring
  simp only
  rw [h, Real.sqrt_sq (by positivity)]
  ring

theorem lensPar_lensRad {p : ℝ × ℝ} (hp : p.2 < 1) : lensPar (lensRad p) = p := by
  have h := lensRho_lensRad hp
  have h1 : (1 - p.2) ≠ 0 := by linarith
  unfold lensPar
  rw [h]
  refine Prod.ext ?_ ?_
  · change (1 - p.2) * p.1 / (1 - p.2) = p.1
    field_simp
  · change 1 - (1 - p.2) = p.2
    ring

theorem lensRad_mem_lensGood {p : ℝ × ℝ} (hp : p.2 < 1) : lensRad p ∈ lensGood := by
  have h1 : 0 < 1 - p.2 := by linarith
  by_cases h0 : p.1 = 0
  · right
    change 0 < (1 - p.2) * (1 - p.1 ^ 2)
    rw [h0]
    simpa using h1
  · left
    change (1 - p.2) * p.1 ≠ 0
    exact mul_ne_zero h1.ne' h0

theorem contDiffOn_lensRho : ContDiffOn ℝ ∞ lensRho lensGood := by
  have hpos : ∀ z ∈ lensGood, z.1 ^ 2 + 4 * z.2 ^ 2 ≠ 0 := by
    intro z hz
    rcases hz with hz | hz
    · have := sq_pos_of_ne_zero hz
      nlinarith [sq_nonneg z.1]
    · have := sq_pos_of_pos hz
      nlinarith [sq_nonneg z.2]
  have hq : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.1 ^ 2 + 4 * z.2 ^ 2) :=
    (contDiff_fst.pow 2).add (contDiff_const.mul (contDiff_snd.pow 2))
  exact ((contDiff_fst.contDiffOn).add (hq.contDiffOn.sqrt hpos)).div_const 2

theorem contDiffOn_lensPar : ContDiffOn ℝ ∞ lensPar lensGood := by
  have hρ := contDiffOn_lensRho
  exact (contDiff_snd.contDiffOn.div hρ fun z hz => (lensRho_pos hz).ne').prodMk
    (contDiffOn_const.sub hρ)

def lensRadDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((-(2 * p.1 * (1 - p.2))) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      (1 - p.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((1 - p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ - p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem lensRadDeriv_apply (p q : ℝ × ℝ) :
    lensRadDeriv p q = (-(2 * p.1 * (1 - p.2)) * q.1 - (1 - p.1 ^ 2) * q.2,
      (1 - p.2) * q.1 - p.1 * q.2) := by
  simp [lensRadDeriv, smul_eq_mul]

theorem hasFDerivAt_lensRad (p : ℝ × ℝ) : HasFDerivAt lensRad (lensRadDeriv p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => (1 - q.2) * (1 - q.1 ^ 2))
      ((-(2 * p.1 * (1 - p.2))) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (1 - p.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    have ha : HasFDerivAt (fun q : ℝ × ℝ => 1 - q.2) (-ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
      simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_sub (1 : ℝ)
    have hb : HasFDerivAt (fun q : ℝ × ℝ => 1 - q.1 ^ 2)
        (-((2 : ℝ) * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      have := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).const_sub (1 : ℝ)
      convert this using 1
      · ext q
        simp only [Pi.mul_apply]
        ring
      · refine ContinuousLinearMap.ext fun q => ?_
        simp [smul_eq_mul]
        ring
    convert ha.mul hb using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [smul_eq_mul]
    ring
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => (1 - q.2) * q.1)
      ((1 - p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ - p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    have ha : HasFDerivAt (fun q : ℝ × ℝ => 1 - q.2) (-ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
      simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_sub (1 : ℝ)
    convert ha.mul (hasFDerivAt_fst (𝕜 := ℝ) (p := p)) using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [smul_eq_mul]
    ring
  exact h1.prodMk h2

theorem lensRadDeriv_injective {p : ℝ × ℝ} (hp : p.2 < 1) :
    Function.Injective (lensRadDeriv p) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  rw [lensRadDeriv_apply, Prod.mk_eq_zero] at hq
  obtain ⟨h1, h2⟩ := hq
  have hw : 0 < 1 - p.2 := by linarith
  have hb : q.2 = 0 := by
    have : q.2 * (1 + p.1 ^ 2) = 0 := by linear_combination -h1 - 2 * p.1 * h2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · nlinarith [sq_nonneg p.1]
  have ha : q.1 = 0 := by
    rw [hb, mul_zero, sub_zero] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  exact Prod.ext ha hb

def lensRadEquiv {p : ℝ × ℝ} (hp : p.2 < 1) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.ofInjectiveEndo (lensRadDeriv p).toLinearMap
    (lensRadDeriv_injective hp)).toContinuousLinearEquiv

theorem lensRadEquiv_coe {p : ℝ × ℝ} (hp : p.2 < 1) :
    ((lensRadEquiv hp : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = lensRadDeriv p :=
  ContinuousLinearMap.ext fun _ => rfl

theorem lensPar_snd_lt_one {z : ℝ × ℝ} (hz : z ∈ lensGood) : (lensPar z).2 < 1 := by
  have := lensRho_pos hz
  change 1 - lensRho z < 1
  linarith

theorem hasFDerivAt_lensPar {z : ℝ × ℝ} (hz : z ∈ lensGood) :
    HasFDerivAt lensPar
      (((lensRadEquiv (lensPar_snd_lt_one hz)).symm : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) z := by
  apply HasFDerivAt.of_local_left_inverse
  · exact (contDiffOn_lensPar.continuousOn.continuousAt (isOpen_lensGood.mem_nhds hz))
  · rw [lensRadEquiv_coe]
    exact hasFDerivAt_lensRad _
  · filter_upwards [isOpen_lensGood.mem_nhds hz] with y hy using lensRad_lensPar hy

theorem isLocalDiffeomorphAt_of_hasFDerivAt_injective {f : ℝ × ℝ → ℝ × ℝ}
    {U : Set (ℝ × ℝ)} {x : ℝ × ℝ} (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    {A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} (hA : HasFDerivAt f A x) (hinj : Function.Injective A) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ f x := by
  let Ae : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo A.toLinearMap hinj).toContinuousLinearEquiv
  have hAe : (Ae : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = A := ContinuousLinearMap.ext fun _ => rfl
  open DifferentialGeometry.Topology.Manifold in
  apply isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv f hf.contMDiffOn hU x hx Ae
  rw [hAe]
  exact hA.hasMFDerivAt

theorem isLocalDiffeomorphAt_lensPar {z : ℝ × ℝ} (hz : z ∈ lensGood) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ lensPar z :=
  isLocalDiffeomorphAt_of_hasFDerivAt_injective isOpen_lensGood hz contDiffOn_lensPar
    (hasFDerivAt_lensPar hz) (lensRadEquiv (lensPar_snd_lt_one hz)).symm.injective

theorem lensPar_curve (τ : ℝ) : lensPar (1 - τ ^ 2, τ) = (τ, 0) := by
  have h : lensRad (τ, 0) = (1 - τ ^ 2, τ) := by simp [lensRad]
  rw [← h, lensPar_lensRad (by norm_num)]

theorem lensPar_axis {v : ℝ} (hv : v ≠ 0) :
    lensPar (0, v) = (v / |v|, 1 - |v|) := by
  have hρ : lensRho (0, v) = |v| := by
    unfold lensRho
    simp only
    rw [show (0 : ℝ) ^ 2 + 4 * v ^ 2 = (2 * |v|) ^ 2 by rw [mul_pow, sq_abs]; ring,
      Real.sqrt_sq (by positivity)]
    ring
  unfold lensPar
  rw [hρ]

theorem curve_mem_lensGood (τ : ℝ) : ((1 - τ ^ 2, τ) : ℝ × ℝ) ∈ lensGood := by
  by_cases h : τ = 0
  · right
    simp [h]
  · left
    exact h

def bigonTube (γ N : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ := γ p.1 + p.2 • N p.1

def bigonTubeDeriv (γ N : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv γ p.1 + p.2 • deriv N p.1) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (N p.1)

theorem bigonTubeDeriv_apply (γ N : ℝ → ℝ × ℝ) (p q : ℝ × ℝ) :
    bigonTubeDeriv γ N p q = q.1 • (deriv γ p.1 + p.2 • deriv N p.1) + q.2 • N p.1 := by
  simp [bigonTubeDeriv]

theorem hasFDerivAt_bigonTube {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) (hN : ContDiff ℝ ∞ N)
    (p : ℝ × ℝ) : HasFDerivAt (bigonTube γ N) (bigonTubeDeriv γ N p) p := by
  have hγd : HasDerivAt γ (deriv γ p.1) p.1 := (hγ.differentiable (by simp) p.1).hasDerivAt
  have hNd : HasDerivAt N (deriv N p.1) p.1 := (hN.differentiable (by simp) p.1).hasDerivAt
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => γ q.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv γ p.1)) p :=
    (hγd.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).congr_fderiv
      (ContinuousLinearMap.ext fun q => by simp)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => N q.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv N p.1)) p :=
    (hNd.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).congr_fderiv
      (ContinuousLinearMap.ext fun q => by simp)
  have h3 := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul h2
  refine (h1.add h3).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun q => ?_
  simp only [bigonTubeDeriv, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', FunLike.coe_smul,
    Pi.smul_apply, smul_add, smul_smul]
  module

theorem contDiff_bigonTube {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) (hN : ContDiff ℝ ∞ N) :
    ContDiff ℝ ∞ (bigonTube γ N) :=
  (hγ.comp contDiff_fst).add (contDiff_snd.smul (hN.comp contDiff_fst))

theorem exists_bigon_normal {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) {ε : ℝ}
    (himm : ∀ t ∈ Icc (-1 - ε) (1 + ε), deriv γ t ≠ 0)
    (htm : 0 < (deriv γ (-1)).2) (htp : (deriv γ 1).2 < 0) :
    ∃ N : ℝ → ℝ × ℝ, ContDiff ℝ ∞ N ∧ (∀ᶠ t in 𝓝 (-1), N t = (1, 0)) ∧
      (∀ᶠ t in 𝓝 1, N t = (-1, 0)) ∧
      ∀ t ∈ Icc (-1 - ε) (1 + ε), (deriv γ t).1 * (N t).2 - (deriv γ t).2 * (N t).1 < 0 := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hd2 : Continuous (fun t => (deriv γ t).2) := continuous_snd.comp hd.continuous
  obtain ⟨η₁, hη₁, hball₁⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hd2) (-1) htm
  obtain ⟨η₂, hη₂, hball₂⟩ := Metric.isOpen_iff.mp
    (isOpen_lt hd2 continuous_const) 1 htp
  set η := min (min η₁ η₂) (1 / 2) with hηdef
  have hη : 0 < η := lt_min (lt_min hη₁ hη₂) (by norm_num)
  have hηle₁ : η ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hηle₂ : η ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  let S := Real.smoothTransition
  let bump : ℝ → ℝ → ℝ := fun c t => S (2 * (t + c) / η + 2) * S (2 - 2 * (t + c) / η)
  let β₁ : ℝ → ℝ := bump 1
  let β₂ : ℝ → ℝ := bump (-1)
  have hS : ContDiff ℝ ∞ S := Real.smoothTransition.contDiff
  have hlin (c : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => 2 * (t + c) / η) :=
    (contDiff_const.mul (contDiff_id.add contDiff_const)).div_const η
  have hbump (c : ℝ) : ContDiff ℝ ∞ (bump c) :=
    (hS.comp ((hlin c).add contDiff_const)).mul (hS.comp (contDiff_const.sub (hlin c)))
  have hβ₁ : ContDiff ℝ ∞ β₁ := hbump 1
  have hβ₂ : ContDiff ℝ ∞ β₂ := hbump (-1)
  have hsupp (c t : ℝ) (h : S (2 * (t + c) / η + 2) * S (2 - 2 * (t + c) / η) ≠ 0) :
      |t + c| < η := by
    rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
    have h1' : 0 < 2 * (t + c) / η + 2 := by
      by_contra hc
      exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have h2' : 0 < 2 - 2 * (t + c) / η := by
      by_contra hc
      exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have e : 2 * (t + c) / η * η = 2 * (t + c) := div_mul_cancel₀ _ hη.ne'
    rw [abs_lt]
    constructor <;> nlinarith [e, h1', h2', hη]
  have hone (c t : ℝ) (h : |t + c| < η / 2) :
      S (2 * (t + c) / η + 2) * S (2 - 2 * (t + c) / η) = 1 := by
    rw [abs_lt] at h
    have h1 : 1 ≤ 2 * (t + c) / η + 2 := by
      rw [← sub_nonneg]
      have : -1 ≤ 2 * (t + c) / η := by
        rw [le_div_iff₀ hη]
        linarith
      linarith
    have h2 : 1 ≤ 2 - 2 * (t + c) / η := by
      have : 2 * (t + c) / η ≤ 1 := by
        rw [div_le_iff₀ hη]
        linarith
      linarith
    change Real.smoothTransition _ * Real.smoothTransition _ = 1
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]
  have hnn (c t : ℝ) : 0 ≤ S (2 * (t + c) / η + 2) * S (2 - 2 * (t + c) / η) :=
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hle (c t : ℝ) : S (2 * (t + c) / η + 2) * S (2 - 2 * (t + c) / η) ≤ 1 := by
    have h1 := Real.smoothTransition.le_one (2 * (t + c) / η + 2)
    have h2 := Real.smoothTransition.le_one (2 - 2 * (t + c) / η)
    have h3 := Real.smoothTransition.nonneg (2 * (t + c) / η + 2)
    have h4 := Real.smoothTransition.nonneg (2 - 2 * (t + c) / η)
    change Real.smoothTransition _ * Real.smoothTransition _ ≤ 1
    nlinarith
  have hβ₂eq (t : ℝ) : β₂ t = S (2 * (t + -1) / η + 2) * S (2 - 2 * (t + -1) / η) := rfl
  refine ⟨fun t => β₁ t • ((1 : ℝ), (0 : ℝ)) + β₂ t • ((-1 : ℝ), (0 : ℝ)) +
    (1 - β₁ t - β₂ t) • ((deriv γ t).2, -(deriv γ t).1), ?_, ?_, ?_, ?_⟩
  · exact ((hβ₁.smul contDiff_const).add (hβ₂.smul contDiff_const)).add
      (((contDiff_const.sub hβ₁).sub hβ₂).smul
        ((continuous_snd.comp hd.continuous |> fun _ => (contDiff_snd.comp hd)).prodMk
          (contDiff_fst.comp hd).neg))
  · have hnear : ∀ᶠ t in 𝓝 (-1 : ℝ), |t + 1| < η / 2 := by
      have : Metric.ball (-1 : ℝ) (η / 2) ∈ 𝓝 (-1 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
      filter_upwards [this] with t ht
      rwa [Metric.mem_ball, Real.dist_eq, sub_neg_eq_add] at ht
    filter_upwards [hnear] with t ht
    have h1 : β₁ t = 1 := hone 1 t ht
    have h2 : β₂ t = 0 := by
      rw [hβ₂eq]
      by_contra hne
      have := hsupp (-1) t hne
      rw [abs_lt] at ht this
      linarith
    rw [h1, h2]
    simp
  · have hnear : ∀ᶠ t in 𝓝 (1 : ℝ), |t + -1| < η / 2 := by
      have : Metric.ball (1 : ℝ) (η / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
      filter_upwards [this] with t ht
      rw [Metric.mem_ball, Real.dist_eq] at ht
      simpa only [sub_eq_add_neg] using ht
    filter_upwards [hnear] with t ht
    have h2 : β₂ t = 1 := by rw [hβ₂eq]; exact hone (-1) t ht
    have h1 : β₁ t = 0 := by
      by_contra hne
      have := hsupp 1 t hne
      rw [abs_lt] at ht this
      linarith
    rw [h1, h2]
    simp
  · intro t ht
    have hb1 := hnn 1 t
    have hb2 : 0 ≤ β₂ t := by rw [hβ₂eq]; exact hnn (-1) t
    have hb1' : β₁ t ≤ 1 := hle 1 t
    have hb2' : β₂ t ≤ 1 := by rw [hβ₂eq]; exact hle (-1) t
    set a := (deriv γ t).1
    set b := (deriv γ t).2
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero, mul_one,
      mul_neg]
    by_cases h1 : β₁ t = 0
    · by_cases h2 : β₂ t = 0
      · rw [h1, h2]
        have hab : a ≠ 0 ∨ b ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact himm t ht (Prod.ext hcon.1 hcon.2)
        have : 0 < a ^ 2 + b ^ 2 := by
          rcases hab with h | h
          · have := sq_pos_of_ne_zero h
            nlinarith [sq_nonneg b]
          · have := sq_pos_of_ne_zero h
            nlinarith [sq_nonneg a]
        nlinarith
      · have hc := hsupp (-1) t (by rwa [← hβ₂eq])
        have hbneg : b < 0 := by
          have := hball₂ (show t ∈ Metric.ball (1 : ℝ) η₂ by
            rw [Metric.mem_ball, Real.dist_eq]
            rw [← sub_eq_add_neg] at hc
            linarith)
          exact this
        rw [h1]
        have hpos : 0 < β₂ t := lt_of_le_of_ne hb2 (Ne.symm h2)
        nlinarith [sq_nonneg a, sq_nonneg b, mul_pos hpos (neg_pos.mpr hbneg)]
    · have hc := hsupp 1 t h1
      have hbpos : 0 < b := by
        have := hball₁ (show t ∈ Metric.ball (-1 : ℝ) η₁ by
          rw [Metric.mem_ball, Real.dist_eq, sub_neg_eq_add]
          linarith)
        exact this
      have h2 : β₂ t = 0 := by
        rw [hβ₂eq]
        by_contra hne
        have := hsupp (-1) t hne
        rw [abs_lt] at hc this
        linarith
      rw [h2]
      have hpos : 0 < β₁ t := lt_of_le_of_ne hb1 (Ne.symm h1)
      nlinarith [sq_nonneg a, sq_nonneg b, mul_pos hpos hbpos]

def lensCutoff (z : ℝ × ℝ) : ℝ :=
  (Real.smoothTransition (4 * z.2 + 3) * Real.smoothTransition (3 - 4 * z.2)) *
    (Real.smoothTransition (32 * z.1 + 2) * Real.smoothTransition (2 - 32 * z.1))

theorem contDiff_lensCutoff : ContDiff ℝ ∞ lensCutoff := by
  have hS : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  unfold lensCutoff
  exact ((hS.comp ((contDiff_const.mul contDiff_snd).add contDiff_const)).mul
      (hS.comp (contDiff_const.sub (contDiff_const.mul contDiff_snd)))).mul
    ((hS.comp ((contDiff_const.mul contDiff_fst).add contDiff_const)).mul
      (hS.comp (contDiff_const.sub (contDiff_const.mul contDiff_fst))))

theorem lensCutoff_nonneg (z : ℝ × ℝ) : 0 ≤ lensCutoff z := by
  unfold lensCutoff
  have h := Real.smoothTransition.nonneg
  exact mul_nonneg (mul_nonneg (h _) (h _)) (mul_nonneg (h _) (h _))

theorem lensCutoff_le_one (z : ℝ × ℝ) : lensCutoff z ≤ 1 := by
  unfold lensCutoff
  have h1 := Real.smoothTransition.le_one (4 * z.2 + 3)
  have h2 := Real.smoothTransition.le_one (3 - 4 * z.2)
  have h3 := Real.smoothTransition.le_one (32 * z.1 + 2)
  have h4 := Real.smoothTransition.le_one (2 - 32 * z.1)
  have g1 := Real.smoothTransition.nonneg (4 * z.2 + 3)
  have g2 := Real.smoothTransition.nonneg (3 - 4 * z.2)
  have g3 := Real.smoothTransition.nonneg (32 * z.1 + 2)
  have g4 := Real.smoothTransition.nonneg (2 - 32 * z.1)
  have h12 : Real.smoothTransition (4 * z.2 + 3) * Real.smoothTransition (3 - 4 * z.2) ≤ 1 := by
    nlinarith
  have h34 : Real.smoothTransition (32 * z.1 + 2) * Real.smoothTransition (2 - 32 * z.1) ≤ 1 := by
    nlinarith
  have := mul_nonneg g1 g2
  have := mul_nonneg g3 g4
  nlinarith

theorem lensCutoff_eq_one {z : ℝ × ℝ} (h2 : |z.2| ≤ 1 / 2) (h1 : |z.1| ≤ 1 / 32) :
    lensCutoff z = 1 := by
  rw [abs_le] at h1 h2
  unfold lensCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

theorem lensCutoff_eq_zero_of_snd {z : ℝ × ℝ} (h : 3 / 4 ≤ |z.2|) : lensCutoff z = 0 := by
  unfold lensCutoff
  rcases le_abs'.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 4 * z.2 + 3 ≤ 0)]
    ring
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - 4 * z.2 ≤ 0)]
    ring

theorem lensCutoff_eq_zero_of_fst {z : ℝ × ℝ} (h : 1 / 16 ≤ |z.1|) : lensCutoff z = 0 := by
  unfold lensCutoff
  rcases le_abs'.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 32 * z.1 + 2 ≤ 0)]
    ring
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 32 * z.1 ≤ 0)]
    ring

theorem lensCutoff_curve_eventually (τ : ℝ) :
    ∀ᶠ z in 𝓝 ((1 - τ ^ 2, τ) : ℝ × ℝ), lensCutoff z = 0 := by
  by_cases hτ : 3 / 4 < |τ|
  · have ho : IsOpen {z : ℝ × ℝ | 3 / 4 < |z.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    filter_upwards [ho.mem_nhds hτ] with z hz using lensCutoff_eq_zero_of_snd hz.le
  · have h1 : 1 / 16 < 1 - τ ^ 2 := by
      have : |τ| ^ 2 ≤ (3 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg τ) (not_lt.mp hτ) 2
      rw [sq_abs] at this
      linarith
    have ho : IsOpen {z : ℝ × ℝ | 1 / 16 < z.1} := isOpen_lt continuous_const continuous_fst
    filter_upwards [ho.mem_nhds h1] with z hz
    exact lensCutoff_eq_zero_of_fst (le_abs.mpr (Or.inl hz.le))

theorem lensCutoff_curve (τ : ℝ) : lensCutoff (1 - τ ^ 2, τ) = 0 :=
  (lensCutoff_curve_eventually τ).self_of_nhds

def bigonGerm (γ N : ℝ → ℝ × ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (1 - lensCutoff z) • bigonTube γ N (lensPar z) + lensCutoff z • z.swap

def bigonHat (γ N : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - lensCutoff (lensRad p)) • bigonTube γ N p + lensCutoff (lensRad p) • (lensRad p).swap

theorem bigonGerm_eq_bigonHat (γ N : ℝ → ℝ × ℝ) {z : ℝ × ℝ} (hz : z ∈ lensGood) :
    bigonGerm γ N z = bigonHat γ N (lensPar z) := by
  unfold bigonGerm bigonHat
  rw [lensRad_lensPar hz]

theorem contDiff_lensRad : ContDiff ℝ ∞ lensRad :=
  ((contDiff_const.sub contDiff_snd).mul (contDiff_const.sub (contDiff_fst.pow 2))).prodMk
    ((contDiff_const.sub contDiff_snd).mul contDiff_fst)

theorem contDiff_bigonHat {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) (hN : ContDiff ℝ ∞ N) :
    ContDiff ℝ ∞ (bigonHat γ N) := by
  have hC := contDiff_lensCutoff.comp contDiff_lensRad
  have hR : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (lensRad p).swap) :=
    (contDiff_snd.prodMk contDiff_fst).comp contDiff_lensRad
  exact ((contDiff_const.sub hC).smul (contDiff_bigonTube hγ hN)).add (hC.smul hR)

theorem contDiffOn_bigonGerm {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) (hN : ContDiff ℝ ∞ N) :
    ContDiffOn ℝ ∞ (bigonGerm γ N) lensGood := by
  have h := (contDiff_bigonHat hγ hN).comp_contDiffOn contDiffOn_lensPar
  exact h.congr fun z hz => bigonGerm_eq_bigonHat γ N hz

theorem bigonGerm_curve (γ N : ℝ → ℝ × ℝ) (τ : ℝ) : bigonGerm γ N (1 - τ ^ 2, τ) = γ τ := by
  unfold bigonGerm
  rw [lensCutoff_curve, lensPar_curve]
  simp [bigonTube]

theorem bigonGerm_axis {γ N : ℝ → ℝ × ℝ} (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hNm : N (-1) = (1, 0)) (hNp : N 1 = (-1, 0)) (v : ℝ) : bigonGerm γ N (0, v) = (v, 0) := by
  unfold bigonGerm
  by_cases hv : v = 0
  · subst hv
    rw [lensCutoff_eq_one (by norm_num) (by norm_num)]
    simp
  · have hT : bigonTube γ N (lensPar (0, v)) = (v, 0) := by
      rw [lensPar_axis hv]
      unfold bigonTube
      rcases lt_or_gt_of_ne hv with h | h
      · rw [abs_of_neg h, div_neg, div_self hv, hγm, hNm]
        refine Prod.ext ?_ ?_ <;> simp
      · rw [abs_of_pos h, div_self hv, hγp, hNp]
        refine Prod.ext ?_ ?_ <;> simp
    rw [hT]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_swap, smul_eq_mul]
      ring
    · simp

def swapCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : _)

theorem swapCLM_apply (q : ℝ × ℝ) : swapCLM q = q.swap := rfl

def bigonHatDeriv (γ N : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (1 - lensCutoff (lensRad p)) • bigonTubeDeriv γ N p +
    (-(fderiv ℝ (lensCutoff ∘ lensRad) p)).smulRight (bigonTube γ N p) +
    (lensCutoff (lensRad p) • (swapCLM.comp (lensRadDeriv p)) +
      (fderiv ℝ (lensCutoff ∘ lensRad) p).smulRight (lensRad p).swap)

theorem hasFDerivAt_bigonHat {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) (hN : ContDiff ℝ ∞ N)
    (p : ℝ × ℝ) : HasFDerivAt (bigonHat γ N) (bigonHatDeriv γ N p) p := by
  have hC : HasFDerivAt (lensCutoff ∘ lensRad) (fderiv ℝ (lensCutoff ∘ lensRad) p) p :=
    ((contDiff_lensCutoff.comp contDiff_lensRad).differentiable (by simp) p).hasFDerivAt
  have h1 : HasFDerivAt (fun q => 1 - (lensCutoff ∘ lensRad) q)
      (-(fderiv ℝ (lensCutoff ∘ lensRad) p)) p := hC.const_sub (1 : ℝ)
  have hR : HasFDerivAt (fun q : ℝ × ℝ => (lensRad q).swap) (swapCLM.comp (lensRadDeriv p)) p :=
    swapCLM.hasFDerivAt.comp p (hasFDerivAt_lensRad p)
  exact (h1.smul (hasFDerivAt_bigonTube hγ hN p)).add (hC.smul hR)

theorem bigonHatDeriv_apply_of_eq {γ N : ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (h : bigonTube γ N p = (lensRad p).swap) (q : ℝ × ℝ) :
    bigonHatDeriv γ N p q = (1 - lensCutoff (lensRad p)) • bigonTubeDeriv γ N p q +
      lensCutoff (lensRad p) • (lensRadDeriv p q).swap := by
  simp only [bigonHatDeriv, add_apply, ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
    Pi.smul_apply, neg_apply, ContinuousLinearMap.comp_apply, swapCLM_apply,
    h]
  module

theorem bigonHatDeriv_injective_axis {γ N : ℝ → ℝ × ℝ} {σ w : ℝ} (hσ : σ ^ 2 = 1) (hw : w < 1)
    (hγσ : γ σ = (σ, 0)) (hNσ : N σ = (-σ, 0)) (hdN : deriv N σ = 0)
    (hsign : σ * (deriv γ σ).2 < 0) : Function.Injective (bigonHatDeriv γ N (σ, w)) := by
  have hT : bigonTube γ N (σ, w) = (lensRad (σ, w)).swap := by
    unfold bigonTube lensRad
    rw [hγσ, hNσ, hσ]
    refine Prod.ext ?_ ?_
    · simp
      ring
    · simp
  rw [injective_iff_map_eq_zero]
  intro q hq
  rw [bigonHatDeriv_apply_of_eq hT, bigonTubeDeriv_apply, lensRadDeriv_apply] at hq
  simp only [hNσ, hdN, smul_zero, add_zero] at hq
  set lam := lensCutoff (lensRad (σ, w))
  have hl0 : 0 ≤ lam := lensCutoff_nonneg _
  have hl1 : lam ≤ 1 := lensCutoff_le_one _
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_swap,
    Prod.snd_swap, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at h1 h2
  set g := (deriv γ σ).2
  have hq1 : q.1 = 0 := by
    have hcoef : (1 - lam) * (σ * g) - 2 * lam * (1 - w) < 0 := by
      have : 0 < 1 - w := by linarith
      by_cases hl : lam = 0
      · rw [hl]; linarith
      · have hlpos : 0 < lam := lt_of_le_of_ne hl0 (Ne.symm hl)
        nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (le_of_lt (neg_pos.mpr hsign))]
    have : q.1 * ((1 - lam) * (σ * g) - 2 * lam * (1 - w)) = 0 := by
      linear_combination σ * h2 + (2 * lam * (1 - w) * q.1 - lam * σ * q.2) * hσ
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  have hq2 : q.2 = 0 := by
    rw [hq1] at h1
    have : σ * q.2 = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp this with h | h
    · rw [h] at hσ; norm_num at hσ
    · exact h
  exact Prod.ext hq1 hq2

theorem bigonTubeDeriv_injective_curve {γ N : ℝ → ℝ × ℝ} {τ : ℝ}
    (hdet : (deriv γ τ).1 * (N τ).2 - (deriv γ τ).2 * (N τ).1 ≠ 0) :
    Function.Injective (bigonTubeDeriv γ N (τ, 0)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  rw [bigonTubeDeriv_apply] at hq
  simp only [zero_smul, add_zero] at hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at h1 h2
  have ha : q.1 * ((deriv γ τ).1 * (N τ).2 - (deriv γ τ).2 * (N τ).1) = 0 := by
    linear_combination (N τ).2 * h1 - (N τ).1 * h2
  have hb : q.2 * ((deriv γ τ).1 * (N τ).2 - (deriv γ τ).2 * (N τ).1) = 0 := by
    linear_combination (deriv γ τ).1 * h2 - (deriv γ τ).2 * h1
  exact Prod.ext ((mul_eq_zero.mp ha).resolve_right hdet) ((mul_eq_zero.mp hb).resolve_right hdet)

theorem bigonGerm_eventuallyEq_bigonHat (γ N : ℝ → ℝ × ℝ) {z : ℝ × ℝ} (hz : z ∈ lensGood) :
    bigonGerm γ N =ᶠ[𝓝 z] bigonHat γ N ∘ lensPar := by
  filter_upwards [isOpen_lensGood.mem_nhds hz] with y hy using bigonGerm_eq_bigonHat γ N hy

theorem isLocalDiffeomorphAt_bigonGerm_origin (γ N : ℝ → ℝ × ℝ) {v : ℝ} (hv : |v| < 1 / 2) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (bigonGerm γ N) (0, v) := by
  let B : Set (ℝ × ℝ) := {z | |z.2| < 1 / 2 ∧ |z.1| < 1 / 32}
  have hB : IsOpen B := (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const)
  have hvB : ((0 : ℝ), v) ∈ B := ⟨hv, by simp⟩
  have heq : ∀ z ∈ B, bigonGerm γ N z = swapCLM z := by
    intro z hz
    unfold bigonGerm
    rw [lensCutoff_eq_one hz.1.le hz.2.le, sub_self, zero_smul, zero_add, one_smul]
    rfl
  refine isLocalDiffeomorphAt_of_hasFDerivAt_injective hB hvB
    (swapCLM.contDiff.contDiffOn.congr heq) ?_
    (fun a b (h : swapCLM a = swapCLM b) => Prod.swap_injective h)
  exact swapCLM.hasFDerivAt.congr_of_eventuallyEq
    (Filter.mem_of_superset (hB.mem_nhds hvB) heq)

theorem isLocalDiffeomorphAt_bigonGerm_axis {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ)
    (hN : ContDiff ℝ ∞ N) (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hNm : ∀ᶠ t in 𝓝 (-1), N t = (1, 0)) (hNp : ∀ᶠ t in 𝓝 1, N t = (-1, 0))
    (htm : 0 < (deriv γ (-1)).2) (htp : (deriv γ 1).2 < 0) {v : ℝ} (hv : v ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (bigonGerm γ N) (0, v) := by
  have hz : ((0 : ℝ), v) ∈ lensGood := Or.inl hv
  set σ := v / |v| with hσdef
  have hpar : lensPar (0, v) = (σ, 1 - |v|) := lensPar_axis hv
  have hinj : Function.Injective (bigonHatDeriv γ N (σ, 1 - |v|)) := by
    have hw : 1 - |v| < 1 := by have := abs_pos.mpr hv; linarith
    rcases lt_or_gt_of_ne hv with h | h
    · have hσ : σ = -1 := by rw [hσdef, abs_of_neg h, div_neg, div_self hv]
      rw [hσ]
      have hE : N =ᶠ[𝓝 (-1)] fun _ => ((1 : ℝ), (0 : ℝ)) := hNm
      refine bigonHatDeriv_injective_axis (by norm_num) hw hγm
        (by rw [hNm.self_of_nhds]; norm_num) ?_ (by linarith)
      rw [hE.deriv_eq]
      simp
    · have hσ : σ = 1 := by rw [hσdef, abs_of_pos h, div_self hv]
      rw [hσ]
      have hE : N =ᶠ[𝓝 1] fun _ => ((-1 : ℝ), (0 : ℝ)) := hNp
      refine bigonHatDeriv_injective_axis (by norm_num) hw hγp
        (by rw [hNp.self_of_nhds]) ?_ (by linarith)
      rw [hE.deriv_eq]
      simp
  have hd : HasFDerivAt (bigonHat γ N ∘ lensPar)
      ((bigonHatDeriv γ N (lensPar (0, v))).comp
        (((lensRadEquiv (lensPar_snd_lt_one hz)).symm : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
          (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (0, v) :=
    (hasFDerivAt_bigonHat hγ hN (lensPar (0, v))).comp (0, v) (hasFDerivAt_lensPar hz)
  rw [← hpar] at hinj
  refine isLocalDiffeomorphAt_of_hasFDerivAt_injective isOpen_lensGood hz
    (contDiffOn_bigonGerm hγ hN) (hd.congr_of_eventuallyEq
      (bigonGerm_eventuallyEq_bigonHat γ N hz)) ?_
  exact hinj.comp (lensRadEquiv (lensPar_snd_lt_one hz)).symm.injective

theorem isLocalDiffeomorphAt_bigonGerm_curve {γ N : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ)
    (hN : ContDiff ℝ ∞ N) {τ : ℝ}
    (hdet : (deriv γ τ).1 * (N τ).2 - (deriv γ τ).2 * (N τ).1 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (bigonGerm γ N) (1 - τ ^ 2, τ) := by
  have hz := curve_mem_lensGood τ
  have hr : lensRad (τ, 0) = (1 - τ ^ 2, τ) := by simp [lensRad]
  have hC : ∀ᶠ p in 𝓝 ((τ, 0) : ℝ × ℝ), lensCutoff (lensRad p) = 0 := by
    have h := lensCutoff_curve_eventually τ
    rw [← hr] at h
    exact contDiff_lensRad.continuous.continuousAt.preimage_mem_nhds h
  have hhat : bigonHat γ N =ᶠ[𝓝 (τ, 0)] bigonTube γ N := by
    filter_upwards [hC] with p hp
    simp [bigonHat, hp]
  have hdT : HasFDerivAt (bigonHat γ N) (bigonTubeDeriv γ N (τ, 0))
      (lensPar (1 - τ ^ 2, τ)) := by
    rw [lensPar_curve]
    exact (hasFDerivAt_bigonTube hγ hN (τ, 0)).congr_of_eventuallyEq hhat
  have hd := hdT.comp (1 - τ ^ 2, τ) (hasFDerivAt_lensPar hz)
  refine isLocalDiffeomorphAt_of_hasFDerivAt_injective isOpen_lensGood hz
    (contDiffOn_bigonGerm hγ hN) (hd.congr_of_eventuallyEq
      (bigonGerm_eventuallyEq_bigonHat γ N hz)) ?_
  exact (bigonTubeDeriv_injective_curve hdet).comp
    (lensRadEquiv (lensPar_snd_lt_one hz)).symm.injective

def lensCurve (τ : ℝ) : ℝ × ℝ := (1 - τ ^ 2, τ)

def lensCore (a : ℝ) : Set (ℝ × ℝ) :=
  {0} ×ˢ Icc (-1 - a) (1 + a) ∪ lensCurve '' Icc (-1 - a) (1 + a)

theorem bigonGerm_lensCurve (γ N : ℝ → ℝ × ℝ) (τ : ℝ) : bigonGerm γ N (lensCurve τ) = γ τ :=
  bigonGerm_curve γ N τ

theorem isCompact_lensCore (a : ℝ) : IsCompact (lensCore a) :=
  (isCompact_singleton.prod isCompact_Icc).union
    (isCompact_Icc.image (by unfold lensCurve; fun_prop))

theorem exists_bigon_germ {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) {ε : ℝ}
    (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hout : ∀ t ∈ Icc (-1 - ε) (1 + ε), t < -1 ∨ 1 < t → (γ t).2 < 0)
    (hin : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < (γ t).2)
    (htm : 0 < (deriv γ (-1)).2) (htp : (deriv γ 1).2 < 0)
    (himm : ∀ t ∈ Icc (-1 - ε) (1 + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (-1 - ε) (1 + ε))) :
    ∃ c₀ : ℝ × ℝ → ℝ × ℝ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ lensCore ε ⊆ U ∧ InjOn c₀ U ∧
      (∀ x ∈ U, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ c₀ x) ∧
      (∀ v, c₀ (0, v) = (v, 0)) ∧ (∀ τ, c₀ (lensCurve τ) = γ τ) ∧
      ∀ z : ℝ × ℝ, |z.2| ≤ 1 / 2 → |z.1| ≤ 1 / 32 → c₀ z = z.swap := by
  obtain ⟨N, hN, hNm, hNp, hdet⟩ := exists_bigon_normal hγ himm htm htp
  have hax := bigonGerm_axis (N := N) hγm hγp hNm.self_of_nhds hNp.self_of_nhds
  have hloc : ∀ x ∈ lensCore ε,
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (bigonGerm γ N) x := by
    rintro x (⟨hx1, -⟩ | ⟨τ, hτ, rfl⟩)
    · obtain ⟨u, v⟩ := x
      have hu : u = 0 := hx1
      subst hu
      by_cases hv : v = 0
      · subst hv
        exact isLocalDiffeomorphAt_bigonGerm_origin γ N (by norm_num)
      · exact isLocalDiffeomorphAt_bigonGerm_axis hγ hN hγm hγp hNm hNp htm htp hv
    · exact isLocalDiffeomorphAt_bigonGerm_curve hγ hN (hdet τ hτ).ne
  have hinjK : InjOn (bigonGerm γ N) (lensCore ε) := by
    have hzero : ∀ τ ∈ Icc (-1 - ε) (1 + ε), (γ τ).2 = 0 → τ = -1 ∨ τ = 1 := by
      intro τ hτ h0
      by_contra hcon
      push Not at hcon
      rcases lt_trichotomy τ (-1) with h | h | h
      · exact (hout τ hτ (Or.inl h)).ne h0
      · exact hcon.1 h
      · rcases lt_trichotomy τ 1 with h' | h' | h'
        · exact (hin τ ⟨h, h'⟩).ne' h0
        · exact hcon.2 h'
        · exact (hout τ hτ (Or.inr h')).ne h0
    have hcross : ∀ v, ∀ τ ∈ Icc (-1 - ε) (1 + ε), ((v, 0) : ℝ × ℝ) = γ τ →
        ((0 : ℝ), v) = lensCurve τ := by
      intro v τ hτ he
      rcases hzero τ hτ (by rw [← he]) with rfl | rfl
      · rw [hγm] at he
        simp only [Prod.mk.injEq] at he
        rw [he.1]
        simp [lensCurve]
      · rw [hγp] at he
        simp only [Prod.mk.injEq] at he
        rw [he.1]
        simp [lensCurve]
    rintro x (⟨hx1, hx2⟩ | ⟨τ, hτ, rfl⟩) y (⟨hy1, hy2⟩ | ⟨σ, hσ, rfl⟩) hxy
    · obtain ⟨u, v⟩ := x
      obtain ⟨u', v'⟩ := y
      have hu : u = 0 := hx1
      have hu' : u' = 0 := hy1
      subst hu hu'
      rw [hax, hax] at hxy
      simp only [Prod.mk.injEq] at hxy
      rw [hxy.1]
    · obtain ⟨u, v⟩ := x
      have hu : u = 0 := hx1
      subst hu
      rw [hax, bigonGerm_lensCurve] at hxy
      exact hcross v σ hσ hxy
    · obtain ⟨u', v'⟩ := y
      have hu' : u' = 0 := hy1
      subst hu'
      rw [hax, bigonGerm_lensCurve] at hxy
      exact (hcross v' τ hτ hxy.symm).symm
    · rw [bigonGerm_lensCurve, bigonGerm_lensCurve] at hxy
      rw [hinj hτ hσ hxy]
  obtain ⟨d, hKd, -, hd⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn_compact
      (I := 𝓘(ℝ, ℝ × ℝ)) (J := 𝓘(ℝ, ℝ × ℝ)) (isCompact_lensCore ε) hinjK hloc isOpen_univ
      (subset_univ _)
  refine ⟨bigonGerm γ N, d.source, d.open_source, hKd, ?_, ?_, hax, bigonGerm_lensCurve γ N, ?_⟩
  · rw [← hd]
    exact d.injOn
  · intro x hx
    rw [← hd]
    exact PartialDiffeomorph.isLocalDiffeomorphAt (I := 𝓘(ℝ, ℝ × ℝ)) (J := 𝓘(ℝ, ℝ × ℝ))
      (n := ∞) d hx
  · intro z h2 h1
    unfold bigonGerm
    rw [lensCutoff_eq_one h2 h1, sub_self, zero_smul, zero_add, one_smul]

end GC.Seifert
