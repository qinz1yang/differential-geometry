import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelPorts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus
import DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph

/-!
# Nested circles

Lane N2d, side model, step 3 (generic part). A family of circles `c ρ + r ρ · S¹` is strictly
nested on `[0, 3]` (`NestedOn`) if `‖c ρ₂ - c ρ₁‖ < r ρ₁ - r ρ₂` for `ρ₁ < ρ₂`. Parametrized
through a rotation `μ ρ` and a real Blaschke factor `blaschke (a ρ) u = (u + a) / (1 + a u)`
(`|a| < 1`), the map `nestedPoint (u, ρ) = c ρ + r ρ · μ ρ · blaschke (a ρ) u` is injective on
`S¹ × [0, 3]` (`nestedPoint_injOn`), maps onto the closed region between the outer circle `ρ = 0`
and the inner circle `ρ = 3` (`nestedPoint_mem`, `exists_nestedPoint_eq`), and is a local
diffeomorphism where `‖c'‖ < -r'` (`isLocalDiffeomorphAt_nestedPoint`): it is the map
`(v, ρ) ↦ c ρ + r ρ · v` composed with the diffeomorphism `(u, ρ) ↦ (μ ρ · blaschke (a ρ) u, ρ)`
of the cylinder, whose Jacobian is `r · (Re (v̄ c') + r')`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

open GC.GraphManifold

theorem norm_add_real_eq_norm_one_add {a : ℝ} (u : Circle) :
    ‖(u : ℂ) + a‖ = ‖1 + (a : ℂ) * u‖ := by
  have hu := Circle.normSq_coe u
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  rw [Complex.normSq_apply] at hu
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, zero_mul, sub_zero,
    zero_add]
  linear_combination (1 - a * a) * hu

theorem one_add_mul_ne_zero {a : ℝ} (ha : |a| < 1) (u : Circle) : 1 + (a : ℂ) * u ≠ 0 := by
  intro h0
  have h1 : ‖(a : ℂ) * u‖ = |a| := by rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  have h2 : (a : ℂ) * u = -1 := by linear_combination h0
  rw [h2, norm_neg, norm_one] at h1
  linarith

def blaschkeVal (a : ℝ) (z : ℂ) : ℂ := (z + a) / (1 + (a : ℂ) * z)

theorem norm_blaschkeVal {a : ℝ} (ha : |a| < 1) (u : Circle) : ‖blaschkeVal a (u : ℂ)‖ = 1 := by
  rw [blaschkeVal, norm_div, norm_add_real_eq_norm_one_add,
    div_self (norm_ne_zero_iff.mpr (one_add_mul_ne_zero ha u))]

def blaschke (a : ℝ) (u : Circle) : Circle := unitOf (blaschkeVal a (u : ℂ))

theorem coe_blaschke {a : ℝ} (ha : |a| < 1) (u : Circle) :
    (blaschke a u : ℂ) = blaschkeVal a (u : ℂ) := by
  have hn := norm_blaschkeVal ha u
  have h0 : blaschkeVal a (u : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [blaschke, coe_unitOf h0, hn, inv_one, one_smul]

theorem blaschke_zero (u : Circle) : blaschke 0 u = u := by
  apply Circle.ext
  rw [coe_blaschke (by norm_num) u, blaschkeVal]
  simp

theorem blaschke_neg_blaschke {a : ℝ} (ha : |a| < 1) (u : Circle) :
    blaschke (-a) (blaschke a u) = u := by
  have ha' : |-a| < 1 := by rwa [abs_neg]
  apply Circle.ext
  rw [coe_blaschke ha', coe_blaschke ha]
  set z : ℂ := (u : ℂ)
  have h1 : 1 + (a : ℂ) * z ≠ 0 := one_add_mul_ne_zero ha u
  have h2 : (1 : ℂ) - (a : ℂ) ^ 2 ≠ 0 := by
    intro h
    have : (a : ℂ) ^ 2 = 1 := by linear_combination -h
    have h' : a ^ 2 = 1 := by exact_mod_cast this
    nlinarith [abs_nonneg a, sq_abs a]
  have hnum : (z + a) / (1 + a * z) + ((-a : ℝ) : ℂ) = z * (1 - (a : ℂ) ^ 2) / (1 + a * z) := by
    rw [eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
    push_cast
    ring
  have hden : 1 + ((-a : ℝ) : ℂ) * ((z + a) / (1 + a * z)) = (1 - (a : ℂ) ^ 2) / (1 + a * z) := by
    rw [eq_div_iff h1, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ h1]
    push_cast
    ring
  simp only [blaschkeVal]
  rw [hnum, hden, div_div_div_cancel_right₀ h1, mul_div_assoc, div_self h2, mul_one]

theorem blaschke_blaschke_neg {a : ℝ} (ha : |a| < 1) (u : Circle) :
    blaschke a (blaschke (-a) u) = u := by
  have h := blaschke_neg_blaschke (a := -a) (by rwa [abs_neg]) u
  rwa [neg_neg] at h

theorem blaschke_injective {a : ℝ} (ha : |a| < 1) : Injective (blaschke a) := fun u v huv => by
  rw [← blaschke_neg_blaschke ha u, huv, blaschke_neg_blaschke ha v]

variable (c : ℝ → ℂ) (r : ℝ → ℝ) (μ : ℝ → Circle) (a : ℝ → ℝ)

def nestedPoint (q : Circle × ℝ) : ℂ :=
  c q.2 + (r q.2 : ℂ) * ((μ q.2 * blaschke (a q.2) q.1 : Circle) : ℂ)

def NestedOn (s : Set ℝ) : Prop := ∀ ρ₁ ∈ s, ∀ ρ₂ ∈ s, ρ₁ < ρ₂ → ‖c ρ₂ - c ρ₁‖ < r ρ₁ - r ρ₂

variable {c r μ a}

theorem norm_nestedPoint_sub {q : Circle × ℝ} (hr : 0 ≤ r q.2) :
    ‖nestedPoint c r μ a q - c q.2‖ = r q.2 := by
  rw [nestedPoint, add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr]

theorem nestedPoint_injOn (hn : NestedOn c r (Icc 0 3)) (hr : ∀ ρ ∈ Icc (0 : ℝ) 3, 0 < r ρ)
    (ha : ∀ ρ ∈ Icc (0 : ℝ) 3, |a ρ| < 1) :
    InjOn (nestedPoint c r μ a) (univ ×ˢ Icc 0 3) := by
  have key : ∀ q q' : Circle × ℝ, q.2 ∈ Icc (0 : ℝ) 3 → q'.2 ∈ Icc (0 : ℝ) 3 → q.2 < q'.2 →
      nestedPoint c r μ a q ≠ nestedPoint c r μ a q' := by
    intro q q' hq hq' hlt he
    have h1 := norm_nestedPoint_sub (c := c) (μ := μ) (a := a) (hr q.2 hq).le
    have h2 := norm_nestedPoint_sub (c := c) (μ := μ) (a := a) (q := q') (hr q'.2 hq').le
    have h3 := hn q.2 hq q'.2 hq' hlt
    rw [he] at h1
    have h4 := norm_sub_le_norm_sub_add_norm_sub (nestedPoint c r μ a q') (c q'.2) (c q.2)
    linarith
  intro q hq q' hq' he
  rcases lt_trichotomy q.2 q'.2 with hlt | heq | hgt
  · exact absurd he (key q q' hq.2 hq'.2 hlt)
  · have hr0 := hr q.2 hq.2
    have e : (r q.2 : ℂ) * ((μ q.2 * blaschke (a q.2) q.1 : Circle) : ℂ) =
        (r q.2 : ℂ) * ((μ q.2 * blaschke (a q.2) q'.1 : Circle) : ℂ) := by
      have := he
      rw [nestedPoint, nestedPoint, ← heq] at this
      exact add_left_cancel this
    have e2 := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr0.ne') e
    have e3 : μ q.2 * blaschke (a q.2) q.1 = μ q.2 * blaschke (a q.2) q'.1 := Circle.ext e2
    have e4 := blaschke_injective (ha q.2 hq.2) (mul_left_cancel e3)
    exact Prod.ext e4 heq
  · exact absurd he.symm (key q' q hq'.2 hq.2 hgt)

theorem nestedPoint_mem (hn : NestedOn c r (Icc 0 3)) (hr : ∀ ρ ∈ Icc (0 : ℝ) 3, 0 ≤ r ρ)
    {q : Circle × ℝ} (hq : q.2 ∈ Icc (0 : ℝ) 3) :
    ‖nestedPoint c r μ a q - c 0‖ ≤ r 0 ∧ r 3 ≤ ‖nestedPoint c r μ a q - c 3‖ := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨le_rfl, by norm_num⟩
  have h3 : (3 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by norm_num, le_rfl⟩
  have hp := norm_nestedPoint_sub (c := c) (μ := μ) (a := a) (hr q.2 hq)
  constructor
  · by_cases he : q.2 = 0
    · rw [he] at hp
      exact hp.le
    · have hlt : 0 < q.2 := lt_of_le_of_ne hq.1 (Ne.symm he)
      have hnest := hn 0 h0 q.2 hq hlt
      have h4 := norm_sub_le_norm_sub_add_norm_sub (nestedPoint c r μ a q) (c q.2) (c 0)
      linarith
  · by_cases he : q.2 = 3
    · rw [he] at hp
      exact hp.ge
    · have hlt : q.2 < 3 := lt_of_le_of_ne hq.2 he
      have hnest := hn q.2 hq 3 h3 hlt
      have h4 := norm_sub_le_norm_sub_add_norm_sub (nestedPoint c r μ a q) (c 3) (c q.2)
      have h5 : ‖c 3 - c q.2‖ = ‖c 3 - c q.2‖ := rfl
      linarith

theorem exists_nestedPoint_eq (hc : ContinuousOn c (Icc 0 3)) (hrc : ContinuousOn r (Icc 0 3))
    (hr : ∀ ρ ∈ Icc (0 : ℝ) 3, 0 < r ρ) (ha : ∀ ρ ∈ Icc (0 : ℝ) 3, |a ρ| < 1) {w : ℂ}
    (h0 : ‖w - c 0‖ ≤ r 0) (h3 : r 3 ≤ ‖w - c 3‖) :
    ∃ q : Circle × ℝ, q.2 ∈ Icc (0 : ℝ) 3 ∧ nestedPoint c r μ a q = w := by
  have hg : ContinuousOn (fun ρ => ‖w - c ρ‖ - r ρ) (Icc 0 3) :=
    ((continuousOn_const.sub hc).norm).sub hrc
  have hmem : (0 : ℝ) ∈ Icc (‖w - c 0‖ - r 0) (‖w - c 3‖ - r 3) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨ρ, hρ, hρ0⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 3) hg hmem
  simp only at hρ0
  have hrρ := hr ρ hρ
  have hne : w - c ρ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ0
    linarith
  set v := unitOf (w - c ρ) with hv
  refine ⟨(blaschke (-a ρ) ((μ ρ)⁻¹ * v), ρ), hρ, ?_⟩
  simp only [nestedPoint]
  rw [blaschke_blaschke_neg (ha ρ hρ), mul_inv_cancel_left]
  have hn : ‖w - c ρ‖ = r ρ := by linarith
  have := norm_smul_unitOf (w - c ρ)
  rw [hn, Complex.real_smul] at this
  rw [this]
  ring


section LocalDiffeo

open GC.Seifert.AnnulusStraightening

theorem isLocalDiffeomorphAt_of_comp_left {E F G H H' H'' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace H''] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
    {f : M → N} {g : N → P} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x)
    (hgf : IsLocalDiffeomorphAt I K ∞ (g ∘ f) x) : IsLocalDiffeomorphAt J K ∞ g (f x) := by
  have h := hf.localInverse_isLocalDiffeomorphAt.comp (P := P) (K := K) (n := ∞)
    (hf.localInverse_left_inv hf.localInverse_mem_target ▸ hgf)
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ h
  filter_upwards [hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source] with y hy
  simp only [Function.comp_apply, hf.localInverse_right_inv hy]

theorem hasDerivAt_coe_cexp (t : ℝ) :
    HasDerivAt (fun s : ℝ => (cexp s : ℂ)) (2 * Real.pi * Complex.I * (cexp t : ℂ)) t := by
  have he : (fun s : ℝ => (cexp s : ℂ)) =
      fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    funext s
    rw [cexp_eq, Circle.coe_exp]
  rw [he]
  have h1 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I
    simpa using this
  have h2 := h1.cexp
  convert h2 using 1
  rw [cexp_eq, Circle.coe_exp]
  push_cast
  ring

theorem injective_of_im_ne {A B : ℂ} (hA : A ≠ 0) (h : (starRingEnd ℂ A * B).im ≠ 0) :
    Injective ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight B) := by
  have H : ∀ x y : ℝ, x • A + y • B = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have e : starRingEnd ℂ A * (x • A + y • B) = 0 := by rw [hxy, mul_zero]
    have hi := congrArg Complex.im e
    have hexp : starRingEnd ℂ A * (x • A + y • B) =
        (x * Complex.normSq A : ℝ) + (y : ℂ) * (starRingEnd ℂ A * B) := by
      rw [Complex.real_smul, Complex.real_smul, mul_add]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [hexp] at hi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
      add_zero, zero_add, Complex.zero_im] at hi
    have hy : y = 0 := by
      rcases mul_eq_zero.mp hi with h0 | h0
      · exact h0
      · exact absurd h0 h
    rw [hy, zero_smul, add_zero] at hxy
    refine ⟨?_, hy⟩
    rcases smul_eq_zero.mp hxy with h0 | h0
    · exact h0
    · exact absurd h0 hA
  intro p q hpq
  have h0 : ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight B) (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h0
  obtain ⟨h1, h2⟩ := H _ _ h0
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)


theorem im_conj_mul_aux (R : ℝ) (w c' : ℂ) (r' : ℝ) (hw : starRingEnd ℂ w * w = 1) :
    (starRingEnd ℂ ((R : ℂ) * (2 * Real.pi * Complex.I * w)) * (c' + (r' : ℂ) * w)).im =
      -(2 * Real.pi * R) * ((starRingEnd ℂ w * c').re + r') := by
  have e : starRingEnd ℂ ((R : ℂ) * (2 * Real.pi * Complex.I * w)) * (c' + (r' : ℂ) * w) =
      ((-(2 * Real.pi * R) : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ w * c' + (r' : ℂ)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * R) * Complex.I * r') * hw
  rw [e]
  simp [Complex.mul_im, Complex.mul_re]

theorem isLocalDiffeomorphAt_circleFamily {c : ℝ → ℂ} {r : ℝ → ℝ} {O : Set ℝ} (hO : IsOpen O)
    (hc : ContDiffOn ℝ ∞ c O) (hr : ContDiffOn ℝ ∞ r O) {v : Circle} {ρ : ℝ} (hρ : ρ ∈ O)
    {c' : ℂ} {r' : ℝ} (hc' : HasDerivAt c c' ρ) (hr' : HasDerivAt r r' ρ) (hr0 : 0 < r ρ)
    (hd : ‖c'‖ < -r') :
    IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun q : Circle × ℝ => c q.2 + (r q.2 : ℂ) * (q.1 : ℂ)) (v, ρ) := by
  obtain ⟨t, rfl⟩ := cexp_surjective v
  set F : ℝ × ℝ → ℂ := fun p => c p.2 + (r p.2 : ℂ) * (cexp p.1 : ℂ) with hF
  have hE : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.map cexp id) (t, ρ) :=
    (isLocalDiffeomorph_cexp t).prodMap ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph ρ)
  set A : ℂ := (r ρ : ℂ) * (2 * Real.pi * Complex.I * (cexp t : ℂ)) with hA
  set B : ℂ := c' + (r' : ℂ) * (cexp t : ℂ) with hB
  have hderiv : HasFDerivAt F ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight B) (t, ρ) := by
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => c p.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight c') (t, ρ) := by
      exact (hc'.hasFDerivAt.comp (f := (Prod.snd : ℝ × ℝ → ℝ)) (t, ρ)
        hasFDerivAt_snd).congr_fderiv (by ext <;> simp)
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => (r p.2 : ℂ))
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (r' : ℂ)) (t, ρ) := by
      exact ((hr'.ofReal_comp).hasFDerivAt.comp (f := (Prod.snd : ℝ × ℝ → ℝ)) (t, ρ)
        hasFDerivAt_snd).congr_fderiv (by ext <;> simp)
    have h3 : HasFDerivAt (fun p : ℝ × ℝ => (cexp p.1 : ℂ))
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (2 * Real.pi * Complex.I * (cexp t : ℂ)))
        (t, ρ) := by
      exact ((hasDerivAt_coe_cexp t).hasFDerivAt.comp (f := (Prod.fst : ℝ × ℝ → ℝ)) (t, ρ)
        hasFDerivAt_fst).congr_fderiv (by ext <;> simp)
    have h4 := h1.add (h2.mul h3)
    convert h4 using 1
    ext
    all_goals simp [hA, hB]
    all_goals ring
  have hsmooth : ContDiffOn ℝ ∞ F (univ ×ˢ O) := by
    have hcexp : ContDiff ℝ ∞ (fun s : ℝ => (cexp s : ℂ)) :=
      contMDiff_iff_contDiff.mp (contMDiff_circle_coe.comp contMDiff_cexp)
    refine (hc.comp contDiffOn_snd (fun p hp => hp.2)).add
      (((Complex.ofRealCLM.contDiff.comp_contDiffOn (hr.comp contDiffOn_snd
        (fun p hp => hp.2)))).mul (hcexp.comp contDiff_fst).contDiffOn)
  have hFl : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ F (t, ρ) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    refine isLocalDiffeomorphAt_of_injective_mfderiv hsmooth.contMDiffOn
      (isOpen_univ.prod hO) ⟨mem_univ _, hρ⟩ (by simp) ?_
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    refine injective_of_im_ne ?_ ?_
    · rw [hA]
      refine mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne') (mul_ne_zero (mul_ne_zero
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Circle.coe_ne_zero _))
    · have hu : starRingEnd ℂ (cexp t : ℂ) * (cexp t : ℂ) = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Circle.norm_coe]
        simp
      have hval := im_conj_mul_aux (r ρ) (cexp t : ℂ) c' r' hu
      rw [← hA, ← hB] at hval
      rw [hval]
      have hre : (starRingEnd ℂ (cexp t : ℂ) * c').re ≤ ‖c'‖ := by
        refine (Complex.re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]
      have hpi := Real.pi_pos
      have : (starRingEnd ℂ (cexp t : ℂ) * c').re + r' < 0 := by linarith
      have h2 : 0 < 2 * Real.pi * r ρ := by positivity
      nlinarith
  have hcomp : (fun q : Circle × ℝ => c q.2 + (r q.2 : ℂ) * (q.1 : ℂ)) ∘ Prod.map cexp id = F := by
    funext p
    rfl
  have := isLocalDiffeomorphAt_of_comp_left hE (hcomp ▸ hFl)
  simpa using this

theorem contDiffAt_blaschkeVal {a : ℝ} {z : ℂ} (h : 1 + (a : ℂ) * z ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => blaschkeVal q.1 q.2) (a, z) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2 + (q.1 : ℂ)) :=
    contDiff_snd.add (Complex.ofRealCLM.contDiff.comp contDiff_fst)
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℂ => 1 + (q.1 : ℂ) * q.2) :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_snd)
  have h3 : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => (1 + (q.1 : ℂ) * q.2)⁻¹) (a, z) :=
    ((contDiffAt_inv ℂ h).restrict_scalars ℝ).comp (a, z) h2.contDiffAt
  have h4 := (h1.contDiffAt (x := (a, z))).mul h3
  simpa only [blaschkeVal, div_eq_mul_inv] using h4

theorem contMDiffOn_blaschke_comp {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {α : M' → ℝ} {β : M' → Circle} {s : Set M'}
    (hα : ContMDiffOn I' 𝓘(ℝ, ℝ) ∞ α s) (hβ : ContMDiffOn I' (𝓡 1) ∞ β s)
    (h : ∀ x ∈ s, |α x| < 1) :
    ContMDiffOn I' (𝓡 1) ∞ (fun x => blaschke (α x) (β x)) s := by
  have hpair : ContMDiffOn I' 𝓘(ℝ, ℝ × ℂ) ∞ (fun x => (α x, ((β x : Circle) : ℂ))) s :=
    hα.prodMk_space (contMDiff_circle_coe.comp_contMDiffOn hβ)
  have hval : ContMDiffOn I' 𝓘(ℝ, ℂ) ∞ (fun x => blaschkeVal (α x) ((β x : Circle) : ℂ)) s := by
    intro x hx
    have hc := (contDiffAt_blaschkeVal (one_add_mul_ne_zero (h x hx) (β x))).contMDiffAt
    exact hc.comp_contMDiffWithinAt x (hpair x hx)
  have hne : MapsTo (fun x => blaschkeVal (α x) ((β x : Circle) : ℂ)) s {z : ℂ | z ≠ 0} := by
    intro x hx h0
    have hn := norm_blaschkeVal (h x hx) (β x)
    rw [show blaschkeVal (α x) ((β x : Circle) : ℂ) = 0 from h0, norm_zero] at hn
    exact zero_ne_one hn
  exact contMDiffOn_unitOf.comp hval hne

def cylTwist (μ : ℝ → Circle) (a : ℝ → ℝ) {O : Set ℝ} (hO : IsOpen O)
    (hμ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ μ O) (ha : ContDiffOn ℝ ∞ a O)
    (ha1 : ∀ ρ ∈ O, |a ρ| < 1) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) (Circle × ℝ) (Circle × ℝ) ∞ where
  toFun q := (μ q.2 * blaschke (a q.2) q.1, q.2)
  invFun q := (blaschke (-a q.2) ((μ q.2)⁻¹ * q.1), q.2)
  source := univ ×ˢ O
  target := univ ×ˢ O
  map_source' q hq := ⟨mem_univ _, hq.2⟩
  map_target' q hq := ⟨mem_univ _, hq.2⟩
  left_inv' q hq := by
    simp only [inv_mul_cancel_left, blaschke_neg_blaschke (ha1 q.2 hq.2)]
  right_inv' q hq := by
    simp only [blaschke_blaschke_neg (ha1 q.2 hq.2), mul_inv_cancel_left]
  open_source := isOpen_univ.prod hO
  open_target := isOpen_univ.prod hO
  contMDiffOn_toFun := by
    have hs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : Circle × ℝ => q.2)
        (univ ×ˢ O) := contMDiff_snd.contMDiffOn
    have hμ' : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun q : Circle × ℝ => μ q.2)
        (univ ×ˢ O) := hμ.comp hs (fun q hq => hq.2)
    have ha' : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : Circle × ℝ => a q.2)
        (univ ×ˢ O) := ha.contMDiffOn.comp hs (fun q hq => hq.2)
    have hb := contMDiffOn_blaschke_comp ha' contMDiff_fst.contMDiffOn
      (fun q hq => ha1 q.2 hq.2)
    exact (hμ'.mul hb).prodMk hs
  contMDiffOn_invFun := by
    have hs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : Circle × ℝ => q.2)
        (univ ×ˢ O) := contMDiff_snd.contMDiffOn
    have hμ' : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun q : Circle × ℝ => μ q.2)
        (univ ×ˢ O) := hμ.comp hs (fun q hq => hq.2)
    have ha' : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : Circle × ℝ => -a q.2)
        (univ ×ˢ O) := (ha.contMDiffOn.comp hs (fun q hq => hq.2)).neg
    have hb := contMDiffOn_blaschke_comp ha' (hμ'.inv.mul contMDiff_fst.contMDiffOn)
      (fun q hq => by rw [abs_neg]; exact ha1 q.2 hq.2)
    exact hb.prodMk hs

theorem isLocalDiffeomorphAt_nestedPoint {O : Set ℝ} (hO : IsOpen O)
    (hc : ContDiffOn ℝ ∞ c O) (hr : ContDiffOn ℝ ∞ r O)
    (hμ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ μ O) (ha : ContDiffOn ℝ ∞ a O)
    (ha1 : ∀ ρ ∈ O, |a ρ| < 1) {u : Circle} {ρ : ℝ} (hρ : ρ ∈ O) {c' : ℂ} {r' : ℝ}
    (hc' : HasDerivAt c c' ρ) (hr' : HasDerivAt r r' ρ) (hr0 : 0 < r ρ) (hd : ‖c'‖ < -r') :
    IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ (nestedPoint c r μ a) (u, ρ) := by
  have h1 := (cylTwist μ a hO hμ ha ha1).isLocalDiffeomorphAt _ _ ∞
    (show (u, ρ) ∈ (cylTwist μ a hO hμ ha ha1).source from ⟨mem_univ _, hρ⟩)
  have h2 := isLocalDiffeomorphAt_circleFamily (v := μ ρ * blaschke (a ρ) u) hO hc hr hρ hc' hr'
    hr0 hd
  exact h1.comp _ _ h2

end LocalDiffeo

end GC.Seifert.SplitTube
