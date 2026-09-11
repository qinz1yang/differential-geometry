import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Reciprocal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_scalar_lower_bound_by_reciprocal_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1) :
    ∃ c : Real, 0 < c ∧ ∀ x : M,
      c * (f x ^ (-1 : Real) + (Module.finrank Real E : Real) *
        f x ^ (-2 : Real)) ≤ metricScalarAt (I := I) g x ∧
      c / f x ≤ c * (f x ^ (-1 : Real) +
        (Module.finrank Real E : Real) * f x ^ (-2 : Real)) := by
  classical
  let n : Real := Module.finrank Real E
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun x : M => metricScalarAt (I := I) g x,
      metricScalar_smooth (I := I) (M := M) g⟩
  have hRpos (x : M) : 0 < R x :=
    normalizedGradientRicciSoliton_scalar_pos_of_not_isGaussian
      (I := I) h hnot x
  have hRnonneg (x : M) : 0 ≤ R x := (hRpos x).le
  have hfpos (x : M) : 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_not_isGaussian
      (I := I) h hnot x
  let B : C^∞⟮I, M; Real⟯ := reciprocalPotentialBarrier (I := I) f hfpos
  have hBval (x : M) : B x = f x ^ (-1 : Real) + n * f x ^ (-2 : Real) := rfl
  have hBpos (x : M) : 0 < B x := by
    rw [hBval]
    have hp1 : 0 < f x ^ (-1 : Real) := Real.rpow_pos_of_pos (hfpos x) _
    have hp2 : 0 < f x ^ (-2 : Real) := Real.rpow_pos_of_pos (hfpos x) _
    have hn : 0 ≤ n := by positivity
    positivity
  let p : M := Classical.choice (inferInstance : Nonempty M)
  let F : Real := max (f p) (2 * n + 1)
  let K : Set M := {x | f x ≤ F}
  have hK_eq : K = (f : M → Real) ⁻¹' Set.Icc 0 F := by
    ext x
    simp only [K, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    exact (and_iff_right (hfpos x).le).symm
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    exact (normalizedGradientRicciSoliton_potential_isProperMap (I := I) h).isCompact_preimage
      isCompact_Icc
  have hpK : p ∈ K := by
    change f p ≤ max (f p) (2 * n + 1)
    exact le_max_left _ _
  let Q : M → Real := fun x => R x / B x
  have hQcont : Continuous Q := by
    exact R.contMDiff.continuous.div B.contMDiff.continuous
      (fun x => (hBpos x).ne')
  obtain ⟨z, hzK, hzmin⟩ :=
    hKcompact.exists_isMinOn ⟨p, hpK⟩ hQcont.continuousOn
  let c : Real := Q z / 2
  have hQzpos : 0 < Q z := div_pos (hRpos z) (hBpos z)
  have hcpos : 0 < c := by dsimp only [c]; linarith
  have hcore (x : M) (hx : x ∈ K) : c * B x < R x := by
    have hzle := hzmin hx
    change Q z ≤ Q x at hzle
    have hcQ : c < Q x := by
      dsimp only [c]
      linarith
    change c < R x / B x at hcQ
    exact (lt_div_iff₀ (hBpos x)).mp hcQ
  have hbarrier : ∀ x : M, c * B x ≤ R x := by
    by_contra hbound
    simp only [not_forall, not_le] at hbound
    obtain ⟨y, hy⟩ := hbound
    let Φ : C^∞⟮I, M; Real⟯ := R + (-c) • B
    have hyΦ : Φ y < 0 := by
      change R y + -c * B y < 0
      linarith
    have hlim1 : Tendsto (fun t : Real => t ^ (-1 : Real)) atTop (nhds 0) := by
      simpa using tendsto_rpow_neg_atTop (show (0 : Real) < 1 by norm_num)
    have hlim2 : Tendsto (fun t : Real => t ^ (-2 : Real)) atTop (nhds 0) := by
      simpa using tendsto_rpow_neg_atTop (show (0 : Real) < 2 by norm_num)
    have hlim : Tendsto
        (fun t : Real => c * (t ^ (-1 : Real) + n * t ^ (-2 : Real)))
        atTop (nhds 0) := by
      have hnlim : Tendsto (fun t : Real => n * t ^ (-2 : Real))
          atTop (nhds 0) := by
        simpa using Tendsto.const_mul n hlim2
      have hsum : Tendsto
          (fun t : Real => t ^ (-1 : Real) + n * t ^ (-2 : Real))
          atTop (nhds 0) := by
        simpa using hlim1.add hnlim
      simpa using Tendsto.const_mul c hsum
    have hsmall : ∀ᶠ t : Real in atTop,
        c * (t ^ (-1 : Real) + n * t ^ (-2 : Real)) < -Φ y / 2 :=
      (tendsto_order.mp hlim).2 (-Φ y / 2) (by linarith)
    have hlarge : ∀ᶠ t : Real in atTop, max F (f y) < t :=
      eventually_gt_atTop (max F (f y))
    obtain ⟨T, hTsmall, hTlarge⟩ := (hsmall.and hlarge).exists
    have hFT : F < T := (le_max_left _ _).trans_lt hTlarge
    have hfyT : f y < T := (le_max_right _ _).trans_lt hTlarge
    have hn : 0 ≤ n := by positivity
    have hFlarge : 2 * n < F := by
      have hlarge : 2 * n + 1 ≤ F := le_max_right _ _
      linarith
    have hTpos : 0 < T := by
      have hn1 : 1 ≤ n := by
        dsimp only [n]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (NeZero.ne (Module.finrank Real E))
      linarith
    let L : Set M := {x | f x ≤ T}
    have hL_eq : L = (f : M → Real) ⁻¹' Set.Icc 0 T := by
      ext x
      simp only [L, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
      exact (and_iff_right (hfpos x).le).symm
    have hLcompact : IsCompact L := by
      rw [hL_eq]
      exact (normalizedGradientRicciSoliton_potential_isProperMap (I := I) h).isCompact_preimage
        isCompact_Icc
    have hyL : y ∈ L := hfyT.le
    obtain ⟨x₀, hx₀L, hx₀min⟩ :=
      hLcompact.exists_isMinOn ⟨y, hyL⟩ Φ.contMDiff.continuous.continuousOn
    have hx₀le := hx₀min hyL
    change Φ x₀ ≤ Φ y at hx₀le
    have hx₀neg : Φ x₀ < 0 := hx₀le.trans_lt hyΦ
    have hout (x : M) (hx : T < f x) : Φ y < Φ x := by
      have hp1 : f x ^ (-1 : Real) ≤ T ^ (-1 : Real) :=
        Real.rpow_le_rpow_of_nonpos hTpos hx.le (by norm_num)
      have hp2 : f x ^ (-2 : Real) ≤ T ^ (-2 : Real) :=
        Real.rpow_le_rpow_of_nonpos hTpos hx.le (by norm_num)
      have hBx : B x ≤ T ^ (-1 : Real) + n * T ^ (-2 : Real) := by
        rw [hBval]
        nlinarith
      change Φ y < R x + -c * B x
      have hBnonneg : 0 ≤ B x := (hBpos x).le
      have hTbarrier : 0 ≤ T ^ (-1 : Real) + n * T ^ (-2 : Real) := by
        positivity
      nlinarith [hRnonneg x]
    have hx₀global : IsMinOn (Φ : M → Real) Set.univ x₀ := by
      intro x hx
      by_cases hxL : x ∈ L
      · exact hx₀min hxL
      · have hfx : T < f x := by
          change ¬ f x ≤ T at hxL
          exact lt_of_not_ge hxL
        exact hx₀le.trans (hout x hfx).le
    have hx₀local : IsLocalMin (Φ : M → Real) x₀ :=
      hx₀global.isLocalMin univ_mem
    have hx₀notK : x₀ ∉ K := by
      intro hxK
      have hpositive := hcore x₀ hxK
      change c * B x₀ < R x₀ at hpositive
      have hΦpositive : 0 < Φ x₀ := by
        change 0 < R x₀ + -c * B x₀
        linarith
      linarith
    have hx₀F : F < f x₀ := by
      change ¬ f x₀ ≤ F at hx₀notK
      exact lt_of_not_ge hx₀notK
    have hx₀large : 2 * (Module.finrank Real E : Real) ≤ f x₀ := by
      change 2 * n ≤ f x₀
      exact (hFlarge.trans hx₀F).le
    have hgradΦ : gradFun (I := I) g Φ x₀ = 0 :=
      Operator.gradientFun_eq_zero_at_spatial_min (I := I) g hx₀local
        ((Φ.contMDiff x₀).mdifferentiableAt (by simp))
    have hlapΦ : 0 ≤ ΔG (I := I) g Φ x₀ := by
      have hmetric : IsMetricCompatible (I := I)
          (LeviCivita (I := I) g) g := by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      have hlap : 0 ≤ laplacian (I := I) (LeviCivita (I := I) g) g Φ x₀ :=
        Operator.laplacian_nonneg_at_spatial_min_of_metricCompatible
          (I := I) (LeviCivita (I := I) g) g hmetric hx₀local
          ((Φ.contMDiff x₀).mdifferentiableAt (by simp))
          (Filter.Eventually.of_forall fun x =>
            (Φ.contMDiff x).mdifferentiableAt (by simp))
          ((gradientFun_contMDiffAt (I := I) g (Φ.contMDiff x₀)).mdifferentiableAt
            (by simp))
      rw [laplacian_levi_eq (I := I) g Φ.contMDiff x₀] at hlap
      exact hlap
    have hweightedΦnonneg : 0 ≤ weightedLaplacian (I := I) g f Φ x₀ := by
      rw [weightedLaplacian_apply, hgradΦ]
      simpa using hlapΦ
    have hweightedR :=
      gradientRicciSoliton_weightedLaplacian_scalar (I := I) h.2.1 x₀
    have hweightedR' : weightedLaplacian (I := I) g f R x₀ =
        R x₀ - 2 * Tensor0SBundle.normSq0S (I := I) g x₀ 2
          (metricRicciAt (I := I) (M := M) g x₀) := by
      convert hweightedR using 1
      change metricScalarAt (I := I) g x₀ -
          2 * Tensor0SBundle.normSq0S (I := I) g x₀ 2
            (metricRicciAt (I := I) (M := M) g x₀) =
        1 * metricScalarAt (I := I) g x₀ -
          2 * Tensor0SBundle.normSq0S (I := I) g x₀ 2
            (metricRicciAt (I := I) (M := M) g x₀)
      ring
    have hweightedB :=
      normalizedGradientRicciSoliton_weightedLaplacian_reciprocalPotentialBarrier_ge
        (I := I) h hfpos x₀ hx₀large
    change B x₀ ≤ weightedLaplacian (I := I) g f B x₀ at hweightedB
    have hric : 0 ≤ Tensor0SBundle.normSq0S (I := I) g x₀ 2
        (metricRicciAt (I := I) (M := M) g x₀) :=
      Tensor0SBundle.normSq0S_nonneg (I := I) g x₀ 2 _
    have hweightedΦle : weightedLaplacian (I := I) g f Φ x₀ ≤ Φ x₀ := by
      rw [show Φ = R + (-c) • B by rfl,
        Operator.weightedLaplacian_add,
        Operator.weightedLaplacian_const_smul]
      change weightedLaplacian (I := I) g f R x₀ +
          -c * weightedLaplacian (I := I) g f B x₀ ≤
        R x₀ + -c * B x₀
      nlinarith
    linarith
  refine ⟨c, hcpos, ?_⟩
  intro x
  have hmain := hbarrier x
  rw [hBval] at hmain
  refine ⟨hmain, ?_⟩
  have hsecond : c * f x ^ (-1 : Real) ≤
      c * (f x ^ (-1 : Real) + n * f x ^ (-2 : Real)) := by
    have hp2 : 0 ≤ f x ^ (-2 : Real) := (Real.rpow_pos_of_pos (hfpos x) _).le
    have hn : 0 ≤ n := by positivity
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hn hp2)) hcpos.le
  calc
    c / f x = c * f x ^ (-1 : Real) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    _ ≤ c * (f x ^ (-1 : Real) + n * f x ^ (-2 : Real)) := hsecond

theorem normalizedGradientRicciSoliton_chow_lu_yang_scalar_lower_bound
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (p : M) :
    ∃ c : Real, 0 < c ∧ ∀ x : M,
      c / (1 + (riemannianEDistOf (I := I) g p x).toReal) ^ 2 ≤
        metricScalarAt (I := I) g x := by
  obtain ⟨c, hc, hbarrier⟩ :=
    normalizedGradientRicciSoliton_scalar_lower_bound_by_reciprocal_potential
      (I := I) h hnot
  have hfpos (x : M) : 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_not_isGaussian
      (I := I) h hnot x
  let A : Real := 2 * Real.sqrt (f p)
  let B : Real := 1 + A
  let cₚ : Real := c / B ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 < B := by dsimp only [B]; linarith
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hcₚ : 0 < cₚ := div_pos hc hBsq
  refine ⟨cₚ, hcₚ, ?_⟩
  intro x
  let d : Real := (riemannianEDistOf (I := I) g p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hsum : d + A ≤ B * (1 + d) := by
    dsimp only [B]
    nlinarith
  have hsum_nonneg : 0 ≤ d + A := add_nonneg hd hA
  have hproduct_nonneg : 0 ≤ B * (1 + d) := by positivity
  have hsq : (d + A) ^ 2 ≤ (B * (1 + d)) ^ 2 :=
    (sq_le_sq₀ hsum_nonneg hproduct_nonneg).2 hsum
  have hpotential :=
    normalizedGradientRicciSoliton_potential_le_sq_distance (I := I) h p x
  change f x ≤ 1 / 4 * (d + A) ^ 2 at hpotential
  have hfupper : f x ≤ 1 / 4 * B ^ 2 * (1 + d) ^ 2 := by
    calc
      f x ≤ 1 / 4 * (d + A) ^ 2 := hpotential
      _ ≤ 1 / 4 * (B * (1 + d)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1 / 4 * B ^ 2 * (1 + d) ^ 2 := by ring
  have hden : 0 < (1 + d) ^ 2 := sq_pos_of_pos (by linarith)
  have hnum : cₚ * f x ≤ c * (1 + d) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hfupper hcₚ.le
    have heq : cₚ * (1 / 4 * B ^ 2 * (1 + d) ^ 2) =
        c / 4 * (1 + d) ^ 2 := by
      dsimp only [cₚ]
      field_simp [hB.ne']
    rw [heq] at hmul
    have hq : 0 ≤ (1 + d) ^ 2 := sq_nonneg _
    nlinarith
  have hcompare : cₚ / (1 + d) ^ 2 ≤ c / f x :=
    (div_le_div_iff₀ hden (hfpos x)).2 hnum
  have hpoint := (hbarrier x).2.trans (hbarrier x).1
  change c / f x ≤ metricScalarAt (I := I) g x at hpoint
  exact hcompare.trans hpoint

theorem gradientRicciSoliton_chow_lu_yang_scalar_lower_bound
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    (hσ : 0 < σ)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f σ)
    (p : M) :
    ∃ c : Real, 0 < c ∧ ∀ x : M,
      c / (1 + (riemannianEDistOf (I := I) g p x).toReal) ^ 2 ≤
        metricScalarAt (I := I) g x := by
  obtain ⟨C, hnormalized⟩ :=
    gradientRicciSoliton_exists_normalized (I := I) hcomplete hsol hσ
  let gHat : SmoothRiemannianMetric I M := scaleMetric (I := I) σ hσ g
  let fHat : C^∞⟮I, M; Real⟯ := f + ContMDiffMap.const (C / σ)
  have hnormalized' : normalizedGradientRicciSoliton (I := I) gHat fHat :=
    hnormalized
  have hnotHat : ¬ isGaussianGradientRicciSoliton (E := E) gHat fHat 1 := by
    intro hGaussian
    have hGaussianShift : isGaussianGradientRicciSoliton (E := E)
        gHat (f + ContMDiffMap.const (C / σ)) 1 := hGaussian
    have hGaussianMetric : isGaussianGradientRicciSoliton (E := E) gHat f 1 :=
      (isGaussianGradientRicciSoliton_add_const (I := I) (g := gHat)
        (f := f) (σ := 1) (C / σ)).mp hGaussianShift
    exact hnot
      ((isGaussianGradientRicciSoliton_scaleMetric (I := I) hσ).mp
        hGaussianMetric)
  obtain ⟨c, hc, hnormalizedBound⟩ :=
    normalizedGradientRicciSoliton_chow_lu_yang_scalar_lower_bound
      (I := I) hnormalized' hnotHat p
  let a : Real := Real.sqrt σ
  let B : Real := 1 + a
  let cₚ : Real := σ * c / B ^ 2
  have ha : 0 < a := Real.sqrt_pos.2 hσ
  have hB : 0 < B := by dsimp only [B]; linarith
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hcₚ : 0 < cₚ := div_pos (mul_pos hσ hc) hBsq
  refine ⟨cₚ, hcₚ, ?_⟩
  intro x
  let d : Real := (riemannianEDistOf (I := I) g p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hdHat :
      (riemannianEDistOf (I := I) gHat p x).toReal = a * d := by
    have hscale := congrArg ENNReal.toReal
      (edistOf_scale (I := I) σ hσ g p x)
    change (riemannianEDistOf (I := I) gHat p x).toReal = a * d
    rw [hscale]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg σ)]
  have hpoint := hnormalizedBound x
  rw [hdHat] at hpoint
  have hscaled : σ * (c / (1 + a * d) ^ 2) ≤
      metricScalarAt (I := I) g x := by
    calc
      σ * (c / (1 + a * d) ^ 2) ≤
          σ * metricScalarAt (I := I) gHat x :=
        mul_le_mul_of_nonneg_left hpoint hσ.le
      _ = metricScalarAt (I := I) g x := by
        dsimp only [gHat]
        rw [metricScalarAt_scaleMetric]
        field_simp
  have hsum : 1 + a * d ≤ B * (1 + d) := by
    dsimp only [B]
    nlinarith
  have hleftpos : 0 < 1 + a * d := by positivity
  have hrightpos : 0 < B * (1 + d) := by positivity
  have hsq : (1 + a * d) ^ 2 ≤ B ^ 2 * (1 + d) ^ 2 := by
    calc
      (1 + a * d) ^ 2 ≤ (B * (1 + d)) ^ 2 :=
        (sq_le_sq₀ hleftpos.le hrightpos.le).2 hsum
      _ = B ^ 2 * (1 + d) ^ 2 := by ring
  have hden : 0 < (1 + d) ^ 2 := sq_pos_of_pos (by linarith)
  have hscaledDen : 0 < (1 + a * d) ^ 2 := sq_pos_of_pos hleftpos
  have hnum : cₚ * (1 + a * d) ^ 2 ≤
      (σ * c) * (1 + d) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsq hcₚ.le
    have heq : cₚ * (B ^ 2 * (1 + d) ^ 2) =
        (σ * c) * (1 + d) ^ 2 := by
      dsimp only [cₚ]
      field_simp [hB.ne']
    exact hmul.trans_eq heq
  have hcompare : cₚ / (1 + d) ^ 2 ≤
      (σ * c) / (1 + a * d) ^ 2 :=
    (div_le_div_iff₀ hden hscaledDen).2 hnum
  have hscaled' : (σ * c) / (1 + a * d) ^ 2 ≤
      metricScalarAt (I := I) g x := by
    convert hscaled using 1
    ring
  exact hcompare.trans hscaled'

theorem gradientRicciSoliton_isGaussian_of_scalar_eq_zero_of_pos
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {sigma : Real} (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) {x : M}
    (hx : metricScalarAt (I := I) g x = 0) :
    isGaussianGradientRicciSoliton (E := E) g f sigma := by
  obtain ⟨C, hnormalized⟩ :=
    gradientRicciSoliton_exists_normalized (I := I) hcomplete hsol hsigma
  let gHat : SmoothRiemannianMetric I M :=
    scaleMetric (I := I) sigma hsigma g
  let fHat : C^∞⟮I, M; Real⟯ :=
    f + ContMDiffMap.const (I := I)
      (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) (C / sigma)
  have hzeroHat : metricScalarAt (I := I) gHat x = 0 := by
    dsimp only [gHat]
    rw [metricScalarAt_scaleMetric]
    simp [hx]
  have hGaussianHat :
      isGaussianGradientRicciSoliton (E := E) gHat fHat 1 :=
    normalizedGradientRicciSoliton_isGaussian_of_scalar_eq_zero
      (I := I) hnormalized hzeroHat
  have hGaussianShift :
      isGaussianGradientRicciSoliton (E := E) gHat f 1 := by
    exact (isGaussianGradientRicciSoliton_add_const (I := I)
      (g := gHat) (f := f) (σ := 1) (C / sigma)).mp hGaussianHat
  exact (isGaussianGradientRicciSoliton_scaleMetric (I := I) hsigma).mp
    hGaussianShift

theorem gradientRicciSoliton_isGaussian_iff_metricRm04At_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) (hsigma : 0 < sigma) :
    isGaussianGradientRicciSoliton (E := E) g f sigma ↔
      ∀ x : M, metricRm04At (I := I) g x = 0 := by
  constructor
  · exact isGaussianGradientRicciSoliton_metricRm04At_eq_zero
  · intro hRm
    let x : M := Classical.choice (inferInstance : Nonempty M)
    exact gradientRicciSoliton_isGaussian_of_scalar_eq_zero_of_pos
      hcomplete hsol hsigma
      (metricScalarAt_eq_zero_of_metricRm04At_eq_zero g x (hRm x))

theorem normalizedGradientRicciSoliton_isGaussian_iff_metricRm04At_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    isGaussianGradientRicciSoliton (E := E) g f 1 ↔
      ∀ x : M, metricRm04At (I := I) g x = 0 :=
  gradientRicciSoliton_isGaussian_iff_metricRm04At_eq_zero h.1 h.2.1 zero_lt_one

end DifferentialGeometry.Geometry
