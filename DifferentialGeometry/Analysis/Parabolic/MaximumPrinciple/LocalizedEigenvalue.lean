import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.EndomorphismScalarization
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.FirstContact
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralBounds
import DifferentialGeometry.Geometry.Connection.NormalSection

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem exists_unit_minimum_eigenvector {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (A : W →L[ℝ] W) (hA : A.toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : W // v ≠ 0}, A.rayleighQuotient v) < 0) :
    ∃ v : W, ‖v‖ = 1 ∧
      A v = (⨅ w : {w : W // w ≠ 0}, A.rayleighQuotient w) • v := by
  have : Nontrivial (W) := by
    rcases subsingleton_or_nontrivial (W) with h | h
    · let : IsEmpty {v : W // v ≠ 0} := ⟨fun v => v.property (Subsingleton.elim _ _)⟩
      simp only [iInf, Set.range_eq_empty, Real.sInf_empty] at hneg
      exact (lt_irrefl 0 hneg).elim
    · exact h
  have hdim := Module.finrank_pos (R := ℝ) (M := W)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdim)
  let v := hA.eigenvectorBasis hn (Fin.last n)
  refine ⟨v, (hA.eigenvectorBasis hn).orthonormal.norm_eq_one _, ?_⟩
  rw [hA.iInf_rayleighQuotient_eq_eigenvalues_last hn]
  exact hA.apply_eigenvectorBasis hn (Fin.last n)


theorem exists_cutoff_negative_minimum_eigenvalue_lower_support
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableWithinAt ℝ (fun q => A q x) (Icc 0 T) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : V x // v ≠ 0}, (A t x).rayleighQuotient v) < 0)
    (χ φ : ℝ → M → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun q => φ q x) (Icc 0 T) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (φ t) y) x) :
    ∃ v : Cₛ^∞⟮I; F, V⟯,
      let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
      let q : ℝ → M → ℝ := fun s y => inner ℝ (A s y (v y)) (v y)
      let ψ : ℝ → M → ℝ := fun s y => -(φ s y * q s y)
      cov v x = 0 ∧
      (∀ᶠ y in 𝓝 x, ‖v y‖ = 1) ∧
      A t x (v x) = ν • v x ∧
      ψ t x = χ t x * max (-ν) 0 ∧
      (∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
        ψ p.1 p.2 ≤ χ p.1 p.2 * max (-(⨅ w : {w : V p.2 // w ≠ 0},
          (A p.1 p.2).rayleighQuotient w)) 0) ∧
      DifferentiableWithinAt ℝ (fun s => ψ s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (ψ t) y) x ∧
      parabolicOperatorWithDrift (I := I) G T X ψ t x =
        -φ t x * inner ℝ
          ((derivWithin (fun s => A s x) (Icc 0 T) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
              (fun y => A t y) x (X t x)) (v x)) (v x) -
        ν * parabolicOperatorWithDrift (I := I) G T X φ t x +
        2 * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
          (gradientAt (I := I) G t (q t) x) := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨v₀, hv₀, heig⟩ := exists_unit_minimum_eigenvector (A t x) hA hneg
  have horth : Orthonormal ℝ (fun _ : Fin 1 => v₀) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp only [hij, ↓reduceIte, real_inner_self_eq_norm_sq, hv₀, one_pow]
  obtain ⟨U, hU, hxU, vs, hvs, hvsx, hvscov⟩ :=
    exists_orthonormal_normal_sections cov hcov x (fun _ : Fin 1 => v₀) horth
  let v := vs 0
  let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
  let q : ℝ → M → ℝ := fun s y => inner ℝ (A s y (v y)) (v y)
  let ψ : ℝ → M → ℝ := fun s y => -(φ s y * q s y)
  have hunit : ∀ᶠ y in 𝓝 x, ‖v y‖ = 1 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hvs y hy).norm_eq_one 0
  have hvx : v x = v₀ := hvsx 0
  have hvnorm : ‖v x‖ = 1 := by rw [hvx]; exact hv₀
  have heigen : A t x (v x) = ν • v x := by rw [hvx]; exact heig
  have hqx : q t x = ν := by
    simp only [q, heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm,
      one_pow, mul_one]
  have hqtime : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t :=
    (hAt.clm_apply (differentiableWithinAt_const (c := v x))).inner ℝ
      (differentiableWithinAt_const (c := v x))
  have hqsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t) :=
    (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle
      v.contMDiff
  have hqspace (y : M) : MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y :=
    hqsmooth.mdifferentiableAt (by simp)
  have hqgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (q t) y) x :=
    (gradientFun_smooth (I := I) (G.metric t) hqsmooth).mdifferentiableAt (by simp)
  have hprodspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => φ t y * q t y) y := by
    filter_upwards [hφspace] with y hy
    exact hy.mul (hqspace y)
  have hprodgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) x := by
    have heq : (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) =ᶠ[𝓝 x]
        (T% fun y : M => φ t y • gradientFun (I := I) (G.metric t) (q t) y +
          q t y • gradientFun (I := I) (G.metric t) (φ t) y) := by
      filter_upwards [hφspace] with y hy
      exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        (gradientFun_mul (I := I) (G.metric t) hy (hqspace y))
    exact (mdifferentiableAt_add_section
      (hφspace.self_of_nhds.smul_section hqgrad)
      ((hqspace x).smul_section hφgrad)).congr_of_eventuallyEq heq
  refine ⟨v, hvscov 0, hunit, heigen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change -(φ t x * q t x) = _
    rw [hqx, hφeq, max_eq_left (neg_nonneg.mpr hneg.le)]
    ring
  · have hunit' : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x), ‖v p.2‖ = 1 :=
      ((continuous_snd.continuousAt : ContinuousAt (fun p : ℝ × M => p.2) (t, x)).eventually
        hunit).filter_mono inf_le_left
    filter_upwards [hunit', hφχ] with p hp hφp
    have hvne : v p.2 ≠ 0 := norm_ne_zero_iff.mp (hp.trans_ne one_ne_zero)
    have hray := (A p.1 p.2).iInf_rayleighQuotient_le hvne
    have hquot : (A p.1 p.2).rayleighQuotient (v p.2) = q p.1 p.2 := by
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hp, one_pow, div_one,
        RCLike.re_to_real, q]
    rw [hquot] at hray
    have hmax : -(q p.1 p.2) ≤ max (-(⨅ w : {w : V p.2 // w ≠ 0},
        (A p.1 p.2).rayleighQuotient w)) 0 :=
      (neg_le_neg hray).trans (le_max_left _ _)
    change -(φ p.1 p.2 * q p.1 p.2) ≤ _
    calc
      _ = φ p.1 p.2 * (-q p.1 p.2) := by ring
      _ ≤ φ p.1 p.2 * max (-(⨅ w : {w : V p.2 // w ≠ 0},
          (A p.1 p.2).rayleighQuotient w)) 0 := mul_le_mul_of_nonneg_left hmax hφp.1
      _ ≤ _ := mul_le_mul_of_nonneg_right hφp.2 (le_max_right _ _)
  · exact (hφtime.mul hqtime).neg
  · filter_upwards [hφspace] with y hy
    exact (hy.mul (hqspace y)).neg
  · have heq : (T% fun y : M => gradientFun (I := I) (G.metric t) (ψ t) y) =ᶠ[𝓝 x]
        (T% fun y : M => (-1 : ℝ) •
          gradientFun (I := I) (G.metric t) (fun z => φ t z * q t z) y) := by
      filter_upwards [hprodspace] with y hy
      apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      have hfun : ψ t = (-1 : ℝ) • (fun z => φ t z * q t z) := by
        funext z
        simp only [ψ, Pi.smul_apply, smul_eq_mul, neg_one_mul]
      rw [hfun]
      exact gradientFun_const_smul (I := I) (G.metric t) (-1 : ℝ) hy
    exact (hprodgrad.smul_const_section (a := (-1 : ℝ))).congr_of_eventuallyEq heq
  · have hmul := parabolic_mul_at (I := I) G T X φ q t x hφtime
      hqtime hφspace (Eventually.of_forall hqspace) hφgrad hqgrad
    have hnegop := parabolic_smul_at (I := I) G T X (-1)
      (fun s y => φ s y * q s y) t x (hφtime.mul hqtime)
      hprodspace hprodgrad
    have hunitInner : ∀ᶠ y in 𝓝 x, inner ℝ (v y) (v y) = 1 := by
      filter_upwards [hunit] with y hy
      simp only [real_inner_self_eq_norm_sq, hy, one_pow]
    have hscalar := parabolicOperatorWithDrift_inner_endomorphism_apply_of_normal_eigenvector
      (I := I) G cov hcov hT ht A v x hx X hGconn hAt hA heigen (hvscov 0) hunitInner
    change parabolicOperatorWithDrift (I := I) G T X q t x = _ at hscalar
    have hψ : (fun s y => (-1 : ℝ) * (φ s y * q s y)) = ψ := by
      funext s y
      simp only [ψ, neg_one_mul]
    change parabolicOperatorWithDrift (I := I) G T X
      (fun s y => (-1 : ℝ) * (φ s y * q s y)) t x =
        -1 * parabolicOperatorWithDrift (I := I) G T X (fun s y => φ s y * q s y) t x at hnegop
    rw [hψ, hmul, hscalar, hqx] at hnegop
    change parabolicOperatorWithDrift (I := I) G T X ψ t x = _
    rw [hnegop]
    ring

theorem exists_cutoff_negative_minimum_eigenvalue_parabolic_inequality_at_spacetime_max
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {t : ℝ} (ht : 0 < t)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableWithinAt ℝ (fun q => A q x) (Icc 0 t) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : V x // v ≠ 0}, (A t x).rayleighQuotient v) < 0)
    (χ φ : ℝ → M → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun q => φ q x) (Icc 0 t) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hmax : IsLocalMaxOn (fun p : ℝ × M => χ p.1 p.2 *
      max (-(⨅ w : {w : V p.2 // w ≠ 0}, (A p.1 p.2).rayleighQuotient w)) 0)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x)) :
    ∃ v : Cₛ^∞⟮I; F, V⟯,
      let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
      cov v x = 0 ∧
      (∀ᶠ y in 𝓝 x, ‖v y‖ = 1) ∧
      A t x (v x) = ν • v x ∧
      φ t x ^ 2 * inner ℝ
          ((derivWithin (fun s => A s x) (Icc 0 t) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
              (fun y => A t y) x (X t x)) (v x)) (v x) +
        ν * φ t x * parabolicOperatorWithDrift (I := I) G t X φ t x +
        2 * ν * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
          (gradientAt (I := I) G t (φ t) x) ≤ 0 := by
  obtain ⟨v, hnormal, hunit, heigen, hcontact, hsupport, htime, hspace, hgrad, hevol⟩ :=
    exists_cutoff_negative_minimum_eigenvalue_lower_support
      (I := I) G cov hcov ht ⟨ht.le, le_rfl⟩ A x hx X hGconn hAt hA hneg
      χ φ hφχ hφeq hφtime hφspace hφgrad
  let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
  let q : ℝ → M → ℝ := fun s y => inner ℝ (A s y (v y)) (v y)
  let ψ : ℝ → M → ℝ := fun s y => -(φ s y * q s y)
  have hψmax : IsLocalMaxOn (fun p : ℝ × M => ψ p.1 p.2)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x) := by
    change ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), ψ p.1 p.2 ≤ ψ t x
    filter_upwards [hmax, hsupport] with p hp hsupp
    exact hsupp.trans (hp.trans_eq hcontact.symm)
  have hL := derivWithin_sub_heatOperatorWithDrift_nonneg_at_spacetime_max
    (I := I) G X ht hψmax hx hspace hgrad
  change 0 ≤ parabolicOperatorWithDrift (I := I) G t X ψ t x at hL
  change parabolicOperatorWithDrift (I := I) G t X ψ t x = _ at hevol
  rw [hevol] at hL
  have hqx : q t x = ν := by
    simp only [q, heigen, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hunit.self_of_nhds, one_pow, mul_one]
    rfl
  have hqspace : MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) x :=
    ((ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle
      v.contMDiff).mdifferentiableAt (by simp)
  have hprodmin : IsLocalMin (fun y => φ t y * q t y) x := by
    have hspacemax : IsLocalMax (ψ t) x := by
      rw [← isLocalMaxOn_univ_iff]
      exact hψmax.comp_continuousOn
        (s := Set.univ) (g := fun y : M ↦ (t, y))
        (by intro y hy; exact ⟨⟨ht.le, le_rfl⟩, hy⟩)
        (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
    simpa only [ψ, neg_neg] using hspacemax.neg
  have hzero := gradientFun_eq_zero_at_spatial_min_of_isInteriorPoint
    (I := I) (G.metric t) hprodmin hx (hφspace.self_of_nhds.mul hqspace)
  rw [gradientFun_mul (I := I) (G.metric t) hφspace.self_of_nhds hqspace, hqx] at hzero
  have hcross := congrArg (fun w => (G.metric t).inner x
    (gradientAt (I := I) G t (φ t) x) w) hzero
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hcross
  have hφnonneg := (hφχ.self_of_nhdsWithin ⟨⟨ht.le, le_rfl⟩, mem_univ x⟩).1
  have hscaled := mul_nonneg hφnonneg hL
  refine ⟨v, hnormal, hunit, heigen, ?_⟩
  change φ t x * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
    (gradientAt (I := I) G t (q t) x) +
    ν * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
      (gradientAt (I := I) G t (φ t) x) = 0 at hcross
  nlinarith [hscaled]

private theorem mul_log_tangent_lower_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * Real.log x + (Real.log x + 1) * (y - x) ≤ y * Real.log y := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  have hmul := mul_le_mul_of_nonneg_left h hy.le
  rw [Real.log_div hy.ne' hx.ne', inv_div] at hmul
  have hcancel : y * (1 - x / y) = y - x := by field_simp
  rw [hcancel] at hmul
  nlinarith

private theorem cutoff_logarithmic_defect_le_of_support
    {r q Q φ χ c : ℝ} (hφ : 0 < φ) (hφχ : φ ≤ χ) (hq : 0 < q) (hqQ : q ≤ Q)
    (hslope : 0 ≤ Real.log (φ * q) + c + 1)
    (hr : r ≤ (Real.log (φ * q) + c + 1) * q) :
    χ * r - (χ * Q) * (Real.log (χ * Q) + c) ≤
      φ * r - (φ * q) * (Real.log (φ * q) + c) := by
  have hχ : 0 < χ := hφ.trans_le hφχ
  have hQ : 0 < Q := hq.trans_le hqQ
  have htangent := mul_log_tangent_lower_bound (mul_pos hφ hq) (mul_pos hχ hQ)
  have hfirst := mul_nonneg (sub_nonneg.mpr hφχ) (sub_nonneg.mpr hr)
  have hsecond := mul_nonneg (mul_nonneg hχ.le hslope) (sub_nonneg.mpr hqQ)
  nlinarith

private theorem eventually_cutoff_logarithmic_defect_le_of_support
    {α : Type*} {l : Filter α} {r q Q φ χ c : α → ℝ} {r₀ q₀ φ₀ c₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (hq : Tendsto q l (𝓝 q₀))
    (hφ : Tendsto φ l (𝓝 φ₀)) (hc : Tendsto c l (𝓝 c₀))
    (hφ₀ : 0 < φ₀) (hq₀ : 0 < q₀)
    (hslope : 0 < Real.log (φ₀ * q₀) + c₀ + 1)
    (hboundary : r₀ = q₀ * (Real.log (φ₀ * q₀) + c₀))
    (hφχ : ∀ᶠ z in l, φ z ≤ χ z) (hqQ : ∀ᶠ z in l, q z ≤ Q z) :
    ∀ᶠ z in l,
      χ z * r z - (χ z * Q z) * (Real.log (χ z * Q z) + c z) ≤
        φ z * r z - (φ z * q z) * (Real.log (φ z * q z) + c z) := by
  have hprod : Tendsto (fun z => φ z * q z) l (𝓝 (φ₀ * q₀)) := hφ.mul hq
  have hlog : Tendsto (fun z => Real.log (φ z * q z)) l (𝓝 (Real.log (φ₀ * q₀))) :=
    (Real.continuousAt_log (mul_pos hφ₀ hq₀).ne').tendsto.comp hprod
  have hsl := (hlog.add hc).add_const 1
  have hgap : Tendsto (fun z => (Real.log (φ z * q z) + c z + 1) * q z - r z) l
      (𝓝 ((Real.log (φ₀ * q₀) + c₀ + 1) * q₀ - r₀)) := (hsl.mul hq).sub hr
  have hgap₀ : 0 < (Real.log (φ₀ * q₀) + c₀ + 1) * q₀ - r₀ := by
    rw [hboundary]
    nlinarith
  filter_upwards [hφ.eventually (Ioi_mem_nhds hφ₀), hq.eventually (Ioi_mem_nhds hq₀),
    hsl.eventually (Ioi_mem_nhds hslope), hgap.eventually (Ioi_mem_nhds hgap₀), hφχ, hqQ]
      with z hφz hqz hsz hrz hφχz hqQz
  exact cutoff_logarithmic_defect_le_of_support hφz hφχz hqz hqQz hsz.le
    (by linarith)


theorem exists_cutoff_logarithmic_minimum_eigenvalue_upper_support
    (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible)
    {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hAt : ContinuousWithinAt (fun s => A s x) J t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) < 0)
    (r χ φ : ℝ → M → ℝ) (c : ℝ → ℝ)
    (hrtime : ContinuousWithinAt (fun s => r s x) J t)
    (hrspace : ContinuousAt (r t) x)
    (hφtime : ContinuousWithinAt (fun s => φ s x) J t)
    (hφspace : ContinuousAt (φ t) x)
    (hctime : ContinuousWithinAt c J t)
    (hφχ : ∀ᶠ p in 𝓝[J ×ˢ (Set.univ : Set M)] (t, x),
      φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x) (hχpos : 0 < χ t x)
    (hslope : 0 < Real.log (χ t x * (-(⨅ w : {w : V x // w ≠ 0},
      (A t x).rayleighQuotient w))) + c t + 1)
    (hboundary : r t x = (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) *
      (Real.log (χ t x * (-(⨅ w : {w : V x // w ≠ 0},
        (A t x).rayleighQuotient w))) + c t)) :
    ∃ v : Cₛ^∞⟮I; F, V⟯,
      let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
      let q : ℝ → M → ℝ := fun s y => -inner ℝ (A s y (v y)) (v y)
      let Q : ℝ → M → ℝ := fun s y =>
        max (-(⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w)) 0
      let ψ : ℝ → M → ℝ := fun s y => φ s y * r s y -
        (φ s y * q s y) * (Real.log (φ s y * q s y) + c s)
      let θ : ℝ → M → ℝ := fun s y => χ s y * r s y -
        (χ s y * Q s y) * (Real.log (χ s y * Q s y) + c s)
      cov v x = 0 ∧ (∀ᶠ y in 𝓝 x, ‖v y‖ = 1) ∧ A t x (v x) = ν • v x ∧
      ψ t x = θ t x ∧
      (∀ᶠ s in 𝓝[J] t, θ s x ≤ ψ s x) ∧
      (∀ᶠ y in 𝓝 x, θ t y ≤ ψ t y) := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨v₀, hv₀, heig⟩ := exists_unit_minimum_eigenvector (A t x) hA hneg
  have horth : Orthonormal ℝ (fun _ : Fin 1 => v₀) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp only [hij, ↓reduceIte, real_inner_self_eq_norm_sq, hv₀, one_pow]
  obtain ⟨U, hU, hxU, vs, hvs, hvsx, hvscov⟩ :=
    exists_orthonormal_normal_sections cov hcov x (fun _ : Fin 1 => v₀) horth
  let v := vs 0
  let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
  let q : ℝ → M → ℝ := fun s y => -inner ℝ (A s y (v y)) (v y)
  let Q : ℝ → M → ℝ := fun s y =>
    max (-(⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w)) 0
  have hunit : ∀ᶠ y in 𝓝 x, ‖v y‖ = 1 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hvs y hy).norm_eq_one 0
  have hvx : v x = v₀ := hvsx 0
  have hvnorm : ‖v x‖ = 1 := by rw [hvx]; exact hv₀
  have heigen : A t x (v x) = ν • v x := by rw [hvx]; exact heig
  have hqx : q t x = -ν := by
    simp only [q, heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm,
      one_pow, mul_one]
  have hQx : Q t x = -ν := max_eq_left (neg_nonneg.mpr hneg.le)
  have hqtime : ContinuousWithinAt (fun s => q s x) J t :=
    ((hAt.clm_apply continuousWithinAt_const).inner continuousWithinAt_const).neg
  have hqspace : ContinuousAt (q t) x :=
    (((ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle
      v.contMDiff).neg).continuous.continuousAt
  have hqbound : ∀ᶠ y in 𝓝 x, ∀ s, q s y ≤ Q s y := by
    filter_upwards [hunit] with y hy s
    have hvne : v y ≠ 0 := norm_ne_zero_iff.mp (hy.trans_ne one_ne_zero)
    have hray := (A s y).iInf_rayleighQuotient_le hvne
    have hquot : (A s y).rayleighQuotient (v y) = -q s y := by
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hy, one_pow, div_one,
        RCLike.re_to_real, q, neg_neg]
    rw [hquot] at hray
    simpa only [q, Q, neg_neg] using (neg_le_neg hray).trans (le_max_left _ _)
  have htm : Tendsto (fun s : ℝ => (s, x)) (𝓝[J] t)
      (𝓝[J ×ˢ (Set.univ : Set M)] (t, x)) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact Tendsto.prodMk tendsto_id tendsto_const_nhds
  have hxm : Tendsto (fun y : M => (t, y)) (𝓝 x)
      (𝓝[J ×ˢ (Set.univ : Set M)] (t, x)) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact Tendsto.prodMk (tendsto_const_nhdsWithin ht) tendsto_id
  have hφpos : 0 < φ t x := hφeq.symm ▸ hχpos
  have hqpos : 0 < q t x := by rw [hqx]; exact neg_pos.mpr hneg
  have hsl : 0 < Real.log (φ t x * q t x) + c t + 1 := by
    rw [hφeq, hqx]
    exact hslope
  have hbd : r t x = q t x * (Real.log (φ t x * q t x) + c t) := by
    rw [hφeq, hqx]
    exact hboundary
  refine ⟨v, hvscov 0, hunit, heigen, ?_, ?_, ?_⟩
  · dsimp only
    rw [show -inner ℝ (A t x (v x)) (v x) = -ν from hqx,
      show max (-ν) 0 = -ν from hQx, hφeq]
  · exact eventually_cutoff_logarithmic_defect_le_of_support
      hrtime hqtime hφtime hctime hφpos hqpos hsl hbd
      (htm.eventually hφχ)
      (Eventually.of_forall (hqbound.self_of_nhds))
  · exact eventually_cutoff_logarithmic_defect_le_of_support
      hrspace hqspace hφspace continuousAt_const hφpos hqpos hsl hbd
      (hxm.eventually hφχ) (hqbound.mono fun _ h => h t)

end DifferentialGeometry.Analysis.Parabolic
