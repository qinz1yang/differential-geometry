import DifferentialGeometry.Geometry.Exponential.FiniteMetric.GaussLemma
import DifferentialGeometry.Analysis.Calculus.Seminorm.Radial
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Radial length bound in a normal chart of a finite-regularity metric

For a chart `e` that agrees with `exp_x` on a `g_x`-ball and has a `C^r` inverse (`2 ≤ r`), the
length of a `C¹` curve inside `e.target` bounds the increase of `|e.symm|_{g_x}` along it
(`ofReal_sub_le_pathELength_of_expChart`): the finite Gauss lemma makes `|e.symm|_{g_x}`
`1`-Lipschitz along curves. The analytic kernel is the semidefinite form of
`ContDiffOn.norm_sub_le_integral_of_inner_deriv_le` (`sqrt_quad_sub_le_integral`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cauchy–Schwarz for a symmetric positive semidefinite bilinear form. -/
theorem le_sqrt_mul_sqrt_of_psd (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u w, B u w = B w u)
    (hnn : ∀ u, 0 ≤ B u u) (u w : E) : B u w ≤ Real.sqrt (B u u) * Real.sqrt (B w w) := by
  rw [← Real.sqrt_mul (hnn u)]
  apply Real.le_sqrt_of_sq_le
  by_cases hw : B w w = 0
  · have key : ∀ t : ℝ, 0 ≤ B u u - 2 * t * B u w := by
      intro t
      have h := hnn (u - t • w)
      have expand : B (u - t • w) (u - t • w) = B u u - 2 * t * B u w + t ^ 2 * B w w := by
        simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
        rw [hsym w u]
        ring
      rw [expand, hw] at h
      linarith
    have hbw : B u w = 0 := by
      by_contra hne
      have h := key ((B u u + 1) / (2 * B u w))
      have h' : 2 * ((B u u + 1) / (2 * B u w)) * B u w = B u u + 1 := by field_simp
      linarith
    rw [hw, hbw]
    simp
  · have hpos : 0 < B w w := lt_of_le_of_ne (hnn w) (Ne.symm hw)
    have h := hnn ((B w w) • u - (B u w) • w)
    have expand : B ((B w w) • u - (B u w) • w) ((B w w) • u - (B u w) • w) =
        B w w * (B w w * B u u - (B u w) ^ 2) := by
      simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
      rw [hsym w u]
      ring
    rw [expand] at h
    nlinarith [(mul_nonneg_iff_of_pos_left hpos).mp h]

/-- **Semidefinite radial kernel.** -/
theorem sqrt_quad_sub_le_integral (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u w, B u w = B w u)
    (hnn : ∀ u, 0 ≤ B u u) {η : ℝ → E} {φ : ℝ → ℝ} {a b : ℝ}
    (hη : ContDiffOn ℝ 1 η (Icc a b)) (hab : a ≤ b) (hφ : IntervalIntegrable φ volume a b)
    (hφnn : ∀ t ∈ Ioo a b, 0 ≤ φ t)
    (hrad : ∀ t ∈ Ioo a b, B (η t) (deriv η t) ≤ Real.sqrt (B (η t) (η t)) * φ t) :
    Real.sqrt (B (η b) (η b)) - Real.sqrt (B (η a) (η a)) ≤ ∫ t in a..b, φ t := by
  have hηac : AbsolutelyContinuousOnInterval η a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hη
  have hρac : AbsolutelyContinuousOnInterval (fun t => Real.sqrt (B (η t) (η t))) a b :=
    (DifferentialGeometry.Analysis.Calculus.psd_sqrt_lipschitz B hsym hnn).comp_absolutelyContinuousOnInterval
      hηac
  have hderiv : ∀ t ∈ Ioo a b, deriv (fun s => Real.sqrt (B (η s) (η s))) t ≤ φ t := by
    intro t ht
    by_cases h0 : B (η t) (η t) = 0
    · have hmin : IsLocalMin (fun s => Real.sqrt (B (η s) (η s))) t := by
        filter_upwards with s
        rw [h0, Real.sqrt_zero]
        exact Real.sqrt_nonneg _
      rw [hmin.deriv_eq_zero]
      exact hφnn t ht
    · have hηd : DifferentiableAt ℝ η t :=
        ((hη.differentiableOn one_ne_zero) t (Ioo_subset_Icc_self ht)).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)
      have hq : HasDerivAt (fun s => B (η s) (η s)) (2 * B (η t) (deriv η t)) t := by
        have h := (B.hasFDerivAt.comp_hasDerivAt t hηd.hasDerivAt).clm_apply hηd.hasDerivAt
        convert h using 1
        · rfl
        · change 2 * B (η t) (deriv η t) = B (deriv η t) (η t) + B (η t) (deriv η t)
          rw [hsym (deriv η t) (η t)]
          ring
      have hpos : 0 < B (η t) (η t) := lt_of_le_of_ne (hnn _) (Ne.symm h0)
      have hs := hq.sqrt hpos.ne'
      rw [hs.deriv]
      have hsq : 0 < Real.sqrt (B (η t) (η t)) := Real.sqrt_pos.mpr hpos
      rw [div_le_iff₀ (by positivity)]
      have := hrad t ht
      nlinarith
  rw [← hρac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hρac.intervalIntegrable_deriv hφ
  change ∀ᵐ t ∂volume.restrict (Icc a b), _ ≤ φ t
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with t ht htab
  exact hderiv t (ht.mpr htab)

end Kernel

section Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem inner_self_nonneg' {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (y : M)
    (u : TangentSpace I y) : 0 ≤ g.inner y u u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact (g.pos y u hu).le

variable [RiemannianBundle (fun x : M => TangentSpace I x)] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **Radial length bound.** In a chart agreeing with `exp_x`, with `C^r` inverse, the length of a
`C¹` curve inside the chart target bounds the increase of the `g_x`-length of `e.symm`. -/
theorem ofReal_sub_le_pathELength_of_expChart (hr : 2 ≤ r)
    (hnorm : ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} (e : OpenPartialHomeomorph E M)
    (hexp : ∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
      e v = g.expMap (⟨x, v⟩ : TangentBundle I M))
    (hsymm : ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hγt : MapsTo γ (Icc a b) e.target) :
    ENNReal.ofReal (Real.sqrt (g.inner x (e.symm (γ b)) (e.symm (γ b))) -
      Real.sqrt (g.inner x (e.symm (γ a)) (e.symm (γ a)))) ≤ Manifold.pathELength I γ a b := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp
  set η : ℝ → E := fun t => e.symm (γ t) with hηdef
  have hηm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc a b) :=
    (hsymm.of_le (by exact_mod_cast hr1)).comp hγ hγt
  have hη : ContDiffOn ℝ 1 η (Icc a b) := contMDiffOn_iff_contDiffOn.mp hηm
  let gc := g.toContinuousRiemannianMetric
  set φ : ℝ → ℝ := fun t => Real.sqrt (g.inner (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t 1)
    (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t 1)) with hφdef
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) := fun t ht => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab_lt) t ht
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : MapsTo
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Icc a b)) := fun _ ht => ht
  have hVel : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t 1)) (Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin le_rfl hUnique).comp
      hLift.continuousOn hMaps).congr (fun _ _ => rfl)
  have hφc : ContinuousOn φ (Icc a b) := by
    intro t ht
    have h : ContinuousWithinAt (fun s => TotalSpace.mk' ℝ
        (E := Bundle.Trivial M ℝ) (γ s) (gc.inner (γ s)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) s 1)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) s 1))) (Icc a b) t :=
      (gc.continuous.continuousAt.comp_continuousWithinAt
        (hγ.continuousOn t ht)).clm_bundle_apply₂ (F₁ := E) (F₂ := E) (hVel t ht) (hVel t ht)
    simp only [FiberBundle.continuousWithinAt_totalSpace] at h
    exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt h.2
  have hφint : IntervalIntegrable φ volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hφc
  have hφ_eq : ∀ t ∈ Ioo a b, φ t = Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) := by
    intro t ht
    simp only [hφdef]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  set f : E → M := fun u => g.expMap (⟨x, u⟩ : TangentBundle I M) with hfdef
  have hbound : Real.sqrt (g.inner x (η b) (η b)) - Real.sqrt (g.inner x (η a) (η a)) ≤
      ∫ t in a..b, φ t := by
    apply sqrt_quad_sub_le_integral (E := E) (g.inner x : E →L[ℝ] E →L[ℝ] ℝ) (g.symm x)
      (g.inner_self_nonneg' x) hη hab hφint
      (fun _ _ => Real.sqrt_nonneg _)
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    set y := γ t with hy
    have hyt : y ∈ e.target := hγt htI
    have hηs : η t ∈ e.source := e.map_target hyt
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      ((hγ t htI).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    have hsd : MDifferentiableAt I 𝓘(ℝ, E) e.symm y :=
      ((hsymm y hyt).contMDiffAt (e.open_target.mem_nhds hyt)).mdifferentiableAt
        (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
    have hfdom : η t ∈ {u : E | (⟨x, u⟩ : TangentBundle I M) ∈ g.expDomain} := (hexp _ hηs).1
    have hfd : MDifferentiableAt 𝓘(ℝ, E) I f (η t) :=
      ((g.contMDiffOn_expMap_fiber hr1 x).contMDiffAt
        ((g.isOpen_expDomain_fiber hr1 x).mem_nhds hfdom)).mdifferentiableAt
        (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
    -- the derivative of `η`
    have hderiv : deriv η t = mfderiv I 𝓘(ℝ, E) e.symm y (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      have hc := mfderiv_comp t hsd hγd
      have h := congrArg (fun D : ℝ →L[ℝ] E => D 1) hc
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η t (1 : ℝ) =
        (mfderiv I 𝓘(ℝ, E) e.symm y) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) at h
      simpa only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! h
    -- `f ∘ e.symm` is the identity near `y`
    have hfe : f ∘ e.symm =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hyt] with y' hy'
      change g.expMap (⟨x, e.symm y'⟩ : TangentBundle I M) = y'
      rw [← (hexp _ (e.map_target hy')).2, e.right_inv hy']
    have hfinv : ∀ w : E, mfderiv 𝓘(ℝ, E) I f (η t) (mfderiv I 𝓘(ℝ, E) e.symm y w) = w := by
      intro w
      have hc : mfderiv I I (f ∘ e.symm) y =
          (mfderiv 𝓘(ℝ, E) I f (e.symm y)).comp (mfderiv I 𝓘(ℝ, E) e.symm y) :=
        mfderiv_comp y hfd hsd
      rw [hfe.mfderiv_eq, mfderiv_id] at hc
      exact (congrArg (fun D => D w) hc).symm
    have hfy : f (η t) = y := by
      change g.expMap (⟨x, e.symm y⟩ : TangentBundle I M) = y
      rw [← (hexp _ hηs).2, e.right_inv hyt]
    set A := mfderiv I 𝓘(ℝ, E) e.symm y (mfderiv 𝓘(ℝ, ℝ) I γ t 1) with hA
    have hgauss1 := g.inner_mfderiv_expMap_radial hr x hfdom A
    have hgauss2 := g.inner_mfderiv_expMap_radial hr x hfdom (η t)
    rw [← hfdef] at hgauss1 hgauss2
    have hA' : mfderiv 𝓘(ℝ, E) I f (η t) A = mfderiv 𝓘(ℝ, ℝ) I γ t 1 := hfinv _
    rw [hA'] at hgauss1
    have key : ∀ z : M, z = y → ∀ u w : E, g.inner z u w ≤
        Real.sqrt (g.inner z u u) * Real.sqrt (g.inner y w w) := by
      intro z hz u w
      rw [hz]
      exact le_sqrt_mul_sqrt_of_psd (E := E) (g.inner y : E →L[ℝ] E →L[ℝ] ℝ) (g.symm y)
        (g.inner_self_nonneg' y) u w
    have e1 : g.inner x (η t) (deriv η t) = g.inner x (η t) A :=
      congrArg (fun w : E => g.inner x (η t) w) hderiv
    have e2 := hφ_eq t ht
    calc g.inner x (η t) (deriv η t) = g.inner x (η t) A := e1
      _ = g.inner (g.expMap (⟨x, η t⟩ : TangentBundle I M)) (mfderiv 𝓘(ℝ, E) I f (η t) (η t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := hgauss1.symm
      _ ≤ Real.sqrt (g.inner (g.expMap (⟨x, η t⟩ : TangentBundle I M))
            (mfderiv 𝓘(ℝ, E) I f (η t) (η t)) (mfderiv 𝓘(ℝ, E) I f (η t) (η t))) *
          Real.sqrt (g.inner y (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) :=
        key _ hfy _ _
      _ = Real.sqrt (g.inner x (η t) (η t)) * φ t := by rw [hgauss2, e2]
  apply (ENNReal.ofReal_le_ofReal hbound).trans
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hφint).mono_set
        Ioo_subset_Icc_self)
      (by filter_upwards with t; exact Real.sqrt_nonneg _)]
  apply setLIntegral_mono_ae' measurableSet_Ioo
  filter_upwards with t ht
  rw [hφ_eq t ht]
  exact (hnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).symm.le

end Manifold

end Bundle.ContMDiffRiemannianMetric
