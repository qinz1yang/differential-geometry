import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Analysis.ODE.Gronwall.Integral

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]
variable [hBoundary : I.Boundaryless] {D : RealTimeInterval} {a b s u : ℝ}
include hBoundary

theorem rfs_csf_integral_bounds (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContDiffOn ℝ ∞ (c.length B.family.metric) (Icc s u) ∧
    ContinuousOn (c.totalCurvature B.family.metric) (Icc s u) ∧
    ContinuousOn (c.energy B.family.metric) (Icc s u) ∧
    (∀ t ∈ Icc s u, derivWithin (c.length B.family.metric) (Icc s u) t =
      -c.energy B.family.metric t - c.integral B.family.metric (c.ricciTangent B.family) t) ∧
    (∀ r ∈ Icc s u, ∀ t ∈ Icc r u,
      c.length B.family.metric t ≤ Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      (∫ v in r..t, c.energy B.family.metric v) ≤
        Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      c.totalCurvature B.family.metric t ≤ c.totalCurvature B.family.metric r +
        ∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
          B.C * c.length B.family.metric v) ∧
      c.totalCurvature B.family.metric t + c.length B.family.metric t ≤
        Real.exp ((B.C + B.B₀) * (t - r)) *
          (c.totalCurvature B.family.metric r + c.length B.family.metric r)) := by
  sorry

theorem totalCurvature_upper_right_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (t : ℝ) (ht : t ∈ Ico s u) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ u →
      (c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t) / h ≤
        (B.C + B.B₀) * c.totalCurvature B.family.metric t +
          B.C * c.length B.family.metric t + ε := by
  obtain ⟨hL, hTheta, _, _, hbounds⟩ := rfs_csf_integral_bounds B hsu hwindow c hc
  let F : ℝ → ℝ := fun v =>
    (B.C + B.B₀) * c.totalCurvature B.family.metric v + B.C * c.length B.family.metric v
  have hF : ContinuousOn F (Icc s u) :=
    (hTheta.const_mul _).add (hL.continuousOn.const_mul _)
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp (hF t ⟨ht.1, ht.2.le⟩) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh htu
  have hth : t ≤ t + h := le_add_of_nonneg_right hh.1.le
  have hsub : Icc t (t + h) ⊆ Icc s u := Icc_subset_Icc ht.1 htu
  have hmono : (∫ v in t..t + h, F v) ≤ h * (F t + ε) := by
    have hle : ∀ v ∈ Icc t (t + h), F v ≤ F t + ε := by
      intro v hv
      have hdist : dist v t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
        linarith [hv.2, hh.2]
      have habs := hclose (hsub hv) hdist
      rw [Real.dist_eq] at habs
      linarith [(abs_lt.mp habs).2]
    have hint := intervalIntegral.integral_mono_on hth
      ((hF.mono hsub).intervalIntegrable_of_Icc hth)
      (continuous_const.intervalIntegrable (μ := volume) t (t + h)) hle
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using hint
  have hint := (hbounds t ⟨ht.1, ht.2.le⟩ (t + h) ⟨hth, htu⟩).2.2.1
  apply (div_le_iff₀ hh.1).mpr
  change c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t ≤
    (F t + ε) * h
  change c.totalCurvature B.family.metric (t + h) ≤
    c.totalCurvature B.family.metric t + ∫ v in t..t + h, F v at hint
  nlinarith

section MaxPrincipleHelpers

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_velocity_contMDiff (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ)) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I γ ∘ fun x : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ))
  exact (hγ.contMDiff_tangentMap (le_refl _)).comp hunit

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_inner_contDiff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ x, TangentSpace I (γ x))
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (V x)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (W x))) :
    ContDiff ℝ ∞ (fun x => g.inner (γ x) (V x) (W x)) := by
  have htotal : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (γ x) (g.inner (γ x) (V x) (W x))) := by
    apply ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.comp hg
    · exact hV
    · exact hW
  apply contMDiff_iff_contDiff.mp
  intro x
  have hx := htotal x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_speed_contDiff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (hi : c.ImmersedOn (I := I) (Icc s u)) (hc : c.SmoothOn (I := I) (Icc s u))
    (t : ℝ) (ht : t ∈ Icc s u) :
    ContDiff ℝ ∞ (fun x => c.speed g x t) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c (Icc s u) hc t ht)
  have hX : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.X (I := I) x t)) := by
    have h := mp_velocity_contMDiff (I := I) (fun x => c.lift x t) hγ
    simpa only [CurveMap.X] using h
  have hinner := mp_inner_contDiff (I := I) (g t) (fun x => c.lift x t)
    (fun x => c.X x t) (fun x => c.X x t) hγ hX hX
  exact hinner.sqrt (fun x => ne_of_gt ((g t).pos (c.lift x t) (c.X x t) (hi x t ht)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem mp_deriv_deriv_nonpos_of_isLocalMax {G : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax G x₀) (hG : ContDiffAt ℝ 2 G x₀) :
    deriv (deriv G) x₀ ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hd0 : deriv G x₀ = 0 := hmax.deriv_eq_zero
  have h2 : HasDerivAt (deriv G) (deriv (deriv G) x₀) x₀ :=
    ((hG.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hEv : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → deriv (deriv G) x₀ / 2 < slope (deriv G) x₀ y := by
    exact eventually_nhdsWithin_iff.mp
      (h2.tendsto_slope.eventually (eventually_gt_nhds (by linarith)))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hEv
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hmax
  obtain ⟨v, hvopen, hvmem, hvCD⟩ :=
    (hG.contDiffWithinAt (s := univ)).contDiffOn' (m := 2) le_rfl (by simp)
  have hvmem' : v ∈ 𝓝 x₀ := hvopen.mem_nhds hvmem
  have hvCD' : ContDiffOn ℝ 2 G v := by simpa using hvCD
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hvmem'
  have hm : 0 < min δ (min ε ρ) := lt_min hδpos (lt_min hεpos hρpos)
  have hhδ : min δ (min ε ρ) / 2 < δ := by
    have := min_le_left δ (min ε ρ); linarith
  have hhε : min δ (min ε ρ) / 2 < ε := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_left ε ρ; linarith
  have hhρ : min δ (min ε ρ) / 2 < ρ := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_right ε ρ; linarith
  have hderivpos : ∀ y ∈ Ioo x₀ (x₀ + min δ (min ε ρ) / 2), 0 < deriv G y := by
    intro y hy
    have hdist : dist y x₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]
      linarith [hy.2, hhδ]
    have hne : y ≠ x₀ := by linarith [hy.1]
    have hb := hδ hdist hne
    have hsl : slope (deriv G) x₀ y = deriv G y / (y - x₀) := by
      rw [slope_def_field, hd0, sub_zero]
    rw [hsl] at hb
    have hyx : 0 < y - x₀ := by linarith [hy.1]
    have : 0 < deriv G y / (y - x₀) := by linarith
    exact (div_pos_iff_of_pos_right hyx).mp this
  have hcont : ContinuousOn G (Icc x₀ (x₀ + min δ (min ε ρ) / 2)) := by
    refine hvCD'.continuousOn.mono ?_
    intro y hy
    refine hρ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1, hm], by linarith [hy.2, hhρ]⟩
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    (fun y hy => by
      rw [interior_Icc] at hy
      exact hderivpos y hy)
  have hlt : G x₀ < G (x₀ + min δ (min ε ρ) / 2) :=
    hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
      (by linarith)
  have hle : G (x₀ + min δ (min ε ρ) / 2) ≤ G x₀ :=
    hε (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hm], by linarith [hhε]⟩)
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem mp_deriv_inv_mul_nonpos {σ φ : ℝ → ℝ} {x₀ L : ℝ}
    (hσ : ContinuousAt σ x₀) (hσpos : 0 < σ x₀)
    (hφ0 : φ x₀ = 0) (hφ : HasDerivAt φ L x₀) (hL : L ≤ 0) :
    deriv (fun y => (σ y)⁻¹ * φ y) x₀ ≤ 0 := by
  have hderiv : HasDerivAt (fun y => (σ y)⁻¹ * φ y) ((σ x₀)⁻¹ * L) x₀ := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 : Tendsto (fun y => (σ y)⁻¹) (𝓝[≠] x₀) (𝓝 ((σ x₀)⁻¹)) :=
      (hσ.inv₀ (ne_of_gt hσpos)).tendsto.mono_left inf_le_left
    have h2 : Tendsto (fun y => (φ y - φ x₀) / (y - x₀)) (𝓝[≠] x₀) (𝓝 L) := by
      simpa only [slope_fun_def_field] using hφ.tendsto_slope
    refine Tendsto.congr' ?_ (h1.mul h2)
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field]
    rw [hφ0]
    ring
  rw [hderiv.deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hL

end MaxPrincipleHelpers

theorem rfs_csf_maximum_principle (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      derivWithin (f.lift x) (Icc s u) t ≤
        c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
          A * f.lift x t + F t)
    (hinit : ∀ x, f.lift x s ≤ y s) :
    ∀ x t, t ∈ Icc s u → f.lift x t ≤ y t := by
  classical
  have _ := hBoundary
  have _ : FiniteDimensional ℝ E := inferInstance
  have _ : CompleteSpace E := inferInstance
  have _ : SigmaCompactSpace M := inferInstance
  have _ : T2Space M := inferInstance
  have _ := hd
  have _ := hF
  have hyc : ContinuousOn y (Icc s u) := fun t ht => (hy t ht).continuousWithinAt
  have hliftper : ∀ (x t : ℝ), f.lift (x + 1) t = f.lift x t := by
    intro x t
    simp only [CurveMap.lift, AddCircle.coe_add_period]
  suffices hkey : ∀ η : ℝ, 0 < η → ∀ x ∈ Icc 0 1, ∀ t ∈ Icc s u,
      Real.exp (-A * (t - s)) * (f.lift x t - y t) ≤ η * (1 + (t - s)) by
    intro x t ht
    have hx : f.lift x t = f.lift (Int.fract x) t := by
      have hp : Function.Periodic (fun z => f.lift z t) 1 := fun z => hliftper z t
      have h1 := hp.int_mul ⌊x⌋ (Int.fract x)
      simp only [mul_one] at h1
      rw [Int.fract_add_floor x] at h1
      exact h1
    have hxI : Int.fract x ∈ Icc 0 1 :=
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have hmain : Real.exp (-A * (t - s)) * (f.lift x t - y t) ≤ 0 := by
      rw [hx]
      have hpos1 : 0 < 1 + (t - s) := by linarith [ht.1]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hη : 0 < ε / (1 + (t - s)) := div_pos hε hpos1
      have h1 := hkey (ε / (1 + (t - s))) hη (Int.fract x) hxI t ht
      have h2 : ε / (1 + (t - s)) * (1 + (t - s)) = ε := by field_simp
      linarith
    nlinarith [hmain, Real.exp_pos (-A * (t - s))]
  intro η hη x₁ hx₁ t₁ ht₁
  by_contra hcon
  rw [not_le] at hcon
  set W : ℝ → ℝ → ℝ := fun x t =>
    Real.exp (-A * (t - s)) * (f.lift x t - y t) - η * (1 + (t - s)) with hW
  have hWper : ∀ x t, W (x + 1) t = W x t := by
    intro x t
    simp only [hW, hliftper x t]
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) (Icc 0 1 ×ˢ Icc s u) := by
    have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-A * (p.2 - s))) univ :=
      Real.continuous_exp.comp_continuousOn (by fun_prop)
    have hy2 : ContinuousOn (fun p : ℝ × ℝ => y p.2) (univ ×ˢ Icc s u) :=
      hyc.comp (f := fun p : ℝ × ℝ => p.2) continuous_snd.continuousOn
        (fun p hp => hp.2)
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        Real.exp (-A * (p.2 - s)) * (f.lift p.1 p.2 - y p.2)) (univ ×ˢ Icc s u) :=
      (hexp.mono (Set.subset_univ _)).mul (hf.continuousOn.sub hy2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => η * (1 + (p.2 - s))) univ :=
      (continuous_const.mul (continuous_const.add
        (continuous_snd.sub continuous_const))).continuousOn
    refine (h1.sub (h2.mono (Set.subset_univ _))).mono ?_
    exact Set.prod_mono (Set.subset_univ _) Subset.rfl
  obtain ⟨p₀, hp₀K, hp₀max⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(0, s), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hsu.le⟩⟩⟩ hcontW
  have hp₀max' : ∀ p ∈ (Icc 0 1 ×ˢ Icc s u),
      W p.1 p.2 ≤ W p₀.1 p₀.2 := fun _ hp => hp₀max hp
  have ht₀ : p₀.2 ∈ Icc s u := hp₀K.2
  have hx₀ : p₀.1 ∈ Icc 0 1 := hp₀K.1
  have hmaxT : IsMaxOn (fun t => W p₀.1 t) (Icc s u) p₀.2 :=
    fun t ht => hp₀max' (p₀.1, t) ⟨hx₀, ht⟩
  have hMpos : 0 < W p₀.1 p₀.2 := by
    have hle : W x₁ t₁ ≤ W p₀.1 p₀.2 := hp₀max' (x₁, t₁) ⟨hx₁, ht₁⟩
    have h1 : 0 < W x₁ t₁ := by
      simp only [hW]
      linarith
    exact lt_of_lt_of_le h1 hle
  have hWs : W p₀.1 s < 0 := by
    have h1 : W p₀.1 s = (f.lift p₀.1 s - y s) - η := by
      simp only [hW, sub_self, mul_zero, Real.exp_zero, one_mul, add_zero, mul_one]
    rw [h1]
    linarith [hinit p₀.1, hη]
  have ht₀pos : s < p₀.2 := by
    rcases lt_or_eq_of_le ht₀.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hMpos
      linarith
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) p₀.2 := (uniqueDiffOn_Icc hsu) p₀.2 ht₀
  have hfdiff : HasDerivWithinAt (fun t => f.lift p₀.1 t)
      (derivWithin (f.lift p₀.1) (Icc s u) p₀.2) (Icc s u) p₀.2 := by
    have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => f.lift p₀.1 t) (Icc s u) p₀.2 :=
      (hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩).comp p₀.2
        (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
        (fun t ht => ⟨trivial, ht⟩)
    exact (hcomp.differentiableWithinAt (by norm_num)).hasDerivWithinAt
  have hderivW : HasDerivWithinAt (fun t => W p₀.1 t)
      (Real.exp (-A * (p₀.2 - s)) * (-A * (f.lift p₀.1 p₀.2 - y p₀.2) +
        (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))) - η)
      (Icc s u) p₀.2 := by
    have h1 : HasDerivWithinAt (fun t : ℝ => Real.exp (-A * (t - s)))
        (Real.exp (-A * (p₀.2 - s)) * (-A)) (Icc s u) p₀.2 := by
      have h2 : HasDerivAt (fun t : ℝ => -A * (t - s)) (-A) p₀.2 := by
        simpa using ((hasDerivAt_id p₀.2).sub_const s).const_mul (-A)
      exact h2.exp.hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t => f.lift p₀.1 t - y t)
        (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))
        (Icc s u) p₀.2 :=
      hfdiff.sub (hy p₀.2 ht₀)
    have h4 : HasDerivWithinAt (fun t : ℝ => η * (1 + (t - s))) η (Icc s u) p₀.2 := by
      have h5 : HasDerivAt (fun t : ℝ => η * (1 + (t - s))) η p₀.2 := by
        simpa using (((hasDerivAt_id p₀.2).sub_const s).const_add 1).const_mul η
      exact h5.hasDerivWithinAt
    have h6 := (h1.mul h3).sub h4
    refine h6.congr_deriv ?_
    ring
  have hnonneg : 0 ≤ derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 := by
    have htend := hasDerivWithinAt_iff_tendsto_slope.mp hderivW
    have hsub : (Icc s u \ {p₀.2}) ∩ Iio p₀.2 ⊆ Icc s u \ {p₀.2} :=
      Set.inter_subset_left
    have htend2 := htend.mono_left (nhdsWithin_mono p₀.2 hsub)
    have hcl : p₀.2 ∈ closure ((Icc s u \ {p₀.2}) ∩ Iio p₀.2) := by
      have hsub' : Ioo s p₀.2 ⊆ (Icc s u \ {p₀.2}) ∩ Iio p₀.2 := by
        intro t ht
        exact ⟨⟨⟨ht.1.le, ht.2.le.trans ht₀.2⟩, ne_of_lt ht.2⟩, ht.2⟩
      have h2 : p₀.2 ∈ closure (Ioo s p₀.2) := by
        rw [closure_Ioo (ne_of_lt ht₀pos)]
        exact right_mem_Icc.mpr ht₀pos.le
      exact closure_mono hsub' h2
    rw [hderivW.derivWithin huniq]
    refine ge_of_tendsto (hx := mem_closure_iff_nhdsWithin_neBot.mp hcl) htend2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨⟨htJ, htne⟩, htlt⟩ := ht
    have hlt : t < p₀.2 := htlt
    have hle : W p₀.1 t ≤ W p₀.1 p₀.2 := hmaxT htJ
    rw [slope_def_field]
    exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  have hlocalW : ∀ᶠ x in 𝓝 p₀.1, W x p₀.2 ≤ W p₀.1 p₀.2 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨1 / 2, by norm_num, fun y hy => ?_⟩
    rw [Real.dist_eq, abs_lt] at hy
    by_cases hy01 : y ∈ Icc 0 1
    · exact hp₀max' (y, p₀.2) ⟨hy01, ht₀⟩
    · rw [mem_Icc] at hy01
      have hy01' : 0 ≤ y → 1 < y := by
        intro h
        by_contra h1
        exact hy01 ⟨h, not_lt.mp h1⟩
      rcases lt_or_ge y 0 with hlt | hge
      · have hy1 : y + 1 ∈ Icc 0 1 :=
          ⟨by linarith [hy.1, hx₀.1], by linarith [hlt]⟩
        rw [← hWper y p₀.2]
        exact hp₀max' (y + 1, p₀.2) ⟨hy1, ht₀⟩
      · have hgt : 1 < y := hy01' hge
        have hy1 : y - 1 ∈ Icc 0 1 :=
          ⟨by linarith [hgt], by linarith [hy.2, hx₀.2]⟩
        have hshift : y - 1 + 1 = y := by ring
        rw [← hshift, hWper (y - 1) p₀.2]
        exact hp₀max' (y - 1, p₀.2) ⟨hy1, ht₀⟩
  have hlocmaxW : IsLocalMax (fun x => W x p₀.2) p₀.1 := hlocalW
  have hlocmaxf : IsLocalMax (fun x => f.lift x p₀.2) p₀.1 := by
    filter_upwards [hlocalW] with z hz
    simp only [hW] at hz
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have h2 : Real.exp (-A * (p₀.2 - s)) * (f.lift z p₀.2 - y p₀.2) ≤
        Real.exp (-A * (p₀.2 - s)) * (f.lift p₀.1 p₀.2 - y p₀.2) := by linarith
    have h3 := le_of_mul_le_mul_left h2 hexp
    linarith
  have hslice2 : ContDiffAt ℝ 2 (fun x => f.lift x p₀.2) p₀.1 := by
    have hjoint : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2)
        (univ ×ˢ Icc s u) (p₀.1, p₀.2) := hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩
    have hsnd : ContDiffWithinAt ℝ ∞ (fun x : ℝ => (x, p₀.2)) univ p₀.1 := by
      fun_prop
    have hmaps : MapsTo (fun x : ℝ => (x, p₀.2)) univ (univ ×ˢ Icc s u) :=
      fun _ _ => ⟨trivial, ht₀⟩
    have hcomp := hjoint.comp p₀.1 hsnd hmaps
    exact ((contDiffWithinAt_univ.mp hcomp).of_le (m := 2)
      (WithTop.coe_le_coe.mpr le_top))
  have hderiv0 : deriv (fun x => f.lift x p₀.2) p₀.1 = 0 := hlocmaxf.deriv_eq_zero
  have hsecond : deriv (deriv (fun x => f.lift x p₀.2)) p₀.1 ≤ 0 :=
    mp_deriv_deriv_nonpos_of_isLocalMax hlocmaxf hslice2
  have hds0 : c.ds g f.lift p₀.1 p₀.2 = 0 := by
    simp only [CurveMap.ds, hderiv0, mul_zero]
  have hdsds : c.ds g (c.ds g f.lift) p₀.1 p₀.2 ≤ 0 := by
    have hσcont : ContinuousAt (fun y => c.speed g y p₀.2) p₀.1 :=
      (mp_speed_contDiff c g hi hc p₀.2 ht₀).continuous.continuousAt
    have hσpos : 0 < c.speed g p₀.1 p₀.2 := c.speed_pos g hi p₀.1 p₀.2 ht₀
    have hφderiv : HasDerivAt (fun y => deriv (fun z => f.lift z p₀.2) y)
        (deriv (deriv (fun z => f.lift z p₀.2)) p₀.1) p₀.1 :=
      ((hslice2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hkey := mp_deriv_inv_mul_nonpos hσcont hσpos hderiv0 hφderiv hsecond
    have hfund : c.ds g (c.ds g f.lift) p₀.1 p₀.2 =
        (c.speed g p₀.1 p₀.2)⁻¹ *
          deriv (fun y => (c.speed g y p₀.2)⁻¹ * deriv (fun z => f.lift z p₀.2) y) p₀.1 :=
      rfl
    rw [hfund]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hkey
  have hbound : derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 < 0 := by
    rw [hderivW.derivWithin huniq]
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have hpde' := hpde p₀.1 p₀.2 ht₀
    have hA : -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2)) ≤
        -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
            d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 +
            A * f.lift p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) := by linarith
    have hB : -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
            d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 +
            A * f.lift p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) =
        c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
          d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 := by ring
    have hC : Real.exp (-A * (p₀.2 - s)) * (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
          d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2) ≤ 0 := by
      rw [hds0, mul_zero, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hexp.le hdsds
    have hD := mul_le_mul_of_nonneg_left (hA.trans_eq hB) hexp.le
    linarith
  linarith [hnonneg, hbound]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem ds_neg (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (f : ℝ → ℝ → ℝ) :
    c.ds g (fun x t => -f x t) = fun x t => -c.ds g f x t := by
  funext x t
  simp only [CurveMap.ds, deriv.fun_neg, mul_neg]

theorem scalar_lower_comparison (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
        A * f.lift x t + F t ≤ derivWithin (f.lift x) (Icc s u) t)
    (hinit : ∀ x, y s ≤ f.lift x s) :
    ∀ x t, t ∈ Icc s u → y t ≤ f.lift x t := by
  let fn : CurveMap ℝ := fun z t => -f z t
  have hfn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fn.lift p.1 p.2) (univ ×ˢ Icc s u) := hf.neg
  have hyn : ∀ t ∈ Icc s u,
      HasDerivWithinAt (fun r => -y r) (A * (-y t) + (-F t)) (Icc s u) t := by
    intro t ht
    convert! (hy t ht).neg using 1
    simp only [neg_add, mul_neg]
  have hpden : ∀ x t, t ∈ Icc s u →
      derivWithin (fn.lift x) (Icc s u) t ≤
        c.ds g (c.ds g fn.lift) x t + d.lift x t * c.ds g fn.lift x t +
          A * fn.lift x t + (-F t) := by
    intro x t ht
    have h := hpde x t ht
    change derivWithin (fun r => -f.lift x r) (Icc s u) t ≤
      c.ds g (c.ds g (fun z r => -f.lift z r)) x t +
        d.lift x t * c.ds g (fun z r => -f.lift z r) x t + A * (-f.lift x t) + (-F t)
    rw [derivWithin.fun_neg, ds_neg g c f.lift, ds_neg g c (c.ds g f.lift)]
    nlinarith
  have hn := rfs_csf_maximum_principle g hsu c hc hi fn d hfn hd A
    (fun r => -F r) (fun r => -y r) hF.neg hyn hpden (fun x => neg_le_neg (hinit x))
  intro x t ht
  exact neg_le_neg_iff.mp (hn x t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
