import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.BaseParameter

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] in
private theorem chartKin_param
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {L : Real} (hL : 0 ≤ L)
    (tau : Nat → Real → Real) (tauLim : Real → Real)
    (htau : ∀ n, ContinuousOn (tau n) (Icc (0 : Real) L))
    (htauLim : ContinuousOn tauLim (Icc (0 : Real) L))
    {J : Set Real} (hJc : IsCompact J) (hJreg : J ⊆ D.regular)
    (htauJ : ∀ n (r : Icc (0 : Real) L), tau n r.1 ∈ J)
    (htauLimJ : ∀ r : Icc (0 : Real) L, tauLim r.1 ∈ J)
    (htauConv : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ tau n r.1)
      (fun r ↦ tauLim r.1) atTop)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (v : Nat → timeH1 E L) (vLim : timeH1 E L)
    (hvK : ∀ n (r : Icc (0 : Real) L), (v n).toFun r.1 ∈ K)
    (hvLimK : ∀ r : Icc (0 : Real) L, vLim.toFun r.1 ∈ K)
    (hv : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (v n).toFun r.1)
      (fun r ↦ vLim.toFun r.1) atTop)
    (hdv : Tendsto (fun n ↦ (v n).deriv) atTop (nhds vLim.deriv)) :
    Tendsto (fun n ↦ ∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G p
          (tau n r, (v n).toFun r) ((v n).deriv r))
        ((v n).deriv r)) atTop
      (nhds (∫ r in (0 : Real)..L,
        (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) G p
            (tauLim r, vLim.toFun r) (vLim.deriv r))
          (vLim.deriv r))) := by
  let A : Nat → Real → E →L[Real] E := fun n r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G p (tau n r, (v n).toFun r)
  let ALim : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G p (tauLim r, vLim.toFun r)
  have hpair (n : Nat) : ContinuousOn
      (fun r ↦ (tau n r, (v n).toFun r)) (Icc (0 : Real) L) :=
    (htau n).prodMk (v n).continuousOn_toFun
  have hpairLim : ContinuousOn
      (fun r ↦ (tauLim r, vLim.toFun r)) (Icc (0 : Real) L) :=
    htauLim.prodMk vLim.continuousOn_toFun
  have hAcont (n : Nat) : ContinuousOn (A n) (Icc (0 : Real) L) := by
    change ContinuousOn
      ((1 / 2 : Real) • fun r ↦ chartGramOp (I := I) G p
        (tau n r, (v n).toFun r)) (Icc (0 : Real) L)
    apply ContinuousOn.const_smul
    exact (chartGramOp_cont (I := I) hG hJreg p hKchart).comp
      (hpair n) fun r hr ↦ ⟨htauJ n ⟨r, hr⟩, hvK n ⟨r, hr⟩⟩
  have hALimCont : ContinuousOn ALim (Icc (0 : Real) L) := by
    change ContinuousOn
      ((1 / 2 : Real) • fun r ↦ chartGramOp (I := I) G p
        (tauLim r, vLim.toFun r)) (Icc (0 : Real) L)
    apply ContinuousOn.const_smul
    exact (chartGramOp_cont (I := I) hG hJreg p hKchart).comp
      hpairLim fun r hr ↦ ⟨htauLimJ ⟨r, hr⟩, hvLimK ⟨r, hr⟩⟩
  have hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure L) := fun n ↦ by
    simpa only [timeMeasure] using
      (hAcont n).aestronglyMeasurable measurableSet_Icc
  have hALim : AEStronglyMeasurable ALim (timeMeasure L) := by
    simpa only [timeMeasure] using
      hALimCont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hG hJreg hJc p hKchart hKc
  have hC : ∀ n, ∀ᵐ r ∂timeMeasure L, ‖A n r‖ ≤ (C : Real) := fun n ↦ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (tau n r, (v n).toFun r)
      ⟨htauJ n ⟨r, hr⟩, hvK n ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hCLim : ∀ᵐ r ∂timeMeasure L, ‖ALim r‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [ALim]
    rw [norm_smul]
    have hb := hCraw (tauLim r, vLim.toFun r)
      ⟨htauLimJ ⟨r, hr⟩, hvLimK ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hpairUnif : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦
        (tau n r.1, (v n).toFun r.1))
      (fun r ↦ (tauLim r.1, vLim.toFun r.1)) atTop := by
    have htwo := htauConv.prodMk hv
    rw [tendstoUniformly_iff_tendsto] at htwo ⊢
    have hdiag : Tendsto (fun n : Nat ↦ (n, n)) atTop (atTop ×ˢ atTop) :=
      tendsto_id.prodMk tendsto_id
    have hpull : Tendsto (fun q : Nat × Icc (0 : Real) L ↦ ((q.1, q.1), q.2))
        (atTop ×ˢ ⊤) ((atTop ×ˢ atTop) ×ˢ ⊤) :=
      (hdiag.comp tendsto_fst).prodMk tendsto_snd
    exact htwo.comp hpull
  have hGramUnif : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦
        chartGramOp (I := I) G p (tau n r.1, (v n).toFun r.1))
      (fun r ↦ chartGramOp (I := I) G p
        (tauLim r.1, vLim.toFun r.1)) atTop := by
    have huc : UniformContinuousOn (chartGramOp (I := I) G p) (J ×ˢ K) :=
      (hJc.prod hKc).uniformContinuousOn_of_continuous
        (chartGramOp_cont (I := I) hG hJreg p hKchart)
    apply huc.comp_tendstoUniformly
    · exact fun n r ↦ ⟨htauJ n r, hvK n r⟩
    · exact fun r ↦ ⟨htauLimJ r, hvLimK r⟩
    · exact hpairUnif
  have hconv : ∀ delta : Real, 0 < delta → ∀ᶠ n in atTop,
      ∀ᵐ r ∂timeMeasure L, ‖A n r - ALim r‖ ≤ delta := by
    intro delta hdelta
    have hev := (Metric.tendstoUniformly_iff.1 hGramUnif)
      (2 * delta) (by positivity)
    filter_upwards [hev] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hraw := hn ⟨r, hr⟩
    have hraw' :
        ‖chartGramOp (I := I) G p (tau n r, (v n).toFun r) -
          chartGramOp (I := I) G p (tauLim r, vLim.toFun r)‖ <
            2 * delta := by
      simpa only [dist_eq_norm, norm_sub_rev] using hraw
    have hscaled : (1 / 2 : Real) *
        ‖chartGramOp (I := I) G p (tau n r, (v n).toFun r) -
          chartGramOp (I := I) G p (tauLim r, vLim.toFun r)‖ < delta := by
      linarith
    dsimp only [A, ALim]
    rw [← smul_sub, norm_smul]
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact hscaled.le
  have hq := timeQuad_strong A ALim hA hALim (fun _ ↦ C) C hC hCLim hconv
    (fun n ↦ (v n).deriv) vLim.deriv hdv
  have hlimEq := timeQuad_eq_integral ALim hALim C hCLim hL vLim.deriv
  have hseqEq :
      (fun n ↦ timeQuad (A n) (hA n) C (hC n) (v n).deriv) =
        (fun n ↦ ∫ r in (0 : Real)..L,
          inner Real (A n r ((v n).deriv r)) ((v n).deriv r)) := by
    funext n
    exact timeQuad_eq_integral (A n) (hA n) C (hC n) hL (v n).deriv
  rw [hlimEq, hseqEq] at hq
  dsimp only [A, ALim] at hq
  simpa only [smul_apply, real_inner_smul_left] using hq

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M] in
private theorem lScalar_param
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    {Rn : Nat → Real} {R a b : Real} (hab : a ≤ b)
    (hRn : Tendsto Rn atTop (nhds R))
    {J : Set Real} (hJc : IsCompact J) (hJcar : J ⊆ D.carrier)
    (hJn : ∀ n s, s ∈ Icc a b → Rn n - s ^ 2 ∈ J)
    (hJlim : ∀ s ∈ Icc a b, R - s ^ 2 ∈ J)
    (alpha : Nat → Real → M) (alphaLim : Real → M)
    (halpha : ∀ n, ContinuousOn (alpha n) (Icc a b))
    (hconv : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ alphaLim s.1) atTop) :
    Tendsto
      (fun n ↦ ∫ s in a..b,
        2 * s ^ 2 * S.scalar (Rn n - s ^ 2) (alpha n s))
      atTop
      (nhds (∫ s in a..b,
        2 * s ^ 2 * S.scalar (R - s ^ 2) (alphaLim s))) := by
  let P : Real × (Real × M) → Real := fun q ↦
    2 * q.1 ^ 2 * S.scalar q.2.1 q.2.2
  have hP : ContinuousOn P (Icc a b ×ˢ (J ×ˢ (univ : Set M))) := by
    have hscalar : ContinuousOn (fun q : Real × (Real × M) ↦
        S.scalar q.2.1 q.2.2) (Icc a b ×ˢ (J ×ˢ (univ : Set M))) := by
      exact hS.scalar_continuousOn.comp continuous_snd.continuousOn
        (fun q hq ↦ ⟨hJcar hq.2.1, mem_univ _⟩)
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hcompact : IsCompact (Icc a b ×ˢ (J ×ˢ (univ : Set M))) :=
    isCompact_Icc.prod (hJc.prod isCompact_univ)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hP
  let C₀ : Real := max C 0
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun _ : Real ↦ C₀) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards with n
    have hpair : ContinuousOn (fun s : Real ↦
        (s, (Rn n - s ^ 2, alpha n s))) (Icc a b) :=
      continuous_id.continuousOn.prodMk
        ((continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk
          (halpha n))
    have hcomp : ContinuousOn (fun s : Real ↦ P
        (s, (Rn n - s ^ 2, alpha n s))) (Icc a b) :=
      hP.comp hpair (fun s hs ↦ ⟨hs, hJn n s hs, mem_univ _⟩)
    exact (hcomp.mono (fun s (hs : s ∈ uIoc a b) ↦ by
      simpa only [uIcc_of_le hab] using
        (uIoc_subset_uIcc hs))).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with n
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      exact (hC (s, (Rn n - s ^ 2, alpha n s))
        ⟨hsIcc, hJn n s hsIcc, mem_univ _⟩).trans (le_max_left C 0)
  · exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      have halphaAt : Tendsto (fun n ↦ alpha n s) atTop
          (nhds (alphaLim s)) := by
        simpa only using hconv.tendsto_at ⟨s, hsIcc⟩
      have htimeAt : Tendsto (fun n ↦ Rn n - s ^ 2) atTop
          (nhds (R - s ^ 2)) := hRn.sub tendsto_const_nhds
      let tDn : Nat → {t : Real // t ∈ D.carrier} := fun n ↦
        ⟨Rn n - s ^ 2, hJcar (hJn n s hsIcc)⟩
      let tD : {t : Real // t ∈ D.carrier} :=
        ⟨R - s ^ 2, hJcar (hJlim s hsIcc)⟩
      have htimeSub : Tendsto tDn atTop (nhds tD) := by
        exact tendsto_subtype_rng.2 htimeAt
      have hscalarAt : Tendsto
          (fun n ↦ S.scalar (Rn n - s ^ 2) (alpha n s)) atTop
          (nhds (S.scalar (R - s ^ 2) (alphaLim s))) := by
        simpa only [tDn, tD, Function.comp_def] using
          hS.continuous_subtype.continuousAt.tendsto.comp
            (htimeSub.prodMk_nhds halphaAt)
      exact tendsto_const_nhds.mul hscalarAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [T2Space M] in
private theorem lAction_head_param
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    {Rn : Nat → Real} {R a c : Real} (hac : a ≤ c)
    (hRn : Tendsto Rn atTop (nhds R)) (p : M)
    (alpha : Nat → Real → M) (gamma : Real → M)
    (v : Nat → timeH1 E (c - a)) (vLim : timeH1 E (c - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a c) (chartAt H p).source)
    (hrep : ∀ n, EqOn (v n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r)))
      (Icc (0 : Real) (c - a)))
    (hsrcLim : MapsTo gamma (Icc a c) (chartAt H p).source)
    (hrepLim : EqOn vLim.toFun
      (fun r ↦ extChartAt I p (gamma (a + r)))
      (Icc (0 : Real) (c - a)))
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (hvK : ∀ n (r : Icc (0 : Real) (c - a)), (v n).toFun r.1 ∈ K)
    (hvLimK : ∀ r : Icc (0 : Real) (c - a), vLim.toFun r.1 ∈ K)
    (hv : TendstoUniformly
      (fun n (r : Icc (0 : Real) (c - a)) ↦ (v n).toFun r.1)
      (fun r ↦ vLim.toFun r.1) atTop)
    (hdv : Tendsto (fun n ↦ (v n).deriv) atTop (nhds vLim.deriv))
    (halpha : ∀ n, ContinuousOn (alpha n) (Icc a c))
    (hunif : TendstoUniformly
      (fun n (s : Icc a c) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    {J : Set Real} (hJc : IsCompact J) (hJreg : J ⊆ D.regular)
    (hJn : ∀ n s, s ∈ Icc a c → Rn n - s ^ 2 ∈ J)
    (hJlim : ∀ s ∈ Icc a c, R - s ^ 2 ∈ J) :
    Tendsto (fun n ↦ lRegAction S (Rn n) (alpha n) a c) atTop
      (nhds (lRegAction S R gamma a c)) := by
  let tau : Nat → Real → Real := fun n r ↦ Rn n - (a + r) ^ 2
  let tauLim : Real → Real := fun r ↦ R - (a + r) ^ 2
  have hL : 0 ≤ c - a := sub_nonneg.mpr hac
  have htau (n : Nat) : ContinuousOn (tau n) (Icc (0 : Real) (c - a)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have htauLim : ContinuousOn tauLim (Icc (0 : Real) (c - a)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hshift (r : Icc (0 : Real) (c - a)) : a + r.1 ∈ Icc a c :=
    ⟨by linarith [r.2.1], by linarith [r.2.2]⟩
  have htauJ (n : Nat) (r : Icc (0 : Real) (c - a)) : tau n r.1 ∈ J := by
    exact hJn n (a + r.1) (hshift r)
  have htauLimJ (r : Icc (0 : Real) (c - a)) : tauLim r.1 ∈ J := by
    exact hJlim (a + r.1) (hshift r)
  have htauConv : TendstoUniformly
      (fun n (r : Icc (0 : Real) (c - a)) ↦ tau n r.1)
      (fun r ↦ tauLim r.1) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro epsilon hepsilon
    have hev : ∀ᶠ n in atTop, dist (Rn n) R < epsilon :=
      hRn.eventually (Metric.ball_mem_nhds R hepsilon)
    filter_upwards [hev] with n hn
    intro r
    simpa only [tau, tauLim, dist_sub_right, dist_comm] using hn
  have hkin := chartKin_param (I := I) hMet p hL tau tauLim
    htau htauLim hJc hJreg htauJ htauLimJ htauConv hKc hKchart
    v vLim hvK hvLimK hv hdv
  have hpot := lScalar_param S hSc hac hRn hJc
    (hJreg.trans D.regular_subset) hJn hJlim alpha gamma halpha hunif
  let t : Fin 2 → Real :=
    Fin.cases a (Fin.cases c fun k ↦ Fin.elim0 k)
  have ht0 : t 0 = a := rfl
  have ht1 : t (Fin.last 1) = c := rfl
  have htLen : partitionIntervalLength t 0 = c - a := rfl
  have htStart : t (0 : Fin 1).castSucc = a := rfl
  have htEnd : t (0 : Fin 1).succ = c := rfl
  have htmono : Monotone t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t]
  have hact (n : Nat) : lRegAction S (Rn n) (alpha n) a c =
      (∫ r in (0 : Real)..(c - a), (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (Rn n - (a + r) ^ 2, (v n).toFun r) ((v n).deriv r))
        ((v n).deriv r)) +
      ∫ s in a..c, 2 * s ^ 2 * S.scalar (Rn n - s ^ 2) (alpha n s) := by
    have hregn : ∀ s ∈ Icc a c, Rn n - s ^ 2 ∈ D.regular :=
      fun s hs ↦ hJreg (hJn n s hs)
    let vn : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) :=
      Fin.cases (v n) fun k ↦ Fin.elim0 k
    have hvn0 : vn 0 = v n := rfl
    have hraw := lRegAction_chart (I := I) (m := 1) S hMet hSc (Rn n) a c t htmono
      ht0 ht1 (fun _ ↦ p) (alpha n)
      vn
      (fun i ↦ by
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa only [htStart, htEnd] using hsrc n)
      (fun i ↦ by
        have hi : i = 0 := Fin.eq_zero i
        subst i
        intro r hr
        change r ∈ Icc (0 : Real) (c - a) at hr
        change (vn 0).toFun r = extChartAt I p (alpha n (a + r))
        rw [hvn0]
        exact hrep n hr) hregn
    rw [Fin.sum_univ_one] at hraw
    dsimp only [partitionIntervalLength, t] at hraw
    rw [hvn0] at hraw
    exact hraw
  have hactLim : lRegAction S R gamma a c =
      (∫ r in (0 : Real)..(c - a), (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (R - (a + r) ^ 2, vLim.toFun r) (vLim.deriv r))
        (vLim.deriv r)) +
      ∫ s in a..c, 2 * s ^ 2 * S.scalar (R - s ^ 2) (gamma s) := by
    have hregLim : ∀ s ∈ Icc a c, R - s ^ 2 ∈ D.regular :=
      fun s hs ↦ hJreg (hJlim s hs)
    let vLimFin : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) :=
      Fin.cases vLim fun k ↦ Fin.elim0 k
    have hvLim0 : vLimFin 0 = vLim := rfl
    have hraw := lRegAction_chart (I := I) (m := 1) S hMet hSc R a c t htmono
      ht0 ht1 (fun _ ↦ p) gamma
      vLimFin
      (fun i ↦ by
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa only [htStart, htEnd] using hsrcLim)
      (fun i ↦ by
        have hi : i = 0 := Fin.eq_zero i
        subst i
        intro r hr
        change r ∈ Icc (0 : Real) (c - a) at hr
        change (vLimFin 0).toFun r = extChartAt I p (gamma (a + r))
        rw [hvLim0]
        exact hrepLim hr) hregLim
    rw [Fin.sum_univ_one] at hraw
    dsimp only [partitionIntervalLength, t] at hraw
    rw [hvLim0] at hraw
    exact hraw
  have hsum := hkin.add hpot
  rw [show (fun n ↦ lRegAction S (Rn n) (alpha n) a c) =
      (fun n ↦
        (∫ r in (0 : Real)..(c - a), (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) S.family p
            (Rn n - (a + r) ^ 2, (v n).toFun r) ((v n).deriv r))
          ((v n).deriv r)) +
        ∫ s in a..c, 2 * s ^ 2 * S.scalar (Rn n - s ^ 2) (alpha n s)) by
        funext n
        exact hact n,
    hactLim]
  simpa only [tau, tauLim] using hsum

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [CompactSpace M] in
private theorem rampDown_add_param {L : Real} (hL : 0 < L) (z w : E) :
    timeH1.rampDown L (z + w) =
      timeH1.rampDown L z + timeH1.rampDown L w := by
  apply timeH1.ext
  · rw [← timeH1.toFun_zero (timeH1.rampDown L (z + w)),
      timeH1.init_add, ← timeH1.toFun_zero (timeH1.rampDown L z),
      ← timeH1.toFun_zero (timeH1.rampDown L w),
      timeH1.rampDown_zero hL, timeH1.rampDown_zero hL,
      timeH1.rampDown_zero hL]
  · rw [timeH1.deriv_add]
    apply Lp.ext
    filter_upwards [timeH1.rampDown_deriv hL (z + w),
      timeH1.rampDown_deriv hL z, timeH1.rampDown_deriv hL w,
      Lp.coeFn_add (timeH1.rampDown L z).deriv
        (timeH1.rampDown L w).deriv] with s hzw hz hw hadd
    rw [hzw, hadd, Pi.add_apply, hz, hw, smul_add]

private def rampDownLMParam (L : Real) (hL : 0 < L) :
    E →ₗ[Real] timeH1 E L where
  toFun := timeH1.rampDown L
  map_add' := rampDown_add_param hL
  map_smul' := timeH1.rampDown_smul hL

omit [NeZero (Module.finrank Real E)] in
private theorem rampDown_lim_param {L : Real} (hL : 0 < L)
    {z : Nat → E} {z₀ : E} (hz : Tendsto z atTop (nhds z₀)) :
    Tendsto (fun n ↦ timeH1.rampDown L (z n)) atTop
      (nhds (timeH1.rampDown L z₀)) := by
  exact (LinearMap.continuous_of_finiteDimensional
    (rampDownLMParam L hL)).continuousAt.tendsto.comp hz

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem h1_uniform_param
    {L : Real} (v : Nat → timeH1 E L) (u : timeH1 E L)
    (hv : Tendsto v atTop (nhds u)) :
    TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (v n).toFun r.1)
      (fun r ↦ u.toFun r.1) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let C : Real := 1 + Real.sqrt L
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hsub : Tendsto (fun n ↦ u - v n) atTop (nhds 0) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub hv :
      Tendsto (fun n ↦ u - v n) atTop (nhds (u - u)))
  have hnorm : Tendsto (fun n ↦ ‖u - v n‖) atTop (nhds 0) := by
    simpa only [Function.comp_def, norm_zero] using
      continuous_norm.tendsto (0 : timeH1 E L) |>.comp hsub
  have hsmall : ∀ᶠ n in atTop, ‖u - v n‖ < epsilon / C :=
    hnorm.eventually (Iio_mem_nhds (div_pos hepsilon hC))
  filter_upwards [hsmall] with n hn
  intro r
  have hfun : (u - v n).toFun r.1 = u.toFun r.1 - (v n).toFun r.1 := by
    rw [sub_eq_add_neg, timeH1.toFun_add u (-v n) r.2]
    have hneg := timeH1.toFun_smul (-1 : Real) (v n) r.2
    simpa only [neg_one_smul, sub_eq_add_neg] using
      congrArg (u.toFun r.1 + ·) hneg
  rw [dist_eq_norm, ← hfun]
  calc
    ‖(u - v n).toFun r.1‖ ≤ C * ‖u - v n‖ :=
      (u - v n).norm_toFun_le_norm r.2
    _ < C * (epsilon / C) := mul_lt_mul_of_pos_left hn hC
    _ = epsilon := by field_simp

omit [NeZero (Module.finrank Real E)] [T2Space M] in
theorem chart_head_T_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    {Rn : Nat → Real} {R a c : Real} (hRn : Tendsto Rn atTop (nhds R))
    (hac : a < c) (p : M) (gamma : Real → M)
    (u₀ : timeH1 E (c - a))
    (hsrc₀ : MapsTo gamma (Icc a c) (chartAt H p).source)
    (hrep₀ : EqOn u₀.toFun (fun r ↦ extChartAt I p (gamma (a + r)))
      (Icc (0 : Real) (c - a)))
    (z : Nat → E) (hz : Tendsto z atTop (nhds 0))
    (K : Set E) (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (hK : ∀ n (r : Icc (0 : Real) (c - a)),
      (u₀ + timeH1.rampDown (c - a) (z n)).toFun r.1 ∈ K)
    (hK₀ : ∀ r : Icc (0 : Real) (c - a), u₀.toFun r.1 ∈ K)
    (J : Set Real) (hJc : IsCompact J) (hJreg : J ⊆ D.regular)
    (hJn : ∀ n s, s ∈ Icc a c → Rn n - s ^ 2 ∈ J)
    (hJlim : ∀ s ∈ Icc a c, R - s ^ 2 ∈ J) :
    Tendsto
      (fun n ↦ lRegAction S (Rn n)
        (fun s ↦ (extChartAt I p).symm
          ((u₀ + timeH1.rampDown (c - a) (z n)).toFun (s - a))) a c)
      atTop (nhds (lRegAction S R gamma a c)) := by
  let v : Nat → timeH1 E (c - a) := fun n ↦
    u₀ + timeH1.rampDown (c - a) (z n)
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I p).symm ((v n).toFun (s - a))
  let beta₀ : Real → M := fun s ↦
    (extChartAt I p).symm (u₀.toFun (s - a))
  have hL : 0 < c - a := sub_pos.mpr hac
  have hv : Tendsto v atTop (nhds u₀) := by
    have hr := rampDown_lim_param (E := E) hL hz
    have hr₀ : timeH1.rampDown (c - a) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampDown_smul hL (0 : Real) (0 : E)
    simpa only [v, hr₀, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform_param v u₀ hv
  have hderiv : Tendsto (fun n ↦ (v n).deriv) atTop (nhds u₀.deriv) := by
    change Tendsto ((timeH1.timeDeriv E (c - a)) ∘ v) atTop
      (nhds ((timeH1.timeDeriv E (c - a)) u₀))
    exact (timeH1.timeDeriv E (c - a)).continuous.continuousAt.tendsto.comp hv
  have hsymm : UniformContinuousOn (extChartAt I p).symm K :=
    hKc.uniformContinuousOn_of_continuous <|
      (continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset)
  have hunif : TendstoUniformly
      (fun n (s : Icc a c) ↦ beta n s.1)
      (fun s ↦ beta₀ s.1) atTop := by
    have hshift : MapsTo (fun s : Icc a c ↦ s.1 - a)
        univ (Icc (0 : Real) (c - a)) := by
      intro s _
      exact ⟨sub_nonneg.mpr s.2.1, sub_le_sub_right s.2.2 a⟩
    have hc' := hcoord.comp (fun s : Icc a c ↦
      ⟨s.1 - a, hshift (mem_univ s)⟩)
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := K) (F := fun n (s : Icc a c) ↦ (v n).toFun (s.1 - a))
      (f := fun s ↦ u₀.toFun (s.1 - a))
    · exact fun n s ↦ hK n ⟨s.1 - a, hshift (mem_univ s)⟩
    · exact fun s ↦ hK₀ ⟨s.1 - a, hshift (mem_univ s)⟩
    · exact hsymm
    · simpa only [beta, beta₀, Function.comp_def] using hc'
  have hcont (n : Nat) : ContinuousOn (beta n) (Icc a c) := by
    have hcoordCont : ContinuousOn (fun s ↦ (v n).toFun (s - a))
        (Icc a c) :=
      (v n).continuousOn_toFun.comp (continuous_sub_right a).continuousOn
        (fun s hs ↦ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩)
    exact (continuousOn_extChartAt_symm p).comp hcoordCont
      (fun s hs ↦ interior_subset (hKchart (hK n ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hsrc (n : Nat) : MapsTo (beta n) (Icc a c)
      (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK n ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hrep (n : Nat) : EqOn (v n).toFun
      (fun r ↦ extChartAt I p (beta n (a + r)))
      (Icc (0 : Real) (c - a)) := by
    intro r hr
    simp only [beta, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK n ⟨r, hr⟩)))).symm
  have hsrcLim : MapsTo beta₀ (Icc a c) (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK₀ ⟨s - a,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
  have hrepLim : EqOn u₀.toFun
      (fun r ↦ extChartAt I p (beta₀ (a + r)))
      (Icc (0 : Real) (c - a)) := by
    intro r hr
    simp only [beta₀, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK₀ ⟨r, hr⟩)))).symm
  have hlim := lAction_head_param (I := I) S hMet hSc hac.le hRn p
    beta beta₀ v u₀ hsrc hrep hsrcLim hrepLim hKc hKchart hK hK₀
    hcoord hderiv hcont hunif hJc hJreg hJn hJlim
  have heq : EqOn beta₀ gamma (Icc a c) := by
    intro s hs
    apply (extChartAt I p).injOn
    · simpa only [extChartAt_source] using hsrcLim hs
    · rw [extChartAt_source]
      exact hsrc₀ hs
    · calc
        extChartAt I p (beta₀ s) = u₀.toFun (s - a) :=
          (extChartAt I p).right_inv
            (interior_subset (hKchart (hK₀ ⟨s - a,
              ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩⟩)))
        _ = extChartAt I p (gamma (a + (s - a))) :=
          hrep₀ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
        _ = extChartAt I p (gamma s) := by
          congr 2
          ring
  have heqAct : lRegAction S R beta₀ a c = lRegAction S R gamma a c :=
    lRegAction_congr (I := I) S R beta₀ gamma a c (by
      have heq' : EqOn beta₀ gamma (uIcc a c) := by
        simpa only [uIcc_of_le hac.le] using heq
      exact heq'.mono uIoo_subset_uIcc_self)
  rw [heqAct] at hlim
  simpa only [beta, v] using hlim

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem eventually_mem_buf_param
    {A : Type*} (f : A → E) (v : Nat → A → E) (K : Set E)
    (hfc : IsCompact (range f)) (hfK : ∀ r, f r ∈ interior K)
    (hv : TendstoUniformly v f atTop) :
    ∀ᶠ n in atTop, ∀ r, v n r ∈ K := by
  obtain ⟨delta, hdelta, hthick⟩ :=
    hfc.exists_thickening_subset_open isOpen_interior (by
      rintro _ ⟨r, rfl⟩
      exact hfK r)
  have hclose := (Metric.tendstoUniformly_iff.mp hv) delta hdelta
  filter_upwards [hclose] with n hn
  intro r
  apply interior_subset
  apply hthick
  exact Metric.mem_thickening_iff.mpr
    ⟨f r, mem_range_self r, by simpa only [dist_comm] using hn r⟩

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem toFun_cast_param {a b : Real} (h : a = b) (v : timeH1 E b) :
    ((h.symm ▸ v : timeH1 E a).toFun) = v.toFun := by
  subst b
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem lCost_lt_param
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {Rn : Nat → Real} {R tau : Real} (hRn : Tendsto Rn atTop (nhds R))
    (htau : 0 < tau) (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      R - s ^ 2 ∈ D.regular)
    (A : Real) (hA : lRegAction S R alpha 0 (Real.sqrt tau) < A)
    (q : Nat → M) (hq : Tendsto q atTop (nhds x)) :
    ∀ᶠ n in atTop, lCost S (Rn n) (q n) y tau < A := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hxSrc : alpha 0 ∈ (chartAt H x).source := by
    rw [hstart]
    exact mem_chart_source H x
  obtain ⟨c, hc, hcb₂, hsrcHead⟩ :=
    DifferentialGeometry.Geometry.exists_chart_initial_segment (H := H)
      (a := (0 : Real)) (b := b / 2) (half_pos hb)
      (halpha.continuous.continuousOn.mono
        (Icc_subset_Icc_right (half_le_self hb.le))) hxSrc
  have hcb : c < b := lt_of_le_of_lt hcb₂ (half_lt_self hb)
  let gamma : Real → M := fun r ↦ alpha r
  have hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) c) := halpha.contMDiffOn
  have hgammaSrc : MapsTo gamma (Icc (0 : Real) c)
      (chartAt H x).source := hsrcHead
  let u₀ : timeH1 E c := chartTimeH1 I hc.le x gamma hgamma hgammaSrc
  have hrep₀ : EqOn u₀.toFun (fun r ↦ extChartAt I x (alpha r))
      (Icc (0 : Real) c) := by
    simpa only [u₀, gamma, Function.comp_def] using
      chartTimeH1_toFun I hc.le x gamma hgamma hgammaSrc
  have htar₀ (r : Icc (0 : Real) c) :
      u₀.toFun r.1 ∈ (extChartAt I x).target := by
    rw [hrep₀ r.2]
    exact (extChartAt I x).map_source (by
      rw [extChartAt_source]
      exact hgammaSrc r.2)
  obtain ⟨K, hKc, _hKclosed, hintoK, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn u₀.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) x)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar₀ ⟨r, hr⟩)
  have hKchart : K ⊆ interior (extChartAt I x).target := by
    simpa only [(isOpen_extChartAt_target (I := I) x).interior_eq] using hKtar
  have hK₀ (r : Icc (0 : Real) c) : u₀.toFun r.1 ∈ K :=
    interior_subset (hintoK ⟨r.1, r.2, rfl⟩)
  have hqSrc : ∀ᶠ n in atTop, q n ∈ (chartAt H x).source :=
    hq.eventually ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  let z : Nat → E := fun n ↦ extChartAt I x (q n) - extChartAt I x x
  have hz : Tendsto z atTop (nhds 0) := by
    have hcq := (continuousAt_extChartAt (I := I) x).tendsto.comp hq
    have hcst : Tendsto (fun _ : Nat ↦ extChartAt I x x) atTop
        (nhds (extChartAt I x x)) := tendsto_const_nhds
    simpa only [z, Function.comp_apply, sub_self] using hcq.sub hcst
  let v : Nat → timeH1 E c := fun n ↦ u₀ + timeH1.rampDown c (z n)
  have hv : Tendsto v atTop (nhds u₀) := by
    have hr := rampDown_lim_param (E := E) hc hz
    have hr₀ : timeH1.rampDown c (0 : E) = 0 := by
      simpa only [zero_smul] using timeH1.rampDown_smul hc (0 : Real) (0 : E)
    simpa only [v, hr₀, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform_param v u₀ hv
  have hu₀Range : IsCompact
      (range fun r : Icc (0 : Real) c ↦ u₀.toFun r.1) := by
    rw [← image_univ]
    exact isCompact_univ.image_of_continuousOn
      (u₀.continuousOn_toFun.comp continuous_subtype_val.continuousOn
        (fun _ _ ↦ Subtype.property _))
  have hvK : ∀ᶠ n in atTop, ∀ r : Icc (0 : Real) c, (v n).toFun r.1 ∈ K :=
    eventually_mem_buf_param (fun r : Icc (0 : Real) c ↦ u₀.toFun r.1)
      (fun n r ↦ (v n).toFun r.1) K hu₀Range
      (fun r ↦ hintoK ⟨r.1, r.2, rfl⟩) hcoord
  let J₀ : Set Real := (fun s : Real ↦ R - s ^ 2) '' Icc (0 : Real) b
  have hJ₀c : IsCompact J₀ :=
    isCompact_Icc.image_of_continuousOn
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJ₀reg : J₀ ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s (by simpa only [b] using hs)
  obtain ⟨epsilon, hepsilon, hthick⟩ :=
    hJ₀c.exists_thickening_subset_open D.regular_isOpen hJ₀reg
  let eta : Real := epsilon / 2
  have heta : 0 < eta := half_pos hepsilon
  let KT : Set Real := Icc (R - eta) (R + eta)
  have hRnKT : ∀ᶠ n in atTop, Rn n ∈ KT := by
    have hball := hRn.eventually (Metric.ball_mem_nhds R heta)
    filter_upwards [hball] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
  let J : Set Real := (fun q : Real × Real ↦ q.1 - q.2 ^ 2) ''
    (KT ×ˢ Icc (0 : Real) b)
  have hJc : IsCompact J :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (continuous_fst.sub (continuous_snd.pow 2)).continuousOn
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨r, hr, rfl⟩
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨R - r.2 ^ 2, ⟨r.2, hr.2, rfl⟩, ?_⟩
    rw [Real.dist_eq]
    have hdist : |r.1 - R| ≤ eta := by
      rw [abs_le]
      exact ⟨by linarith [hr.1.1], by linarith [hr.1.2]⟩
    simpa only [sub_sub_sub_cancel_right] using hdist.trans_lt (half_lt_self hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hqSrc.and (hvK.and hRnKT))
  let q' : Nat → M := fun n ↦ q (n + N)
  let z' : Nat → E := fun n ↦ z (n + N)
  let Rn' : Nat → Real := fun n ↦ Rn (n + N)
  have hq'Src (n : Nat) : q' n ∈ (chartAt H x).source :=
    (hN _ (Nat.le_add_left N n)).1
  have hz' : Tendsto z' atTop (nhds 0) := hz.comp (tendsto_add_atTop_nat N)
  have hRn' : Tendsto Rn' atTop (nhds R) := hRn.comp (tendsto_add_atTop_nat N)
  have hv'K (n : Nat) (r : Icc (0 : Real) c) :
      (u₀ + timeH1.rampDown c (z' n)).toFun r.1 ∈ K := by
    simpa only [v, z'] using (hN _ (Nat.le_add_left N n)).2.1 r
  have hRn'KT (n : Nat) : Rn' n ∈ KT :=
    (hN _ (Nat.le_add_left N n)).2.2
  have hJn (n : Nat) (s : Real) (hs : s ∈ Icc (0 : Real) b) :
      Rn' n - s ^ 2 ∈ J :=
    ⟨(Rn' n, s), ⟨hRn'KT n, hs⟩, rfl⟩
  have hJlim (s : Real) (hs : s ∈ Icc (0 : Real) b) :
      R - s ^ 2 ∈ J := by
    refine ⟨(R, s), ⟨?_, hs⟩, rfl⟩
    exact ⟨by linarith [heta], by linarith [heta]⟩
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I x).symm ((u₀ + timeH1.rampDown c (z' n)).toFun s)
  have hheadLim : Tendsto
      (fun n ↦ lRegAction S (Rn' n) (beta n) 0 c) atTop
      (nhds (lRegAction S R alpha 0 c)) := by
    let u₀' : timeH1 E (c - 0) := (sub_zero c).symm ▸ u₀
    have hu₀' : u₀'.toFun = u₀.toFun :=
      toFun_cast_param (sub_zero c) u₀
    have hrep₀' : EqOn u₀'.toFun
        (fun r ↦ extChartAt I x (alpha (0 + r)))
        (Icc (0 : Real) (c - 0)) := by
      rw [hu₀']
      simpa only [sub_zero, zero_add] using hrep₀
    have hv'K' : ∀ n (r : Icc (0 : Real) (c - 0)),
        (u₀' + timeH1.rampDown (c - 0) (z' n)).toFun r.1 ∈ K := by
      intro n r
      have hr : r.1 ∈ Icc (0 : Real) c := by simpa only [sub_zero] using r.2
      have h := hv'K n ⟨r.1, hr⟩
      rw [timeH1.toFun_add _ _ r.2,
        timeH1.rampDown_apply (by simpa only [sub_zero] using hc.le) (z' n) r.2,
        hu₀']
      rw [timeH1.toFun_add _ _ hr, timeH1.rampDown_apply hc.le (z' n) hr] at h
      simpa only [sub_zero] using h
    have hK₀' : ∀ r : Icc (0 : Real) (c - 0), u₀'.toFun r.1 ∈ K := by
      intro r
      rw [hu₀']
      exact hK₀ ⟨r.1, by simpa only [sub_zero] using r.2⟩
    have hlim := chart_head_T_lim (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      hRn' hc x alpha u₀' hsrcHead hrep₀' z' hz' K hKc hKchart
      hv'K' hK₀' J hJc hJreg
      (fun n s hs ↦ hJn n s ⟨hs.1, hs.2.trans hcb.le⟩)
      (fun s hs ↦ hJlim s ⟨hs.1, hs.2.trans hcb.le⟩)
    have hactEq (n : Nat) :
        lRegAction S (Rn' n)
          (fun s ↦ (extChartAt I x).symm
            ((u₀' + timeH1.rampDown (c - 0) (z' n)).toFun (s - 0))) 0 c =
          lRegAction S (Rn' n) (beta n) 0 c := by
      apply lRegAction_congr (I := I) S (Rn' n) _ _ 0 c
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) c := by
        simpa only [uIoo_of_le hc.le] using hs
      have hsc : s ∈ Icc (0 : Real) c := ⟨hs'.1.le, hs'.2.le⟩
      have hsL : s - 0 ∈ Icc (0 : Real) (c - 0) := by
        simpa only [sub_zero] using hsc
      simp only [beta]
      congr 1
      rw [timeH1.toFun_add _ _ hsL,
        timeH1.rampDown_apply (by simpa only [sub_zero] using hc.le) (z' n) hsL,
        hu₀']
      rw [timeH1.toFun_add _ _ hsc, timeH1.rampDown_apply hc.le (z' n) hsc]
      simp only [sub_zero]
    rw [show (fun n ↦ lRegAction S (Rn' n)
        (fun s ↦ (extChartAt I x).symm
          ((u₀' + timeH1.rampDown (c - 0) (z' n)).toFun (s - 0))) 0 c) =
        (fun n ↦ lRegAction S (Rn' n) (beta n) 0 c) by
          funext n
          exact hactEq n] at hlim
    exact hlim
  have hu₀c1 : ContDiffOn Real 1 u₀.toFun (Icc (0 : Real) c) := by
    exact (chartCoord_contDiff I x gamma hgamma hgammaSrc).congr
      (fun r hr ↦ by simpa only [gamma, Function.comp_apply] using hrep₀ hr)
  have hbetaC1 (n : Nat) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1 (beta n) (Icc (0 : Real) c) := by
    let w₀ : timeH1 E c := u₀ + timeH1.rampDown c (z' n)
    have hwC1 : ContDiffOn Real 1 w₀.toFun (Icc (0 : Real) c) := by
      have hrampC1 : ContDiffOn Real 1
          (fun r : Real ↦ ((c - r) / c) • z' n) (Icc (0 : Real) c) :=
        (((contDiff_const.sub contDiff_id).div_const c).smul_const
          (z' n)).contDiffOn
      apply (hu₀c1.add hrampC1).congr
      intro r hr
      rw [timeH1.toFun_add _ _ hr, timeH1.rampDown_apply hc.le (z' n) hr]
    let w : timeH1 E (c - 0) := (sub_zero c).symm ▸ w₀
    have hwfun : w.toFun = w₀.toFun := toFun_cast_param (sub_zero c) w₀
    apply curve_c1_local I x (beta n) w
    · intro s hs
      rw [← extChartAt_source (I := I) x]
      exact (extChartAt I x).map_target
        (interior_subset (hKchart (hv'K n ⟨s, hs⟩)))
    · intro r hr
      rw [hwfun]
      simp only [beta, zero_add]
      exact ((extChartAt I x).right_inv
        (interior_subset (hKchart (hv'K n
          ⟨r, by simpa only [sub_zero] using hr⟩)))).symm
    · rw [hwfun]
      simpa only [sub_zero] using hwC1
  have hbetaSrc (n : Nat) : MapsTo (beta n) (Icc (0 : Real) c)
      (chartAt H x).source := by
    intro s hs
    rw [← extChartAt_source (I := I) x]
    exact (extChartAt I x).map_target
      (interior_subset (hKchart (hv'K n ⟨s, hs⟩)))
  have hbeta₀ (n : Nat) : beta n 0 = q' n := by
    apply (extChartAt I x).injOn
    · simpa only [extChartAt_source] using hbetaSrc n ⟨le_rfl, hc.le⟩
    · rw [extChartAt_source]
      exact hq'Src n
    · have hright : extChartAt I x (beta n 0) =
          (u₀ + timeH1.rampDown c (z' n)).toFun 0 :=
        (extChartAt I x).right_inv
          (interior_subset (hKchart (hv'K n ⟨0, ⟨le_rfl, hc.le⟩⟩)))
      have hu₀0 : u₀.toFun 0 = extChartAt I x x := by
        calc
          u₀.toFun 0 = extChartAt I x (alpha 0) := by
            simpa only using hrep₀ ⟨le_rfl, hc.le⟩
          _ = extChartAt I x x := congrArg (extChartAt I x) hstart
      rw [hright, timeH1.toFun_add _ _ ⟨le_rfl, hc.le⟩,
        timeH1.rampDown_zero hc, hu₀0]
      simp only [z', z, q', add_sub_cancel]
  have hbetaC (n : Nat) : beta n c = alpha c := by
    apply (extChartAt I x).injOn
    · simpa only [extChartAt_source] using hbetaSrc n ⟨hc.le, le_rfl⟩
    · rw [extChartAt_source]
      exact hsrcHead ⟨hc.le, le_rfl⟩
    · have hright : extChartAt I x (beta n c) =
          (u₀ + timeH1.rampDown c (z' n)).toFun c :=
        (extChartAt I x).right_inv
          (interior_subset (hKchart (hv'K n ⟨c, ⟨hc.le, le_rfl⟩⟩)))
      rw [hright, timeH1.toFun_add _ _ ⟨hc.le, le_rfl⟩,
        timeH1.rampDown_end hc, add_zero, hrep₀ ⟨hc.le, le_rfl⟩]
  have hreg₀c : ∀ s ∈ Icc (0 : Real) c, R - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, by simpa only [b] using hs.2.trans hcb.le⟩
  have hregcb : ∀ s ∈ Icc c b, R - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hheadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    R 0 c hc.le alpha halpha.contMDiffOn hreg₀c
  have htailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    R c b hcb.le alpha halpha.contMDiffOn hregcb
  have halphaAdd := lRegAction_add (I := I) S R alpha 0 c b hheadInt htailInt
  have htailLim : Tendsto (fun n ↦ lRegAction S (Rn' n) alpha c b) atTop
      (nhds (lRegAction S R alpha c b)) :=
    ((lRegAction_T_cont (I := I) S hS R c b alpha halpha
      (by simpa only [uIcc_of_le hcb.le] using hregcb)).tendsto.comp hRn')
  have hpiece : Tendsto
      (fun n ↦ lRegAction S (Rn' n) (beta n) 0 c +
        lRegAction S (Rn' n) alpha c b)
      atTop (nhds (lRegAction S R alpha 0 b)) := by
    have hsum := hheadLim.add htailLim
    rw [halphaAdd] at hsum
    exact hsum
  have hsmall : ∀ᶠ n in atTop,
      lRegAction S (Rn' n) (beta n) 0 c +
        lRegAction S (Rn' n) alpha c b < A :=
    hpiece.eventually (Iio_mem_nhds (by simpa only [b] using hA))
  have hcost' : ∀ᶠ n in atTop, lCost S (Rn' n) (q' n) y tau < A := by
    filter_upwards [hsmall] with n hn
    have hregn : ∀ s ∈ Icc (0 : Real) b,
        Rn' n - s ^ 2 ∈ D.regular := fun s hs ↦ hJreg (hJn n s hs)
    have hregn₀c : ∀ s ∈ Icc (0 : Real) c,
        Rn' n - s ^ 2 ∈ D.regular := fun s hs ↦
      hregn s ⟨hs.1, hs.2.trans hcb.le⟩
    have hregncb : ∀ s ∈ Icc c b,
        Rn' n - s ^ 2 ∈ D.regular := fun s hs ↦
      hregn s ⟨hc.le.trans hs.1, hs.2⟩
    obtain ⟨etaCurve, m, t, p, w, heta₀, heta₁, htmono, htfirst, htlast,
        _hcnode, hsrc, hrep⟩ :=
      exists_chartH1_join (I := I) 0 c b hc hcb (beta n) alpha
        (hbetaC1 n) halpha.contMDiffOn (hbetaC n)
    obtain ⟨delta, _u, hdelta, hdelta₀, hdeltab, _hsrcDelta, _hrepDelta,
        _hu, _hunif, hdeltaAct⟩ :=
      lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        (Rn' n) 0 b t htmono htfirst htlast p etaCurve w hsrc hrep hregn
    have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 etaCurve
        (Icc (0 : Real) c) := (hbetaC1 n).congr fun s hs ↦ heta₀ hs
    have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 etaCurve
        (Icc c b) := halpha.contMDiffOn.congr fun s hs ↦ heta₁ hs
    have hetaHeadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ (Rn' n) 0 c hc.le etaCurve hetaHead hregn₀c
    have hetaTailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ (Rn' n) c b hcb.le etaCurve hetaTail hregncb
    have hetaAdd := lRegAction_add (I := I) S (Rn' n) etaCurve 0 c b
      hetaHeadInt hetaTailInt
    have hetaHeadAct : lRegAction S (Rn' n) etaCurve 0 c =
        lRegAction S (Rn' n) (beta n) 0 c :=
      lRegAction_congr (I := I) S (Rn' n) etaCurve (beta n) 0 c (by
        intro s hs
        have hs' : s ∈ Ioo (0 : Real) c := by
          simpa only [uIoo_of_le hc.le] using hs
        exact heta₀ ⟨hs'.1.le, hs'.2.le⟩)
    have hetaTailAct : lRegAction S (Rn' n) etaCurve c b =
        lRegAction S (Rn' n) alpha c b :=
      lRegAction_congr (I := I) S (Rn' n) etaCurve alpha c b (by
        intro s hs
        have hs' : s ∈ Ioo c b := by
          simpa only [uIoo_of_le hcb.le] using hs
        exact heta₁ ⟨hs'.1.le, hs'.2.le⟩)
    have hetaLt : lRegAction S (Rn' n) etaCurve 0 b < A := by
      rw [← hetaAdd, hetaHeadAct, hetaTailAct]
      exact hn
    have hdeltaSmall : ∀ᶠ k in atTop,
        lRegAction S (Rn' n) (delta k) 0 b < A :=
      hdeltaAct.eventually (Iio_mem_nhds hetaLt)
    obtain ⟨k, hk⟩ := hdeltaSmall.exists
    rw [lCost_eq_reg (I := I) S (Rn' n) (q' n) y tau htau.le]
    have htimeN : Icc (Rn' n - tau) (Rn' n) ⊆ D.carrier := by
      intro r hr
      have hnonneg : 0 ≤ Rn' n - r := by linarith [hr.2]
      have hle : Rn' n - r ≤ tau := by linarith [hr.1]
      have hsqrt : Real.sqrt (Rn' n - r) ∈ Icc (0 : Real) b := by
        refine ⟨Real.sqrt_nonneg _, ?_⟩
        simpa only [b] using Real.sqrt_le_sqrt hle
      have hregR := hregn (Real.sqrt (Rn' n - r)) hsqrt
      have heqR : Rn' n - (Real.sqrt (Rn' n - r)) ^ 2 = r := by
        rw [Real.sq_sqrt hnonneg]
        ring
      exact D.regular_subset (by simpa only [heqR] using hregR)
    have hbackN : ∀ s ∈ Icc (0 : Real) b,
        Rn' n - s ^ 2 ∈ Icc (Rn' n - tau) (Rn' n) := by
      intro s hs
      have hsq : s ^ 2 ≤ tau := by
        calc
          s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
          _ = tau := by simp only [b, Real.sq_sqrt htau.le]
      exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    exact lt_of_le_of_lt
      (lRegCostC1_le (I := I) S hS (Rn' n) (Rn' n - tau) (Rn' n)
        0 b hb.le htimeN hbackN (q' n) y (delta k) (hdelta k)
        ((hdelta₀ k).trans ((heta₀ ⟨le_rfl, hc.le⟩).trans (hbeta₀ n)))
        ((hdeltab k).trans ((heta₁ ⟨hcb.le, le_rfl⟩).trans
          (by simpa only [b] using hend))) hregn) hk
  rw [← map_add_atTop_eq_nat N]
  change ∀ᶠ n in atTop, lCost S (Rn (n + N)) (q (n + N)) y tau < A
  exact hcost'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
