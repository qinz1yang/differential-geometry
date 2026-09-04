import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.WeakConvergence
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Basic
import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold Topology ContDiff Interval

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartKin_liminf {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) L, uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E L,
      Tendsto (fun n ↦ inner Real (u n).deriv z) atTop
        (nhds (inner Real uLim.deriv z))) :
    (∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G alpha (τ r, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) ≤
      liminf (fun n ↦ ∫ r in (0 : Real)..L,
        (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
          ((u n).deriv r)) atTop := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  let A : ℕ → Real → E →L[Real] E := fun n r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G alpha (τ r, (u n).toFun r)
  let ALim : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G alpha (τ r, uLim.toFun r)
  have hpair (n : ℕ) : ContinuousOn
      (fun r ↦ (τ r, (u n).toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk (u n).continuousOn_toFun
  have hpairLim : ContinuousOn
      (fun r ↦ (τ r, uLim.toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk uLim.continuousOn_toFun
  have hAcont (n : ℕ) : ContinuousOn (A n) (Icc (0 : Real) L) := by
    dsimp only [A]
    exact ((chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
      (hpair n) fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩).const_smul (1 / 2 : Real)
  have hALimCont : ContinuousOn ALim (Icc (0 : Real) L) := by
    dsimp only [ALim]
    exact ((chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
      hpairLim fun r hr ↦ ⟨⟨r, hr, rfl⟩, huLimK ⟨r, hr⟩⟩).const_smul (1 / 2 : Real)
  have hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure L) := fun n ↦ by
    simpa only [timeMeasure] using
      (hAcont n).aestronglyMeasurable measurableSet_Icc
  have hALim : AEStronglyMeasurable ALim (timeMeasure L) := by
    simpa only [timeMeasure] using
      hALimCont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hG hJreg hJc alpha hKchart hKc
  have hC : ∀ n, ∀ᵐ r ∂timeMeasure L, ‖A n r‖ ≤ (C : Real) := fun n ↦ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (τ r, (u n).toFun r) ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hCLim : ∀ᵐ r ∂timeMeasure L, ‖ALim r‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [ALim]
    rw [norm_smul]
    have hb := hCraw (τ r, uLim.toFun r) ⟨⟨r, hr, rfl⟩, huLimK ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hGramUnif : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦
        chartGramOp (I := I) G alpha (τ r.1, (u n).toFun r.1))
      (fun r ↦ chartGramOp (I := I) G alpha (τ r.1, uLim.toFun r.1)) atTop :=
    chartGramOp_unif (I := I) hG hJreg hJc alpha hKchart hKc
      (fun r ↦ ⟨r.1, r.2, rfl⟩) (Eventually.of_forall huK) huLimK hu
  have hconv : ∀ δ : Real, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ r ∂timeMeasure L, ‖A n r - ALim r‖ ≤ δ := by
    intro δ hδ
    have hev := (Metric.tendstoUniformly_iff.1 hGramUnif) (2 * δ) (by positivity)
    filter_upwards [hev] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hraw := hn ⟨r, hr⟩
    have hraw' :
        ‖chartGramOp (I := I) G alpha (τ r, (u n).toFun r) -
          chartGramOp (I := I) G alpha (τ r, uLim.toFun r)‖ < 2 * δ := by
      simpa only [dist_eq_norm, norm_sub_rev] using hraw
    have hscaled : (1 / 2 : Real) *
        ‖chartGramOp (I := I) G alpha (τ r, (u n).toFun r) -
          chartGramOp (I := I) G alpha (τ r, uLim.toFun r)‖ < δ := by
      linarith
    dsimp only [A, ALim]
    rw [← smul_sub, norm_smul]
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact hscaled.le
  have hself : ∀ n, ∀ᵐ r ∂timeMeasure L, IsSelfAdjoint (A n r) := fun n ↦
    Eventually.of_forall fun r ↦ by
      exact (IsSelfAdjoint.all (1 / 2 : Real)).smul
        (chartGramOp_self (I := I) G alpha (τ r, (u n).toFun r))
  have hpos : ∀ n, ∀ᵐ r ∂timeMeasure L, ∀ x,
      0 ≤ inner Real (A n r x) x := fun n ↦ Eventually.of_forall fun r x ↦ by
    dsimp only [A]
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) G alpha (τ r, (u n).toFun r) x)
  have hq := timeQuad_weak_unif A ALim hA hALim (fun _ ↦ C) C hC hCLim hconv
    hself hpos (fun n ↦ (u n).deriv) uLim.deriv hdu
  have hlimEq := timeQuad_eq_integral ALim hALim C hCLim hL uLim.deriv
  have hseqEq :
      (fun n ↦ timeQuad (A n) (hA n) C (hC n) (u n).deriv) =
        (fun n ↦ ∫ r in (0 : Real)..L,
          inner Real (A n r ((u n).deriv r)) ((u n).deriv r)) := by
    funext n
    exact timeQuad_eq_integral (A n) (hA n) C (hC n) hL (u n).deriv
  rw [hlimEq, hseqEq] at hq
  dsimp only [A, ALim] at hq
  simpa only [smul_apply, real_inner_smul_left] using hq

theorem chartH1_norm_bound {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) {B : Real}
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (hkin : ∀ n, (∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) ≤ B) :
    ∃ C : Real, ∀ n, ‖u n‖ ≤ C := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  obtain ⟨c, hc, hcLower⟩ :=
    chartGramOp_lower (I := I) hG hJreg hJc alpha hKchart hKc
  obtain ⟨A, hA⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  have hinit (n : ℕ) : ‖(u n).init‖ ≤ A := by
    apply hA
    refine ⟨(u n).init, ?_, rfl⟩
    rw [← timeH1.toFun_zero]
    exact huK n ⟨0, ⟨le_refl 0, hL⟩⟩
  have hderiv (n : ℕ) : ‖(u n).deriv‖ ^ 2 ≤ B / (c / 2) := by
    let Aop : Real → E →L[Real] E := fun r ↦
      chartGramOp (I := I) G alpha (τ r, (u n).toFun r)
    have hpair : ContinuousOn
        (fun r ↦ (τ r, (u n).toFun r)) (Icc (0 : Real) L) :=
      hτc.prodMk (u n).continuousOn_toFun
    have hAcont : ContinuousOn Aop (Icc (0 : Real) L) := by
      exact (chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
        hpair fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩
    have hAmeas : AEStronglyMeasurable Aop (timeMeasure L) := by
      simpa only [timeMeasure] using
        hAcont.aestronglyMeasurable measurableSet_Icc
    obtain ⟨C, hCraw⟩ :=
      chartGramOp_bound (I := I) hG hJreg hJc alpha hKchart hKc
    have hC : ∀ᵐ r ∂timeMeasure L, ‖Aop r‖ ≤ (C : Real) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hCraw (τ r, (u n).toFun r)
        ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩
    have hnormInt : IntervalIntegrable
        (fun r ↦ ‖(u n).deriv r‖ ^ 2) volume 0 L := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
      change Integrable (fun r ↦ ‖(u n).deriv r‖ ^ 2) (timeMeasure L)
      simpa only [real_inner_self_eq_norm_sq] using
        (MeasureTheory.L2.integrable_inner (𝕜 := Real) (u n).deriv (u n).deriv)
    have hkinInt : IntervalIntegrable
        (fun r ↦ (1 / 2 : Real) *
          inner Real (Aop r ((u n).deriv r)) ((u n).deriv r)) volume 0 L := by
      exact (timeQuad_int Aop hAmeas C hC hL (u n).deriv).const_mul (1 / 2 : Real)
    have hmono :
        (∫ r in (0 : Real)..L, (c / 2) * ‖(u n).deriv r‖ ^ 2) ≤
          ∫ r in (0 : Real)..L, (1 / 2 : Real) *
            inner Real (Aop r ((u n).deriv r)) ((u n).deriv r) := by
      refine intervalIntegral.integral_mono_on hL
        (hnormInt.const_mul (c / 2)) hkinInt ?_
      intro r hr
      dsimp only [Aop]
      calc
        (c / 2) * ‖(u n).deriv r‖ ^ 2 =
            (1 / 2 : Real) * (c * ‖(u n).deriv r‖ ^ 2) := by ring
        _ ≤ (1 / 2 : Real) * inner Real
            (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
            ((u n).deriv r) :=
          mul_le_mul_of_nonneg_left
            (hcLower (τ r, (u n).toFun r)
              ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩ ((u n).deriv r)) (by norm_num)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hnormEq :
        (∫ r in (0 : Real)..L, ‖(u n).deriv r‖ ^ 2) = ‖(u n).deriv‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hL,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← norm_sq_eq_integral]
    rw [hnormEq] at hmono
    exact (le_div_iff₀' (by positivity : 0 < c / 2)).2 (hmono.trans (hkin n))
  let C : Real := Real.sqrt (A ^ 2 + B / (c / 2))
  refine ⟨C, fun n ↦ ?_⟩
  have hinitSq : ‖(u n).init‖ ^ 2 ≤ A ^ 2 := by
    nlinarith [hinit n, norm_nonneg (u n).init]
  have hsq : ‖u n‖ ^ 2 ≤ A ^ 2 + B / (c / 2) := by
    rw [timeH1.norm_sq_eq]
    exact add_le_add hinitSq (hderiv n)
  have hrad : 0 ≤ A ^ 2 + B / (c / 2) :=
    (sq_nonneg ‖u n‖).trans hsq
  dsimp only [C]
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (A ^ 2 + B / (c / 2)),
    norm_nonneg (u n)]

theorem chartH1_subseq {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) {B : Real}
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (hkin : ∀ n, (∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) ≤ B) :
    ∃ (phi : ℕ → ℕ) (uLim : timeH1 E L),
      StrictMono phi ∧
        (∀ z : timeL2 E L,
          Tendsto (fun n ↦ inner Real (u (phi n)).deriv z) atTop
            (nhds (inner Real uLim.deriv z))) ∧
        TendstoUniformly
          (fun n (r : Icc (0 : Real) L) ↦ (u (phi n)).toFun r.1)
          (fun r ↦ uLim.toFun r.1) atTop := by
  obtain ⟨C, hC⟩ := chartH1_norm_bound (I := I) hG alpha hL τ hτc hτreg
    hKc hKchart u huK hkin
  obtain ⟨phi, uLim, hphi, hweak, hunif⟩ := timeH1.compact_subseq u hC
  refine ⟨phi, uLim, hphi, ?_, hunif⟩
  intro z
  have hz := hweak (timeH1.mk 0 z)
  simpa only [timeH1.inner_def, timeH1.init_mk, timeH1.deriv_mk,
    inner_zero_right, zero_add] using hz

theorem chartH1_fin {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {m : ℕ} (p : Fin m → M) (L : Fin m → Real)
    (hL : ∀ i, 0 ≤ L i) (τ : (i : Fin m) → Real → Real)
    (hτc : ∀ i, ContinuousOn (τ i) (Icc (0 : Real) (L i)))
    (hτreg : ∀ i, MapsTo (τ i) (Icc (0 : Real) (L i)) D.regular)
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (u : (i : Fin m) → ℕ → timeH1 E (L i)) (B : Fin m → Real)
    (huK : ∀ i n (r : Icc (0 : Real) (L i)), (u i n).toFun r.1 ∈ K i)
    (hkin : ∀ i n, (∫ r in (0 : Real)..L i,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G (p i) (τ i r, (u i n).toFun r) ((u i n).deriv r))
        ((u i n).deriv r)) ≤ B i) :
    ∃ (phi : ℕ → ℕ) (uLim : (i : Fin m) → timeH1 E (L i)),
      StrictMono phi ∧
        (∀ i (z : timeL2 E (L i)),
          Tendsto (fun n ↦ inner Real (u i (phi n)).deriv z) atTop
            (nhds (inner Real (uLim i).deriv z))) ∧
        (∀ i, TendstoUniformly
          (fun n (r : Icc (0 : Real) (L i)) ↦ (u i (phi n)).toFun r.1)
          (fun r ↦ (uLim i).toFun r.1) atTop) := by
  have hbound : ∀ i, ∃ C : Real, ∀ n, ‖u i n‖ ≤ C := fun i =>
    chartH1_norm_bound (I := I) hG (p i) (hL i) (τ i) (hτc i) (hτreg i)
      (hKc i) (hKchart i) (u i) (huK i) (hkin i)
  choose C hC using hbound
  exact timeH1.compact_subseq_fin L u C hC

end DifferentialGeometry.Geometry.Curvature
