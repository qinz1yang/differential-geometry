import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.WeakConvergence
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Basic
import DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier

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

theorem chartH1_norm_bound_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτregularity : MapsTo τ (Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) {B : Real}
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (hkin : ∀ n, (∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) ≤ B) :
    ∃ C : Real, ∀ n, ‖u n‖ ≤ C := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hτregularity hr
  obtain ⟨c, hc, hcLower⟩ :=
    chartGramOp_lower_of_carrier (I := I) hG hJreg hJc alpha hKchart hKc
  obtain ⟨A, hA⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  have hinit (n : ℕ) : ‖(u n).initial‖ ≤ A := by
    apply hA
    refine ⟨(u n).initial, ?_, rfl⟩
    rw [← timeH1.toFun_zero]
    exact huK n ⟨0, ⟨le_refl 0, hL⟩⟩
  have hderiv (n : ℕ) : ‖(u n).deriv‖ ^ 2 ≤ B / (c / 2) := by
    let Aop : Real → E →L[Real] E := fun r ↦
      chartGramOp (I := I) G alpha (τ r, (u n).toFun r)
    have hpair : ContinuousOn
        (fun r ↦ (τ r, (u n).toFun r)) (Icc (0 : Real) L) :=
      hτc.prodMk (u n).continuousOn_toFun
    have hAcont : ContinuousOn Aop (Icc (0 : Real) L) := by
      exact (chartGramOp_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart).comp
        hpair fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩
    have hAmeas : AEStronglyMeasurable Aop (timeMeasure L) := by
      simpa only [timeMeasure] using
        hAcont.aestronglyMeasurable measurableSet_Icc
    obtain ⟨C, hCraw⟩ :=
      chartGramOp_bound_of_carrier (I := I) hG hJreg hJc alpha hKchart hKc
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
  have hinitSq : ‖(u n).initial‖ ^ 2 ≤ A ^ 2 := by
    nlinarith [hinit n, norm_nonneg (u n).initial]
  have hsq : ‖u n‖ ^ 2 ≤ A ^ 2 + B / (c / 2) := by
    rw [timeH1.norm_sq_eq]
    exact add_le_add hinitSq (hderiv n)
  have hrad : 0 ≤ A ^ 2 + B / (c / 2) :=
    (sq_nonneg ‖u n‖).trans hsq
  dsimp only [C]
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (A ^ 2 + B / (c / 2)),
    norm_nonneg (u n)]

theorem chartH1_subseq_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτregularity : MapsTo τ (Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
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
  obtain ⟨C, hC⟩ := chartH1_norm_bound_of_carrier (I := I) hG alpha hL τ hτc hτregularity
    hKc hKchart u huK hkin
  obtain ⟨phi, uLim, hphi, hweak, huniform⟩ := timeH1.compact_subseq u hC
  refine ⟨phi, uLim, hphi, ?_, huniform⟩
  intro z
  have hz := hweak (timeH1.mk 0 z)
  simpa only [timeH1.inner_def, timeH1.initial_mk, timeH1.deriv_mk,
    inner_zero_right, zero_add] using hz

theorem chartH1_fin_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {m : ℕ} (p : Fin m → M) (L : Fin m → Real)
    (hL : ∀ i, 0 ≤ L i) (τ : (i : Fin m) → Real → Real)
    (hτc : ∀ i, ContinuousOn (τ i) (Icc (0 : Real) (L i)))
    (hτregularity : ∀ i, MapsTo (τ i) (Icc (0 : Real) (L i)) D.carrier)
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ (extChartAt I (p i)).target)
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
    chartH1_norm_bound_of_carrier (I := I) hG (p i) (hL i) (τ i) (hτc i) (hτregularity i)
      (hKc i) (hKchart i) (u i) (huK i) (hkin i)
  choose C hC using hbound
  exact timeH1.compact_subseq_fin L u C hC

end DifferentialGeometry.Geometry.Curvature
