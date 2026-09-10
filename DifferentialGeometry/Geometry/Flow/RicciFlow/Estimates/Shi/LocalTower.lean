import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceCutoff

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Bundle Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]



section Solution

variable [NeZero (Module.finrank Real E)] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

def shiFixedCutoffError (d : ℕ) (T r₁ r₂ Clap Cconn Hb : Real) : Real :=
  max (shiInitialCutoffA d T 1 r₁ r₂)
    (shiInitialCutoffB d T 1 r₁ r₂ Clap +
      shiInitialCutoffD r₁ r₂ Cconn * (2 * Real.sqrt T * Hb))


theorem shiFixedCutoffError_nonneg (d : ℕ) (T r₁ r₂ Clap Cconn Hb : Real) :
    0 ≤ shiFixedCutoffError d T r₁ r₂ Clap Cconn Hb :=
  le_trans (shiInitialCutoffA_nonneg _ _ _ _ _) (le_max_left _ _)

def ShiInitialDistanceCutoff.toFixedCutoff
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T r₁ r₂ A Bcst Dcoef : Real} {p : M} {Theta : Real → M → Real}
    (idc : ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A Bcst Dcoef Theta)
    (hA : 0 ≤ A) (hD : 0 ≤ Dcoef)
    {Hbound cn : Real} (hH : 0 ≤ Hbound) (hcn : 0 ≤ cn)
    (hRm1 : ∀ s ∈ Set.Ioc (0 : Real) T, ∀ y : M, 0 < idc.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 1 s y ≤ Hbound ^ 2 / s)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < idc.chi x →
      ∃ s ∈ Set.Ioc (0 : Real) t,
        Theta t x ≤ cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) :
    ShiFixedCutoff (I := I) (flowG (I := I) S) T
      (max A (Bcst + Dcoef * (cn * Hbound))) where
  chi := fun _ y => idc.chi y
  support := idc.support
  err_nonneg := le_trans hA (le_max_left _ _)
  support_compact := idc.support_compact
  support_zero := fun _ _ x hx => idc.support_zero x hx
  range := fun _ _ x => idc.chi_mem_Icc x
  joint_cont := (idc.chi_continuous.comp continuous_snd).continuousOn
  lower_support := by
    intro t ht htpos x hx
    have htIoc : t ∈ Set.Ioc (0 : Real) T := ⟨htpos, ht.2⟩
    obtain ⟨s, hs, hsle⟩ := hTheta t htIoc x hx
    have hsT : s ∈ Set.Ioc (0 : Real) T := ⟨hs.1, hs.2.trans ht.2⟩
    have hcurv1 := hRm1 s hsT x hx
    have hprod : s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x ≤ Hbound ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hcurv1 hs.1.le
      rwa [mul_div_cancel₀ (Hbound ^ 2) (ne_of_gt hs.1)] at hmul
    have hchi0 : 0 ≤ idc.chi x := (idc.chi_mem_Icc x).1
    have hchi1 : idc.chi x ≤ 1 := (idc.chi_mem_Icc x).2
    have hsqrt : Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) ≤ Hbound := by
      calc Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)
          ≤ Real.sqrt (Hbound ^ 2) := Real.sqrt_le_sqrt hprod
        _ = Hbound := Real.sqrt_sq hH
    have hThetaBound : Theta t x ≤ cn * Hbound :=
      hsle.trans (mul_le_mul_of_nonneg_left hsqrt hcn)
    have hsqrt_chi : Real.sqrt (idc.chi x) ≤ 1 := by
      have h := Real.sqrt_le_sqrt hchi1
      rwa [Real.sqrt_one] at h
    have hcoef0 : (0 : Real) ≤ Dcoef * Real.sqrt (idc.chi x) :=
      mul_nonneg hD (Real.sqrt_nonneg _)
    have hLam : Bcst + Dcoef * Real.sqrt (idc.chi x) * Theta t x ≤
        Bcst + Dcoef * (cn * Hbound) := by
      have hstep : Dcoef * Real.sqrt (idc.chi x) * Theta t x ≤
          Dcoef * (cn * Hbound) := by
        calc Dcoef * Real.sqrt (idc.chi x) * Theta t x
            ≤ Dcoef * Real.sqrt (idc.chi x) * (cn * Hbound) :=
              mul_le_mul_of_nonneg_left hThetaBound hcoef0
          _ ≤ Dcoef * (cn * Hbound) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hcn hH)
              calc Dcoef * Real.sqrt (idc.chi x) ≤ Dcoef * 1 :=
                    mul_le_mul_of_nonneg_left hsqrt_chi hD
                _ = Dcoef := mul_one _
      linarith only [hstep]
    exact ⟨(idc.lower_support t htIoc x hx).some.toCutoffLowerSupport
      (le_max_left _ _) (hLam.trans (le_max_right _ _)) hchi0⟩

variable [CompleteSpace E] [IsManifold I 2 M] [BoundarylessManifold I M]

omit [VectorBundle Real E (TangentSpace I : M → Type _)] in
theorem exists_shiFixedCutoff_ball_error_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T Ksec R r₁ r₂ Hb Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn (nablaRmSupWeight (I := I) S))
    (hHb0 : 0 ≤ Hb)
    (hHb : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₂ →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤ Hb / Real.sqrt t) :
    ∃ fc : ShiFixedCutoff (I := I) (flowG (I := I) S) T
        (shiFixedCutoffError (Module.finrank Real E) T r₁ r₂ Clap Cconn Hb),
      (∀ t : Real, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
          fc.chi t x = 1) ∧
      fc.support ⊆ {y : M |
        riemannianEDistOf (I := I) (S.base.metric 0) p y < ENNReal.ofReal r₂} := by
  classical
  have hslab : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier := by
    intro s hs
    exact ⟨le_trans halpha.le hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  have hIccReg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  obtain ⟨idc⟩ :=
    nonempty_shiInitialDistanceCutoff_of_solution (I := I) S hS (K := 1) p hT hslab
      (fun s hs => hIccReg ⟨hs.1.le, hs.2⟩) hball hKsec hsec hu hr₁ hr₁₂ hr₂R hClap
      hCconn (fun t y => nablaRmSupWeight_nonneg (I := I) S t y) hlap
  have hball : ∀ y : M, 0 < idc.chi y →
      riemannianEDistOf (I := I) (S.base.metric 0) p y < ENNReal.ofReal r₂ := by
    intro y hy
    refine idc.support_subset_ball ?_
    by_contra hns
    rw [idc.support_zero y hns] at hy
    exact lt_irrefl 0 hy
  have hRm1 : ∀ s ∈ Set.Ioc (0 : Real) T, ∀ y : M, 0 < idc.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 1 s y ≤ Hb ^ 2 / s := by
    intro s hs y hy
    have hb := hHb s hs y (le_of_lt (hball y hy))
    have hw0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 s y :=
      nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 s y
    have hmono :
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y)) ^ 2 ≤
          (Hb / Real.sqrt s) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    rw [Real.sq_sqrt hw0, div_pow, Real.sq_sqrt hs.1.le] at hmono
    exact hmono
  have hThetaAtt : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < idc.chi x →
      ∃ s ∈ Set.Ioc (0 : Real) t,
        nablaRmSupWeight (I := I) S t x ≤
          2 * Real.sqrt T *
            Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := by
    intro t ht x _
    have hsub : Set.Icc (0 : Real) t ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular :=
      fun s hs => hIccReg ⟨hs.1, hs.2.trans ht.2⟩
    obtain ⟨s, hs, hle⟩ := exists_mem_Icc_nablaRmSupWeight_le (I := I) S ht.1.le ht.2 x
      (continuousOn_nablaKRm04NormSqIntrinsic_of_subset_regular (I := I) hS 1 hsub x)
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · refine ⟨t, ⟨ht.1, le_rfl⟩, ?_⟩
      rw [← h0] at hle
      have hzero : nablaRmSupWeight (I := I) S t x ≤ 0 := by simpa using hle
      have hnn : 0 ≤ 2 * Real.sqrt T *
          Real.sqrt (t * nablaKRm04NormSqIntrinsic (I := I) S 1 t x) := by positivity
      linarith
    · exact ⟨s, ⟨hpos, hs.2⟩, hle⟩
  refine ⟨idc.toFixedCutoff (shiInitialCutoffA_nonneg _ _ _ _ _)
    (shiInitialCutoffD_nonneg hr₁₂.le hCconn) hHb0 (by positivity) hRm1 hThetaAtt,
    ?_, ?_⟩
  · intro t x hx
    exact idc.chi_eq_one x hx
  · exact idc.support_subset_ball

omit [VectorBundle Real E (TangentSpace I : M → Type _)] in
theorem exists_shiFixedCutoff_ball_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T Ksec R r₁ r₂ Hb Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn (nablaRmSupWeight (I := I) S))
    (hHb0 : 0 ≤ Hb)
    (hHb : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₂ →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤ Hb / Real.sqrt t) :
    ∃ (e : Real) (fc : ShiFixedCutoff (I := I) (flowG (I := I) S) T e), 0 ≤ e ∧
      (∀ t : Real, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
          fc.chi t x = 1) ∧
      fc.support ⊆ {y : M |
        riemannianEDistOf (I := I) (S.base.metric 0) p y < ENNReal.ofReal r₂} := by
  obtain ⟨fc, hone, hsupp⟩ :=
    exists_shiFixedCutoff_ball_error_of_solution (I := I) S hS (R := R) p halpha hT
      hTomega hball hKsec hsec hu hr₁ hr₁₂ hr₂R hClap hCconn hlap hHb0 hHb
  exact ⟨_, fc, shiFixedCutoffError_nonneg _ _ _ _ _ _ _, hone, hsupp⟩



def shiLocalRadius (R : Real) (j : ℕ) : Real := R / 2 + R / 2 ^ (j + 2)


theorem shiLocalRadius_zero (R : Real) : shiLocalRadius R 0 = 3 * R / 4 := by
  rw [shiLocalRadius]
  norm_num
  ring


theorem half_lt_shiLocalRadius {R : Real} (hR : 0 < R) (j : ℕ) :
    R / 2 < shiLocalRadius R j := by
  have hpos : 0 < R / 2 ^ (j + 2) := by positivity
  rw [shiLocalRadius]
  linarith


theorem shiLocalRadius_le {R : Real} (hR : 0 < R) (j : ℕ) : shiLocalRadius R j ≤ R := by
  have h2 : (2 : Real) ≤ 2 ^ (j + 2) := by
    calc (2 : Real) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : R / 2 ^ (j + 2) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) h2
  rw [shiLocalRadius]
  linarith


theorem shiLocalRadius_pos {R : Real} (hR : 0 < R) (j : ℕ) : 0 < shiLocalRadius R j :=
  lt_trans (by linarith) (half_lt_shiLocalRadius hR j)


theorem shiLocalRadius_antitone {R : Real} (hR : 0 < R) : Antitone (shiLocalRadius R) := by
  intro i j hij
  have hpow : (2 : Real) ^ (i + 2) ≤ 2 ^ (j + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : R / 2 ^ (j + 2) ≤ R / 2 ^ (i + 2) :=
    div_le_div_of_nonneg_left hR.le (by positivity) hpow
  rw [shiLocalRadius, shiLocalRadius]
  linarith


theorem shiLocalRadius_succ_lt {R : Real} (hR : 0 < R) (j : ℕ) :
    shiLocalRadius R (j + 1) < shiLocalRadius R j := by
  have hpow : (2 : Real) ^ (j + 2) < 2 ^ (j + 1 + 2) := by
    apply pow_lt_pow_right₀ (by norm_num) (by omega)
  have hlt : R / 2 ^ (j + 1 + 2) < R / 2 ^ (j + 2) :=
    div_lt_div_of_pos_left hR (by positivity) hpow
  rw [shiLocalRadius, shiLocalRadius]
  linarith

omit [I.Boundaryless] [VectorBundle Real E (TangentSpace I : M → Type _)]
  [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem shi_local_all_orders_unnormalized_of_normalized
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T K R C : Real} {m : ℕ} (p : M)
    (hK : 0 < K) (h0 : (0 : Real) ∈ D.carrier)
    (hnorm : ∀ s ∈ Set.Ioc (0 : Real) (K * T), ∀ x : M,
      riemannianEDistOf (I := I)
          ((parabolicSolution (I := I) S 0 K hK h0).base.metric 0) p x ≤
            ENNReal.ofReal (R / 2) →
        Real.sqrt (s ^ m * nablaKRm04NormSqIntrinsic (I := I)
          (parabolicSolution (I := I) S 0 K hK h0) m s x) ≤ C) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (R / (2 * Real.sqrt K)) →
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C * K := by
  intro t ht x hball
  have hKne : K ≠ 0 := ne_of_gt hK
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have hsqK : (0 : Real) < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsqKne : Real.sqrt K ≠ 0 := ne_of_gt hsqK
  have hKt : K * t ∈ Set.Ioc (0 : Real) (K * T) :=
    ⟨mul_pos hK ht.1, mul_le_mul_of_nonneg_left ht.2 hK.le⟩
  have hmetric : (parabolicSolution (I := I) S 0 K hK h0).base.metric 0 =
      scaleMetric (I := I) K hK (S.base.metric 0) := by
    have h := congrFun (parabolicSolution_metric (I := I) S 0 K hK h0) 0
    rw [h, parabolicTime_zero]
  have hball' : riemannianEDistOf (I := I)
      ((parabolicSolution (I := I) S 0 K hK h0).base.metric 0) p x ≤
        ENNReal.ofReal (R / 2) := by
    rw [hmetric, edistOf_scale K hK (S.base.metric 0) p x]
    calc ENNReal.ofReal (Real.sqrt K) *
          riemannianEDistOf (I := I) (S.base.metric 0) p x
        ≤ ENNReal.ofReal (Real.sqrt K) *
            ENNReal.ofReal (R / (2 * Real.sqrt K)) := mul_le_mul' le_rfl hball
      _ = ENNReal.ofReal (R / 2) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg K)]
          congr 1
          field_simp
  have hkey := hnorm (K * t) hKt x hball'
  have hptime : parabolicTime 0 K (K * t) = t := by
    unfold parabolicTime
    field_simp
    ring
  rw [parabolicNablaKRmNormSq (I := I) S 0 K hK h0 m (K * t) x, hptime] at hkey
  have hcancel : K ^ m * (K⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hKne, one_pow]
  have hrw : (K * t) ^ m *
        ((K⁻¹) ^ (2 + m) * nablaKRm04NormSqIntrinsic (I := I) S m t x) =
      (K⁻¹) ^ 2 * (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) := by
    calc (K * t) ^ m *
          ((K⁻¹) ^ (2 + m) * nablaKRm04NormSqIntrinsic (I := I) S m t x)
        = (K ^ m * (K⁻¹) ^ m) *
            ((K⁻¹) ^ 2 * (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x)) := by
          rw [mul_pow, pow_add]
          ring
      _ = (K⁻¹) ^ 2 * (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) := by
          rw [hcancel, one_mul]
  rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq hKinv.le] at hkey
  have hscaled := mul_le_mul_of_nonneg_left hkey hK.le
  rw [← mul_assoc, mul_inv_cancel₀ hKne, one_mul] at hscaled
  linarith

end Solution

end DifferentialGeometry.PDE.RicciFlow

end
