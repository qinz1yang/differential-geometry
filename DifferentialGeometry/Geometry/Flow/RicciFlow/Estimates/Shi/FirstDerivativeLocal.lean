import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.BernsteinMaximumSelfCoupled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.FirstDerivativeReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology Bundle

section Constants

def shiFirstDerivativeCoupling (a cn : Real) : Real := cn / Real.sqrt a

def shiFirstDerivativeLocalBound (d : Nat) (a T A B Dcoef cn : Real) : Real :=
  Real.sqrt
    (bernsteinSelfCoupledBound (shiFirstTimeCoeff a) (shiFirstTimeConst d a T)
      A B Dcoef (shiFirstDerivativeCoupling a cn) T / a)


theorem shiFirstDerivativeLocalBound_nonneg (d : Nat) (a T A B Dcoef cn : Real) :
    0 ≤ shiFirstDerivativeLocalBound d a T A B Dcoef cn :=
  Real.sqrt_nonneg _

def shiFirstDerivativeLocalConst (d : Nat) (a T r₁ r₂ Clap Cconn cn : Real) : Real :=
  shiFirstDerivativeLocalBound d a T (shiInitialCutoffA d T 1 r₁ r₂)
    (shiInitialCutoffB d T 1 r₁ r₂ Clap) (shiInitialCutoffD r₁ r₂ Cconn) cn


theorem shiFirstDerivativeLocalConst_nonneg
    (d : Nat) (a T r₁ r₂ Clap Cconn cn : Real) :
    0 ≤ shiFirstDerivativeLocalConst d a T r₁ r₂ Clap Cconn cn :=
  shiFirstDerivativeLocalBound_nonneg _ _ _ _ _ _ _

end Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

theorem shiFirstDerivative_local_of_cutoff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T a A B Dcoef cn r₁ r₂ : Real} {p : M} {Theta : Real → M → Real}
    (cut : ShiInitialDistanceCutoff (I := I) S T p r₁ r₂ A B Dcoef Theta)
    (hT : 0 < T) (ha : 32 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ Dcoef) (hcn : 0 ≤ cn)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M, 0 < cut.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hcont : ContinuousOn
      (fun q : Real × M => shiFirstBernsteinTimeQuantity (I := I) S a q.1 q.2)
      (spacetimeSlab (M := M) T))
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, 0 < cut.chi x →
      ∃ s ∈ Set.Icc (0 : Real) t,
        Theta t x ≤
          cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
          shiFirstDerivativeLocalBound (Module.finrank Real E) a T A B Dcoef cn /
            Real.sqrt t := by
  have hapos : (0 : Real) < a := by linarith
  have hsqa : (0 : Real) < Real.sqrt a := Real.sqrt_pos.mpr hapos
  have hcoup : shiFirstDerivativeCoupling a cn = cn / Real.sqrt a := rfl
  have hkappa : 0 ≤ shiFirstDerivativeCoupling a cn := by
    rw [hcoup]
    exact div_nonneg hcn hsqa.le
  have hTheta' : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      0 < (cut.toSelfCoupledCutoff).chi x →
        ∃ s ∈ Set.Icc (0 : Real) t,
          Theta t x ≤ shiFirstDerivativeCoupling a cn *
            Real.sqrt (shiFirstBernsteinTimeQuantity (I := I) S a s x) := by
    intro t ht x hx
    have hx' : 0 < cut.chi x := hx
    obtain ⟨s, hs, hle⟩ := hTheta t ht x hx'
    refine ⟨s, hs, ?_⟩
    have hv := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 s x
    have hu0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 s x
    have hs0 : (0 : Real) ≤ s := hs.1
    have hGeq : shiFirstBernsteinTimeQuantity (I := I) S a s x =
        s * ((a + nablaKRm04NormSqIntrinsic (I := I) S 0 s x) *
          nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := rfl
    have hcmp : a * (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) ≤
        shiFirstBernsteinTimeQuantity (I := I) S a s x := by
      rw [hGeq]
      nlinarith [mul_nonneg (mul_nonneg hs0 hu0) hv]
    have hroot : Real.sqrt a *
        Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) ≤
          Real.sqrt (shiFirstBernsteinTimeQuantity (I := I) S a s x) := by
      rw [← Real.sqrt_mul hapos.le]
      exact Real.sqrt_le_sqrt hcmp
    have hmul := mul_le_mul_of_nonneg_left hroot (div_nonneg hcn hsqa.le)
    have hid : cn / Real.sqrt a *
        (Real.sqrt a *
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) =
        cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := by
      field_simp
    rw [hid] at hmul
    rw [hcoup]
    linarith
  have hmax := bernstein_maximum_of_selfCoupled_cutoff (I := I)
    (kappa := shiFirstDerivativeCoupling a cn) (cut.toSelfCoupledCutoff)
    (shiFirstBernsteinTimeQuantity (I := I) S a) hT (shiFirstTimeCoeff_pos ha)
    (shiFirstTimeConst_nonneg ha (Module.finrank Real E) T) hA hB hD hkappa
    (fun s hs y => shiFirstBernsteinTimeQuantity_nonneg (I := I) S
      (by linarith : (0 : Real) ≤ a) hs.1 y)
    (fun y => shiFirstBernsteinTimeQuantity_zero (I := I) S a y) hcont
    (fun s hs _ y =>
      (differentiableAt_shiFirstBernsteinTimeQuantity (I := I) S hS a
        (hreg hs) y).differentiableWithinAt)
    (fun s _ _ y =>
      (contMDiff_shiFirstBernsteinTimeQuantity (I := I) S a
        s).contMDiffAt.mdifferentiableAt (by simp))
    (fun s _ _ y =>
      gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric s)
        (contMDiff_shiFirstBernsteinTimeQuantity (I := I) S a s) y)
    (fun s hs hspos y hy =>
      parabolicOperatorWithDrift_shiFirstBernsteinTimeQuantity_le
        (I := I) S hS hT ha hreg hs hspos y (hu s hs y hy))
    hTheta'
  intro t ht x hball
  have htmem : t ∈ Set.Icc (0 : Real) T := ⟨ht.1.le, ht.2⟩
  have hbound := hmax t htmem x
  have hscx : (cut.toSelfCoupledCutoff).chi x = 1 := cut.chi_eq_one x hball
  rw [hscx, one_mul] at hbound
  have hv := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have hu0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
  have hGeq : shiFirstBernsteinTimeQuantity (I := I) S a t x =
      t * ((a + nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x) := rfl
  rw [hGeq] at hbound
  have hkey : nablaKRm04NormSqIntrinsic (I := I) S 1 t x * t ≤
      bernsteinSelfCoupledBound (shiFirstTimeCoeff a)
          (shiFirstTimeConst (Module.finrank Real E) a T) A B Dcoef
          (shiFirstDerivativeCoupling a cn) T / a := by
    rw [le_div_iff₀ hapos]
    nlinarith [mul_nonneg (mul_nonneg ht.1.le hu0) hv]
  have hbnd : shiFirstDerivativeLocalBound (Module.finrank Real E) a T A B Dcoef cn =
      Real.sqrt
        (bernsteinSelfCoupledBound (shiFirstTimeCoeff a)
          (shiFirstTimeConst (Module.finrank Real E) a T) A B Dcoef
          (shiFirstDerivativeCoupling a cn) T / a) := rfl
  rw [hbnd, le_div_iff₀ (Real.sqrt_pos.mpr ht.1), ← Real.sqrt_mul hv]
  exact Real.sqrt_le_sqrt hkey

section CutoffProduction

variable [SigmaCompactSpace M]

theorem shiFirstDerivative_local_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T a cn Ksec R r₁ r₂ Clap Cconn : Real} (p : M) {Theta : Real → M → Real}
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (ha : 32 ≤ a)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn) (hcn : 0 ≤ cn)
    (hThetaNonneg : ∀ t : Real, ∀ y : M, 0 ≤ Theta t y)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn Theta)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      ∃ s ∈ Set.Icc (0 : Real) t,
        Theta t x ≤
          cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
          shiFirstDerivativeLocalConst (Module.finrank Real E) a T r₁ r₂ Clap Cconn cn /
            Real.sqrt t := by
  have hreg : Set.Icc 0 T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  have hslab : Set.Icc 0 T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
    hreg.trans (RealTimeInterval.closedOpen alpha omega halphaomega).regular_subset
  obtain ⟨cut⟩ :=
    nonempty_shiInitialDistanceCutoff_of_solution (I := I) S hS (K := 1) (r₂ := r₂) p hT
      hslab (fun s hs => hreg ⟨hs.1.le, hs.2⟩) hball hKsec hsec hu hr₁ hr₁₂ hr₂R hClap
      hCconn hThetaNonneg hlap
  have huc : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M, 0 < cut.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1 := by
    intro s hs y hy
    refine hu s hs y ?_
    have hsupp : y ∈ cut.support := by
      by_contra hns
      rw [cut.support_zero y hns] at hy
      exact lt_irrefl 0 hy
    have hlt : riemannianEDistOf (I := I) (S.base.metric 0) p y <
        ENNReal.ofReal r₂ := cut.support_subset_ball hsupp
    exact hlt.le.trans (ENNReal.ofReal_le_ofReal hr₂R)
  exact shiFirstDerivative_local_of_cutoff (I := I) S hS cut hT ha
    (shiInitialCutoffA_nonneg _ _ _ _ _)
    (shiInitialCutoffB_nonneg _ hr₁₂.le hClap)
    (shiInitialCutoffD_nonneg hr₁₂.le hCconn) hcn hreg huc
    (continuousOn_shiFirstBernsteinTimeQuantity (I := I) (a := a) hS halpha hTomega)
    (fun t ht x _ => hTheta t ht x)

theorem exists_shiFirstDerivative_local_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T a cn Ksec R r₁ r₂ Clap Cconn : Real} (p : M) {Theta : Real → M → Real}
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (ha : 32 ≤ a)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn) (hcn : 0 ≤ cn)
    (hThetaNonneg : ∀ t : Real, ∀ y : M, 0 ≤ Theta t y)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn Theta)
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      ∃ s ∈ Set.Icc (0 : Real) t,
        Theta t x ≤
          cn * Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
            C / Real.sqrt t :=
  ⟨shiFirstDerivativeLocalConst (Module.finrank Real E) a T r₁ r₂ Clap Cconn cn,
    shiFirstDerivativeLocalConst_nonneg _ _ _ _ _ _ _ _,
    shiFirstDerivative_local_of_solution (I := I) S hS p halpha hT hTomega ha hball
      hKsec hsec hu hr₁ hr₁₂ hr₂R hClap hCconn hcn hThetaNonneg hlap hTheta⟩

end CutoffProduction

section Unnormalized

theorem shiFirstDerivative_local_unnormalized_of_cutoff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K a A B Dcoef cn r₁ r₂ : Real} {p : M} {Theta : Real → M → Real}
    (hK : 0 < K) (h0 : (0 : Real) ∈ D.carrier)
    (cut : ShiInitialDistanceCutoff (I := I)
      (parabolicSolution (I := I) S 0 K hK h0) (K * T) p r₁ r₂ A B Dcoef Theta)
    (hT : 0 < T) (ha : 32 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ Dcoef) (hcn : 0 ≤ cn)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M, 0 < cut.chi y →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2)
    (hcont : ContinuousOn
      (fun q : Real × M => shiFirstBernsteinTimeQuantity (I := I)
        (parabolicSolution (I := I) S 0 K hK h0) a q.1 q.2)
      (spacetimeSlab (M := M) (K * T)))
    (hTheta : ∀ t ∈ Set.Ioc (0 : Real) (K * T), ∀ x : M, 0 < cut.chi x →
      ∃ s ∈ Set.Icc (0 : Real) t,
        Theta t x ≤ cn * Real.sqrt (s *
          nablaKRm04NormSqIntrinsic (I := I)
            (parabolicSolution (I := I) S 0 K hK h0) 1 s x)) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (r₁ / Real.sqrt K) →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
          shiFirstDerivativeLocalBound (Module.finrank Real E) a (K * T)
              A B Dcoef cn * K / Real.sqrt t := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have hsqK : (0 : Real) < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hKT : (0 : Real) < K * T := mul_pos hK hT
  have hparaMem : ∀ s ∈ Set.Icc (0 : Real) (K * T),
      parabolicTime 0 K s ∈ Set.Icc (0 : Real) T := by
    intro s hs
    have hpt : parabolicTime 0 K s = s / K := by
      unfold parabolicTime
      ring
    rw [hpt]
    refine ⟨div_nonneg hs.1 hK.le, ?_⟩
    rw [div_le_iff₀ hK]
    linarith [hs.2]
  have hregp : Set.Icc (0 : Real) (K * T) ⊆
      (parabolicInterval D 0 K h0).regular := fun s hs => hreg (hparaMem s hs)
  have hup : ∀ s ∈ Set.Icc (0 : Real) (K * T), ∀ y : M, 0 < cut.chi y →
      nablaKRm04NormSqIntrinsic (I := I)
        (parabolicSolution (I := I) S 0 K hK h0) 0 s y ≤ 1 := by
    intro s hs y hy
    have hexp0 : (2 + 0 : Nat) = 2 := rfl
    rw [parabolicNablaKRmNormSq (I := I) S 0 K hK h0 0 s y, hexp0]
    have hb := hu (parabolicTime 0 K s) (hparaMem s hs) y hy
    have hid : ((K⁻¹ : Real) ^ 2) * K ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hKne, one_pow]
    have hp2 : (0 : Real) < (K⁻¹ : Real) ^ 2 := pow_pos hKinv 2
    nlinarith [hb, hp2, hid]
  have hmain := shiFirstDerivative_local_of_cutoff (I := I)
    (parabolicSolution (I := I) S 0 K hK h0) (parabolicSolution_isSolutionOn (I := I) S hS 0 K hK h0) cut
    hKT ha hA hB hD hcn hregp hup hcont hTheta
  intro t ht x hball
  have hKt : K * t ∈ Set.Ioc (0 : Real) (K * T) :=
    ⟨mul_pos hK ht.1, mul_le_mul_of_nonneg_left ht.2 hK.le⟩
  have hmetric : (parabolicSolution (I := I) S 0 K hK h0).base.metric 0 =
      scaleMetric (I := I) K hK (S.base.metric 0) := by
    have h := congrFun (parabolicSolution_metric (I := I) S 0 K hK h0) 0
    rw [h, parabolicTime_zero]
  have hball' : riemannianEDistOf (I := I)
      ((parabolicSolution (I := I) S 0 K hK h0).base.metric 0) p x ≤
        ENNReal.ofReal r₁ := by
    rw [hmetric, edistOf_scale K hK (S.base.metric 0) p x]
    calc ENNReal.ofReal (Real.sqrt K) *
          riemannianEDistOf (I := I) (S.base.metric 0) p x
        ≤ ENNReal.ofReal (Real.sqrt K) *
            ENNReal.ofReal (r₁ / Real.sqrt K) := mul_le_mul' le_rfl hball
      _ = ENNReal.ofReal r₁ := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg K)]
          congr 1
          field_simp
  have hkey := hmain (K * t) hKt x hball'
  have hexp1 : (2 + 1 : Nat) = 3 := rfl
  have hptime : parabolicTime 0 K (K * t) = t := by
    unfold parabolicTime
    field_simp
    ring
  rw [parabolicNablaKRmNormSq (I := I) S 0 K hK h0 1 (K * t) x, hexp1, hptime] at hkey
  have hv := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have hp3 : (0 : Real) < (K⁻¹ : Real) ^ 3 := pow_pos hKinv 3
  have hsplit : Real.sqrt ((K⁻¹ : Real) ^ 3 *
      nablaKRm04NormSqIntrinsic (I := I) S 1 t x) =
      Real.sqrt ((K⁻¹ : Real) ^ 3) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) :=
    Real.sqrt_mul hp3.le _
  have hcalc : ((K⁻¹ : Real) ^ 3) * K = (K⁻¹ : Real) ^ 2 := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hKne, mul_one]
  have hc3 : Real.sqrt ((K⁻¹ : Real) ^ 3) * Real.sqrt K = K⁻¹ := by
    rw [← Real.sqrt_mul hp3.le, hcalc, Real.sqrt_sq hKinv.le]
  have hsqt : (0 : Real) < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  rw [hsplit, Real.sqrt_mul hK.le t,
    le_div_iff₀ (mul_pos hsqK hsqt)] at hkey
  have heq : Real.sqrt ((K⁻¹ : Real) ^ 3) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
        (Real.sqrt K * Real.sqrt t) =
      Real.sqrt ((K⁻¹ : Real) ^ 3) * Real.sqrt K *
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
          Real.sqrt t) := by ring
  rw [heq, hc3] at hkey
  have hscaled := mul_le_mul_of_nonneg_left hkey hK.le
  rw [← mul_assoc, mul_inv_cancel₀ hKne, one_mul] at hscaled
  rw [le_div_iff₀ hsqt]
  linarith [hscaled]

end Unnormalized

end DifferentialGeometry.PDE.RicciFlow

end
