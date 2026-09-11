import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.HigherDerivativeReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalTower

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Bundle Topology



section Constants

theorem sqrt_pow_of_nonneg {t : Real} (ht : 0 ≤ t) (m : ℕ) :
    Real.sqrt (t ^ m) = Real.sqrt t ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg ht m), ih]

theorem shiHigherStepBound_nonneg (d m : ℕ) (T Astar eps : Real) :
    0 ≤ shiHigherStepBound d m T Astar eps := by
  unfold shiHigherStepBound
  exact div_nonneg (le_trans zero_le_one (one_le_bernsteinMaximumBound _ _ _ _))
    (shiHigherShift_pos Astar).le

def shiAllOrdersBound (d : ℕ) (T : Real) (eps : ℕ → Real) : ℕ → Real
  | 0 => 1
  | m + 1 =>
      max (shiAllOrdersBound d T eps m)
        (Real.sqrt (shiHigherStepBound d m T (shiAllOrdersBound d T eps m) (eps m)))


theorem shiAllOrdersBound_zero (d : ℕ) (T : Real) (eps : ℕ → Real) :
    shiAllOrdersBound d T eps 0 = 1 := rfl


theorem shiAllOrdersBound_succ (d : ℕ) (T : Real) (eps : ℕ → Real) (m : ℕ) :
    shiAllOrdersBound d T eps (m + 1) =
      max (shiAllOrdersBound d T eps m)
        (Real.sqrt (shiHigherStepBound d m T (shiAllOrdersBound d T eps m) (eps m))) := rfl


theorem one_le_shiAllOrdersBound (d : ℕ) (T : Real) (eps : ℕ → Real) (m : ℕ) :
    1 ≤ shiAllOrdersBound d T eps m := by
  induction m with
  | zero => exact le_of_eq (shiAllOrdersBound_zero d T eps).symm
  | succ m ih =>
      rw [shiAllOrdersBound_succ]
      exact le_trans ih (le_max_left _ _)


theorem shiAllOrdersBound_nonneg (d : ℕ) (T : Real) (eps : ℕ → Real) (m : ℕ) :
    0 ≤ shiAllOrdersBound d T eps m :=
  le_trans zero_le_one (one_le_shiAllOrdersBound d T eps m)

theorem shiAllOrdersBound_monotone (d : ℕ) (T : Real) (eps : ℕ → Real) :
    Monotone (shiAllOrdersBound d T eps) := by
  refine monotone_nat_of_le_succ fun m => ?_
  rw [shiAllOrdersBound_succ]
  exact le_max_left _ _

def shiLocalFirstDerivativeConst (d : ℕ) (T R Clap Cconn : Real) : Real :=
  shiFirstDerivativeLocalConst d 32 T (3 * R / 4) R Clap Cconn (2 * Real.sqrt T)


theorem shiLocalFirstDerivativeConst_nonneg (d : ℕ) (T R Clap Cconn : Real) :
    0 ≤ shiLocalFirstDerivativeConst d T R Clap Cconn :=
  shiFirstDerivativeLocalConst_nonneg _ _ _ _ _ _ _ _

def shiLocalCutoffError (d : ℕ) (T R Clap Cconn Hb : Real) (j : ℕ) : Real :=
  shiFixedCutoffError d T (shiLocalRadius R (j + 1)) (shiLocalRadius R j) Clap Cconn Hb

def shiLocalAllOrdersConst (d m : ℕ) (T R Clap Cconn : Real) : Real :=
  shiAllOrdersBound d T
    (shiLocalCutoffError d T R Clap Cconn
      (shiLocalFirstDerivativeConst d T R Clap Cconn)) m


theorem one_le_shiLocalAllOrdersConst (d m : ℕ) (T R Clap Cconn : Real) :
    1 ≤ shiLocalAllOrdersConst d m T R Clap Cconn :=
  one_le_shiAllOrdersBound _ _ _ _


theorem shiLocalAllOrdersConst_nonneg (d m : ℕ) (T R Clap Cconn : Real) :
    0 ≤ shiLocalAllOrdersConst d m T R Clap Cconn :=
  shiAllOrdersBound_nonneg _ _ _ _

end Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]



section RadiiInduction

omit [SigmaCompactSpace M] in
theorem tpow_mul_nablaKRm04NormSqIntrinsic_le_of_fixedCutoffs
    {alpha omega T R : Real} {halphaomega : alpha < omega} {eps : ℕ → Real}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) (p : M)
    (fc : ∀ k : ℕ, ShiFixedCutoff (I := I) (flowG (I := I) S) T (eps k))
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hone : ∀ k : ℕ, ∀ t : Real, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (shiLocalRadius R (k + 1)) → (fc k).chi t x = 1)
    (hsupp : ∀ k : ℕ, (fc k).support ⊆ {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y <
        ENNReal.ofReal (shiLocalRadius R k)}) :
    ∀ m j : ℕ, 1 ≤ j → j ≤ m → ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (shiLocalRadius R m) →
        t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤
          shiAllOrdersBound (Module.finrank Real E) T eps m ^ 2 := by
  intro m
  induction m with
  | zero => exact fun j hj1 hj0 => absurd (le_trans hj1 hj0) (by omega)
  | succ m ih =>
      have hAstar : (1 : Real) ≤ shiAllOrdersBound (Module.finrank Real E) T eps m :=
        one_le_shiAllOrdersBound _ _ _ _
      have hnest : ∀ y : M,
          riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
              ENNReal.ofReal (shiLocalRadius R (m + 1)) →
            riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
              ENNReal.ofReal (shiLocalRadius R m) := fun y hy =>
        le_trans hy
          (ENNReal.ofReal_le_ofReal (shiLocalRadius_antitone hR (Nat.le_succ m)))
      have hsuppOmega : (fc m).support ⊆ {y : M |
          riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
            ENNReal.ofReal (shiLocalRadius R m)} := by
        intro y hy
        have h : riemannianEDistOf (I := I) (S.base.metric 0) p y <
            ENNReal.ofReal (shiLocalRadius R m) := hsupp m hy
        exact le_of_lt h
      have hstep := tpow_succ_mul_nablaKRm04NormSqIntrinsic_le_of_fixedCutoff (I := I) S hS m
        (fc m)
        (Omega := {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (shiLocalRadius R m)})
        (Omega' := {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (shiLocalRadius R (m + 1))})
        halpha hT hTomega hAstar hsuppOmega
        (fun s _ y hy => hone m s y hy)
        (fun s hs y hy => hu s ⟨hs.1.le, hs.2⟩ y
          (le_trans hy (ENNReal.ofReal_le_ofReal (shiLocalRadius_le hR m))))
        (fun j hj1 hjm s hs y hy => ih j hj1 hjm s hs y hy)
      intro j hj1 hjm t ht x hx
      have hmono : shiAllOrdersBound (Module.finrank Real E) T eps m ≤
          shiAllOrdersBound (Module.finrank Real E) T eps (m + 1) := by
        rw [shiAllOrdersBound_succ]
        exact le_max_left _ _
      rcases Nat.eq_or_lt_of_le hjm with heq | hlt
      · subst heq
        have hval := hstep t ht x hx
        have hnn : (0 : Real) ≤ shiHigherStepBound (Module.finrank Real E) m T
            (shiAllOrdersBound (Module.finrank Real E) T eps m) (eps m) :=
          shiHigherStepBound_nonneg _ _ _ _ _
        have hsqrt : Real.sqrt (shiHigherStepBound (Module.finrank Real E) m T
            (shiAllOrdersBound (Module.finrank Real E) T eps m) (eps m)) ≤
              shiAllOrdersBound (Module.finrank Real E) T eps (m + 1) := by
          rw [shiAllOrdersBound_succ]
          exact le_max_right _ _
        have hsq := Real.sq_sqrt hnn
        nlinarith [Real.sqrt_nonneg (shiHigherStepBound (Module.finrank Real E) m T
          (shiAllOrdersBound (Module.finrank Real E) T eps m) (eps m))]
      · refine le_trans (ih j hj1 (by omega) t ht x (hnest x hx)) ?_
        exact pow_le_pow_left₀ (shiAllOrdersBound_nonneg _ _ _ _) hmono 2

end RadiiInduction



section Theorem

theorem shi_local_all_orders_sq_explicit_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal R}
        r Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
        t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x ≤
          shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn ^ 2 := by
  classical
  have hR34 : ∀ k : ℕ, shiLocalRadius R k ≤ 3 * R / 4 := by
    intro k
    have h := shiLocalRadius_antitone hR (Nat.zero_le k)
    rwa [shiLocalRadius_zero] at h
  have hHb0 : (0 : Real) ≤
      shiLocalFirstDerivativeConst (Module.finrank Real E) T R Clap Cconn :=
    shiLocalFirstDerivativeConst_nonneg _ _ _ _ _
  have hHb := shiFirstDerivative_local_nablaRmSupWeight_of_solution (I := I) S hS
    (a := 32) (r₁ := 3 * R / 4) (r₂ := R) p halpha hT hTomega le_rfl hball hKsec
    hsec hu (by linarith) (by linarith) le_rfl hClap hCconn
    (hlap (3 * R / 4) ⟨by linarith, by linarith⟩)
  have hcutex : ∀ k : ℕ,
      ∃ cut : ShiFixedCutoff (I := I) (flowG (I := I) S) T
          (shiLocalCutoffError (Module.finrank Real E) T R Clap Cconn
            (shiLocalFirstDerivativeConst (Module.finrank Real E) T R Clap Cconn) k),
        (∀ t : Real, ∀ x : M,
          riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
              ENNReal.ofReal (shiLocalRadius R (k + 1)) → cut.chi t x = 1) ∧
        cut.support ⊆ {y : M |
          riemannianEDistOf (I := I) (S.base.metric 0) p y <
            ENNReal.ofReal (shiLocalRadius R k)} := by
    intro k
    refine exists_shiFixedCutoff_ball_error_of_solution (I := I) S hS p halpha hT
      hTomega hball hKsec hsec hu (shiLocalRadius_pos hR (k + 1))
      (shiLocalRadius_succ_lt hR k) (shiLocalRadius_le hR k) hClap hCconn
      (hlap (shiLocalRadius R (k + 1))
        ⟨half_lt_shiLocalRadius hR (k + 1), shiLocalRadius_le hR (k + 1)⟩)
      hHb0 ?_
    intro t ht x hx
    exact hHb t ht x (le_trans hx (ENNReal.ofReal_le_ofReal (hR34 k)))
  choose fc hone hsupp using hcutex
  intro m t ht x hx
  have hxm : riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
      ENNReal.ofReal (shiLocalRadius R m) :=
    le_trans hx (ENNReal.ofReal_le_ofReal (half_lt_shiLocalRadius hR m).le)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [shiLocalAllOrdersConst, shiAllOrdersBound_zero, pow_zero, one_mul, one_pow]
    exact hu t ⟨ht.1.le, ht.2⟩ x
      (le_trans hx (ENNReal.ofReal_le_ofReal (by linarith)))
  · exact tpow_mul_nablaKRm04NormSqIntrinsic_le_of_fixedCutoffs (I := I) S hS p
      (eps := shiLocalCutoffError (Module.finrank Real E) T R Clap Cconn
        (shiLocalFirstDerivativeConst (Module.finrank Real E) T R Clap Cconn))
      fc halpha hT hTomega hR hu hone hsupp m m hmpos le_rfl t ht x hxm

theorem shi_local_all_orders_norm_explicit_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal R}
        r Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn ∧
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn /
              Real.sqrt t ^ m := by
  intro m
  have hC0 := shiLocalAllOrdersConst_nonneg (Module.finrank Real E) m T R Clap Cconn
  have hC := shi_local_all_orders_sq_explicit_of_laplacianInput (I := I) S hS p halpha hT
    hTomega hR hball hKsec hsec hu hClap hCconn hlap m
  set C : Real := shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn
    with hCdef
  intro t ht x hx
  have hbound := hC t ht x hx
  have hu0 : (0 : Real) ≤ nablaKRm04NormSqIntrinsic (I := I) S m t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have hsqrtle : Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C := by
    have h := Real.sqrt_le_sqrt hbound
    rwa [Real.sqrt_sq hC0] at h
  refine ⟨hsqrtle, ?_⟩
  have hspos : (0 : Real) < Real.sqrt t ^ m :=
    pow_pos (Real.sqrt_pos.mpr ht.1) m
  rw [le_div_iff₀ hspos]
  have hsplit : Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) =
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) * Real.sqrt t ^ m := by
    rw [Real.sqrt_mul (pow_nonneg ht.1.le m), sqrt_pow_of_nonneg ht.1.le, mul_comm]
  rw [← hsplit]
  exact hsqrtle

theorem shi_local_all_orders_sq_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal R}
        r Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x ≤ C ^ 2 := fun m =>
  ⟨shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn,
    shiLocalAllOrdersConst_nonneg _ _ _ _ _ _,
    shi_local_all_orders_sq_explicit_of_laplacianInput (I := I) S hS p halpha hT hTomega
      hR hball hKsec hsec hu hClap hCconn hlap m⟩

theorem shi_local_all_orders_norm_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal R}
        r Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C ∧
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
              C / Real.sqrt t ^ m := fun m =>
  ⟨shiLocalAllOrdersConst (Module.finrank Real E) m T R Clap Cconn,
    shiLocalAllOrdersConst_nonneg _ _ _ _ _ _,
    shi_local_all_orders_norm_explicit_of_laplacianInput (I := I) S hS p halpha hT
      hTomega hR hball hKsec hsec hu hClap hCconn hlap m⟩

end Theorem

end DifferentialGeometry.PDE.RicciFlow

end
