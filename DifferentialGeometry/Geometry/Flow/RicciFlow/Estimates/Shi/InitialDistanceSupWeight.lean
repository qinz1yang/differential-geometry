import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.FirstDerivativeLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialConnectionDifference
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology Bundle

section Scalar

private theorem exists_mem_Icc_sSup_image_eq {f : Real → Real} {t : Real}
    (ht : 0 ≤ t) (hf : ContinuousOn f (Set.Icc 0 t)) :
    ∃ s ∈ Set.Icc (0 : Real) t, sSup (f '' Set.Icc 0 t) = f s := by
  obtain ⟨s, hs, hmax⟩ :=
    (isCompact_Icc (a := (0 : Real)) (b := t)).exists_isMaxOn
      (Set.nonempty_Icc.mpr ht) hf
  refine ⟨s, hs, IsGreatest.csSup_eq ⟨⟨s, hs, rfl⟩, ?_⟩⟩
  rintro y ⟨z, hz, rfl⟩
  exact hmax hz

private theorem intervalIntegral_sqrt_le_of_sqrt_mul_le
    {v : Real → Real} {t Ms : Real} (ht : 0 < t)
    (hmem : ∀ s ∈ Set.Icc (0 : Real) t, Real.sqrt (s * v s) ≤ Ms)
    (hint : IntervalIntegrable (fun s => Real.sqrt (v s)) MeasureTheory.volume 0 t) :
    (∫ s in (0 : Real)..t, Real.sqrt (v s)) ≤ 2 * Real.sqrt t * Ms := by
  have hintg : IntervalIntegrable (fun s : Real => Ms * s ^ (-(1 / 2) : Real))
      MeasureTheory.volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : Real))
      (by norm_num)).const_mul Ms
  have hpt : ∀ s ∈ Set.Ioo (0 : Real) t,
      Real.sqrt (v s) ≤ Ms * s ^ (-(1 / 2) : Real) := by
    intro s hs
    have hs0 : (0 : Real) < s := hs.1
    have hsq : (0 : Real) < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have hle : Real.sqrt s * Real.sqrt (v s) ≤ Ms := by
      rw [← Real.sqrt_mul hs0.le]
      exact hmem s ⟨hs0.le, hs.2.le⟩
    have hrw : s ^ (-(1 / 2) : Real) = (Real.sqrt s)⁻¹ := by
      rw [Real.rpow_neg hs0.le, ← Real.sqrt_eq_rpow]
    rw [hrw, ← div_eq_mul_inv, le_div_iff₀ hsq]
    calc Real.sqrt (v s) * Real.sqrt s
        = Real.sqrt s * Real.sqrt (v s) := mul_comm _ _
      _ ≤ Ms := hle
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint hintg hpt
  have hexp : (-(1 / 2 : Real)) + 1 = 1 / 2 := by norm_num
  have hI : (∫ s in (0 : Real)..t, s ^ (-(1 / 2) : Real)) = 2 * Real.sqrt t := by
    rw [integral_rpow (a := (0 : Real)) (b := t) (r := -(1 / 2 : Real))
      (Or.inl (by norm_num)), hexp,
      Real.zero_rpow (by norm_num : (1 / 2 : Real) ≠ 0), ← Real.sqrt_eq_rpow]
    ring
  have hval : (∫ s in (0 : Real)..t, Ms * s ^ (-(1 / 2) : Real)) =
      2 * Real.sqrt t * Ms := by
    rw [intervalIntegral.integral_const_mul, hI]
    ring
  rw [hval] at hmono
  exact hmono

theorem intervalIntegral_sqrt_le_two_mul_sqrt_mul_sSup
    {v : Real → Real} {t : Real} (ht : 0 < t)
    (hbdd : BddAbove ((fun s => Real.sqrt (s * v s)) '' Set.Icc 0 t))
    (hint : IntervalIntegrable (fun s => Real.sqrt (v s)) MeasureTheory.volume 0 t) :
    (∫ s in (0 : Real)..t, Real.sqrt (v s)) ≤
      2 * Real.sqrt t * sSup ((fun s => Real.sqrt (s * v s)) '' Set.Icc 0 t) :=
  intervalIntegral_sqrt_le_of_sqrt_mul_le ht
    (fun s hs => le_csSup hbdd ⟨s, hs, rfl⟩) hint

end Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]



def nablaRmSupWeight
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real → M → Real :=
  fun t x =>
    2 * Real.sqrt t *
      sSup ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
        Set.Icc 0 t)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRmSupWeight_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    0 ≤ nablaRmSupWeight (I := I) S t x := by
  have hdef : nablaRmSupWeight (I := I) S t x =
      2 * Real.sqrt t *
        sSup ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
          Set.Icc 0 t) := rfl
  rcases le_or_gt (0 : Real) t with ht | ht
  · by_cases hbdd :
        BddAbove ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
          Set.Icc 0 t)
    · have h0 : (0 : Real) ≤
          sSup ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
            Set.Icc 0 t) := by
        have h := le_csSup hbdd
          (Set.mem_image_of_mem
            (fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x))
            (Set.left_mem_Icc.mpr ht))
        simpa using h
      rw [hdef]
      have h2 : (0 : Real) ≤ 2 * Real.sqrt t := by positivity
      exact mul_nonneg h2 h0
    · rw [hdef, Real.sSup_of_not_bddAbove hbdd]
      simp
  · rw [hdef, Real.sqrt_eq_zero_of_nonpos ht.le]
    simp

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_mem_Icc_nablaRmSupWeight_eq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t : Real} (ht : 0 ≤ t) (x : M)
    (hcont : ContinuousOn
      (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s x) (Set.Icc 0 t)) :
    ∃ s ∈ Set.Icc (0 : Real) t,
      nablaRmSupWeight (I := I) S t x =
        2 * Real.sqrt t *
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := by
  have hmul : ContinuousOn
      (fun s : Real => s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)
      (Set.Icc 0 t) := continuousOn_id.mul hcont
  obtain ⟨s, hs, hsup⟩ := exists_mem_Icc_sSup_image_eq ht hmul.sqrt
  refine ⟨s, hs, ?_⟩
  have hdef : nablaRmSupWeight (I := I) S t x =
      2 * Real.sqrt t *
        sSup ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
          Set.Icc 0 t) := rfl
  rw [hdef, hsup]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_mem_Icc_nablaRmSupWeight_le
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t T : Real} (ht : 0 ≤ t) (htT : t ≤ T)
    (x : M)
    (hcont : ContinuousOn
      (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s x) (Set.Icc 0 t)) :
    ∃ s ∈ Set.Icc (0 : Real) t,
      nablaRmSupWeight (I := I) S t x ≤
        2 * Real.sqrt T *
          Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := by
  obtain ⟨s, hs, heq⟩ := exists_mem_Icc_nablaRmSupWeight_eq (I := I) S ht x hcont
  refine ⟨s, hs, ?_⟩
  rw [heq]
  have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have h2 : 2 * Real.sqrt t ≤ 2 * Real.sqrt T := by linarith
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)



omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRmTimeIntegral_le_nablaRmSupWeight_of_bddAbove
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t : Real} (ht : 0 < t) (x : M)
    (hbdd : BddAbove
      ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
        Set.Icc 0 t))
    (hint : IntervalIntegrable
      (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x))
      MeasureTheory.volume 0 t) :
    nablaRmTimeIntegral (I := I) S t x ≤ nablaRmSupWeight (I := I) S t x := by
  have hdefI : nablaRmTimeIntegral (I := I) S t x =
      ∫ s in (0 : Real)..t,
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := rfl
  have hdefS : nablaRmSupWeight (I := I) S t x =
      2 * Real.sqrt t *
        sSup ((fun s => Real.sqrt (s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)) ''
          Set.Icc 0 t) := rfl
  rw [hdefI, hdefS]
  exact intervalIntegral_sqrt_le_two_mul_sqrt_mul_sSup ht hbdd hint

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRmTimeIntegral_le_nablaRmSupWeight
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t : Real} (ht : 0 < t) (x : M)
    (hcont : ContinuousOn
      (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s x) (Set.Icc 0 t)) :
    nablaRmTimeIntegral (I := I) S t x ≤ nablaRmSupWeight (I := I) S t x := by
  have hmul : ContinuousOn
      (fun s : Real => s * nablaKRm04NormSqIntrinsic (I := I) S 1 s x)
      (Set.Icc 0 t) := continuousOn_id.mul hcont
  have hbdd := (isCompact_Icc (a := (0 : Real)) (b := t)).bddAbove_image hmul.sqrt
  have hint : IntervalIntegrable
      (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x))
      MeasureTheory.volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht.le]
    exact hcont.sqrt
  exact nablaRmTimeIntegral_le_nablaRmSupWeight_of_bddAbove (I := I) S ht x hbdd hint



omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless]
  [IsManifold I 1 M] [T2Space M] in
theorem InitialConnectionDifferenceBound.mono
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T Cconn : Real} {B : Set M} {Theta₁ Theta₂ : Real → M → Real}
    (h : InitialConnectionDifferenceBound (I := I) S T B Cconn Theta₁)
    (hCconn : 0 ≤ Cconn)
    (hle : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, Theta₁ t x ≤ Theta₂ t x) :
    InitialConnectionDifferenceBound (I := I) S T B Cconn Theta₂ := by
  intro t ht x hxB u w
  refine (h t ht x hxB u w).trans ?_
  have h1 : Cconn * Theta₁ t x ≤ Cconn * Theta₂ t x :=
    mul_le_mul_of_nonneg_left (hle t ht x) hCconn
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless]
  [T2Space M] in
theorem InitialDistanceFlowLaplacianBound.mono
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : Real} {p : M} {B : Set M} {r₁ Ksec Clap Cconn : Real}
    {Theta₁ Theta₂ : Real → M → Real}
    (h : InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn
      Theta₁)
    (hCconn : 0 ≤ Cconn)
    (hle : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, Theta₁ t x ≤ Theta₂ t x) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn
      Theta₂ := by
  intro t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq hhess
  refine (h t ht x hxB rho U hU hxU hrhoOn hr₁rho hvalue hupper hgradEq
    hhess).trans ?_
  have h1 : Cconn * Theta₁ t x ≤ Cconn * Theta₂ t x :=
    mul_le_mul_of_nonneg_left (hle t ht x) hCconn
  linarith



omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless] in
theorem initialConnectionDifferenceBound_nablaRmSupWeight_of_nablaRmTimeIntegral
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {T Cconn : Real}
    {B : Set M}
    (h : InitialConnectionDifferenceBound (I := I) S T B Cconn
      (nablaRmTimeIntegral (I := I) S))
    (hCconn : 0 ≤ Cconn)
    (hcont : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      ContinuousOn
        (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s x) (Set.Icc 0 t)) :
    InitialConnectionDifferenceBound (I := I) S T B Cconn
      (nablaRmSupWeight (I := I) S) :=
  h.mono hCconn (fun t ht x =>
    nablaRmTimeIntegral_le_nablaRmSupWeight (I := I) S ht.1 x (hcont t ht x))

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless] in
theorem initialDistanceFlowLaplacianBound_nablaRmSupWeight_of_nablaRmTimeIntegral
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : Real} {p : M} {B : Set M} {r₁ Ksec Clap Cconn : Real}
    (h : InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn
      (nablaRmTimeIntegral (I := I) S))
    (hCconn : 0 ≤ Cconn)
    (hcont : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      ContinuousOn
        (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s x) (Set.Icc 0 t)) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn
      (nablaRmSupWeight (I := I) S) :=
  h.mono hCconn (fun t ht x =>
    nablaRmTimeIntegral_le_nablaRmSupWeight (I := I) S ht.1 x (hcont t ht x))

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialConnectionDifferenceBound_nablaRmSupWeight_of_connectionVariation
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {T K cn : Real} {B : Set M}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hcn : 0 ≤ cn)
    {Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y}
    {NR : Real → (y : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y}
    (hkoszul : ConnectionVariationKoszulOn (I := I) S T Z NR)
    (hNR : NablaRicciNormBoundOn (I := I) S T cn NR)
    (hrep : ConnectionDifferenceTimeIntegralOn (I := I) S T Z)
    (hcont : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M,
      ContinuousOn
        (fun s => nablaKRm04NormSqIntrinsic (I := I) S 1 s y) (Set.Icc 0 t)) :
    InitialConnectionDifferenceBound (I := I) S T B
      (3 * cn *
        Real.exp (3 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T))
      (nablaRmSupWeight (I := I) S) := by
  have hint : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M,
      IntervalIntegrable
        (fun s : Real => Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y))
        MeasureTheory.volume 0 t := by
    intro t ht y
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht.1.le]
    exact (hcont t ht y).sqrt
  have hbase := initialConnectionDifferenceBound_of_connectionVariation (I := I) S hS
    hT hslab hreg hcurv hcn hkoszul hNR hrep hint
  refine hbase.mono
    (mul_nonneg (mul_nonneg (by norm_num) hcn) (Real.exp_pos _).le)
    (fun t ht y =>
      nablaRmTimeIntegral_le_nablaRmSupWeight (I := I) S ht.1 y (hcont t ht y))

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialDistanceFlowLaplacianBoundOn_of_solution_nablaRmSupWeight
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {T K Ksec r₁ Cconn : Real} {B : Set M}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) (hCconn : 0 ≤ Cconn)
    (hdiff : InitialConnectionDifferenceBound (I := I) S T B Cconn
      (nablaRmSupWeight (I := I) S))
    (p : M) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        (2 / r₁ + Real.sqrt (-Ksec)))
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        Cconn)
      (nablaRmSupWeight (I := I) S) :=
  initialDistanceFlowLaplacianBoundOn_of_solution (I := I) S hS hT hslab hreg
    hcurv hr₁ hCconn
    (fun t _ y => nablaRmSupWeight_nonneg (I := I) S t y) hdiff p



section Regular

variable [CompleteSpace E] [IsManifold I 2 M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem continuousOn_nablaKRm04NormSqIntrinsic_of_subset_regular
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) (k : Nat) {A : Set Real}
    (hsub : A ⊆ (RealTimeInterval.closedOpen alpha omega halphaomega).regular)
    (x : M) :
    ContinuousOn (fun s => nablaKRm04NormSqIntrinsic (I := I) S k s x) A := by
  have hjoint := (towerNorm_joint (I := I) hS k).continuousOn
  have hmaps : Set.MapsTo (fun s : Real => (s, x)) A
      ((RealTimeInterval.closedOpen alpha omega halphaomega).regular ×ˢ
        (Set.univ : Set M)) := fun s hs => ⟨hsub hs, trivial⟩
  exact hjoint.comp (continuous_id.prodMk continuous_const).continuousOn hmaps

section CutoffProduction

variable [VectorBundle Real E (TangentSpace I : M → Type _)]

theorem shiFirstDerivative_local_nablaRmSupWeight_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T a Ksec R r₁ r₂ Clap Cconn : Real} (p : M)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
          shiFirstDerivativeLocalConst (Module.finrank Real E) a T r₁ r₂ Clap Cconn
              (2 * Real.sqrt T) /
            Real.sqrt t := by
  have hreg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  refine shiFirstDerivative_local_of_solution (I := I) S hS
    (a := a) (r₂ := r₂) (cn := 2 * Real.sqrt T) p halpha hT hTomega ha hball
    hKsec hsec hu hr₁ hr₁₂ hr₂R hClap hCconn (by positivity)
    (fun t y => nablaRmSupWeight_nonneg (I := I) S t y) hlap ?_
  intro t ht x
  have hsub : Set.Icc (0 : Real) t ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular :=
    fun s hs => hreg ⟨hs.1, hs.2.trans ht.2⟩
  exact exists_mem_Icc_nablaRmSupWeight_le (I := I) S ht.1.le ht.2 x
    (continuousOn_nablaKRm04NormSqIntrinsic_of_subset_regular (I := I) hS 1 hsub x)

theorem exists_shiFirstDerivative_local_nablaRmSupWeight_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T a Ksec R r₁ r₂ Clap Cconn : Real} (p : M)
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
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ Ksec Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
            C / Real.sqrt t :=
  ⟨shiFirstDerivativeLocalConst (Module.finrank Real E) a T r₁ r₂ Clap Cconn
      (2 * Real.sqrt T),
    shiFirstDerivativeLocalConst_nonneg _ _ _ _ _ _ _ _,
    shiFirstDerivative_local_nablaRmSupWeight_of_solution (I := I) S hS
      (a := a) (r₂ := r₂) p halpha hT hTomega ha hball hKsec hsec hu hr₁ hr₁₂ hr₂R
      hClap hCconn hlap⟩

theorem exists_shiFirstDerivative_local_nablaRmSupWeight_of_solution_of_sectional_nonneg
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T a R r₁ r₂ Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (ha : 32 ≤ a)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hsec : ∀ y : M, metricRm04At (I := I) (S.base.metric 0) y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound (I := I) S T p
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal R}
      r₁ 0 Clap Cconn (nablaRmSupWeight (I := I) S)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
            C / Real.sqrt t :=
  exists_shiFirstDerivative_local_nablaRmSupWeight_of_solution (I := I) S hS
    (a := a) (r₂ := r₂) p halpha hT hTomega ha hball le_rfl
    (fun y _ => sectionalBoundedBelow_zero_of_mem_cone (I := I)
      (S.base.metric 0) hsec y)
    hu hr₁ hr₁₂ hr₂R hClap hCconn hlap

end CutoffProduction

end Regular

end DifferentialGeometry.PDE.RicciFlow

end
