import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.TimeWeighted
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TimeIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.EndpointConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.TimeIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceLaplacian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open Set MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} (hT : 0 < T)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    InitialConnectionDifferenceBound S T univ
      ((3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)) *
          (2 * Real.sqrt ((2 : ℝ) ^ 1 *
      (towerConst (max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (max 1 K * T) 1) ^ 2 * (max 1 K) ^ 2))) (fun t _ => Real.sqrt t) := by
  have hcurvNorm : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K := by
    intro t ht x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      using hcurv t ht x
  have hinitial : ∀ (x : M) (u w v : TangentSpace I x),
      ContinuousWithinAt
        (fun r : ℝ => (S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric r))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
        (Icc (0 : ℝ) T) 0 :=
    continuousWithinAt_initial_connection_pairing_of_complete_bounded_curvature
      S hS hT hcarrier hregular hcomplete hK hcurvNorm
  let A : ℝ := ((2 : ℝ) ^ 1 *
      (towerConst (max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (max 1 K * T) 1) ^ 2 * (max 1 K) ^ 2)
  have hweighted := time_weighted_curvature_derivative_bound_of_complete
    S hS hcarrier hregular hcomplete hK hcurvNorm 1
  have hbound : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      (t - 0) * nablaKRm04NormSqIntrinsic S 1 t x ≤ A := by
    intro t ht x
    simpa only [A, pow_one, sub_zero] using hweighted t ht x
  have hint : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      IntervalIntegrable (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x))
        volume 0 t := by
    intro t ht x
    exact intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le
      S hS ht.1.le (fun _ hs => hregular ⟨hs.1, hs.2.trans ht.2⟩) 1 x
      (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩ x)
  have hspeed : ∀ (x : M) (u w v : TangentSpace I x),
      IntervalIntegrable
        (fun s => (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v)
        volume 0 T := by
    intro x u w v
    exact intervalIntegrable_connectionVariationSpeed_pairing_of_curvature_bound
      S hS hT.le hcarrier hregular x u w v (fun s hs => hcurv s hs x)
      (hint T ⟨hT, le_rfl⟩ x)
  have hrep := connectionDifferenceTimeIntegralOn_of_initial_continuity
    S hS hcarrier hregular hinitial hspeed
  let C₀ : ℝ := 3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
    Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hconn : InitialConnectionDifferenceBound S T univ C₀
      (nablaRmTimeIntegral S) :=
    initialConnectionDifferenceBound_of_connectionVariation S hS hT hcarrier hregular
      (fun s hs y _ => hcurv s hs y) (Real.sqrt_nonneg _)
      (connectionVariationKoszulOn_connectionVariationSpeed S T)
      (nablaRicciNormBoundOn_nablaRicci S T) hrep hint
  have hintegral : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      nablaRmTimeIntegral S t x ≤ 2 * Real.sqrt A * Real.sqrt t := by
    intro t ht x
    have h := integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le
      S hS ht.1.le (fun _ hs => hregular ⟨hs.1, hs.2.trans ht.2⟩) 1 x
      (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩ x)
    simpa only [sub_zero, nablaRmTimeIntegral] using h
  intro t ht x hx u w
  have h := hconn.mono hC₀ hintegral t ht x hx u w
  dsimp at h ⊢
  convert h using 1
  ring

theorem exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} (hT : 0 < T)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      InitialConnectionDifferenceBound S T univ C (fun t _ => Real.sqrt t) := by
  refine ⟨(3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)) *
          (2 * Real.sqrt ((2 : ℝ) ^ 1 *
      (towerConst (max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (max 1 K * T) 1) ^ 2 * (max 1 K) ^ 2)), by positivity, ?_⟩
  exact initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    S hS hT hcarrier hregular hcomplete hK hcurv

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open Set
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem InitialConnectionDifferenceBound.timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {a b C : ℝ} {B : Set M} {Theta : ℝ → M → ℝ}
    (h : InitialConnectionDifferenceBound (S.timeShift a) (b - a) B C Theta) :
    ∀ t ∈ Ioc a b, ∀ x ∈ B, ∀ u w : TangentSpace I x,
      Real.sqrt ((S.base.metric a).inner x
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)) ≤
        C * Theta (t - a) x *
          Real.sqrt ((S.base.metric a).inner x u u) *
          Real.sqrt ((S.base.metric a).inner x w w) := by
  intro t ht x hx u w
  have htshift : t - a ∈ Ioc (0 : ℝ) (b - a) := by
    constructor <;> linarith [ht.1, ht.2]
  have hbound := h (t - a) htshift x hx u w
  simpa only [SolutionOn.timeShift_base_metric, zero_add, sub_add_cancel] using hbound

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open Set
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_connection_difference_sqrt_bound_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M, nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc a b, ∀ x : M, ∀ u w : TangentSpace I x,
      Real.sqrt ((S.base.metric a).inner x
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)) ≤
        C * Real.sqrt (t - a) *
          Real.sqrt ((S.base.metric a).inner x u u) *
          Real.sqrt ((S.base.metric a).inner x w w) := by
  have hcarrier' : Icc (0 : ℝ) (b - a) ⊆ (D.timeShift a).carrier := by
    intro s hs
    change s + a ∈ D.carrier
    apply hcarrier
    constructor <;> linarith [hs.1, hs.2]
  have hregular' : Ioc (0 : ℝ) (b - a) ⊆ (D.timeShift a).regular := by
    intro s hs
    change s + a ∈ D.regular
    apply hregular
    constructor <;> linarith [hs.1, hs.2]
  have hcomplete' : RiemannianMetricComplete (I := I) ((S.timeShift a).base.metric 0) := by
    simpa only [SolutionOn.timeShift_base_metric, zero_add] using hcomplete
  have hcurv' : ∀ s ∈ Icc (0 : ℝ) (b - a), ∀ x : M,
      nablaKRm04NormSqIntrinsic (S.timeShift a) 0 s x ≤ K := by
    intro s hs x
    change nablaKRm04NormSqIntrinsic S 0 (s + a) x ≤ K
    apply hcurv (s + a) _ x
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨C, hC, hbound⟩ :=
    exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
      (S.timeShift a) (isSolutionOn_timeShift hS a) (sub_pos.mpr hab)
      hcarrier' hregular' hcomplete' hK hcurv'
  refine ⟨C, hC, ?_⟩
  intro t ht x u w
  exact hbound.timeShift (S := S) (a := a) (b := b) t ht x (mem_univ _) u w

end DifferentialGeometry.PDE.RicciFlow
