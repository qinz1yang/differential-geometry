import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology Bundle BigOperators

universe u uE uH

section Constants

def shiLocalClap (d : ℕ) (T R : Real) : Real :=
  (d : Real) * Real.exp (2 * (d : Real) ^ 2 * T) * (4 / R + 1)

def shiLocalCconn (d : ℕ) (T : Real) : Real :=
  (d : Real) * Real.exp (2 * (d : Real) ^ 2 * T) *
    (3 * Real.sqrt ((d : Real) ^ 5) * Real.exp (3 * (d : Real) ^ 2 * T))


theorem shiLocalClap_nonneg (d : ℕ) (T : Real) {R : Real} (hR : 0 < R) :
    0 ≤ shiLocalClap d T R := by
  have h : (0 : Real) ≤ 4 / R := by positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) (by linarith)


theorem shiLocalCconn_nonneg (d : ℕ) (T : Real) : 0 ≤ shiLocalCconn d T := by
  unfold shiLocalCconn
  positivity

theorem shiLocalClap_eq (d : ℕ) (T R : Real) {c : Real} (hc : Real.sqrt (-c) = 1) :
    (d : Real) * Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt 1) * T) *
        (2 / (R / 2) + Real.sqrt (-c)) = shiLocalClap d T R := by
  have h4 : (2 : Real) / (R / 2) = 4 / R := by
    rw [div_div_eq_mul_div]
    norm_num
  rw [shiLocalClap, h4, hc]
  simp only [Real.sqrt_one, mul_one]

theorem shiLocalCconn_eq (d : ℕ) (T : Real) :
    (d : Real) * Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt 1) * T) *
        (3 * Real.sqrt ((d : Real) ^ 5) *
          Real.exp (3 * ((d : Real) ^ 2 * Real.sqrt 1) * T)) = shiLocalCconn d T := by
  rw [shiLocalCconn]
  simp only [Real.sqrt_one, mul_one]

def shiLocalUniformBound (d m : ℕ) (T R : Real) : Real :=
  shiLocalAllOrdersConst d m T R (shiLocalClap d T R) (shiLocalCconn d T)


theorem shiLocalUniformBound_nonneg (d m : ℕ) (T R : Real) :
    0 ≤ shiLocalUniformBound d m T R :=
  shiLocalAllOrdersConst_nonneg _ _ _ _ _ _

end Constants

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] [IsManifold I 1 M] in
private theorem inner_eq_sum_repr {Idx : Type*} [Fintype Idx] {x : M}
    (g : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    g.inner x X Y = ∑ m, bas.repr X m * g.inner x (bas m) Y := by
  classical
  have hX : (∑ m, bas.repr X m • bas m) = X := bas.sum_repr X
  calc g.inner x X Y = g.inner x (∑ m, bas.repr X m • bas m) Y := by rw [hX]
    _ = ∑ m, bas.repr X m * g.inner x (bas m) Y := by
        rw [map_sum]
        simp

omit [FiniteDimensional Real E] [IsManifold I 1 M] in
private theorem repr_eq_sum_gInv_mul_inner {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (g : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) g x bas gInv)
    (Y : TangentSpace I x) (i : Idx) :
    bas.repr Y i = ∑ j, gInv i j * g.inner x Y (bas j) := by
  classical
  have step1 : ∑ j : Idx, gInv i j * g.inner x Y (bas j)
      = ∑ j : Idx, ∑ k : Idx, bas.repr Y k * (gInv i j * g.inner x (bas j) (bas k)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_eq_sum_repr (I := I) g bas Y (bas j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [g.symm x (bas k) (bas j)]
    ring
  have step2 : ∀ k : Idx,
      (∑ j : Idx, gInv i j * g.inner x (bas j) (bas k)) = if i = k then (1 : Real) else 0 :=
    fun k => (hinv i k).1
  rw [step1, Finset.sum_comm]
  simp only [← Finset.mul_sum, step2]
  simp

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem tensor0S_sum_smul_apply {Idx : Type*} {x : M} {q : ℕ}
    (c : (Fin q → Idx) → Real)
    (F : (Fin q → Idx) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) q x)
    (m : Fin q → TangentSpace I x) (s : Finset (Fin q → Idx)) :
    (∑ slots ∈ s, c slots • F slots) m = ∑ slots ∈ s, c slots * (F slots) m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl

omit [IsManifold I ∞ M] in
private theorem tensor0S_apply_eq_sum_component {Idx : Type*} [Fintype Idx]
    {x : M} {q : ℕ}
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) q x)
    (m : Fin q → TangentSpace I x) :
    A m = ∑ slots : Fin q → Idx,
      component0S (I := I) bas A slots * (tensor0SBasis (I := I) bas q slots) m := by
  classical
  have hsum := (tensor0SBasis (I := I) bas q).sum_repr A
  calc A m
      = (∑ slots : Fin q → Idx,
          (tensor0SBasis (I := I) bas q).repr A slots •
            (tensor0SBasis (I := I) bas q slots)) m := by
        rw [hsum]
    _ = ∑ slots : Fin q → Idx,
          (tensor0SBasis (I := I) bas q).repr A slots *
            (tensor0SBasis (I := I) bas q slots) m :=
        tensor0S_sum_smul_apply (I := I) _ _ m Finset.univ
    _ = ∑ slots : Fin q → Idx,
          component0S (I := I) bas A slots * (tensor0SBasis (I := I) bas q slots) m := by
        refine Finset.sum_congr rfl fun slots _ => ?_
        rw [tensor0SBasis_repr (I := I) bas A slots]

end Pointwise



section RegularWindow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem continuousOn_connectionVariationSpeed_pairing
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hreg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular) :
    ConnectionVariationSpeedTimeContinuousOn (I := I) S T
      (connectionVariationSpeed (I := I) S) := by
  classical
  intro x u w v
  have hxmem : x ∈ coordinateFrameSet (I := I) x := coordinateFrameAt_mem (I := I) x
  have hinvcont : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      ContinuousOn (fun s : Real => coordInv (I := I) S x s x i j) (Set.Icc 0 T) := by
    intro i j s hs
    have hslice : ContMDiffAt 𝓘(Real, Real) (𝓘(Real, Real).prod I) ∞
        (fun r : Real => (r, x)) s := contMDiffAt_id.prodMk contMDiffAt_const
    have hcomp := (coordInvSmoothAt (I := I) S hS x ⟨s, hreg hs⟩ x hxmem i j).comp s hslice
    exact hcomp.continuousAt.continuousWithinAt
  have htower : ∀ slots : Fin (4 + 1) → CoordinateIdx (𝕜 := Real) E,
      ContinuousOn (fun s : Real =>
        component0S (I := I) (coordinateFrameAtToBasis (I := I) x)
          (nablaKRm04Field (I := I) S s 1 x) slots) (Set.Icc 0 T) := by
    intro slots
    have hargs : (fun a : Fin (4 + 1) =>
        coordinateFrameAtToBasis (I := I) x (slots a)) =
        frameTuple (I := I) (coordinateFrameAt (I := I) x) x slots := by
      funext a
      simp [frameTuple]
    have hfun : (fun s : Real =>
        component0S (I := I) (coordinateFrameAtToBasis (I := I) x)
          (nablaKRm04Field (I := I) S s 1 x) slots) =
        fun s : Real => iteratedRmComp (I := I) (coordinateFrameAt (I := I) x)
          (solutionChristoffelComponents (I := I) S x)
          (solutionCurvatureComponents (I := I) S x) 1 s x slots := by
      funext s
      rw [iteratedRmComp_eq_nablaKRm04Field (I := I) S x s 1 hxmem slots,
        component0S_apply, hargs]
    rw [hfun]
    intro s hs
    have hslice : ContMDiffAt 𝓘(Real, Real) (𝓘(Real, Real).prod I) ∞
        (fun r : Real => (r, x)) s := contMDiffAt_id.prodMk contMDiffAt_const
    have hcomp := (coordTowerSmooth (I := I) hS x ⟨s, hreg hs⟩ x
      (self_mem_chartLeviCivitaGoodSet (I := I) x) 1 slots).comp s hslice
    exact hcomp.continuousAt.continuousWithinAt
  have hfield : ∀ m : Fin (4 + 1) → TangentSpace I x,
      ContinuousOn (fun s : Real => (nablaKRm04Field (I := I) S s 1 x) m)
        (Set.Icc 0 T) := by
    intro m
    have hexp : ∀ s : Real, (nablaKRm04Field (I := I) S s 1 x) m =
        ∑ slots : Fin (4 + 1) → CoordinateIdx (𝕜 := Real) E,
          component0S (I := I) (coordinateFrameAtToBasis (I := I) x)
            (nablaKRm04Field (I := I) S s 1 x) slots *
            (tensor0SBasis (I := I) (coordinateFrameAtToBasis (I := I) x) (4 + 1) slots) m :=
      fun s => tensor0S_apply_eq_sum_component (I := I)
        (coordinateFrameAtToBasis (I := I) x) (nablaKRm04Field (I := I) S s 1 x) m
    refine ContinuousOn.congr ?_ (fun s _ => hexp s)
    exact continuousOn_finsetSum _ fun slots _ => (htower slots).mul continuousOn_const
  have hnrc : ∀ a b c : TangentSpace I x,
      ContinuousOn (fun s : Real => nablaRicci (I := I) S s x (vec3 (I := I) a b c))
        (Set.Icc 0 T) := by
    intro a b c
    have heq : ∀ s : Real,
        nablaRicci (I := I) S s x (vec3 (I := I) a b c) =
          ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
            coordInv (I := I) S x s x i j *
              (nablaKRm04Field (I := I) S s 1 x)
                (vec5 (I := I) a (coordinateFrameAtToBasis (I := I) x i) b c
                  (coordinateFrameAtToBasis (I := I) x j)) := by
      intro s
      exact nablaRicTraceAt_nablaRicci (I := I) S s (coordinateFrameAtToBasis (I := I) x)
        (fun i j => coordInv (I := I) S x s x i j) (coordInvReal (I := I) S x s) a b c
    refine ContinuousOn.congr ?_ (fun s _ => heq s)
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (hinvcont i j).mul (hfield _)
  have hkoscont : ∀ j : CoordinateIdx (𝕜 := Real) E,
      ContinuousOn (fun s : Real =>
        koszulRicciCovector (I := I) (nablaRicci (I := I) S s x) u w
          (coordinateFrameAtToBasis (I := I) x j)) (Set.Icc 0 T) := by
    intro j
    have heq : ∀ s : Real,
        koszulRicciCovector (I := I) (nablaRicci (I := I) S s x) u w
            (coordinateFrameAtToBasis (I := I) x j) =
          -(nablaRicci (I := I) S s x)
              (vec3 (I := I) u w (coordinateFrameAtToBasis (I := I) x j)) -
            (nablaRicci (I := I) S s x)
              (vec3 (I := I) w u (coordinateFrameAtToBasis (I := I) x j)) +
            (nablaRicci (I := I) S s x)
              (vec3 (I := I) (coordinateFrameAtToBasis (I := I) x j) u w) :=
      fun s => koszulRicciCovector_apply (I := I) (nablaRicci (I := I) S s x) u w
        (coordinateFrameAtToBasis (I := I) x j)
    refine ContinuousOn.congr ?_ (fun s _ => heq s)
    exact ((hnrc u w (coordinateFrameAtToBasis (I := I) x j)).neg.sub
      (hnrc w u (coordinateFrameAtToBasis (I := I) x j))).add
        (hnrc (coordinateFrameAtToBasis (I := I) x j) u w)
  have hmain : ∀ s ∈ Set.Icc (0 : Real) T,
      (S.base.metric 0).inner x (connectionVariationSpeed (I := I) S s x u w) v =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          (∑ j : CoordinateIdx (𝕜 := Real) E,
            coordInv (I := I) S x s x i j *
              koszulRicciCovector (I := I) (nablaRicci (I := I) S s x) u w
                (coordinateFrameAtToBasis (I := I) x j)) *
            (S.base.metric 0).inner x (coordinateFrameAtToBasis (I := I) x i) v := by
    intro s _
    rw [inner_eq_sum_repr (I := I) (S.base.metric 0) (coordinateFrameAtToBasis (I := I) x)
      (connectionVariationSpeed (I := I) S s x u w) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [repr_eq_sum_gInv_mul_inner (I := I) (S.base.metric s)
      (coordinateFrameAtToBasis (I := I) x) (fun i j => coordInv (I := I) S x s x i j)
      (coordInvReal (I := I) S x s) (connectionVariationSpeed (I := I) S s x u w) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact inner_metricSharp (I := I) (S.base.metric s) x
      (koszulRicciCovector (I := I) (nablaRicci (I := I) S s x) u w)
      (coordinateFrameAtToBasis (I := I) x j)
  refine ContinuousOn.congr ?_ hmain
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.mul ?_ continuousOn_const
  exact continuousOn_finsetSum _ fun j _ => (hinvcont i j).mul (hkoscont j)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem intervalIntegrable_sqrt_nablaRmNormSq
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hreg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M,
      IntervalIntegrable
        (fun s : Real => Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y))
        MeasureTheory.volume 0 t := by
  intro t ht y
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le ht.1.le]
  exact (continuousOn_nablaKRm04NormSqIntrinsic_of_subset_regular (I := I) hS 1
    (fun s hs => hreg ⟨hs.1, hs.2.trans ht.2⟩) y).sqrt

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialConnectionDifferenceBound_of_solution_regular_window
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real} {B : Set M}
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega)
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K) :
    InitialConnectionDifferenceBound (I := I) S T B
      (3 * Real.sqrt ((Module.finrank Real E : Real) ^ 5) *
        Real.exp (3 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T))
      (nablaRmTimeIntegral (I := I) S) := by
  have hreg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  exact initialConnectionDifferenceBound_of_connectionVariation (I := I) S hS hT
    (hreg.trans (RealTimeInterval.closedOpen alpha omega halphaomega).regular_subset)
    (fun s hs => hreg ⟨hs.1.le, hs.2⟩) hcurv (Real.sqrt_nonneg _)
    (connectionVariationKoszulOn_connectionVariationSpeed (I := I) S T)
    (nablaRicciNormBoundOn_nablaRicci (I := I) S T)
    (connectionDifferenceTimeIntegralOn_connectionVariationSpeed (I := I) S hS hreg
      (continuousOn_connectionVariationSpeed_pairing (I := I) S hS hreg))
    (intervalIntegrable_sqrt_nablaRmNormSq (I := I) hS hreg)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialDistanceFlowLaplacianBound_of_solution_regular_window
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K Ksec r₁ : Real} {B : Set M} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega)
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (hr₁ : 0 < r₁) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        (2 / r₁ + Real.sqrt (-Ksec)))
      ((Module.finrank Real E : Real) *
        Real.exp (2 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) *
        (3 * Real.sqrt ((Module.finrank Real E : Real) ^ 5) *
          Real.exp (3 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T)))
      (nablaRmSupWeight (I := I) S) := by
  have hreg : Set.Icc (0 : Real) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  have hCconn : (0 : Real) ≤
      3 * Real.sqrt ((Module.finrank Real E : Real) ^ 5) *
        Real.exp (3 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T) := by
    positivity
  have hcont : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M,
      ContinuousOn (fun s : Real => nablaKRm04NormSqIntrinsic (I := I) S 1 s y)
        (Set.Icc 0 t) := by
    intro t ht y
    exact continuousOn_nablaKRm04NormSqIntrinsic_of_subset_regular (I := I) hS 1
      (fun s hs => hreg ⟨hs.1, hs.2.trans ht.2⟩) y
  exact initialDistanceFlowLaplacianBoundOn_of_solution_nablaRmSupWeight (I := I) S hS hT
    (hreg.trans (RealTimeInterval.closedOpen alpha omega halphaomega).regular_subset)
    (fun s hs => hreg ⟨hs.1.le, hs.2⟩) hcurv hr₁ hCconn
    (initialConnectionDifferenceBound_nablaRmSupWeight_of_nablaRmTimeIntegral
      (initialConnectionDifferenceBound_of_solution_regular_window (I := I) S hS
        halpha hT hTomega hcurv) hCconn hcont) p

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem InitialDistanceFlowLaplacianBound.mono_radius
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : Real} {p : M} {B : Set M} {r₁ r₂ Ksec Clap Cconn : Real}
    {Theta : Real → M → Real}
    (h : InitialDistanceFlowLaplacianBound (I := I) S T p B r₁ Ksec Clap Cconn Theta)
    (hle : r₁ ≤ r₂) :
    InitialDistanceFlowLaplacianBound (I := I) S T p B r₂ Ksec Clap Cconn Theta := by
  intro t ht x hxB rho U hU hxU hrhoOn hr₂rho hvalue hupper hgradEq hhess
  exact h t ht x hxB rho U hU hxU hrhoOn (hle.trans hr₂rho) hvalue hupper hgradEq
    hhess

section Theorem

variable [VectorBundle Real E (TangentSpace I : M → Type _)]

theorem shi_local_all_orders_norm_of_solution_uniform
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalUniformBound (Module.finrank Real E) m T R ∧
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalUniformBound (Module.finrank Real E) m T R / Real.sqrt t ^ m := by
  have hR2 : (0 : Real) < R / 2 := by linarith
  have hc : Real.sqrt (-(-1 : Real)) = 1 := by
    norm_num
  have hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y (-1) := fun y hy =>
    sectionalBoundedBelowAt_of_curvature_bound (I := I) S (K := 1) zero_le_one y
      (by simpa using hu 0 ⟨le_rfl, hT.le⟩ y hy)
  have hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I) S T p
        {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal R}
        r (-1) (shiLocalClap (Module.finrank Real E) T R)
        (shiLocalCconn (Module.finrank Real E) T)
        (nablaRmSupWeight (I := I) S) := by
    intro r hr
    rw [← shiLocalClap_eq (Module.finrank Real E) T R hc,
      ← shiLocalCconn_eq (Module.finrank Real E) T]
    exact (initialDistanceFlowLaplacianBound_of_solution_regular_window (I := I) S hS p
      halpha hT hTomega (fun s hs y hy => hu s hs y hy) hR2).mono_radius hr.1.le
  exact shi_local_all_orders_norm_explicit_of_laplacianInput (I := I) S hS p halpha hT
    hTomega hR hball (by norm_num) hsec hu (shiLocalClap_nonneg _ _ hR)
    (shiLocalCconn_nonneg _ _) hlap

theorem shi_local_all_orders_norm_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T R : Real} (p : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C ∧
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
              C / Real.sqrt t ^ m := fun m =>
  ⟨shiLocalUniformBound (Module.finrank Real E) m T R,
    shiLocalUniformBound_nonneg _ _ _ _,
    shi_local_all_orders_norm_of_solution_uniform (I := I) S hS p halpha hT hTomega hR
      hball hu m⟩

theorem shi_local_all_orders_curvature_scale_of_solution_uniform
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T K R : Real} (p : M)
    (halpha : alpha < 0) (hK : 0 < K) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (h0 : (0 : Real) ∈
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (R / (2 * Real.sqrt K)) →
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalUniformBound (Module.finrank Real E) m (K * T) R * K ∧
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalUniformBound (Module.finrank Real E) m (K * T) R * K /
              Real.sqrt t ^ m := by
  have hsec : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
      ENNReal.ofReal (R / Real.sqrt K) →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          (S.base.metric 0) y (-K) := fun y hy =>
    sectionalBoundedBelowAt_of_curvature_bound (I := I) S hK.le y
      (hu 0 ⟨le_rfl, hT.le⟩ y hy)
  have hKne : K ≠ 0 := ne_of_gt hK
  have hc : Real.sqrt (-(-K / K)) = 1 := by
    rw [neg_div, neg_neg, div_self hKne, Real.sqrt_one]
  have hR2 : (0 : Real) < R / 2 := by linarith
  have hradius : Real.sqrt K * (R / Real.sqrt K) = R := by
    have hsk : (0 : Real) < Real.sqrt K := Real.sqrt_pos.mpr hK
    field_simp
  have hballEq : {y : M |
      riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
          ENNReal.ofReal R} =
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    have h := closedBall_scaleMetric_eq (I := I) (S.base.metric 0) K hK p
      (R / Real.sqrt K)
    rw [hradius] at h
    rw [curvatureScaleSolution_metric_zero (I := I) S hK h0]
    exact h
  have hu' : ∀ s ∈ Set.Icc (0 : Real) (K * T), ∀ y ∈ {z : M |
      riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p z ≤
          ENNReal.ofReal R},
      nablaKRm04NormSqIntrinsic (I := I) (curvatureScaleSolution (I := I) S hK h0) 0 s y
        ≤ 1 := by
    intro s hs y hy
    rw [hballEq] at hy
    have hy' : riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) := hy
    rw [nablaKRm04NormSqIntrinsic_curvatureScaleSolution (I := I) S hK h0 0 s y]
    have hsK : s / K ∈ Set.Icc (0 : Real) T := by
      refine ⟨div_nonneg hs.1 hK.le, ?_⟩
      rw [div_le_iff₀ hK]
      calc s ≤ K * T := hs.2
        _ = T * K := by ring
    have hb := hu (s / K) hsK y hy'
    have hpow : (0 : Real) ≤ (K⁻¹) ^ (2 + 0) := by positivity
    calc (K⁻¹) ^ (2 + 0) * nablaKRm04NormSqIntrinsic (I := I) S 0 (s / K) y
        ≤ (K⁻¹) ^ (2 + 0) * K ^ 2 := mul_le_mul_of_nonneg_left hb hpow
      _ = 1 := by
          have h2 : (K⁻¹ : Real) ^ (2 + 0) = (K⁻¹ : Real) ^ 2 := by norm_num
          rw [h2, ← mul_pow, inv_mul_cancel₀ hKne, one_pow]
  have hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I)
        (curvatureScaleSolution (I := I) S hK h0) (K * T) p
        {y : M | riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
            ENNReal.ofReal R}
        r (-K / K)
        (shiLocalClap (Module.finrank Real E) (K * T) R)
        (shiLocalCconn (Module.finrank Real E) (K * T))
        (nablaRmSupWeight (I := I) (curvatureScaleSolution (I := I) S hK h0)) := by
    intro r hr
    rw [← shiLocalClap_eq (Module.finrank Real E) (K * T) R hc,
      ← shiLocalCconn_eq (Module.finrank Real E) (K * T)]
    exact (initialDistanceFlowLaplacianBound_of_solution_regular_window (I := I)
      (curvatureScaleSolution (I := I) S hK h0)
      (isSolutionOn_curvatureScaleSolution (I := I) S hS hK h0) p
      (mul_neg_of_pos_of_neg hK halpha) (mul_pos hK hT)
      (mul_lt_mul_of_pos_left hTomega hK) hu' hR2).mono_radius hr.1.le
  exact shi_local_all_orders_curvature_scale_explicit_of_laplacianInput (I := I) S hS p
    halpha hK hT hTomega hR h0 hball (by linarith : (-K : Real) ≤ 0) hsec hu
    (shiLocalClap_nonneg _ _ hR) (shiLocalCconn_nonneg _ _) hlap

theorem shi_local_all_orders_curvature_scale_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T K R : Real} (p : M)
    (halpha : alpha < 0) (hK : 0 < K) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (h0 : (0 : Real) ∈
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
            ENNReal.ofReal (R / (2 * Real.sqrt K)) →
          Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C * K ∧
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
              C * K / Real.sqrt t ^ m := fun m =>
  ⟨shiLocalUniformBound (Module.finrank Real E) m (K * T) R,
    shiLocalUniformBound_nonneg _ _ _ _,
    shi_local_all_orders_curvature_scale_of_solution_uniform (I := I) S hS p halpha hK hT
      hTomega hR h0 hball hu m⟩

variable (I) in
theorem shi_local_all_orders_uniform_constant
    (m : ℕ) {T K R : Real}
    (hT : 0 < T) (hK : 0 < K) (hR : 0 < R) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle Real E (TangentSpace I : M → Type _)]
        {alpha omega : Real} {halphaomega : alpha < omega}
        (Sc : SolutionOn (I := I) (M := M)
          (RealTimeInterval.closedOpen alpha omega halphaomega)),
        IsSolutionOn (I := I) Sc → ∀ p : M, alpha < 0 → T < omega →
        IsCompact {y : M |
          riemannianEDistOf (I := I) (Sc.base.metric 0) p y ≤
            ENNReal.ofReal (R / Real.sqrt K)} →
        (∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
          riemannianEDistOf (I := I) (Sc.base.metric 0) p y ≤
              ENNReal.ofReal (R / Real.sqrt K) →
            nablaKRm04NormSqIntrinsic (I := I) Sc 0 s y ≤ K ^ 2) →
        ∀ tau ∈ Set.Ioc (0 : Real) T, ∀ z : M,
          riemannianEDistOf (I := I) (Sc.base.metric 0) p z ≤
              ENNReal.ofReal (R / (2 * Real.sqrt K)) →
            Real.sqrt (tau ^ m * nablaKRm04NormSqIntrinsic (I := I) Sc m tau z) ≤
              C * K := by
  refine ⟨shiLocalUniformBound (Module.finrank Real E) m (K * T) R,
    shiLocalUniformBound_nonneg _ _ _ _, ?_⟩
  intro M _ _ _ _ _ _ _ _ alpha omega halphaomega Sc hSc p halpha hTomega hball hu tau
    htau z hz
  have h0 : (0 : Real) ∈
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
    ⟨halpha.le, lt_trans hT hTomega⟩
  exact (shi_local_all_orders_curvature_scale_of_solution_uniform (I := I) Sc hSc p halpha
    hK hT hTomega hR h0 hball hu m tau htau z hz).1

end Theorem

end RegularWindow

end DifferentialGeometry.PDE.RicciFlow

end
