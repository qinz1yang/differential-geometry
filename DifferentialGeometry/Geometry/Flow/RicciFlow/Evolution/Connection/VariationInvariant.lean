import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Sections
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialConnectionDifference

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology Bundle BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]



def nablaRicci
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) (y : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y :=
  metricNablaRic (I := I) (M := M) (S.base.metric s) y

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRicTraceAt_nablaRicci
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {y : M} (basis : Module.Basis Idx Real (TangentSpace I y))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) (S.base.metric s) y basis gInv) :
    NablaRicTraceAt (I := I) basis gInv
      (nablaKRm04Field (I := I) S s 1 y) (nablaRicci (I := I) S s y) := by
  have h := levi_civita_covariant_ricci_eq_riemann_trace (I := I) (M := M)
    (S.base.metric s) basis gInv hinv
  intro A B C
  exact h A B C



omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem exists_metricOrthonormalBasis
    (g : SmoothRiemannianMetric I M) (y : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I y))) Real
        (TangentSpace I y),
      ∀ i j, g.inner y (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let Dat := (tangentMetricDataGen (I := I) g y).metric
  let _ : InnerProductSpace.Core Real (TangentSpace I y) := Dat.toCore
  let _ : NormedAddCommGroup (TangentSpace I y) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I y) _ _ _ Dat.toCore
  let _ : InnerProductSpace Real (TangentSpace I y) :=
    @InnerProductSpace.ofCore Real (TangentSpace I y) _ _ _ Dat.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I y)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = Dat.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner Dat (ob i) (ob j)
  change g.inner y (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricDataGen.inner_eq_gen
    (tangentMetricDataGen (I := I) g y) (ob.toBasis i) (ob.toBasis j)]
  change Dat.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem metricInverseInBasis_identity_of_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {y : M}
    (b : Module.Basis Idx Real (TangentSpace I y))
    (hON : ∀ i j, g.inner y (b i) (b j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis (I := I) g y b (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] in
private theorem normSq0S_le_of_nablaRicTraceAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {y : M}
    (basis : Module.Basis Idx Real (TangentSpace I y))
    (hinv : MetricInverseInBasis (I := I) g y basis (identityInvMetric (Idx := Idx)))
    (NRm : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 y)
    (NRic : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y)
    (htrace : NablaRicTraceAt (I := I) basis (identityInvMetric (Idx := Idx)) NRm NRic) :
    normSq0S (I := I) g y 3 NRic ≤
      (Fintype.card Idx : Real) ^ 5 * normSq0S (I := I) g y 5 NRm := by
  classical
  have hsrc : 0 ≤ normSq0S (I := I) g y 5 NRm := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g y 5 basis hinv NRm]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomp : ∀ slots : Fin 3 → Idx,
      component0S (I := I) basis NRic slots =
        ∑ i : Idx,
          component0S (I := I) basis NRm ![slots 0, i, slots 1, slots 2, i] := by
    intro slots
    have hv3 : (fun a : Fin 3 => basis (slots a)) =
        vec3 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
      funext a
      fin_cases a <;> simp [vec3]
    rw [component0S_apply, hv3,
      htrace (basis (slots 0)) (basis (slots 1)) (basis (slots 2))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hv5 : (fun a : Fin 5 => basis (![slots 0, i, slots 1, slots 2, i] a)) =
        vec5 (I := I) (basis (slots 0)) (basis i) (basis (slots 1))
          (basis (slots 2)) (basis i) := by
      funext a
      fin_cases a <;> simp [vec5]
    rw [component0S_apply, hv5]
    simp [identityInvMetric, diagonalInvMetric]
  have habs : ∀ slots : Fin 3 → Idx,
      |component0S (I := I) basis NRic slots| ≤
        (Fintype.card Idx : Real) * Real.sqrt (normSq0S (I := I) g y 5 NRm) := by
    intro slots
    rw [hcomp slots]
    calc |∑ i : Idx, component0S (I := I) basis NRm ![slots 0, i, slots 1, slots 2, i]|
        ≤ ∑ i : Idx,
            |component0S (I := I) basis NRm ![slots 0, i, slots 1, slots 2, i]| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Idx, Real.sqrt (normSq0S (I := I) g y 5 NRm) :=
          Finset.sum_le_sum fun i _ =>
            component_le_sqrt (I := I) g basis hinv NRm
              ![slots 0, i, slots 1, slots 2, i]
      _ = (Fintype.card Idx : Real) * Real.sqrt (normSq0S (I := I) g y 5 NRm) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [normSq0S_identity_eq_sum_sq (I := I) g y 3 basis hinv NRic]
  calc ∑ slots : Fin 3 → Idx, (component0S (I := I) basis NRic slots) ^ 2
      ≤ ∑ _slots : Fin 3 → Idx,
          ((Fintype.card Idx : Real) *
            Real.sqrt (normSq0S (I := I) g y 5 NRm)) ^ 2 := by
        refine Finset.sum_le_sum fun slots _ => ?_
        obtain ⟨hlo, hhi⟩ := abs_le.mp (habs slots)
        exact sq_le_sq' hlo hhi
    _ = (Fintype.card (Fin 3 → Idx) : Real) *
        ((Fintype.card Idx : Real) *
          Real.sqrt (normSq0S (I := I) g y 5 NRm)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card Idx : Real) ^ 5 * normSq0S (I := I) g y 5 NRm := by
        rw [Fintype.card_fun, Fintype.card_fin, mul_pow, Real.sq_sqrt hsrc]
        push_cast
        ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRicciNormBoundOn_nablaRicci
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real) :
    NablaRicciNormBoundOn (I := I) S T
      (Real.sqrt ((Module.finrank Real E : Real) ^ 5)) (nablaRicci (I := I) S) := by
  classical
  intro s _ y
  obtain ⟨b, hON⟩ := exists_metricOrthonormalBasis (I := I) (S.base.metric s) y
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) (S.base.metric s) b hON
  have htrace := nablaRicTraceAt_nablaRicci (I := I) S s b
    (identityInvMetric
      (Idx := Fin (Module.finrank Real (TangentSpace I y)))) hinv
  have hbound := normSq0S_le_of_nablaRicTraceAt (I := I) (S.base.metric s) b hinv
    (nablaKRm04Field (I := I) S s 1 y) (nablaRicci (I := I) S s y) htrace
  have hcard : (Fintype.card (Fin (Module.finrank Real (TangentSpace I y))) : Real) =
      (Module.finrank Real E : Real) := by
    rw [Fintype.card_fin]
    rfl
  rw [hcard] at hbound
  have hfinal : normSq0S (I := I) (S.base.metric s) y 3 (nablaRicci (I := I) S s y) ≤
      (Module.finrank Real E : Real) ^ 5 *
        nablaKRm04NormSqIntrinsic (I := I) S 1 s y := hbound
  calc Real.sqrt (normSq0S (I := I) (S.base.metric s) y 3 (nablaRicci (I := I) S s y))
      ≤ Real.sqrt ((Module.finrank Real E : Real) ^ 5 *
          nablaKRm04NormSqIntrinsic (I := I) S 1 s y) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt ((Module.finrank Real E : Real) ^ 5) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y) :=
        Real.sqrt_mul (by positivity) _



omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec3_update_zero {y : M} (p q r z : TangentSpace I y) :
    Function.update (vec3 (I := I) p q r) 0 z = vec3 (I := I) z q r := by
  funext a
  fin_cases a <;> simp [vec3, Function.update]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec3_update_two {y : M} (p q r z : TangentSpace I y) :
    Function.update (vec3 (I := I) p q r) 2 z = vec3 (I := I) p q z := by
  funext a
  fin_cases a <;> simp [vec3, Function.update]

def koszulRicciCovector {y : M}
    (NRy : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y)
    (u w : TangentSpace I y) : TangentSpace I y →ₗ[Real] Real where
  toFun v :=
    -NRy (vec3 (I := I) u w v) - NRy (vec3 (I := I) w u v)
      + NRy (vec3 (I := I) v u w)
  map_add' := by
    intro a b
    have h1 := NRy.map_update_add (vec3 (I := I) u w a) 2 a b
    have h2 := NRy.map_update_add (vec3 (I := I) w u a) 2 a b
    have h3 := NRy.map_update_add (vec3 (I := I) a u w) 0 a b
    simp only [vec3_update_two, vec3_update_zero] at h1 h2 h3
    rw [h1, h2, h3]
    ring
  map_smul' := by
    intro c a
    have h1 := NRy.map_update_smul (vec3 (I := I) u w a) 2 c a
    have h2 := NRy.map_update_smul (vec3 (I := I) w u a) 2 c a
    have h3 := NRy.map_update_smul (vec3 (I := I) a u w) 0 c a
    simp only [vec3_update_two, vec3_update_zero] at h1 h2 h3
    rw [h1, h2, h3]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem koszulRicciCovector_apply {y : M}
    (NRy : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y)
    (u w v : TangentSpace I y) :
    koszulRicciCovector (I := I) NRy u w v =
      -NRy (vec3 (I := I) u w v) - NRy (vec3 (I := I) w u v)
        + NRy (vec3 (I := I) v u w) := rfl

def connectionVariationSpeed
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) (y : M)
    (u w : TangentSpace I y) : TangentSpace I y :=
  metricSharp (I := I) (S.base.metric s) y
    (koszulRicciCovector (I := I) (nablaRicci (I := I) S s y) u w)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionVariationKoszulOn_connectionVariationSpeed
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real) :
    ConnectionVariationKoszulOn (I := I) S T
      (connectionVariationSpeed (I := I) S) (nablaRicci (I := I) S) := by
  intro s _ y u w v
  exact inner_metricSharp (I := I) (S.base.metric s) y
    (koszulRicciCovector (I := I) (nablaRicci (I := I) S s y) u w) v



def ConnectionDifferenceTimeDerivativeOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y) :
    Prop :=
  ∀ s ∈ Set.Icc (0 : Real) T, ∀ x : M, ∀ u w v : TangentSpace I x,
    HasDerivWithinAt
      (fun r : Real => (S.base.metric 0).inner x
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric r))
          (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
      ((S.base.metric 0).inner x (Z s x u w) v) (Set.Icc (0 : Real) T) s

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] in
private theorem connectionDifference_metric_zero_self
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.difference
        (LeviCivita (I := I) (S.base.metric 0))
        (LeviCivita (I := I) (S.base.metric 0)) x u w = 0 := by
  have h := congrFun
    (DifferentialGeometry.PDE.DeTurck.connectionDifference_self
      (I := I) (S.base.metric 0)) x
  have h2 := congrArg
    (fun A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
      A u w) h
  simpa [DifferentialGeometry.PDE.DeTurck.connectionDifference] using h2

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] in
theorem connectionDifferenceTimeIntegralOn_of_hasDerivWithinAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {T : Real}
    {Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y}
    (hderiv : ConnectionDifferenceTimeDerivativeOn (I := I) S T Z)
    (hcont : ∀ x : M, ∀ u w v : TangentSpace I x,
      ContinuousOn (fun s : Real => (S.base.metric 0).inner x (Z s x u w) v)
        (Set.Icc (0 : Real) T)) :
    ConnectionDifferenceTimeIntegralOn (I := I) S T Z := by
  intro t ht x u w v
  obtain ⟨ht0, htT⟩ := ht
  have hsub : Set.Icc (0 : Real) t ⊆ Set.Icc (0 : Real) T :=
    Set.Icc_subset_Icc le_rfl htT
  have hint : IntervalIntegrable
      (fun s : Real => (S.base.metric 0).inner x (Z s x u w) v)
      MeasureTheory.volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht0.le]
    exact (hcont x u w v).mono hsub
  refine ⟨hint, ?_⟩
  have hpair : ∀ s ∈ Set.Icc (0 : Real) T,
      HasDerivWithinAt
        (fun r : Real => (S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric r))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
        ((S.base.metric 0).inner x (Z s x u w) v) (Set.Icc (0 : Real) T) s :=
    fun s hs => hderiv s hs x u w v
  have hcontF : ContinuousOn
      (fun r : Real => (S.base.metric 0).inner x
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric r))
          (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
      (Set.Icc (0 : Real) t) := by
    intro s hs
    exact ((hpair s (hsub hs)).continuousWithinAt).mono hsub
  have hright : ∀ s ∈ Set.Ioo (0 : Real) t,
      HasDerivWithinAt
        (fun r : Real => (S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric r))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
        ((S.base.metric 0).inner x (Z s x u w) v) (Set.Ioi s) s := by
    intro s hs
    have hsT : s < T := lt_of_lt_of_le hs.2 htT
    have hnhds : Set.Icc (0 : Real) T ∈ nhds s := Icc_mem_nhds hs.1 hsT
    exact ((hpair s ⟨hs.1.le, hsT.le⟩).hasDerivAt hnhds).hasDerivWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    ht0.le hcontF hright hint
  rw [hftc]
  simp [connectionDifference_metric_zero_self (I := I) S x u w]

end DifferentialGeometry.PDE.RicciFlow
