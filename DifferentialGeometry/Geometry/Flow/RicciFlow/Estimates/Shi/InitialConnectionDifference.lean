import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Family.Basic
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceLaplacian

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]



private theorem sqrt_le_of_le_mul_sqrt {a B : Real} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (h : a ≤ B * Real.sqrt a) : Real.sqrt a ≤ B := by
  rcases (Real.sqrt_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact hB
  · nlinarith [Real.mul_self_sqrt ha]

private theorem sqrt_le_exp_mul_sqrt {a b c : Real}
    (h : a ≤ Real.exp (2 * c) * b) :
    Real.sqrt a ≤ Real.exp c * Real.sqrt b := by
  have hrw : Real.exp (2 * c) * b = Real.exp c ^ 2 * b := by
    rw [show (2 : Real) * c = c + c by ring, Real.exp_add]
    ring
  rw [hrw] at h
  calc Real.sqrt a ≤ Real.sqrt (Real.exp c ^ 2 * b) := Real.sqrt_le_sqrt h
    _ = Real.exp c * Real.sqrt b := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_nonneg c)]



def ConnectionVariationKoszulOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y)
    (NR : Real → (y : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y) :
    Prop :=
  ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M, ∀ u w v : TangentSpace I y,
    (S.base.metric s).inner y (Z s y u w) v =
      -(NR s y) (vec3 (I := I) u w v) - (NR s y) (vec3 (I := I) w u v)
        + (NR s y) (vec3 (I := I) v u w)

def ConnectionDifferenceTimeIntegralOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y) :
    Prop :=
  ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M, ∀ u w v : TangentSpace I x,
    IntervalIntegrable
        (fun s : Real => (S.base.metric 0).inner x (Z s x u w) v)
        MeasureTheory.volume 0 t ∧
      (S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric t))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v =
        ∫ s in (0 : Real)..t, (S.base.metric 0).inner x (Z s x u w) v

def NablaRicciNormBoundOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T cn : Real)
    (NR : Real → (y : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y) :
    Prop :=
  ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
    Real.sqrt (normSq0S (I := I) (S.base.metric s) y 3 (NR s y)) ≤
      cn * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y)



omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] in
private theorem sqrt_metric_speed_bound
    (g₀ g : SmoothRiemannianMetric I M) (y : M)
    (NRy : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 y)
    (Zy a b : TangentSpace I y) {r c : Real}
    (hkos : ∀ v : TangentSpace I y,
      g.inner y Zy v =
        -NRy (vec3 (I := I) a b v) - NRy (vec3 (I := I) b a v)
          + NRy (vec3 (I := I) v a b))
    (hr : 0 ≤ r)
    (hNR : Real.sqrt (normSq0S (I := I) g y 3 NRy) ≤ r)
    (hlow : ∀ v : TangentSpace I y,
      Real.sqrt (g₀.inner y v v) ≤ Real.exp c * Real.sqrt (g.inner y v v))
    (hup : ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) ≤ Real.exp c * Real.sqrt (g₀.inner y v v)) :
    Real.sqrt (g₀.inner y Zy Zy) ≤
      3 * r * Real.exp (3 * c) *
        Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
  classical
  have hprod : ∀ p q z : TangentSpace I y,
      (∏ i : Fin 3, Real.sqrt (g.inner y
          (vec3 (I := I) p q z i) (vec3 (I := I) p q z i))) =
        Real.sqrt (g.inner y p p) * Real.sqrt (g.inner y q q) *
          Real.sqrt (g.inner y z z) := by
    intro p q z
    rw [Fin.prod_univ_three]
    simp [vec3]
  have hterm : ∀ p q z : TangentSpace I y,
      |NRy (vec3 (I := I) p q z)| ≤
        Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          (Real.sqrt (g.inner y p p) * Real.sqrt (g.inner y q q) *
            Real.sqrt (g.inner y z z)) := by
    intro p q z
    have h := abs_apply_le_norm0S (I := I) g y 3 NRy (vec3 (I := I) p q z)
    rw [hprod p q z] at h
    exact h
  have hNRnn : 0 ≤ Real.sqrt (normSq0S (I := I) g y 3 NRy) := Real.sqrt_nonneg _
  have hpair : ∀ v : TangentSpace I y,
      |g.inner y Zy v| ≤
        3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) *
          Real.sqrt (g.inner y v v) := by
    intro v
    rw [hkos v]
    obtain ⟨h1a, h1b⟩ := abs_le.mp (hterm a b v)
    obtain ⟨h2a, h2b⟩ := abs_le.mp (hterm b a v)
    obtain ⟨h3a, h3b⟩ := abs_le.mp (hterm v a b)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hZg : Real.sqrt (g.inner y Zy Zy) ≤
      3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
        Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) := by
    refine sqrt_le_of_le_mul_sqrt
      (DifferentialGeometry.metric_inner_self_nonneg
        (I := I) (M := M) g y Zy)
      (by positivity) ?_
    exact le_trans (le_abs_self _) (hpair Zy)
  have hstep1 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) ≤ 3 * r :=
    mul_le_mul_of_nonneg_left hNR (by norm_num)
  have hstep2 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
      Real.sqrt (g.inner y a a) ≤
      3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) :=
    mul_le_mul hstep1 (hup a) (Real.sqrt_nonneg _) (by linarith)
  have hstep3 : 3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
      Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b) ≤
      3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) *
        (Real.exp c * Real.sqrt (g₀.inner y b b)) := by
    refine mul_le_mul hstep2 (hup b) (Real.sqrt_nonneg _) ?_
    have : 0 ≤ Real.exp c * Real.sqrt (g₀.inner y a a) := by positivity
    nlinarith [hr]
  have hexp3 : Real.exp (3 * c) = Real.exp c * Real.exp c * Real.exp c := by
    rw [show (3 : Real) * c = c + c + c by ring, Real.exp_add, Real.exp_add]
  calc Real.sqrt (g₀.inner y Zy Zy)
      ≤ Real.exp c * Real.sqrt (g.inner y Zy Zy) := hlow Zy
    _ ≤ Real.exp c * (3 * Real.sqrt (normSq0S (I := I) g y 3 NRy) *
          Real.sqrt (g.inner y a a) * Real.sqrt (g.inner y b b)) :=
        mul_le_mul_of_nonneg_left hZg (Real.exp_nonneg c)
    _ ≤ Real.exp c * (3 * r * (Real.exp c * Real.sqrt (g₀.inner y a a)) *
          (Real.exp c * Real.sqrt (g₀.inner y b b))) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.exp_nonneg c)
    _ = 3 * r * Real.exp (3 * c) *
          Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
        rw [hexp3]
        ring



omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem initialConnectionDifferenceBound_of_connectionVariation
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K cn : Real} {B : Set M}
    (_hT : 0 < T)
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
    (hnablaRmInt : ∀ t ∈ Set.Ioc (0 : Real) T, ∀ y : M,
      IntervalIntegrable
        (fun s : Real => Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y))
        MeasureTheory.volume 0 t) :
    InitialConnectionDifferenceBound (I := I) S T B
      (3 * cn *
        Real.exp (3 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) * T))
      (nablaRmTimeIntegral (I := I) S) := by
  classical
  set dR : Real := (Module.finrank Real E : Real) with hdR
  set Lam : Real := dR ^ 2 * Real.sqrt K with hLam
  set Cc : Real := 3 * cn * Real.exp (3 * Lam * T) with hCc
  have hLam0 : 0 ≤ Lam := by
    rw [hLam, hdR]
    positivity
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]
    exact mul_nonneg (mul_nonneg (by norm_num) hcn) (Real.exp_pos _).le
  have hcurv0 : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B,
      normSq0S (I := I) (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K := by
    intro s hs y hy
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y hy
  have hricQuad : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) (S.base.metric s) y v v| ≤
        Lam * (S.base.metric s).inner y v v := by
    intro s hs y hy v
    rw [hLam, hdR]
    exact ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S y v (hcurv0 s hs y hy)
  have hpde := metricPDE_Icc (I := I) S hS hslab
    (fun _ h => hreg ⟨h.1, h.2.le⟩)
  have hequiv :=
    metricEquiv_Icc_on (I := I) (fun s => S.base.metric s) B hpde hricQuad
  have hcompare : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B, ∀ v : TangentSpace I y,
      (S.base.metric 0).inner y v v ≤
        Real.exp (2 * (Lam * s)) * (S.base.metric s).inner y v v := by
    intro s hs y hy v
    have hlo' : Real.exp (-(2 * Lam * s)) * (S.base.metric 0).inner y v v ≤
        (S.base.metric s).inner y v v := by
      simpa only [sub_zero] using (hequiv s hs y hy v).1
    have hmul := mul_le_mul_of_nonneg_left hlo' (Real.exp_pos (2 * Lam * s)).le
    have heq : Real.exp (2 * Lam * s) *
        (Real.exp (-(2 * Lam * s)) * (S.base.metric 0).inner y v v) =
        (S.base.metric 0).inner y v v := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [heq] at hmul
    rw [show (2 : Real) * (Lam * s) = 2 * Lam * s by ring]
    exact hmul
  have hupper : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B, ∀ v : TangentSpace I y,
      (S.base.metric s).inner y v v ≤
        Real.exp (2 * (Lam * s)) * (S.base.metric 0).inner y v v := by
    intro s hs y hy v
    have h := (hequiv s hs y hy v).2
    simp only [sub_zero] at h
    rw [show (2 : Real) * (Lam * s) = 2 * Lam * s by ring]
    exact h
  have hspeed : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ B,
      ∀ a b : TangentSpace I y,
        Real.sqrt ((S.base.metric 0).inner y (Z s y a b) (Z s y a b)) ≤
          Cc * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y) *
            Real.sqrt ((S.base.metric 0).inner y a a) *
            Real.sqrt ((S.base.metric 0).inner y b b) := by
    intro s hs y hy a b
    have hcore := sqrt_metric_speed_bound (I := I)
      (S.base.metric 0) (S.base.metric s) y (NR s y) (Z s y a b) a b
      (r := cn * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y))
      (c := Lam * s)
      (fun v => hkoszul s hs y a b v)
      (mul_nonneg hcn (Real.sqrt_nonneg _))
      (hNR s hs y)
      (fun v => sqrt_le_exp_mul_sqrt (hcompare s hs y hy v))
      (fun v => sqrt_le_exp_mul_sqrt (hupper s hs y hy v))
    refine hcore.trans ?_
    have hexp : Real.exp (3 * (Lam * s)) ≤ Real.exp (3 * Lam * T) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hs.1, hs.2, hLam0]
    have hfront : 3 * (cn * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y)) *
        Real.exp (3 * (Lam * s)) ≤
        Cc * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s y) := by
      rw [hCc]
      nlinarith [mul_nonneg hcn
        (Real.sqrt_nonneg (nablaKRm04NormSqIntrinsic (I := I) S 1 s y)), hexp]
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  intro t ht x hxB u w
  have ht0 : (0 : Real) < t := ht.1
  have htT : t ≤ T := ht.2
  have hThetann : 0 ≤ nablaRmTimeIntegral (I := I) S t x :=
    nablaRmTimeIntegral_nonneg (I := I) S ht0.le x
  have key : ∀ v : TangentSpace I x,
      |(S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric t))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v| ≤
        Cc * nablaRmTimeIntegral (I := I) S t x *
          Real.sqrt ((S.base.metric 0).inner x u u) *
          Real.sqrt ((S.base.metric 0).inner x w w) *
          Real.sqrt ((S.base.metric 0).inner x v v) := by
    intro v
    obtain ⟨hZint, hZeq⟩ := hrep t ht x u w v
    rw [hZeq]
    have hpt : ∀ s ∈ Set.Icc (0 : Real) t,
        |(S.base.metric 0).inner x (Z s x u w) v| ≤
          (Cc * Real.sqrt ((S.base.metric 0).inner x u u) *
              Real.sqrt ((S.base.metric 0).inner x w w) *
              Real.sqrt ((S.base.metric 0).inner x v v)) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x) := by
      intro s hs
      have hsT : s ∈ Set.Icc (0 : Real) T := ⟨hs.1, hs.2.trans htT⟩
      calc |(S.base.metric 0).inner x (Z s x u w) v|
          ≤ Real.sqrt ((S.base.metric 0).inner x (Z s x u w) (Z s x u w)) *
              Real.sqrt ((S.base.metric 0).inner x v v) :=
            DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
              (I := I) (M := M)
              (S.base.metric 0) x (Z s x u w) v
        _ ≤ (Cc * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x) *
              Real.sqrt ((S.base.metric 0).inner x u u) *
              Real.sqrt ((S.base.metric 0).inner x w w)) *
              Real.sqrt ((S.base.metric 0).inner x v v) :=
            mul_le_mul_of_nonneg_right (hspeed s hsT x hxB u w) (Real.sqrt_nonneg _)
        _ = _ := by ring
    calc |∫ s in (0 : Real)..t, (S.base.metric 0).inner x (Z s x u w) v|
        ≤ ∫ s in (0 : Real)..t, |(S.base.metric 0).inner x (Z s x u w) v| :=
          intervalIntegral.abs_integral_le_integral_abs ht0.le
      _ ≤ ∫ s in (0 : Real)..t,
            (Cc * Real.sqrt ((S.base.metric 0).inner x u u) *
                Real.sqrt ((S.base.metric 0).inner x w w) *
                Real.sqrt ((S.base.metric 0).inner x v v)) *
              Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 s x) :=
          intervalIntegral.integral_mono_on ht0.le hZint.abs
            ((hnablaRmInt t ht x).const_mul _) hpt
      _ = (Cc * Real.sqrt ((S.base.metric 0).inner x u u) *
              Real.sqrt ((S.base.metric 0).inner x w w) *
              Real.sqrt ((S.base.metric 0).inner x v v)) *
            nablaRmTimeIntegral (I := I) S t x := by
          rw [intervalIntegral.integral_const_mul]
          rfl
      _ = _ := by ring
  refine sqrt_le_of_le_mul_sqrt
    (DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) (S.base.metric 0) x _)
    (mul_nonneg (mul_nonneg (mul_nonneg hCc0 hThetann) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))
    (le_trans (le_abs_self _) (key _))

end DifferentialGeometry.PDE.RicciFlow
