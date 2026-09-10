import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local instance metricCurvatureDifferenceOne : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

local instance metricCurvatureDifferenceTopSucc : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

private def metricVectorNorm (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : ℝ := Real.sqrt (g.inner x v v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metricVectorNorm_nonneg (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) : 0 ≤ metricVectorNorm g x v :=
  Real.sqrt_nonneg _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metricVectorNorm_add_le (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    metricVectorNorm g x (v + w) ≤ metricVectorNorm g x v + metricVectorNorm g x w :=
  sqrt_inner_add_le g x v w

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metricVectorNorm_sub_le (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    metricVectorNorm g x (v - w) ≤ metricVectorNorm g x v + metricVectorNorm g x w := by
  simpa only [sub_eq_add_neg, metricVectorNorm, map_neg, neg_apply, neg_neg] using
    metricVectorNorm_add_le g x v (-w)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metric_inner_abs_le (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ metricVectorNorm g x v * metricVectorNorm g x w := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hi (a b : TangentSpace I x) : g.inner x a b = inner ℝ a b := by
    rw [← TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen (I := I) g x) a b]
    exact (MetricFiberData.toCore_inner D a b).symm
  have hn (a : TangentSpace I x) : metricVectorNorm g x a = ‖a‖ := by
    rw [metricVectorNorm, hi, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]
  rw [hi, hn, hn]
  exact abs_real_inner_le_norm v w

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem metric_inner_abs_le_of_equivalent
    {g h : SmoothRiemannianMetric I M} {x : M} {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) {x} g h Λ)
    (v w : TangentSpace I x) :
    |h.inner x v w| ≤ Λ * metricVectorNorm g x v * metricVectorNorm g x w := by
  have hΛ : 0 ≤ Λ := (zero_le_one.trans hEq.1)
  have hn (a : TangentSpace I x) :
      metricVectorNorm h x a ≤ Real.sqrt Λ * metricVectorNorm g x a := by
    calc
      _ ≤ Real.sqrt (Λ * g.inner x a a) :=
        Real.sqrt_le_sqrt (hEq.2 x (Set.mem_singleton x) a).2
      _ = _ := Real.sqrt_mul hΛ _
  calc
    _ ≤ metricVectorNorm h x v * metricVectorNorm h x w := metric_inner_abs_le h x v w
    _ ≤ (Real.sqrt Λ * metricVectorNorm g x v) *
        (Real.sqrt Λ * metricVectorNorm g x w) :=
      mul_le_mul (hn v) (hn w) (metricVectorNorm_nonneg h x w)
        (mul_nonneg (Real.sqrt_nonneg _) (metricVectorNorm_nonneg g x v))
    _ = Λ * metricVectorNorm g x v * metricVectorNorm g x w := by
      calc
        _ = (Real.sqrt Λ) ^ 2 * metricVectorNorm g x v * metricVectorNorm g x w := by ring
        _ = _ := by rw [Real.sq_sqrt hΛ]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
private theorem metric_inner_difference_le
    (g h : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |h.inner x v w - g.inner x v w| ≤
      metricDerivNorm (I := I) 0 h g g x * metricVectorNorm g x v *
        metricVectorNorm g x w := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) g x
  have ht := abs_apply_le_sqrt_normSq0S (I := I) (g := g) (x := x) (s := 2)
    b hb (metricDiffCovDerivAt (I := I) 0 h g g x) ![v, w]
  change |metricDiffCovDerivAt (I := I) 0 h g g x (vec2 (I := I) v w)| ≤ _ at ht
  rw [metricDiffCovDerivAt_zero_apply] at ht
  simpa only [metricDerivNorm,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    metricVectorNorm, mul_assoc] using ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem riemannOp_difference_eq
    (g h : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) h) x v w u -
        riemannOp (cov := LeviCivita (I := I) g) x v w u =
      (covDerivConnectionDifference (I := I) g h
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x -
        covDerivConnectionDifference (I := I) g h
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x u) x) +
      ((CovariantDerivative.difference (LeviCivita (I := I) h)
          (LeviCivita (I := I) g) x
          (CovariantDerivative.difference (LeviCivita (I := I) h)
            (LeviCivita (I := I) g) x u w) v) -
        (CovariantDerivative.difference (LeviCivita (I := I) h)
          (LeviCivita (I := I) g) x
          (CovariantDerivative.difference (LeviCivita (I := I) h)
            (LeviCivita (I := I) g) x u v) w)) := by
  let V := smoothExtensionTangent (I := I) x v
  let W := smoothExtensionTangent (I := I) x w
  let U := smoothExtensionTangent (I := I) x u
  have hV := smoothExtensionTangent_contMDiff (I := I) x v
  have hW := smoothExtensionTangent_contMDiff (I := I) x w
  have hU := smoothExtensionTangent_contMDiff (I := I) x u
  have hg := riemannOp_apply_smooth (LeviCivita (I := I) g) hV hW hU (x := x)
  have hh := riemannOp_apply_smooth (LeviCivita (I := I) h) hV hW hU (x := x)
  have hd := riemannSec_difference (LeviCivita (I := I) g) (LeviCivita (I := I) h)
    hV hW hU (LeviCivita_torsion_eq_zero g) x
  simp only [smoothExtensionTangent_eq] at hg hh
  rw [← hg, ← hh] at hd
  have hc : riemannOp (cov := LeviCivita (I := I) h) x v w u =
      riemannOp (cov := LeviCivita (I := I) g) x v w u +
        (covDerivConnectionDifference (I := I) g h V W U x -
          covDerivConnectionDifference (I := I) g h W V U x) +
        (CovariantDerivative.difference (LeviCivita (I := I) h)
            (LeviCivita (I := I) g) x
            (CovariantDerivative.difference (LeviCivita (I := I) h)
              (LeviCivita (I := I) g) x u w) v -
          CovariantDerivative.difference (LeviCivita (I := I) h)
            (LeviCivita (I := I) g) x
            (CovariantDerivative.difference (LeviCivita (I := I) h)
              (LeviCivita (I := I) g) x u v) w) := by
    simpa only [covDerivConnectionDifference, diffSec,
      smoothExtensionTangent_eq, V, W, U] using hd
  rw [hc]
  dsimp only [V, W, U]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannOp_difference_le_metric_jets
    {g h : SmoothRiemannianMetric I M} {x : M} {d1 d2 : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) {x} g h 2)
    (h1 : metricCovDerivNorm (I := I) 1 h g x ≤ d1)
    (h2 : metricCovDerivNorm (I := I) 2 h g x ≤ d2)
    (v w u : TangentSpace I x) :
    Real.sqrt (g.inner x
        (riemannOp (cov := LeviCivita (I := I) h) x v w u -
          riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) h) x v w u -
          riemannOp (cov := LeviCivita (I := I) g) x v w u)) ≤
      (48 * d2 + 384 * d1 ^ 2) * Real.sqrt (g.inner x v v) *
        Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x u u) := by
  have hd1 : 0 ≤ d1 := (Real.sqrt_nonneg _).trans h1
  have hJ1 : MetricCovDerivOrderBoundOn (I := I) {x} 1 h g d1 := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using h1
  have hJ2 : MetricCovDerivOrderBoundOn (I := I) {x} 2 h g d2 := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using h2
  let A := CovariantDerivative.difference (LeviCivita (I := I) h)
    (LeviCivita (I := I) g) x
  let B (a b c : TangentSpace I x) := covDerivConnectionDifference (I := I) g h
    (smoothExtensionTangent (I := I) x a) (smoothExtensionTangent (I := I) x b)
    (smoothExtensionTangent (I := I) x c) x
  have hA (a b : TangentSpace I x) :
      metricVectorNorm g x (A b a) ≤
        (12 * d1) * metricVectorNorm g x a * metricVectorNorm g x b := by
    have ht := connectionDifference_gJet_le (I := I) hEq hJ1 (Set.mem_singleton x) a b
    have hcoef : (3 / 2 : ℝ) * 2 ^ 3 = 12 := by norm_num
    rw [hcoef] at ht
    exact ht
  have hB (a b c : TangentSpace I x) :
      metricVectorNorm g x (B a b c) ≤
        (24 * d2 + 48 * d1 ^ 2) * metricVectorNorm g x a *
          metricVectorNorm g x b * metricVectorNorm g x c := by
    have ht := covDerivConnectionDifference_gJet_le (I := I)
      hEq hJ1 hJ2 (Set.mem_singleton x) a b c
    have hcoef : (3 / 2 : ℝ) * 2 ^ 4 * (d2 + 2 * d1 ^ 2) =
        24 * d2 + 48 * d1 ^ 2 := by ring
    rw [hcoef] at ht
    exact ht
  have hAA (a b c : TangentSpace I x) :
      metricVectorNorm g x (A (A c b) a) ≤
        (144 * d1 ^ 2) * metricVectorNorm g x a *
          metricVectorNorm g x b * metricVectorNorm g x c := by
    calc
      _ ≤ 12 * d1 * metricVectorNorm g x a * metricVectorNorm g x (A c b) := hA a _
      _ ≤ 12 * d1 * metricVectorNorm g x a *
          (12 * d1 * metricVectorNorm g x b * metricVectorNorm g x c) :=
        mul_le_mul_of_nonneg_left (hA b c)
          (mul_nonneg (mul_nonneg (by norm_num) hd1) (metricVectorNorm_nonneg g x a))
      _ = _ := by ring
  have heq := riemannOp_difference_eq g h x v w u
  change metricVectorNorm g x _ ≤ _
  rw [heq]
  change metricVectorNorm g x (B v w u - B w v u + (A (A u w) v - A (A u v) w)) ≤ _
  calc
    _ ≤ metricVectorNorm g x (B v w u - B w v u) +
        metricVectorNorm g x (A (A u w) v - A (A u v) w) := metricVectorNorm_add_le g x _ _
    _ ≤ (metricVectorNorm g x (B v w u) + metricVectorNorm g x (B w v u)) +
        (metricVectorNorm g x (A (A u w) v) + metricVectorNorm g x (A (A u v) w)) :=
      add_le_add (metricVectorNorm_sub_le g x _ _) (metricVectorNorm_sub_le g x _ _)
    _ ≤ ((24 * d2 + 48 * d1 ^ 2) * metricVectorNorm g x v *
          metricVectorNorm g x w * metricVectorNorm g x u +
        (24 * d2 + 48 * d1 ^ 2) * metricVectorNorm g x w *
          metricVectorNorm g x v * metricVectorNorm g x u) +
        (144 * d1 ^ 2 * metricVectorNorm g x v *
          metricVectorNorm g x w * metricVectorNorm g x u +
        144 * d1 ^ 2 * metricVectorNorm g x w *
          metricVectorNorm g x v * metricVectorNorm g x u) :=
      add_le_add (add_le_add (hB v w u) (hB w v u))
        (add_le_add (hAA v w u) (hAA w v u))
    _ = _ := by dsimp only [metricVectorNorm]; ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem metricRm04_difference_le_metric_jets
    {g h : SmoothRiemannianMetric I M} {x : M} {d1 d2 : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) {x} g h 2)
    (h1 : metricCovDerivNorm (I := I) 1 h g x ≤ d1)
    (h2 : metricCovDerivNorm (I := I) 2 h g x ≤ d2)
    (v w u z : TangentSpace I x) :
    |metricRm04StandardAt (I := I) h x v w u z - metricRm04StandardAt (I := I) g x v w u z| ≤
      metricDerivNorm (I := I) 0 h g g x * Real.sqrt (g.inner x z z) *
        Real.sqrt (g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g) x v w u)) +
      (96 * d2 + 768 * d1 ^ 2) * Real.sqrt (g.inner x v v) *
        Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x z z) := by
  let Rg := riemannOp (cov := LeviCivita (I := I) g) x v w u
  let Rh := riemannOp (cov := LeviCivita (I := I) h) x v w u
  have heq : h.inner x z Rh - g.inner x z Rg =
      (h.inner x z Rg - g.inner x z Rg) + h.inner x z (Rh - Rg) := by
    rw [map_sub]
    ring
  rw [rm04_eq_inner_riem, rm04_eq_inner_riem]
  change |h.inner x z Rh - g.inner x z Rg| ≤ _
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add (metric_inner_difference_le g h x z Rg) ?_)
  have hR := riemannOp_difference_le_metric_jets hEq h1 h2 v w u
  calc
    _ ≤ 2 * metricVectorNorm g x z * metricVectorNorm g x (Rh - Rg) :=
      metric_inner_abs_le_of_equivalent hEq z _
    _ ≤ 2 * metricVectorNorm g x z *
        ((48 * d2 + 384 * d1 ^ 2) * metricVectorNorm g x v *
          metricVectorNorm g x w * metricVectorNorm g x u) :=
      mul_le_mul_of_nonneg_left hR
        (mul_nonneg (by norm_num) (metricVectorNorm_nonneg g x z))
    _ = _ := by dsimp only [metricVectorNorm]; ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem metricRm04_difference_le_of_metricDerivNorm_le
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a h g g x ≤ delta)
    (v w u z : TangentSpace I x) :
    |metricRm04StandardAt (I := I) h x v w u z - metricRm04StandardAt (I := I) g x v w u z| ≤
      delta * (Real.sqrt (g.inner x z z) *
          Real.sqrt (g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g) x v w u)) +
        864 * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
          Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x z z)) := by
  have hquad (a : TangentSpace I x) :
      |h.inner x a a - g.inner x a a| ≤ (1 / 2 : ℝ) * g.inner x a a := by
    have ht := metricQuadFormDiff_le_metricDerivNorm (I := I) h g g x a
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hcoef : (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 h g g x ≤
        1 / 2 := (mul_le_mul_of_nonneg_left (hjet 0 (by norm_num)) hn).trans hsmall
    exact ht.trans (mul_le_mul_of_nonneg_right hcoef
      (DifferentialGeometry.metric_inner_self_nonneg g x a))
  have heq : MetricUniformEquivalentOn (I := I) {x} g h 2 := by
    have ht := metricUniformEquivalentOn_of_quadFormDiff (I := I)
      (K := {x}) (g := g) (h := h) (δ := 1 / 2) (by norm_num) (by norm_num)
      (fun y hy a => by
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hquad a)
    norm_num at ht
    exact ht
  have hsucc (a : ℕ) : metricDerivNorm (I := I) (a + 1) h g g x =
      metricCovDerivNorm (I := I) (a + 1) h g x := by
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [covDeriv_self_succ]
    change Real.sqrt (normSq0S (I := I) g x (a + 1 + 2)
      (CheegerGromovCompactness.metricCovDeriv (I := I) h g (a + 1) x - 0)) = _
    rw [sub_zero]
    rfl
  have h1 : metricCovDerivNorm (I := I) 1 h g x ≤ delta := by
    rw [← hsucc 0]
    exact hjet 1 (by norm_num)
  have h2 : metricCovDerivNorm (I := I) 2 h g x ≤ delta := by
    rw [← hsucc 1]
    exact hjet 2 (by norm_num)
  have ht := metricRm04_difference_le_metric_jets heq h1 h2 v w u z
  have hdd : delta ^ 2 ≤ delta := by nlinarith
  have hcoef : 96 * delta + 768 * delta ^ 2 ≤ 864 * delta := by linarith
  have hnorm (a : TangentSpace I x) : 0 ≤ Real.sqrt (g.inner x a a) := Real.sqrt_nonneg _
  refine ht.trans ?_
  calc
    _ ≤ delta * Real.sqrt (g.inner x z z) *
          Real.sqrt (g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g) x v w u)) +
        (864 * delta) * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
          Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x z z) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hjet 0 (by norm_num)) (hnorm z)) (hnorm _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef (hnorm v)) (hnorm w)) (hnorm u)) (hnorm z))
    _ = _ := by ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
