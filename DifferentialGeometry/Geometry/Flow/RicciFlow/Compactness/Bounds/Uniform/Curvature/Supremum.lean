import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Curvature.RiemannOperatorDifferenceBounds

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceEstimates
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.JetBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gAddNorm_le
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have haa : 0 ≤ g.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g x a
  have hbb : 0 ≤ g.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g x b
  have hcs : g.inner x a b ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
    refine le_trans (le_abs_self _) ?_
    exact abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x a b
  have hexpand : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h1 : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      rw [map_add (g.inner x), add_apply]
    have h2 : g.inner x a (a + b) = g.inner x a a + g.inner x a b :=
      map_add (g.inner x a) a b
    have h3 : g.inner x b (a + b) = g.inner x b a + g.inner x b b :=
      map_add (g.inner x b) a b
    have h4 : g.inner x b a = g.inner x a b := g.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hsum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) =
      Real.sqrt ((Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2) from
    (Real.sqrt_sq hsum_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand]
  have hsq : (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2 =
      g.inner x a a + 2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) +
        g.inner x b b := by
    rw [add_sq, Real.sq_sqrt haa, Real.sq_sqrt hbb]; ring
  rw [hsq]
  linarith [hcs]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gSubNorm_le
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a - b) (a - b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have h := gAddNorm_le (I := I) (M := M) g x a (-b)
  have hnb : g.inner x (-b) (-b) = g.inner x b b := by
    rw [map_neg (g.inner x), neg_apply, map_neg, neg_neg]
  rw [hnb] at h
  rw [show a - b = a + (-b) from by abel]
  exact h

def riemannDiffC (Λ Λ' Λ'' : ℝ) : ℝ :=
  2 * (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2)) +
    2 * (3 / 2 * Λ ^ 3 * Λ') ^ 2


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannDiff_gJet_le
    {K : Set M} (g₂ g₁ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    {x : M} (hx : x ∈ K) (v w u : TangentSpace I x) :
    g₂.inner x
        (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
          riemannOp (cov := LeviCivita (I := I) g₂) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
          riemannOp (cov := LeviCivita (I := I) g₂) x v w u) ≤
      riemannDiffC Λ Λ' Λ'' ^ 2 *
        g₂.inner x v v * g₂.inner x w w * g₂.inner x u u := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hL1
  have hJ1 : metricCovDerivNorm (I := I) 1 g₁ g₂ x ≤ Λ' := hJet1 x hx
  have hJ2 : metricCovDerivNorm (I := I) 2 g₁ g₂ x ≤ Λ'' := hJet2 x hx
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) hJ1
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) hJ2
  set C0 : ℝ := 3 / 2 * Λ ^ 3 * Λ' with hC0
  set C1 : ℝ := 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) with hC1
  set Cd : ℝ := riemannDiffC Λ Λ' Λ'' with hCd
  have hC0nn : (0 : ℝ) ≤ C0 := by
    rw [hC0]
    positivity
  have hC1nn : (0 : ℝ) ≤ C1 := by
    rw [hC1]
    positivity
  have hCd_expand : Cd = 2 * C1 + 2 * C0 ^ 2 := by
    rw [hCd, hC1, hC0]
    rfl
  have hCdnn : (0 : ℝ) ≤ Cd := by
    rw [hCd_expand]
    positivity
  set X : Π b : M, TangentSpace I b :=
    smoothExtensionTangent (I := I) x v with hX
  set Y : Π b : M, TangentSpace I b :=
    smoothExtensionTangent (I := I) x w with hY
  set Z : Π b : M, TangentSpace I b :=
    smoothExtensionTangent (I := I) x u with hZ
  have hX_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff x v
  have hY_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) :=
    smoothExtensionTangent_contMDiff x w
  have hZ_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) :=
    smoothExtensionTangent_contMDiff x u
  have hXx : X x = v := smoothExtensionTangent_eq x v
  have hYx : Y x = w := smoothExtensionTangent_eq x w
  have hZx : Z x = u := smoothExtensionTangent_eq x u
  set R1 : TangentSpace I x :=
    riemannOp (cov := LeviCivita (I := I) g₁) x v w u with hR1
  set R0 : TangentSpace I x :=
    riemannOp (cov := LeviCivita (I := I) g₂) x v w u with hR0
  have hR1_sec : R1 = riemannSec (LeviCivita (I := I) g₁) X Y Z x := by
    rw [hR1, ← hXx, ← hYx, ← hZx,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hX_sm hY_sm hZ_sm]
  have hR0_sec : R0 = riemannSec (LeviCivita (I := I) g₂) X Y Z x := by
    rw [hR0, ← hXx, ← hYx, ← hZx,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₂) hX_sm hY_sm hZ_sm]
  have htor : (LeviCivita (I := I) g₂).torsion = 0 :=
    LeviCivita_torsion_eq_zero (I := I) g₂
  have hdiff :=
    riemannSec_difference (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
      hX_sm hY_sm hZ_sm htor x
  set A1 : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x with hA1
  set A2 : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁ Y X Z x with hA2
  set S1 : TangentSpace I x :=
    diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) Y Z x with hS1
  set S2 : TangentSpace I x :=
    diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X Z x with hS2
  set Q1 : TangentSpace I x :=
    CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₂) x S1 (X x) with hQ1
  set Q2 : TangentSpace I x :=
    CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₂) x S2 (Y x) with hQ2
  have hRsub : R1 - R0 = (A1 - A2) + (Q1 - Q2) := by
    rw [hR1_sec, hR0_sec, hdiff]
    rw [show covDerivDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
          X Y Z x = A1 from rfl,
      show covDerivDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
          Y X Z x = A2 from rfl]
    abel
  set Sv : ℝ := Real.sqrt (g₂.inner x v v) with hSv
  set Sw : ℝ := Real.sqrt (g₂.inner x w w) with hSw
  set Su : ℝ := Real.sqrt (g₂.inner x u u) with hSu
  have hSvnn : (0 : ℝ) ≤ Sv := by rw [hSv]; positivity
  have hSwnn : (0 : ℝ) ≤ Sw := by rw [hSw]; positivity
  have hSunn : (0 : ℝ) ≤ Su := by rw [hSu]; positivity
  have hA1_bd : Real.sqrt (g₂.inner x A1 A1) ≤ C1 * Sv * Sw * Su := by
    have h := covDerivConnectionDifference_gJet_le (I := I) hEq hJet1 hJet2 hx v w u
    rw [← hX, ← hY, ← hZ, ← hSv, ← hSw, ← hSu] at h
    rw [hA1, hC1]
    exact h
  have hA2_bd : Real.sqrt (g₂.inner x A2 A2) ≤ C1 * Sw * Sv * Su := by
    have h := covDerivConnectionDifference_gJet_le (I := I) hEq hJet1 hJet2 hx w v u
    rw [← hX, ← hY, ← hZ, ← hSv, ← hSw, ← hSu] at h
    rw [hA2, hC1]
    exact h
  have hS1_eq :
      S1 = (CovariantDerivative.difference
          (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x u) w := by
    rw [hS1]
    change (CovariantDerivative.difference
        (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Z x)) (Y x) = _
    rw [hZx, hYx]
  have hS2_eq :
      S2 = (CovariantDerivative.difference
          (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x u) v := by
    rw [hS2]
    change (CovariantDerivative.difference
        (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Z x)) (X x) = _
    rw [hZx, hXx]
  have hS1_bd : Real.sqrt (g₂.inner x S1 S1) ≤ C0 * Sw * Su := by
    rw [hS1_eq, hC0, hSw, hSu]
    exact connectionDifference_gJet_le (I := I) hEq hJet1 hx w u
  have hS2_bd : Real.sqrt (g₂.inner x S2 S2) ≤ C0 * Sv * Su := by
    rw [hS2_eq, hC0, hSv, hSu]
    exact connectionDifference_gJet_le (I := I) hEq hJet1 hx v u
  have hQ1_raw :
      Real.sqrt (g₂.inner x Q1 Q1) ≤
        C0 * Sv * Real.sqrt (g₂.inner x S1 S1) := by
    rw [hQ1, hXx, hC0, hSv]
    exact connectionDifference_gJet_le (I := I) hEq hJet1 hx v S1
  have hQ2_raw :
      Real.sqrt (g₂.inner x Q2 Q2) ≤
        C0 * Sw * Real.sqrt (g₂.inner x S2 S2) := by
    rw [hQ2, hYx, hC0, hSw]
    exact connectionDifference_gJet_le (I := I) hEq hJet1 hx w S2
  have hQ1_bd :
      Real.sqrt (g₂.inner x Q1 Q1) ≤ C0 ^ 2 * Sv * Sw * Su := by
    calc
      Real.sqrt (g₂.inner x Q1 Q1) ≤
          C0 * Sv * Real.sqrt (g₂.inner x S1 S1) := hQ1_raw
      _ ≤ C0 * Sv * (C0 * Sw * Su) :=
        mul_le_mul_of_nonneg_left hS1_bd (mul_nonneg hC0nn hSvnn)
      _ = C0 ^ 2 * Sv * Sw * Su := by ring
  have hQ2_bd :
      Real.sqrt (g₂.inner x Q2 Q2) ≤ C0 ^ 2 * Sv * Sw * Su := by
    calc
      Real.sqrt (g₂.inner x Q2 Q2) ≤
          C0 * Sw * Real.sqrt (g₂.inner x S2 S2) := hQ2_raw
      _ ≤ C0 * Sw * (C0 * Sv * Su) :=
        mul_le_mul_of_nonneg_left hS2_bd (mul_nonneg hC0nn hSwnn)
      _ = C0 ^ 2 * Sv * Sw * Su := by ring
  have hRsub_bd :
      Real.sqrt (g₂.inner x (R1 - R0) (R1 - R0)) ≤ Cd * Sv * Sw * Su := by
    rw [hRsub]
    have hA2_norm : Real.sqrt (g₂.inner x A2 A2) ≤ C1 * Sv * Sw * Su := by
      calc
        Real.sqrt (g₂.inner x A2 A2) ≤ C1 * Sw * Sv * Su := hA2_bd
        _ = C1 * Sv * Sw * Su := by ring
    have htri1 : Real.sqrt (g₂.inner x (A1 - A2) (A1 - A2)) ≤
        C1 * Sv * Sw * Su + C1 * Sv * Sw * Su :=
      le_trans (gSubNorm_le (I := I) (M := M) g₂ x A1 A2)
        (add_le_add hA1_bd hA2_norm)
    have htri2 : Real.sqrt (g₂.inner x (Q1 - Q2) (Q1 - Q2)) ≤
        C0 ^ 2 * Sv * Sw * Su + C0 ^ 2 * Sv * Sw * Su :=
      le_trans (gSubNorm_le (I := I) (M := M) g₂ x Q1 Q2)
        (add_le_add hQ1_bd hQ2_bd)
    have htri := gAddNorm_le (I := I) (M := M) g₂ x (A1 - A2) (Q1 - Q2)
    calc
      Real.sqrt
          (g₂.inner x ((A1 - A2) + (Q1 - Q2)) ((A1 - A2) + (Q1 - Q2))) ≤
          Real.sqrt (g₂.inner x (A1 - A2) (A1 - A2)) +
            Real.sqrt (g₂.inner x (Q1 - Q2) (Q1 - Q2)) := htri
      _ ≤ (C1 * Sv * Sw * Su + C1 * Sv * Sw * Su) +
          (C0 ^ 2 * Sv * Sw * Su + C0 ^ 2 * Sv * Sw * Su) :=
        add_le_add htri1 htri2
      _ = Cd * Sv * Sw * Su := by rw [hCd_expand]; ring
  have hRnn : 0 ≤ g₂.inner x (R1 - R0) (R1 - R0) :=
    metric_inner_self_nonneg (I := I) (M := M) g₂ x (R1 - R0)
  have hrhs_nn : 0 ≤ Cd * Sv * Sw * Su :=
    mul_nonneg (mul_nonneg (mul_nonneg hCdnn hSvnn) hSwnn) hSunn
  have hsq :
      g₂.inner x (R1 - R0) (R1 - R0) ≤ (Cd * Sv * Sw * Su) ^ 2 := by
    have hmul := mul_le_mul hRsub_bd hRsub_bd (Real.sqrt_nonneg _) hrhs_nn
    rw [Real.mul_self_sqrt hRnn] at hmul
    rw [sq]
    exact hmul
  calc
    g₂.inner x
        (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
          riemannOp (cov := LeviCivita (I := I) g₂) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
          riemannOp (cov := LeviCivita (I := I) g₂) x v w u) =
        g₂.inner x (R1 - R0) (R1 - R0) := by rw [hR1, hR0]
    _ ≤ (Cd * Sv * Sw * Su) ^ 2 := hsq
    _ = Cd ^ 2 * (Sv ^ 2) * (Sw ^ 2) * (Su ^ 2) := by ring
    _ = Cd ^ 2 * g₂.inner x v v * g₂.inner x w w * g₂.inner x u u := by
      rw [hSv, hSw, hSu, Real.sq_sqrt
          (metric_inner_self_nonneg (I := I) (M := M) g₂ x v),
        Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₂ x w),
        Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₂ x u)]
    _ = riemannDiffC Λ Λ' Λ'' ^ 2 *
        g₂.inner x v v * g₂.inner x w w * g₂.inner x u u := by rw [hCd]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curvSup_of_diff
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hdiff : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) :
    ∀ (x : M) (v w u : TangentSpace I x),
      g₀.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
        (Λ ^ 2 * (Cd + Real.sqrt Kb)) ^ 2 *
          g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  intro x v w u
  set R0 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₀) x v w u with hR0
  set Rb : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) gBase) x v w u with hRb
  have hbvv0 : 0 ≤ gBase.inner x v v := metric_inner_self_nonneg (I := I) (M := M) gBase x v
  have hbww0 : 0 ≤ gBase.inner x w w := metric_inner_self_nonneg (I := I) (M := M) gBase x w
  have hbuu0 : 0 ≤ gBase.inner x u u := metric_inner_self_nonneg (I := I) (M := M) gBase x u
  set P3 : ℝ := gBase.inner x v v * gBase.inner x w w * gBase.inner x u u with hP3
  have hP30 : 0 ≤ P3 := by
    rw [hP3]; exact mul_nonneg (mul_nonneg hbvv0 hbww0) hbuu0
  have h := hdiff x v w u
  rw [← hR0, ← hRb] at h
  have hk := hKb x v w u
  rw [← hRb] at hk
  have hd3 : gBase.inner x (R0 - Rb) (R0 - Rb) ≤ Cd ^ 2 * P3 := by
    rw [hP3]
    calc gBase.inner x (R0 - Rb) (R0 - Rb)
        ≤ Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := h
      _ = Cd ^ 2 * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  have hb3 : gBase.inner x Rb Rb ≤ Kb * P3 := by
    rw [hP3]
    calc gBase.inner x Rb Rb
        ≤ Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := hk
      _ = Kb * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  have hnDiff : Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) ≤ Cd * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb))
        ≤ Real.sqrt (Cd ^ 2 * P3) := Real.sqrt_le_sqrt hd3
      _ = Cd * Real.sqrt P3 := by rw [Real.sqrt_mul (sq_nonneg Cd), Real.sqrt_sq hCd]
  have hnRb : Real.sqrt (gBase.inner x Rb Rb) ≤ Real.sqrt Kb * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x Rb Rb)
        ≤ Real.sqrt (Kb * P3) := Real.sqrt_le_sqrt hb3
      _ = Real.sqrt Kb * Real.sqrt P3 := by rw [Real.sqrt_mul hKb0]
  have hcancel : (R0 - Rb) + Rb = R0 := by abel
  have htri : Real.sqrt (gBase.inner x R0 R0) ≤
      (Cd + Real.sqrt Kb) * Real.sqrt P3 := by
    have htr := gAddNorm_le (I := I) (M := M) gBase x (R0 - Rb) Rb
    rw [hcancel] at htr
    calc Real.sqrt (gBase.inner x R0 R0)
        ≤ Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) +
            Real.sqrt (gBase.inner x Rb Rb) := htr
      _ ≤ Cd * Real.sqrt P3 + Real.sqrt Kb * Real.sqrt P3 := add_le_add hnDiff hnRb
      _ = (Cd + Real.sqrt Kb) * Real.sqrt P3 := by ring
  have hR0nn : 0 ≤ gBase.inner x R0 R0 :=
    metric_inner_self_nonneg (I := I) (M := M) gBase x R0
  have hbaseSq : gBase.inner x R0 R0 ≤ (Cd + Real.sqrt Kb) ^ 2 * P3 := by
    have hmm := mul_self_le_mul_self (Real.sqrt_nonneg _) htri
    rw [Real.mul_self_sqrt hR0nn] at hmm
    calc gBase.inner x R0 R0
        ≤ ((Cd + Real.sqrt Kb) * Real.sqrt P3) *
            ((Cd + Real.sqrt Kb) * Real.sqrt P3) := hmm
      _ = (Cd + Real.sqrt Kb) ^ 2 * (Real.sqrt P3 * Real.sqrt P3) := by ring
      _ = (Cd + Real.sqrt Kb) ^ 2 * P3 := by rw [Real.mul_self_sqrt hP30]
  have hout : g₀.inner x R0 R0 ≤ Λ * gBase.inner x R0 R0 := (hcomp x R0).2
  have hcoeff_nn : 0 ≤ (Cd + Real.sqrt Kb) ^ 2 := sq_nonneg _
  have hinConvergence : ∀ z : TangentSpace I x, gBase.inner x z z ≤ Λ * g₀.inner x z z := by
    intro z
    have hz := (hcomp x z).1
    have hz2 := mul_le_mul_of_nonneg_left hz hΛ0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz2
  have hg0vv0 : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hg0ww0 : 0 ≤ g₀.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have hΛg0vv : 0 ≤ Λ * g₀.inner x v v := mul_nonneg hΛ0.le hg0vv0
  have hΛg0ww : 0 ≤ Λ * g₀.inner x w w := mul_nonneg hΛ0.le hg0ww0
  have hstep1 : gBase.inner x v v * gBase.inner x w w ≤
      (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) :=
    mul_le_mul (hinConvergence v) (hinConvergence w) hbww0 hΛg0vv
  have hstep2 : P3 ≤ (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) * (Λ * g₀.inner x u u) := by
    rw [hP3]
    exact mul_le_mul hstep1 (hinConvergence u) hbuu0 (mul_nonneg hΛg0vv hΛg0ww)
  have hP3_convergence : P3 ≤ Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u) := by
    refine le_trans hstep2 (le_of_eq ?_); ring
  calc g₀.inner x R0 R0
      ≤ Λ * gBase.inner x R0 R0 := hout
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 * P3) :=
          mul_le_mul_of_nonneg_left hbaseSq hΛ0.le
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 *
          (Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hP3_convergence hcoeff_nn) hΛ0.le
    _ = (Λ ^ 2 * (Cd + Real.sqrt Kb)) ^ 2 *
          g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem uniformCurvSup_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb : ℝ} (hΛ : 1 ≤ Λ)
    (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w u : TangentSpace I x),
      g₀.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
        (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb)) ^ 2 *
          g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  have hCd : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  exact curvSup_of_diff (I := I) (M := M) gBase g₀ hΛ hcomp
    hKb0 hKb hCd
      (fun x v w u =>
        riemannDiff_gJet_le (I := I) (M := M) gBase g₀
          hEq hjet1 hjet2 (Set.mem_univ x) v w u)

omit [SigmaCompactSpace M] in
theorem uniformCurvSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        g₀.inner x
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ
  have hCd : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  exact uniformCurvatureSup_singleLink_of_diff (I := I) (M := M)
    gBase g₀ hΛ hcomp hCd
      (fun x v w u =>
        riemannDiff_gJet_le (I := I) (M := M) gBase g₀
          hEq hjet1 hjet2 (Set.mem_univ x) v w u)

end RicciFlow
end PDE
end DifferentialGeometry

end
