import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureJetsLow

import DifferentialGeometry.Geometry.Metric.DeTurck.CovariantDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurck.Pullback
import DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetTowerComparison
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound

set_option autoImplicit false


noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

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


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference_tens (g₂ g₁ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z X' Y' Z' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : X x = X' x) (hY : Y x = Y' x) (hZ : Z x = Z' x) :
    covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x =
      covDerivConnectionDifference (I := I) g₂ g₁ X' Y' Z' x := by
  classical
  have hflat : ∀ p q : TangentSpace I x,
      (g0FlatCLM (I := I) g₂ x p) (fun _ : Fin 1 => q) = g₂.inner x p q := by
    intro p q
    rw [show (g0FlatCLM (I := I) g₂ x p) (fun _ : Fin 1 => q) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₂ x p) q from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₂ x p q]
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₂ x
      (covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x - covDerivConnectionDifference (I := I) g₂ g₁ X' Y' Z' x))
  have h1 := connectionDifferenceSection_covGrad_eq_covDerivConnectionDifference (I := I) g₁ g₂ om X Z Y x
  have h2 := connectionDifferenceSection_covGrad_eq_covDerivConnectionDifference (I := I) g₁ g₂ om X' Z' Y' x
  rw [hX, hY, hZ] at h1
  have h3 : om x (fun _ : Fin 1 => covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x) =
      om x (fun _ : Fin 1 => covDerivConnectionDifference (I := I) g₂ g₁ X' Y' Z' x) := by
    rw [← h1, h2]
  rw [hom, hflat, hflat] at h3
  have hz : g₂.inner x
      (covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x - covDerivConnectionDifference (I := I) g₂ g₁ X' Y' Z' x)
      (covDerivConnectionDifference (I := I) g₂ g₁ X Y Z x -
        covDerivConnectionDifference (I := I) g₂ g₁ X' Y' Z' x) = 0 := by
    rw [map_sub, h3, sub_self]
  by_contra hne
  exact absurd hz (ne_of_gt (g₂.pos x _ (sub_ne_zero.mpr hne)))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem rhsTermBound (gBase g₀ : SmoothRiemannianMetric I M) {Λ C₀ C₁ : ℝ}
    (hΛ : 1 ≤ Λ) (hC₀0 : 0 ≤ C₀) (hC₁0 : 0 ≤ C₁)
    (hcomp : ∀ (y : M) (u : TangentSpace I y),
      Λ⁻¹ * gBase.inner y u u ≤ g₀.inner y u u ∧
        g₀.inner y u u ≤ Λ * gBase.inner y u u)
    (hC₀ : ∀ (y : M) (p q : TangentSpace I y),
      Real.sqrt (gBase.inner y
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase y p q)
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase y p q)) ≤
        C₀ * Real.sqrt (gBase.inner y p p) * Real.sqrt (gBase.inner y q q))
    (hC₁ : ∀ (y : M) (p q r : TangentSpace I y),
      Real.sqrt (gBase.inner y
          (covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) y p)
            (smoothExtensionTangent (I := I) y q)
            (smoothExtensionTangent (I := I) y r) y)
          (covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) y p)
            (smoothExtensionTangent (I := I) y q)
            (smoothExtensionTangent (I := I) y r) y)) ≤
        C₁ * Real.sqrt (gBase.inner y p p) * Real.sqrt (gBase.inner y q q) *
          Real.sqrt (gBase.inner y r r))
    (x : M) (v w b : TangentSpace I x) (hb : g₀.inner x b b = 1) :
    |g₀.inner x
        (covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x b) (smoothExtensionTangent (I := I) x b) x
          + (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b b) v
              - DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b
                  (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v)
              - DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                  (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v) b)) w|
      ≤ (C₁ + 3 * C₀ ^ 2) * Λ ^ 4 * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hsqΛ : Real.sqrt Λ ≤ Λ := by
    have h1 : (1 : ℝ) ≤ Real.sqrt Λ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hΛ
    nlinarith [Real.sq_sqrt hΛ0.le, Real.sqrt_nonneg Λ]
  have hcross : ∀ u : TangentSpace I x,
      Real.sqrt (gBase.inner x u u) ≤ Λ * Real.sqrt (g₀.inner x u u) := by
    intro u
    have h1 : gBase.inner x u u ≤ Λ * g₀.inner x u u := by
      have hz := mul_le_mul_of_nonneg_left (hcomp x u).1 hΛ0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz
    calc Real.sqrt (gBase.inner x u u) ≤ Real.sqrt (Λ * g₀.inner x u u) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt Λ * Real.sqrt (g₀.inner x u u) := Real.sqrt_mul hΛ0.le _
      _ ≤ Λ * Real.sqrt (g₀.inner x u u) :=
          mul_le_mul_of_nonneg_right hsqΛ (Real.sqrt_nonneg _)
  have hcross' : ∀ u : TangentSpace I x,
      Real.sqrt (g₀.inner x u u) ≤ Λ * Real.sqrt (gBase.inner x u u) := by
    intro u
    calc Real.sqrt (g₀.inner x u u) ≤ Real.sqrt (Λ * gBase.inner x u u) :=
          Real.sqrt_le_sqrt (hcomp x u).2
      _ = Real.sqrt Λ * Real.sqrt (gBase.inner x u u) := Real.sqrt_mul hΛ0.le _
      _ ≤ Λ * Real.sqrt (gBase.inner x u u) :=
          mul_le_mul_of_nonneg_right hsqΛ (Real.sqrt_nonneg _)
  have hbB : Real.sqrt (gBase.inner x b b) ≤ Λ := by
    have := hcross b
    rwa [hb, Real.sqrt_one, mul_one] at this
  have hvB : Real.sqrt (gBase.inner x v v) ≤ Λ * Real.sqrt (g₀.inner x v v) := hcross v
  have hSv0 : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hSw0 : (0 : ℝ) ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hpair : ∀ (Y : TangentSpace I x) (c : ℝ),
      Real.sqrt (gBase.inner x Y Y) ≤ c →
      |g₀.inner x Y w| ≤ Λ * c * Real.sqrt (g₀.inner x w w) := by
    intro Y c hc
    refine le_trans (abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x Y w) ?_
    exact mul_le_mul_of_nonneg_right
      (le_trans (hcross' Y) (mul_le_mul_of_nonneg_left hc hΛ0.le)) (Real.sqrt_nonneg _)
  have hAle : ∀ (p q : TangentSpace I x) (cp cq : ℝ), 0 ≤ cp →
      Real.sqrt (gBase.inner x p p) ≤ cp → Real.sqrt (gBase.inner x q q) ≤ cq →
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x p q)
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x p q)) ≤
        C₀ * cp * cq := by
    intro p q cp cq hcp hp hq
    refine le_trans (hC₀ x p q) ?_
    calc C₀ * Real.sqrt (gBase.inner x p p) * Real.sqrt (gBase.inner x q q)
        ≤ C₀ * cp * Real.sqrt (gBase.inner x q q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC₀0) (Real.sqrt_nonneg _)
      _ ≤ C₀ * cp * cq := mul_le_mul_of_nonneg_left hq (mul_nonneg hC₀0 hcp)
  have hCbound : Real.sqrt (gBase.inner x
      (covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x b) (smoothExtensionTangent (I := I) x b) x)
      (covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x b) (smoothExtensionTangent (I := I) x b) x)) ≤
      C₁ * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by
    refine le_trans (hC₁ x v b b) ?_
    have h1 : C₁ * Real.sqrt (gBase.inner x v v) ≤ C₁ * (Λ * Real.sqrt (g₀.inner x v v)) :=
      mul_le_mul_of_nonneg_left hvB hC₁0
    have hbase0 : (0 : ℝ) ≤ C₁ * (Λ * Real.sqrt (g₀.inner x v v)) :=
      mul_nonneg hC₁0 (mul_nonneg hΛ0.le hSv0)
    calc C₁ * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x b b) *
            Real.sqrt (gBase.inner x b b)
        ≤ C₁ * (Λ * Real.sqrt (g₀.inner x v v)) * Real.sqrt (gBase.inner x b b) *
            Real.sqrt (gBase.inner x b b) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      _ ≤ C₁ * (Λ * Real.sqrt (g₀.inner x v v)) * Λ * Real.sqrt (gBase.inner x b b) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbB hbase0) (Real.sqrt_nonneg _)
      _ ≤ C₁ * (Λ * Real.sqrt (g₀.inner x v v)) * Λ * Λ :=
          mul_le_mul_of_nonneg_left hbB (mul_nonneg hbase0 hΛ0.le)
      _ = C₁ * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by ring
  have hPbound : Real.sqrt (gBase.inner x
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b b)
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b b)) ≤
      C₀ * Λ * Λ :=
    hAle b b Λ Λ hΛ0.le hbB hbB
  have hRbound : Real.sqrt (gBase.inner x
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v)
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v)) ≤
      C₀ * Λ * (Λ * Real.sqrt (g₀.inner x v v)) :=
    hAle b v Λ (Λ * Real.sqrt (g₀.inner x v v)) hΛ0.le hbB hvB
  have hQ1 : Real.sqrt (gBase.inner x
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b b) v)
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b b) v)) ≤
      C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by
    have h := hAle _ v (C₀ * Λ * Λ) (Λ * Real.sqrt (g₀.inner x v v))
      (by positivity) hPbound hvB
    calc _ ≤ C₀ * (C₀ * Λ * Λ) * (Λ * Real.sqrt (g₀.inner x v v)) := h
      _ = C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by ring
  have hQ2 : Real.sqrt (gBase.inner x
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v))
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v))) ≤
      C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by
    have h := hAle b _ Λ (C₀ * Λ * (Λ * Real.sqrt (g₀.inner x v v))) hΛ0.le hbB hRbound
    calc _ ≤ C₀ * Λ * (C₀ * Λ * (Λ * Real.sqrt (g₀.inner x v v))) := h
      _ = C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by ring
  have hQ3 : Real.sqrt (gBase.inner x
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v) b)
      (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
        (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x b v) b)) ≤
      C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by
    have h := hAle _ b (C₀ * Λ * (Λ * Real.sqrt (g₀.inner x v v))) Λ
      (by positivity) hRbound hbB
    calc _ ≤ C₀ * (C₀ * Λ * (Λ * Real.sqrt (g₀.inner x v v))) * Λ := h
      _ = C₀ ^ 2 * Λ ^ 3 * Real.sqrt (g₀.inner x v v) := by ring
  have hadd1 : ∀ p q : TangentSpace I x,
      g₀.inner x (p + q) w = g₀.inner x p w + g₀.inner x q w := by
    intro p q; rw [map_add, add_apply]
  have hsub1 : ∀ p q : TangentSpace I x,
      g₀.inner x (p - q) w = g₀.inner x p w - g₀.inner x q w := by
    intro p q; rw [map_sub, sub_apply]
  rw [hadd1, hsub1, hsub1]
  rcases abs_le.mp (hpair _ _ hCbound) with ⟨h1l, h1r⟩
  rcases abs_le.mp (hpair _ _ hQ1) with ⟨h2l, h2r⟩
  rcases abs_le.mp (hpair _ _ hQ2) with ⟨h3l, h3r⟩
  rcases abs_le.mp (hpair _ _ hQ3) with ⟨h4l, h4r⟩
  refine abs_le.mpr ⟨by nlinarith, by nlinarith⟩


noncomputable def vfZeroC (Λ : ℝ) : ℝ :=
  (Module.finrank ℝ E : ℝ) *
    ((connectionDifferenceOneC Λ + 3 * connectionDifferenceZeroC Λ ^ 2) * Λ ^ 4)


omit [SigmaCompactSpace M] in
theorem uniformCovDerivVF_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      |g₀.inner x ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g₀ gBase :
            Π b : M, TangentSpace I b) b) x v) w| ≤
        vfZeroC (E := E) Λ * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
  classical
  let C₀ : ℝ := connectionDifferenceZeroC Λ
  let C₁ : ℝ := connectionDifferenceOneC Λ
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀, connectionDifferenceZeroC]
    positivity
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁, connectionDifferenceOneC]
    positivity
  have hC₀ := connectionDifferenceSup_le (I := I) (M := M)
    gBase g₀ hΛ hcomp hjet1
  have hC₁ := covConnectionDifference_le (I := I) (M := M)
    gBase g₀ hΛ hcomp hjet1 hjet2
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hκ0 : (0 : ℝ) ≤ (C₁ + 3 * C₀ ^ 2) * Λ ^ 4 := by
    have h1 : (0 : ℝ) ≤ C₁ + 3 * C₀ ^ 2 := by nlinarith [sq_nonneg C₀]
    have h2 : (0 : ℝ) ≤ Λ ^ 4 := by positivity
    exact mul_nonneg h1 h2
  intro x v w
  rw [DifferentialGeometry.PDE.DeTurck.deTurckVF_covDeriv_eq (I := I) g₀ gBase x v,
    map_sum, sum_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      |g₀.inner x
        (covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i) x
          + (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                  (smoothOrthoFrame (I := I) g₀ x i x)
                  (smoothOrthoFrame (I := I) g₀ x i x)) v
              - DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                  (smoothOrthoFrame (I := I) g₀ x i x)
                  (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                    (smoothOrthoFrame (I := I) g₀ x i x) v)
              - DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                  (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x
                    (smoothOrthoFrame (I := I) g₀ x i x) v)
                  (smoothOrthoFrame (I := I) g₀ x i x))) w| ≤
        (C₁ + 3 * C₀ ^ 2) * Λ ^ 4 * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
    intro i _
    have hb : g₀.inner x (smoothOrthoFrame (I := I) g₀ x i x)
        (smoothOrthoFrame (I := I) g₀ x i x) = 1 := by
      rw [smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i i]; simp
    have htens : covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
          (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i) x =
        covDerivConnectionDifference (I := I) gBase g₀ (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₀ x i x)) x := by
      refine covDerivConnectionDifference_tens (I := I) gBase g₀ x
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent_contMDiff (I := I) x v))
        (ContMDiffSection.mk (smoothOrthoFrame (I := I) g₀ x i)
          (smoothOrthoFrame_smooth (I := I) g₀ x i))
        (ContMDiffSection.mk (smoothOrthoFrame (I := I) g₀ x i)
          (smoothOrthoFrame_smooth (I := I) g₀ x i))
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent_contMDiff (I := I) x v))
        (ContMDiffSection.mk
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothExtensionTangent_contMDiff (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x)))
        (ContMDiffSection.mk
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothExtensionTangent_contMDiff (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x)))
        rfl
        (smoothExtensionTangent_eq (I := I) x (smoothOrthoFrame (I := I) g₀ x i x)).symm
        (smoothExtensionTangent_eq (I := I) x (smoothOrthoFrame (I := I) g₀ x i x)).symm
    rw [htens]
    exact rhsTermBound (I := I) (M := M) gBase g₀ hΛ hC₀0 hC₁0 hcomp hC₀ hC₁ x v w _ hb
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  dsimp [vfZeroC, C₀, C₁]
  ring


omit [SigmaCompactSpace M] in
theorem uniformCovDerivVF
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) (v w : TangentSpace I x),
        |g₀.inner x ((LeviCivita (I := I) g₀).toFun
            (fun b : M => (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g₀ gBase :
              Π b : M, TangentSpace I b) b) x v) w| ≤
          K * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  refine ⟨vfZeroC (E := E) Λ, ?_,
    uniformCovDerivVF_of (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2⟩
  dsimp [vfZeroC, connectionDifferenceZeroC, connectionDifferenceOneC]
  positivity


noncomputable def rhsZeroC (Λ Kb : ℝ) : ℝ :=
  2 * ricciZeroC (E := E) Λ Kb + 2 * vfZeroC (E := E) Λ


omit [SigmaCompactSpace M] in
theorem uniformRHSBilin_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      |deTurckRicciRHS (I := I) gBase g₀ x v w| ≤
        rhsZeroC (E := E) Λ Kb * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
  classical
  let Kr : ℝ := ricciZeroC (E := E) Λ Kb
  let Kl : ℝ := vfZeroC (E := E) Λ
  have hKr := ricciBilin_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  have hKl := uniformCovDerivVF_of (I := I) (M := M)
    gBase g₀ hΛ hcomp hjet1 hjet2
  intro x v w
  dsimp [rhsZeroC, Kr, Kl]
  rw [deTurckRicciRHS_apply (I := I) gBase g₀ x v w,
    DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric (I := I) g₀
      (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g₀ gBase) x v w]
  have h1 := hKr x v w
  have h2 := hKl x v w
  have h3 : |g₀.inner x v ((LeviCivita (I := I) g₀).toFun
        (fun b : M => (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g₀ gBase :
          Π b : M, TangentSpace I b) b) x w)| ≤
      Kl * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
    rw [g₀.symm x v _]
    have h := hKl x w v
    have heq : Kl * Real.sqrt (g₀.inner x w w) * Real.sqrt (g₀.inner x v v)
        = Kl * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
    linarith
  rcases abs_le.mp h1 with ⟨h1l, h1r⟩
  rcases abs_le.mp h2 with ⟨h2l, h2r⟩
  rcases abs_le.mp h3 with ⟨h3l, h3r⟩
  refine abs_le.mpr ⟨by nlinarith, by nlinarith⟩


theorem uniformRHSBilin
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) (v w : TangentSpace I x),
        |deTurckRicciRHS (I := I) gBase g₀ x v w| ≤
          K * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  have hKr0 : 0 ≤ ricciZeroC (E := E) Λ Kb := by
    dsimp [ricciZeroC]
    exact mul_nonneg (Nat.cast_nonneg _) <|
      mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  have hKl0 : 0 ≤ vfZeroC (E := E) Λ := by
    dsimp [vfZeroC, connectionDifferenceZeroC, connectionDifferenceOneC]
    positivity
  refine ⟨rhsZeroC (E := E) Λ Kb, ?_,
    uniformRHSBilin_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2⟩
  dsimp [rhsZeroC]
  linarith


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem rhsZeroC_nonneg {Kb Λ : ℝ} (hΛ : 1 ≤ Λ) :
    0 ≤ rhsZeroC (E := E) Λ Kb := by
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  have hRic0 : 0 ≤ ricciZeroC (E := E) Λ Kb := by
    dsimp [ricciZeroC]
    exact mul_nonneg (Nat.cast_nonneg _) <|
      mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  have hVF0 : 0 ≤ vfZeroC (E := E) Λ := by
    dsimp [vfZeroC, connectionDifferenceZeroC, connectionDifferenceOneC]
    positivity
  dsimp [rhsZeroC]
  linarith

noncomputable def ksupZeroC (Λ Kb : ℝ) : ℝ :=
  (Module.finrank ℝ E : ℝ) * rhsZeroC (E := E) Λ Kb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem ksupZeroC_nonneg {Kb Λ : ℝ} (hΛ : 1 ≤ Λ) :
    0 ≤ ksupZeroC (E := E) Λ Kb := by
  exact mul_nonneg (Nat.cast_nonneg _) (rhsZeroC_nonneg (E := E) hΛ)


omit [SigmaCompactSpace M] in
theorem uniformRHSFib_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckRHSSection (I := I) gBase g₀).toSection x) ≤
          ksupZeroC (E := E) Λ Kb ^ 2 := by
  classical
  let K₀ : ℝ := rhsZeroC (E := E) Λ Kb
  have hK₀0 : 0 ≤ K₀ := rhsZeroC_nonneg (E := E) hΛ
  have hK₀ := uniformRHSBilin_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  intro x
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₀ x
  rw [riemannianFiberNormSq0_unit_eq (I := I) g₀ 2 x (deTurckRHSSection (I := I) gBase g₀)]
  have hcompbound : ∀ slots : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x)),
      |Tensor0SBundle.component0S (I := I) basis
          (ccUnitField (I := I) g₀ 2 (deTurckRHSSection (I := I) gBase g₀) x) slots| ≤ K₀ := by
    intro slots
    have hval : Tensor0SBundle.component0S (I := I) basis
        (ccUnitField (I := I) g₀ 2 (deTurckRHSSection (I := I) gBase g₀) x) slots =
        deTurckRicciRHS (I := I) gBase g₀ x (basis (slots 0)) (basis (slots 1)) := by
      rw [Tensor0SBundle.component0S_apply,
        ← deTurckRHSSection_eval (I := I) gBase g₀ x (fun a => basis (slots a))]
      rfl
    rw [hval]
    have h := hK₀ x (basis (slots 0)) (basis (slots 1))
    have h0 : g₀.inner x (basis (slots 0)) (basis (slots 0)) = 1 := by
      rw [hON (slots 0) (slots 0)]; simp
    have h1 : g₀.inner x (basis (slots 1)) (basis (slots 1)) = 1 := by
      rw [hON (slots 1) (slots 1)]; simp
    rwa [h0, h1, Real.sqrt_one, mul_one, mul_one] at h
  have hnormsq := Tensor0SBundle.normSq0S_le_card_of_component_bound (I := I) g₀ x 2 basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON)
    (ccUnitField (I := I) g₀ 2 (deTurckRHSSection (I := I) gBase g₀) x) K₀ hK₀0 hcompbound
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      (Module.finrank ℝ E : ℝ) ^ 2 := by
    have hc : Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) =
        Module.finrank ℝ E ^ 2 := by
      change Fintype.card (Fin 2 → Fin (Module.finrank ℝ E)) = Module.finrank ℝ E ^ 2
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hc]; push_cast; ring
  rw [hcard] at hnormsq
  calc Tensor0SBundle.normSq0S (I := I) g₀ x 2
        (ccUnitField (I := I) g₀ 2 (deTurckRHSSection (I := I) gBase g₀) x)
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K₀ ^ 2 := hnormsq
    _ = ksupZeroC (E := E) Λ Kb ^ 2 := by
      dsimp [ksupZeroC, K₀]
      ring


theorem uniformRHSFib
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckRHSSection (I := I) gBase g₀).toSection x) ≤ K ^ 2 := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  exact ⟨ksupZeroC (E := E) Λ Kb, ksupZeroC_nonneg (E := E) hΛ,
    uniformRHSFib_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2⟩


omit [SigmaCompactSpace M] in
theorem uniformKsupZero_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb : ℝ} (hΛ : 1 ≤ Λ)
    (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0
          (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤
        ksupZeroC (E := E) Λ Kb ^ 2 := by
  exact uniformRHSFib_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2


theorem uniformKsupZero
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 2 0
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ K ^ 2 := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  exact ⟨ksupZeroC (E := E) Λ Kb, ksupZeroC_nonneg (E := E) hΛ,
    uniformKsupZero_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2⟩

end RicciFlow
end PDE
end DifferentialGeometry

end
