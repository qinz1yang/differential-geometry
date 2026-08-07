import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroCore
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend
    dLaBiContrFibFixedFrame_toModel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def covDerivConnDiffSqrt
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) : ℝ :=
  let A := covDerivConnDiff (I := I) g₀ g₁
    (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent (I := I) x w)
    (smoothExtensionTangent (I := I) x u) x
  Real.sqrt (g₀.inner x A A)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem connDiffCovDerivOp_sqrt_le_of_bounds [SigmaCompactSpace M]
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (Cq Cbg CaB Cc κ CK : ℝ)
    (hCq_nn : 0 ≤ Cq) (hCbg_nn : 0 ≤ Cbg) (hCaB_nn : 0 ≤ CaB)
    (hCc_nn : 0 ≤ Cc) (hκ_nn : 0 ≤ κ)
    (hCK_def : CK = (Cq + Cbg + 3 * (CaB * (CaB + Cc))) * (κ * κ))
    (hquad : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g₁ x v w u ≤
        Cq * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u))
    (hbg : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g_bg x v w u ≤
        Cbg * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u))
    (hconn_g1 : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)))
    (hconn_gbg : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)) ≤
      (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)))
    (hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ)
    (v0 : TangentSpace I x) (hv0 : g₀.inner x v0 v0 = 1)
    (a' b' : Fin (Module.finrank ℝ E)) :
    Real.sqrt (g₀.inner x
      (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x b' x))
      (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x b' x))) ≤ CK := by
  set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
  set Bb : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x b' x with hBb
  have hBa_le : Real.sqrt (g₀.inner x Ba Ba) ≤ κ := hpinch a'
  have hBb_le : Real.sqrt (g₀.inner x Bb Bb) ≤ κ := hpinch b'
  have hBa_nn : 0 ≤ Real.sqrt (g₀.inner x Ba Ba) := Real.sqrt_nonneg _
  have hBb_nn : 0 ≤ Real.sqrt (g₀.inner x Bb Bb) := Real.sqrt_nonneg _
  have hv0_sqrt : Real.sqrt (g₀.inner x v0 v0) = 1 := by rw [hv0, Real.sqrt_one]
  rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x v0 Ba Bb]
  set A1 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g₁
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x Bb)
    (smoothExtensionTangent (I := I) x Ba) x with hA1
  set A2 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x Bb)
    (smoothExtensionTangent (I := I) x Ba) x with hA2
  set Q1 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
    (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0 with hQ1
  set Q2 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb with hQ2
  set Q3 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0) with hQ3
  have t1 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1 - Q2) Q3
  have t2 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1) Q2
  have t3 := sqrt_metric_inner_add_le (I := I) (M := M) g₀ x (A1 - A2) Q1
  have t4 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x A1 A2
  have hA1_le : Real.sqrt (g₀.inner x A1 A1) ≤ Cq * (κ * κ) := by
    have h := hquad v0 Bb Ba
    rw [hv0_sqrt] at h
    refine le_trans h ?_
    calc Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
        ≤ Cq * 1 * κ * κ := by
          have h1 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cq * 1 * κ :=
            mul_le_mul_of_nonneg_left hBb_le (by linarith [hCq_nn])
          have h2 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
              Cq * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
            mul_le_mul_of_nonneg_right h1 hBa_nn
          refine le_trans h2 ?_
          exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
      _ = Cq * (κ * κ) := by ring
  have hA2_le : Real.sqrt (g₀.inner x A2 A2) ≤ Cbg * (κ * κ) := by
    have h := hbg v0 Bb Ba
    rw [hv0_sqrt] at h
    refine le_trans h ?_
    calc Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
        ≤ Cbg * 1 * κ * κ := by
          have h1 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cbg * 1 * κ :=
            mul_le_mul_of_nonneg_left hBb_le (by linarith [hCbg_nn])
          have h2 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
              Cbg * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
            mul_le_mul_of_nonneg_right h1 hBa_nn
          refine le_trans h2 ?_
          exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
      _ = Cbg * (κ * κ) := by ring
  have hin_bg : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)
      (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)) ≤ (CaB + Cc) * (κ * κ) := by
    refine le_trans (hconn_gbg Ba Bb) ?_
    have hmul : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤ κ * κ := by
      have h1 : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤
          κ * Real.sqrt (g₀.inner x Bb Bb) := mul_le_mul_of_nonneg_right hBa_le hBb_nn
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left hBb_le hκ_nn
    exact mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)
  have hQ1_le : Real.sqrt (g₀.inner x Q1 Q1) ≤ CaB * ((CaB + Cc) * (κ * κ)) := by
    have h := hconn_g1 (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0
    rw [hv0_sqrt, mul_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hin_bg hCaB_nn)
  have hin2 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) ≤ CaB * κ := by
    have h := hconn_g1 Ba v0
    rw [hv0_sqrt, mul_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hBa_le hCaB_nn)
  have hQ2_le : Real.sqrt (g₀.inner x Q2 Q2) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
    have h := hconn_gbg (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb
    refine le_trans h ?_
    have hmul : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) * Real.sqrt (g₀.inner x Bb Bb) ≤
        (CaB * κ) * κ := by
      have h1 := mul_le_mul_of_nonneg_right hin2 hBb_nn
      exact le_trans h1 (mul_le_mul_of_nonneg_left hBb_le (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
    apply le_of_eq
    ring
  have hin3 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ CaB * κ := by
    have h := hconn_g1 Bb v0
    rw [hv0_sqrt, mul_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hBb_le hCaB_nn)
  have hQ3_le : Real.sqrt (g₀.inner x Q3 Q3) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
    have h := hconn_gbg Ba (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
    refine le_trans h ?_
    have hmul : Real.sqrt (g₀.inner x Ba Ba) *
        Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ κ * (CaB * κ) := by
      have h1 : Real.sqrt (g₀.inner x Ba Ba) *
          Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤
          κ * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) :=
        mul_le_mul_of_nonneg_right hBa_le (Real.sqrt_nonneg _)
      exact le_trans h1 (mul_le_mul_of_nonneg_left hin3 hκ_nn)
    refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
    apply le_of_eq
    ring
  have hchain : Real.sqrt (g₀.inner x (A1 - A2 + Q1 - Q2 - Q3) (A1 - A2 + Q1 - Q2 - Q3)) ≤
      Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
        Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2) +
        Real.sqrt (g₀.inner x Q3 Q3) := by
    refine le_trans t1 ?_
    have s2 := le_trans t2 (by linarith [t3, t4] :
      Real.sqrt (g₀.inner x (A1 - A2 + Q1) (A1 - A2 + Q1)) +
          Real.sqrt (g₀.inner x Q2 Q2) ≤
        Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
          Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2))
    linarith [s2]
  refine le_trans hchain ?_
  rw [hCK_def]
  nlinarith [hA1_le, hA2_le, hQ1_le, hQ2_le, hQ3_le]

omit [I.Boundaryless] in
private theorem deTurckLieConnDiffDerivCoeffField_component_sq_le
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δP : ℝ}
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hδP_lt1 : δP < 1)
    (hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δP)
    (x : M) (κ CK : ℝ) (hκ_nn : 0 ≤ κ) (hCK_nn : 0 ≤ CK)
    (hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ)
    (hkernel : ∀ (v0 : TangentSpace I x), g₀.inner x v0 v0 = 1 →
      ∀ a' b' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))) ≤ CK)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hunit : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1)
    (K J : Fin 2 → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
  have hunit_sqrt : ∀ i : Fin n, Real.sqrt (g₀.inner x (e i) (e i)) = 1 := by
    intro i
    rw [hunit i, Real.sqrt_one]
  have hcomp_eq : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J =
    Tensor0SSpace.toModel
      ((connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
      (fun i : Fin 2 => (e (J i) : E)) := rfl
  have hmodel : Tensor0SSpace.toModel
      ((connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
      (fun i : Fin 2 => (e (J i) : E)) =
    (-1 : ℝ) * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
      (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))
        + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 0))) *
        Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
            (smoothOrthoFrame (I := I) g₁ x b' x : E)] :=
    dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x
      (coframeS (I := I) (M := M) g₀ x 2 e K) (fun i : Fin 2 => (e (J i) : E))
  have hsingle : ∀ a' b' : Fin (Module.finrank ℝ E),
      |(g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))
        + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 0))) *
        Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
            (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ 4 * CK * (κ * κ) := by
    intro a' b'
    rw [abs_mul]
    have hK01 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
        (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
        (e (J 1))| ≤ 2 * CK := by
      refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
        (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
      rw [hunit_sqrt (J 1), mul_one]
      have h := hkernel (e (J 0)) (hunit (J 0)) a' b'
      linarith
    have hK10 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
        (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
        (e (J 0))| ≤ 2 * CK := by
      refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
        (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
      rw [hunit_sqrt (J 0), mul_one]
      have h := hkernel (e (J 1)) (hunit (J 1)) a' b'
      linarith
    have hfac1 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
        (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
        (e (J 1))
        + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 0))| ≤ 4 * CK := by
      refine le_trans (abs_add_le _ _) ?_
      linarith [hK01, hK10]
    have hfac2 : |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
        ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
          (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ κ * κ := by
      rw [toModel_coframeS_two (I := I) (M := M) g₀ x e K _ _]
      rw [abs_mul]
      have hcs1 : |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a' x)| ≤ κ := by
        refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
        rw [hunit_sqrt (K 0), one_mul]
        exact hpinch a'
      have hcs2 : |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b' x)| ≤ κ := by
        refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
        rw [hunit_sqrt (K 1), one_mul]
        exact hpinch b'
      exact mul_le_mul hcs1 hcs2 (abs_nonneg _) hκ_nn
    calc |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))
          + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))| *
        |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
            (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
        ≤ (4 * CK) * (κ * κ) := by
          refine mul_le_mul hfac1 hfac2 (abs_nonneg _) ?_
          linarith [hCK_nn]
      _ = 4 * CK * (κ * κ) := by ring
  have habs_comp : |fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J| ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
    rw [hcomp_eq, hmodel, neg_one_mul, abs_neg]
    calc |∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 1))
            + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 0))) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
              ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
        ≤ ∑ a' : Fin (Module.finrank ℝ E), |∑ b' : Fin (Module.finrank ℝ E),
          (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 1))
            + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 0))) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
              ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          |(g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 1))
            + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 0))) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
              ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
          Finset.sum_le_sum (fun a' _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            (4 * CK * (κ * κ)) :=
          Finset.sum_le_sum (fun a' _ => Finset.sum_le_sum (fun b' _ => hsingle a' b'))
      _ = (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs_comp 2

omit [I.Boundaryless] in
private theorem deTurckLieConnDiffDerivCoeffField_fiberNormSq_le_of_kernel_bound
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δP : ℝ}
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hδP_lt1 : δP < 1)
    (hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δP)
    (x : M) (κ CK : ℝ) (hκ_nn : 0 ≤ κ) (hCK_nn : 0 ≤ CK)
    (hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ)
    (hkernel : ∀ (v0 : TangentSpace I x), g₀.inner x v0 v0 = 1 →
      ∀ a' b' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))) ≤ CK) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          (4 * CK * (κ * κ)))) ^ 2 := by
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := hn
  have hunit : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1 := by
    intro i
    have h := horth i i
    rw [if_pos rfl] at h
    exact h
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 2 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
    intro K J
    exact deTurckLieConnDiffDerivCoeffField_component_sq_le (I := I) (M := M)
      g₀ g₁ g_bg P htie hδP_lt1 hδP_bound x κ CK hκ_nn hCK_nn hpinch hkernel
      e hunit K J
  calc ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
          Fintype.card_fin]
        rw [hnE]
        push_cast
        ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  in
private theorem smoothOrthoFrame_g0Norm_le_of_perturbation
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δP δ₁ κ : ℝ}
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δP)
    (hδP_le : δP ≤ δ₁) (hcoeff : 0 < 1 - δ₁)
    (hκ_def : κ = Real.sqrt (1 / (1 - δ₁))) (x : M)
    (a' : Fin (Module.finrank ℝ E)) :
    Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
      (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ := by
  set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
  have hg1BB : g₁.inner x Ba Ba = 1 := by
    have h := smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a' a'
    rw [if_pos rfl] at h
    exact h
  have hBB_nn : 0 ≤ g₀.inner x Ba Ba :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x Ba
  have hsq : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) =
      g₀.inner x Ba Ba := Real.mul_self_sqrt hBB_nn
  have hpert' : |ccTensorBilinSymm (I := I) g₀ P x Ba Ba| ≤
      δP * g₀.inner x Ba Ba := by
    calc |ccTensorBilinSymm (I := I) g₀ P x Ba Ba|
        ≤ δP * Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) :=
          hδP_bound x Ba Ba
      _ = δP * g₀.inner x Ba Ba := by rw [mul_assoc, hsq]
  have htie' := htie x Ba Ba
  rw [hg1BB] at htie'
  have hlow : g₀.inner x Ba Ba - δP * g₀.inner x Ba Ba ≤ 1 := by
    have h1 := (abs_le.mp hpert').1
    linarith [htie'.symm]
  have hBB_le : g₀.inner x Ba Ba ≤ 1 / (1 - δ₁) := by
    have hδP1 : 1 - δ₁ ≤ 1 - δP := by linarith [hδP_le]
    have h2 : (1 - δP) * g₀.inner x Ba Ba ≤ 1 := by nlinarith [hlow]
    have h3 : (1 - δ₁) * g₀.inner x Ba Ba ≤ (1 - δP) * g₀.inner x Ba Ba :=
      mul_le_mul_of_nonneg_right hδP1 hBB_nn
    rw [le_div_iff₀ hcoeff]
    nlinarith [h2, h3]
  calc Real.sqrt (g₀.inner x Ba Ba) ≤ Real.sqrt (1 / (1 - δ₁)) :=
      Real.sqrt_le_sqrt hBB_le
    _ = κ := hκ_def.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
private theorem connDiff_sqrt_le_of_firstCovGrad_norm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (Ca0 N1 B CaB : ℝ) (hCa0_nn : 0 ≤ Ca0) (hN1_le : N1 ≤ B)
    (hCaB_def : CaB = Ca0 * B)
    (hbase : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      Ca0 * N1 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) :
    ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
  intro u v
  refine le_trans (hbase u v) ?_
  have hsu : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
  have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hmono : Ca0 * N1 ≤ Ca0 * B := mul_le_mul_of_nonneg_left hN1_le hCa0_nn
  calc Ca0 * N1 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)
      ≤ Ca0 * B * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hsu) hsv
    _ = CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
        rw [hCaB_def]
        ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] in
private theorem connDiff_background_sqrt_le
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (CaB Cc : ℝ)
    (hconn_g1 : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)))
    (hfixed : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)) ≤
      Cc * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) :
    ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)) ≤
      (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
  intro u v
  have hcocy : PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  rw [hcocy]
  refine le_trans (sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x _ _) ?_
  calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v))
        + Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v))
      ≤ CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
        + Cc * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) :=
          add_le_add (hconn_g1 u v) (hfixed u v)
    _ = (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
        ring

noncomputable def tensorRSRiemannianNorm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (W : TensorRSSpace r s I x) : ℝ :=
  let instRS : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ r s
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    (instRS.g.toCore x).toNormedAddCommGroupOfTopology
      (instRS.g.continuousAt x) (instRS.g.isVonNBounded x)
  letI : NormedSpace ℝ (TensorRSSpace r s I x) :=
    (instRS.g.toCore x).toNormedSpaceOfTopology
      (instRS.g.continuousAt x) (instRS.g.isVonNBounded x)
  ‖W‖

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private theorem tensorRSRiemannianNorm_nonneg
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (W : TensorRSSpace r s I x) :
    0 ≤ tensorRSRiemannianNorm (I := I) (M := M) g₀ r s x W := by
  let instRS : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ r s
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    (instRS.g.toCore x).toNormedAddCommGroupOfTopology
      (instRS.g.continuousAt x) (instRS.g.isVonNBounded x)
  letI : NormedSpace ℝ (TensorRSSpace r s I x) :=
    (instRS.g.toCore x).toNormedSpaceOfTopology
      (instRS.g.continuousAt x) (instRS.g.isVonNBounded x)
  change 0 ≤ ‖W‖
  exact norm_nonneg W

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem firstCovGrad_fiberNorm_le_pointwiseC2Sum
    (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) {B : ℝ}
    (henv : (∑ k ∈ Finset.range 3,
      tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x)) ≤ B) :
    tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 3 x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ B := by
  classical
  have hterms : ∀ k ∈ Finset.range 3, (0 : ℝ) ≤
      tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) := by
    intro k _
    exact tensorRSRiemannianNorm_nonneg (I := I) (M := M) g₀ 0 (2 + k) x _
  exact (Finset.single_le_sum hterms (by norm_num : (1 : ℕ) ∈ Finset.range 3)).trans henv

theorem deTurckLieConnDiffDerivCoeffField_fiberNormSq_le_of_scalar_bounds
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) {δP δ₁ κ B Cq Cbg Cc Ca0 CaB CK : ℝ}
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hδP_lt1 : δP < 1)
    (hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δP)
    (hδP_le : δP ≤ δ₁) (hcoeff : 0 < 1 - δ₁)
    (hκ_def : κ = Real.sqrt (1 / (1 - δ₁))) (hκ_nn : 0 ≤ κ)
    (henv : (∑ k ∈ Finset.range 3,
      tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x)) ≤ B)
    (hquad : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g₁ x v w u ≤
        Cq * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u))
    (hbg : ∀ v w u : TangentSpace I x,
      covDerivConnDiffSqrt (I := I) g₀ g_bg x v w u ≤
        Cbg * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u))
    (hbase : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      Ca0 * tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
        Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
    (hfixed : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)) ≤
      Cc * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
    (hCq_nn : 0 ≤ Cq) (hCbg_nn : 0 ≤ Cbg) (hCc_nn : 0 ≤ Cc)
    (hCa0_nn : 0 ≤ Ca0) (hCaB_nn : 0 ≤ CaB)
    (hCaB_def : CaB = Ca0 * B)
    (hCK_def : CK = (Cq + Cbg + 3 * (CaB * (CaB + Cc))) * (κ * κ))
    (hCK_nn : 0 ≤ CK) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
  set N1 : ℝ := tensorRSRiemannianNorm (I := I) (M := M) g₀ 0 3 x
    ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) with hN1_def
  have hN1_le : N1 ≤ B := by
    have h := firstCovGrad_fiberNorm_le_pointwiseC2Sum (I := I) (M := M)
      g₀ P x henv
    rw [← hN1_def] at h
    exact h
  have hbase' : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      Ca0 * N1 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    intro u v
    rw [hN1_def]
    exact hbase u v
  have hconn_g1 := connDiff_sqrt_le_of_firstCovGrad_norm_le (I := I) (M := M)
    g₀ g₁ x Ca0 N1 B CaB hCa0_nn hN1_le hCaB_def hbase'
  have hconn_gbg := connDiff_background_sqrt_le (I := I) (M := M)
    g₀ g₁ g_bg x CaB Cc hconn_g1 hfixed
  have hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ := by
    intro a'
    exact smoothOrthoFrame_g0Norm_le_of_perturbation (I := I) (M := M)
      g₀ g₁ P htie hδP_bound hδP_le hcoeff hκ_def x a'
  have hkernel := connDiffCovDerivOp_sqrt_le_of_bounds (I := I) (M := M)
    g₀ g₁ g_bg x Cq Cbg CaB Cc κ CK hCq_nn hCbg_nn hCaB_nn hCc_nn hκ_nn hCK_def
    hquad hbg hconn_g1 hconn_gbg hpinch
  exact deTurckLieConnDiffDerivCoeffField_fiberNormSq_le_of_kernel_bound
    g₀ g₁ g_bg P htie hδP_lt1 hδP_bound x κ CK hκ_nn hCK_nn hpinch hkernel


end DifferentialGeometry.Analysis.Sobolev

end
