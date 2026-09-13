import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SweptAreaEstimates

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}


def curveShorteningLeastAreaSlope (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (γ : ℝ → ContinuousFreeLoop M),
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) →
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        2 * B.B₀ * loopFamilyLeastArea B.family.metric γ t +
          (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) t + ε

def curveShorteningTotalCurvatureBound (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ (c : ProductCurve M),
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    ∀ t ∈ Icc a b, c.totalCurvature B.family.metric lambda t +
        c.length B.family.metric lambda t ≤ Real.exp ((B.C + B.B₀) * (t - a)) *
          (c.totalCurvature B.family.metric lambda a +
            c.length B.family.metric lambda a)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem totalCurvature_le_mul_exp_of_growth_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (h : curveShorteningTotalCurvatureBound B)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (Theta₀ L₀ : ℝ)
    (htot : c.totalCurvature B.family.metric lambda a ≤ Theta₀)
    (hlen : c.length B.family.metric lambda a ≤ L₀) :
    ∀ t ∈ Icc a b, c.totalCurvature B.family.metric lambda t ≤
      (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by
  have hlen_nonneg : ∀ v : ℝ, 0 ≤ c.length B.family.metric lambda v := by
    intro v
    rw [ProductCurve.length, ProductCurve.integral]
    exact intervalIntegral.integral_nonneg zero_le_one fun x _ => by
      rw [one_mul]
      exact ProductCurve.speed_nonneg c B.family.metric lambda x v
  have htot_nonneg : 0 ≤ c.totalCurvature B.family.metric lambda a := by
    rw [ProductCurve.totalCurvature, ProductCurve.integral]
    exact intervalIntegral.integral_nonneg zero_le_one fun x _ =>
      mul_nonneg (ProductCurve.curvature_nonneg c B.family.metric lambda x a)
        (ProductCurve.speed_nonneg c B.family.metric lambda x a)
  have hC : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    nlinarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hinit : c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a ≤
      Theta₀ + L₀ := add_le_add htot hlen
  intro t ht
  have hexp : Real.exp ((B.C + B.B₀) * (t - a)) ≤ Real.exp ((B.C + B.B₀) * (b - a)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC
  have h1 : Real.exp ((B.C + B.B₀) * (t - a)) *
        (c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a) ≤
      Real.exp ((B.C + B.B₀) * (b - a)) *
        (c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a) :=
    mul_le_mul_of_nonneg_right hexp (add_nonneg htot_nonneg (hlen_nonneg a))
  calc c.totalCurvature B.family.metric lambda t
      ≤ c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t := by
        linarith [hlen_nonneg t]
    _ ≤ Real.exp ((B.C + B.B₀) * (t - a)) *
          (c.totalCurvature B.family.metric lambda a +
            c.length B.family.metric lambda a) := h lambda hlambda hlambda_one c hc t ht
    _ ≤ Real.exp ((B.C + B.B₀) * (b - a)) * (Theta₀ + L₀) :=
        h1.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)
    _ = (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by ring

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
