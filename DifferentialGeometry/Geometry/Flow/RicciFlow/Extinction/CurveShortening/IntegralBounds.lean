import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Analysis.ODE.Gronwall.Integral

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]
variable [hBoundary : I.Boundaryless] {D : RealTimeInterval} {a b s u : ℝ}
include hBoundary

theorem rfs_csf_integral_bounds (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContDiffOn ℝ ∞ (c.length B.family.metric) (Icc s u) ∧
    ContinuousOn (c.totalCurvature B.family.metric) (Icc s u) ∧
    ContinuousOn (c.energy B.family.metric) (Icc s u) ∧
    (∀ t ∈ Icc s u, derivWithin (c.length B.family.metric) (Icc s u) t =
      -c.energy B.family.metric t - c.integral B.family.metric (c.ricciTangent B.family) t) ∧
    (∀ r ∈ Icc s u, ∀ t ∈ Icc r u,
      c.length B.family.metric t ≤ Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      (∫ v in r..t, c.energy B.family.metric v) ≤
        Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      c.totalCurvature B.family.metric t ≤ c.totalCurvature B.family.metric r +
        ∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
          B.C * c.length B.family.metric v) ∧
      c.totalCurvature B.family.metric t + c.length B.family.metric t ≤
        Real.exp ((B.C + B.B₀) * (t - r)) *
          (c.totalCurvature B.family.metric r + c.length B.family.metric r)) := by
  sorry

theorem totalCurvature_upper_right_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (t : ℝ) (ht : t ∈ Ico s u) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ u →
      (c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t) / h ≤
        (B.C + B.B₀) * c.totalCurvature B.family.metric t +
          B.C * c.length B.family.metric t + ε := by
  obtain ⟨hL, hTheta, _, _, hbounds⟩ := rfs_csf_integral_bounds B hsu hwindow c hc
  let F : ℝ → ℝ := fun v =>
    (B.C + B.B₀) * c.totalCurvature B.family.metric v + B.C * c.length B.family.metric v
  have hF : ContinuousOn F (Icc s u) :=
    (hTheta.const_mul _).add (hL.continuousOn.const_mul _)
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp (hF t ⟨ht.1, ht.2.le⟩) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh htu
  have hth : t ≤ t + h := le_add_of_nonneg_right hh.1.le
  have hsub : Icc t (t + h) ⊆ Icc s u := Icc_subset_Icc ht.1 htu
  have hmono : (∫ v in t..t + h, F v) ≤ h * (F t + ε) := by
    have hle : ∀ v ∈ Icc t (t + h), F v ≤ F t + ε := by
      intro v hv
      have hdist : dist v t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
        linarith [hv.2, hh.2]
      have habs := hclose (hsub hv) hdist
      rw [Real.dist_eq] at habs
      linarith [(abs_lt.mp habs).2]
    have hint := intervalIntegral.integral_mono_on hth
      ((hF.mono hsub).intervalIntegrable_of_Icc hth)
      (continuous_const.intervalIntegrable (μ := volume) t (t + h)) hle
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using hint
  have hint := (hbounds t ⟨ht.1, ht.2.le⟩ (t + h) ⟨hth, htu⟩).2.2.1
  apply (div_le_iff₀ hh.1).mpr
  change c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t ≤
    (F t + ε) * h
  change c.totalCurvature B.family.metric (t + h) ≤
    c.totalCurvature B.family.metric t + ∫ v in t..t + h, F v at hint
  nlinarith

theorem rfs_csf_maximum_principle (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      derivWithin (f.lift x) (Icc s u) t ≤
        c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
          A * f.lift x t + F t)
    (hinit : ∀ x, f.lift x s ≤ y s) :
    ∀ x t, t ∈ Icc s u → f.lift x t ≤ y t := by
  sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem ds_neg (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (f : ℝ → ℝ → ℝ) :
    c.ds g (fun x t => -f x t) = fun x t => -c.ds g f x t := by
  funext x t
  simp only [CurveMap.ds, deriv.fun_neg, mul_neg]

theorem scalar_lower_comparison (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
        A * f.lift x t + F t ≤ derivWithin (f.lift x) (Icc s u) t)
    (hinit : ∀ x, y s ≤ f.lift x s) :
    ∀ x t, t ∈ Icc s u → y t ≤ f.lift x t := by
  let fn : CurveMap ℝ := fun z t => -f z t
  have hfn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fn.lift p.1 p.2) (univ ×ˢ Icc s u) := hf.neg
  have hyn : ∀ t ∈ Icc s u,
      HasDerivWithinAt (fun r => -y r) (A * (-y t) + (-F t)) (Icc s u) t := by
    intro t ht
    convert! (hy t ht).neg using 1
    simp only [neg_add, mul_neg]
  have hpden : ∀ x t, t ∈ Icc s u →
      derivWithin (fn.lift x) (Icc s u) t ≤
        c.ds g (c.ds g fn.lift) x t + d.lift x t * c.ds g fn.lift x t +
          A * fn.lift x t + (-F t) := by
    intro x t ht
    have h := hpde x t ht
    change derivWithin (fun r => -f.lift x r) (Icc s u) t ≤
      c.ds g (c.ds g (fun z r => -f.lift z r)) x t +
        d.lift x t * c.ds g (fun z r => -f.lift z r) x t + A * (-f.lift x t) + (-F t)
    rw [derivWithin.fun_neg, ds_neg g c f.lift, ds_neg g c (c.ds g f.lift)]
    nlinarith
  have hn := rfs_csf_maximum_principle g hsu c hc hi fn d hfn hd A
    (fun r => -F r) (fun r => -y r) hF.neg hyn hpden (fun x => neg_le_neg (hinit x))
  intro x t ht
  exact neg_le_neg_iff.mp (hn x t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
