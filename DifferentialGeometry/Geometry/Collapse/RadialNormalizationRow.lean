import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunction
import DifferentialGeometry.Geometry.Collapse.RadialNormalization

/-!
# One buffered radial witness with all centered normalization clauses

Ambient distances are identified with the actual metric length distance. The same
buffered smoothing works for every point of the closed shell and every scale at least eighty.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem riemannianBallOf_scaled_eq_ball (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (q : M) {lam : ℝ} (hlam : 0 < lam) :
    riemannianBallOf (scaleMetric (lam ^ 2) (by positivity) g) q 1 =
      Metric.ball q lam⁻¹ := by
  have hs := riemannianBallOf_scaleMetric (lam ^ 2) (by positivity) g q lam⁻¹
  rw [Real.sqrt_sq hlam.le, mul_inv_cancel₀ hlam.ne'] at hs
  rw [hs]
  ext x
  change riemannianEDistOf g q x < ENNReal.ofReal lam⁻¹ ↔ dist x q < lam⁻¹
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
    ← IsRiemannianManifold.out (I := I), edist_dist, dist_comm q x]
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity)

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M]

theorem exists_centered_buffered_radialFunction (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ δ₀ > 0, δ₀ = radialSmoothingConeError (ε / 4) ∧
      ∀ (p : M) (C : Type*) [MetricSpace C] (o : C) (δ : ℝ),
        KleinerLottApprox p o δ → RadialConeData o →
        (∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2)) →
        δ < δ₀ → ∀ e, 0 < e → e < 1 / 40 →
        ∃ η : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) η ∧
          (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O) ∧
          (∀ x, |η x - Metric.infDist x {p}| < e) ∧
          (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} →
            η x = Metric.infDist x {p}) ∧
          (∀ x y, |(η x - Metric.infDist x {p}) - (η y - Metric.infDist y {p})| ≤
            ε * dist x y) ∧
          (∀ x, 0 ≤ η x) ∧ η p = 0 ∧
          (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
            1 - ε ≤ Real.sqrt (g.inner q (gradFun g η q) (gradFun g η q)) ∧
              Real.sqrt (g.inner q (gradFun g η q) (gradFun g η q)) ≤ 1 + ε) ∧
          (∀ x, η x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
          η ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
          (∃ O' : Set M, IsOpen O' ∧ η ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O' ∧ ∀ q ∈ O', gradFun g η q ≠ 0) ∧
          ∀ q, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam (hlam : 80 ≤ lam),
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => lam * (η x - η q))
              (riemannianBallOf (scaleMetric (lam ^ 2) (by nlinarith) g) q 1) ∧
            lam * (η q - η q) = 0 ∧ lam * dist p q - lam * dist p q = 0 ∧
            (∀ x y, |(lam * (η x - η q) - (lam * dist p x - lam * dist p q)) -
                (lam * (η y - η q) - (lam * dist p y - lam * dist p q))| ≤
              ε * (lam * dist x y)) ∧
            (∀ x, |lam * (η x - η q) - (lam * dist p x - lam * dist p q)| ≤
              ε * (lam * dist q x)) ∧
            (∀ x y, |lam * (η x - η q) - lam * (η y - η q)| ≤
              (1 + ε) * (lam * dist x y)) ∧
            ∀ x ∈ riemannianBallOf (scaleMetric (lam ^ 2) (by nlinarith) g) q 1,
              |lam * (η x - η q) - (lam * dist p x - lam * dist p q)| < ε
 := by
  refine ⟨radialSmoothingConeError (ε / 4), radialSmoothingConeError_pos (by positivity),
    rfl, ?_⟩
  intro p C instC o δ φ HC hsec hδ e he he1
  obtain ⟨η, hLip, ⟨O, hO, hCO, hηO⟩, hclose, hout, hdiff, hη0, hηp, hgrad,
    hlevels, hsub, hregular⟩ := exists_buffered_radialFunction_of_kleinerLottApprox
      g hEnorm φ HC hsec hε (by linarith) hδ he he1
  refine ⟨η, hLip, ⟨O, hO, hCO, hηO⟩, hclose, hout, hdiff, hη0, hηp, hgrad,
    hlevels, hsub, hregular, ?_⟩
  intro q hq1 hq2 lam hlam
  have hlampos : 0 < lam := by linarith
  have hball := riemannianBallOf_scaled_eq_ball g hEnorm q hlampos
  have hbuffer := (ball_subset_buffer_of_shell hq1 hq2 hlam).trans hCO
  have hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => lam * (η x - η q))
      (riemannianBallOf (scaleMetric (lam ^ 2) (by nlinarith) g) q 1) := by
    rw [hball]
    exact contMDiffOn_const.mul ((hηO.mono hbuffer).sub contMDiffOn_const)
  have hdiff' : ∀ x y, |(η x - dist x p) - (η y - dist y p)| ≤ ε * dist x y := by
    simpa only [Metric.infDist_singleton] using hdiff
  obtain ⟨hcenter, hucenter, hnorm, hval, hψLip⟩ :=
    centered_radial_normalization hdiff' q hlampos
  refine ⟨hsmooth, hcenter, hucenter, hnorm, hval, hψLip, ?_⟩
  intro x hx
  rw [hball] at hx
  have hdist : lam * dist q x < 1 := by
    have hx' : dist x q < lam⁻¹ := hx
    rw [dist_comm, inv_eq_one_div] at hx'
    have h := (lt_div_iff₀ hlampos).mp hx'
    nlinarith
  exact (hval x).trans_lt (by nlinarith)

end DifferentialGeometry.Geometry.Collapse
