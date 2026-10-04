import DifferentialGeometry.Geometry.Collapse.RadialNormalizationRow
import DifferentialGeometry.Geometry.Comparison.AdaptedStabilityRiemannian
import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateInverse

/-!
# Actual consumers of the radial normalization and graph inverse adapters

The radial witness is chosen once. The adapted radial specialization uses the same
comparison coordinate, and the real-line graph example constructs a smooth inverse.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_radial_smooth_unit_ball (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4)
    {p : M} {C : Type*} [MetricSpace C] {o : C} {δ e : ℝ}
    (φ : KleinerLottApprox p o δ) (HC : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2))
    (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e) (he1 : e < 1 / 40) :
    ∃ η : M → ℝ, η p = 0 ∧
      ∀ q, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam (hlam : 80 ≤ lam),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => lam * (η x - η q))
          (riemannianBallOf (scaleMetric (lam ^ 2) (by nlinarith) g) q 1) ∧
        ∀ x ∈ riemannianBallOf (scaleMetric (lam ^ 2) (by nlinarith) g) q 1,
          |lam * (η x - η q) - (lam * dist p x - lam * dist p q)| < ε := by
  obtain ⟨δ₀, _hδpos, hδ₀, hmain⟩ := exists_centered_buffered_radialFunction g hEnorm hε hε4
  have hδ' : δ < δ₀ := by rwa [hδ₀]
  obtain ⟨η, _hLip, _hO, _hclose, _hout, _hdiff, _hη0, hηp, _hgrad, _hlevels,
    _hsub, _hreg, hnorm⟩ := hmain p C o δ φ HC hsec hδ' e he he1
  refine ⟨η, hηp, ?_⟩
  intro q hq1 hq2 lam hlam
  have h := hnorm q hq1 hq2 lam hlam
  exact ⟨h.1, h.2.2.2.2.2.2⟩

theorem radial_adapted_of_lipschitz_comparison (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (p q : M) {η φ Φ : M → ℝ} {γ t ε ζ : ℝ}
    (hγ : 0 < γ) (ht : 0 ≤ t) (hε : 0 ≤ ε) (hζ : γ + (t + ε) ≤ ζ)
    (hηs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η (Metric.ball q 1))
    (hφs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1)) (hφq : φ q = 0)
    (hηdiff : ∀ x y, |(η x - dist x p) - (η y - dist y p)| ≤ ε * dist x y)
    (hcomp : ∀ x y, |((dist p x - dist p q) - φ x) -
      ((dist p y - dist p q) - φ y)| ≤ t * dist x y)
    (hφlip : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |φ x - φ y| ≤ (1 + γ) * dist x y)
    (hφ1 : ∀ x ∈ Metric.ball q 1, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ)
    (hφ2 : ∀ s ∈ Ioo (-1 : ℝ) 1, Metric.infDist s (φ '' Metric.ball q 1) ≤ γ)
    (hφtest : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q γ⁻¹, 1 < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) φ x w - (Φ y - Φ x) / dist x y| < γ) :
    (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |(η x - η q) - (η y - η q)| ≤ (1 + ζ) * dist x y) ∧
    (∀ x ∈ Metric.ball q 1, Metric.infDist (η x - η q) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
    (∀ s ∈ Ioo (-1 : ℝ) 1,
      Metric.infDist s ((fun x => η x - η q) '' Metric.ball q 1) ≤ ζ) ∧
    ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q ζ⁻¹, 1 < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) (fun x => η x - η q) x w - (Φ y - Φ x) / dist x y| < ζ := by
  apply adapted_of_lipschitz_perturbation g hEnorm q hγ (add_nonneg ht hε) hζ
    hφs (hηs.sub contMDiffOn_const) hφq (sub_self _) hφlip hφ1 hφ2 hφtest
  intro x _hx y _hy
  have hsplit : ((η x - η q) - φ x) - ((η y - η q) - φ y) =
      ((η x - dist x p) - (η y - dist y p)) +
        (((dist p x - dist p q) - φ x) - ((dist p y - dist p q) - φ y)) := by
    rw [dist_comm x p, dist_comm y p]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add (hηdiff x y) (hcomp x y)).trans_eq (by ring))

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Analysis

theorem real_line_retained_coordinate_inverse (R : ℝ) :
    IsOpen (Subtype.val '' Metric.ball (0 : (⊤ : Submodule ℝ ℝ)) R) ∧
      ∃ σ : ℝ → (⊤ : Submodule ℝ ℝ),
        InvOn σ (fun t : (⊤ : Submodule ℝ ℝ) => t.val) (Metric.ball 0 R)
          (Subtype.val '' Metric.ball (0 : (⊤ : Submodule ℝ ℝ)) R) ∧
        ContDiffOn ℝ ∞ σ (Subtype.val '' Metric.ball (0 : (⊤ : Submodule ℝ ℝ)) R) := by
  simpa only [ContinuousLinearMap.id_apply, add_zero, zero_add] using
    exists_smooth_inverse_retained_coordinate_graph (⊤ : Submodule ℝ ℝ)
      (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.norm_id_le)
      (m := 1) (a := 0) (fun v hv => by simp) (by norm_num) (by simp)
      (fun _t => (0 : ℝ)) contDiffOn_const (fun t _ht => by
        have hd : fderiv ℝ (fun _t : (⊤ : Submodule ℝ ℝ) => (0 : ℝ)) t = 0 :=
          (hasFDerivAt_const (0 : ℝ) t).fderiv
        rw [hd]
        change ‖(0 : (⊤ : Submodule ℝ ℝ) →L[ℝ] ℝ)‖ ≤ (0 : ℝ)
        exact le_of_eq ContinuousLinearMap.opNorm_zero) (0 : ℝ)

end DifferentialGeometry.Analysis
