import DifferentialGeometry.Geometry.Collapse.SimultaneousAnnularStrainers
import DifferentialGeometry.Geometry.Collapse.OriginalRadialSplitting

/-!
# Joint original radial comparison

One outward point is chosen before every scale. The splitting map retains the original
radial function, and all prefixes of that point are calibrated against its actual coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Real Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open GC.MetricGeometry

theorem exists_simultaneous_original_radial_comparison {σ β : ℝ}
    (hσ : 0 < σ) (hσone : σ < 1) (hβ : 0 < β) (hβone : β < 1) :
    ∃ θ δstar Λstar : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < δstar ∧ 0 < Λstar ∧
      δstar ≤ min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600)) ∧
      max (20 * σ⁻¹) (max ((1 / 60) / sqrt σ) 2) ≤ Λstar ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M), IsMetricNorm g → ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δstar →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∃ z : M, dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
        ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
          ∃ (z₀ : Z) (F : @KleinerLottApprox M
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
            inferInstance q (WithLp.toLp 2 (0, z₀)) β),
            (∀ x : M, (@KleinerLottApprox.toFun M
              (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
              inferInstance q (WithLp.toLp 2 (0, z₀)) β F x).fst = WithLp.toLp 2
              (Function.const (Fin 1) (lam * (dist p x - dist p q)))) ∧
            (∀ x : M, 0 < dist q x → dist q x + dist x z = dist q z →
              lam * dist q x - 2 * (lam * dist q x) * (1 - cos θ) <
                (@KleinerLottApprox.toFun M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
                  inferInstance q (WithLp.toLp 2 (0, z₀)) β F x).fst 0 ∧
                (@KleinerLottApprox.toFun M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
                  inferInstance q (WithLp.toLp 2 (0, z₀)) β F x).fst 0 ≤ lam * dist q x) ∧
            ∃ a b : M, dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
              dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
              Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
                (lam * dist a b)
 := by
  obtain ⟨θ, hθ, hθone, -, hannular⟩ :=
    exists_simultaneous_original_annular_strainers (I := I) hσ hσone
  obtain ⟨δ₀, Λ₀, hδ₀, hΛ₀, hradial⟩ :=
    exists_original_radial_splitting_parameter_riemannian (I := I) hβ hβone
  let δσ := min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600))
  let Λσ := max (20 * σ⁻¹) (max ((1 / 60) / sqrt σ) 2)
  have hcos : 0 < 1 - cos θ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hθ
    rw [cos_zero] at h
    linarith
  have hδσ : 0 < δσ := by dsimp [δσ]; positivity
  refine ⟨θ, min δ₀ δσ, max Λ₀ Λσ, hθ, hθone,
    lt_min hδ₀ hδσ, lt_max_of_lt_left hΛ₀, min_le_right _ _, le_max_right _ _, ?_⟩
  intro M m cM sM scM cmM coM rM rmM crM g hEnorm p hsec C mC o H δ φ hδ q hq1 hq2
  have hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b) := by
    intro a b
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_dist]
  dsimp only at hannular
  obtain ⟨z, hz, he, -, hpref, hanchors⟩ :=
    hannular M g hEnorm p hsec C o H φ
      (hδ.trans_le (min_le_right _ _)) q hq1 hq2
  refine ⟨z, hz, he, ?_⟩
  intro lam hlam hΛ
  obtain ⟨Z, mZ, z₀, F, hcoord⟩ := hradial M g hmetric p hsec C o H φ
    (hδ.trans_le (min_le_left _ _)) q hq1 hq2 lam hlam ((le_max_left _ _).trans hΛ)
  let := mZ
  refine ⟨Z, mZ, z₀, F, hcoord, ?_, ?_⟩
  · intro x hx hxz
    have heval : (@KleinerLottApprox.toFun M
        (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
        inferInstance q (WithLp.toLp 2 (0, z₀)) β F x).fst 0 =
        lam * (dist p x - dist p q) := by rw [hcoord]; rfl
    rw [heval]
    have h := (hpref x hx hxz).2.2 lam hlam
    simpa only [mul_sub, dist_comm q p] using h
  · obtain ⟨-, -, hactualAnchors⟩ :=
      hanchors lam ((le_max_right _ _).trans hΛ)
    exact hactualAnchors

end DifferentialGeometry.Geometry.Collapse
