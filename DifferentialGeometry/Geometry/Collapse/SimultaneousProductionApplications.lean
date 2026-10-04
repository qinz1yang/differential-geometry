import DifferentialGeometry.Geometry.Collapse.SimultaneousComparisonData
import DifferentialGeometry.Geometry.Collapse.NormalizedCenterData
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicity

/-!
The original volume radius and standing curvature data supply one joint normalized analytic
package at every actual center. Prefix and circle consumers retain their literal source data.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Real Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

section Prefix

theorem simultaneous_annular_real_line {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ)
    (hbudget : 90 * δ < 1 - cos τ) :
    π - τ < comparisonAngleNegCurvature ((1 / 3) ^ 2)
      (dist (0 : ℝ) (-2 / 5)) (dist (0 : ℝ) (2 / 5)) (dist (-2 / 5 : ℝ) (2 / 5)) := by
  apply simultaneous_annular_prefix_model_angle (-1 : ℝ) 0 1 (-2 / 5) (2 / 5)
    (a := 1) (δ := δ) (by norm_num) zero_lt_one
  all_goals norm_num [Real.dist_eq] at *
  · linarith
  · exact hτ
  · exact hbudget

theorem simultaneous_edge_real_line {Δ τ : ℝ} (hΔ : 0 < Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) :
    1 + cos (comparisonAngleNegCurvature 0 (dist (0 : ℝ) (-Δ))
      (dist (0 : ℝ) Δ) (dist (-Δ : ℝ) Δ)) < 100 * τ := by
  have hleft : dist (0 : ℝ) (-Δ) = Δ := by simp [Real.dist_eq, abs_of_pos hΔ]
  have hright : dist (0 : ℝ) Δ = Δ := by simp [Real.dist_eq, abs_of_pos hΔ]
  have hchord : dist (-Δ : ℝ) Δ = 2 * Δ := by
    rw [Real.dist_eq, show -Δ - Δ = -(2 * Δ) by ring, abs_neg,
      abs_of_pos (mul_pos (by norm_num) hΔ)]
  rw [hleft, hright, hchord]
  simpa only [zero_pow (by decide : 2 ≠ 0)] using
    simultaneous_edge_model_angle_bound (κ := 0) (by norm_num) hΔ hτ hτsmall
      (by linarith) (by nlinarith) (by norm_num)
      (by simp only [sub_self, abs_zero]; positivity) (by linarith) (by nlinarith)

end Prefix

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompleteSpace M]

omit [CompleteSpace E] in
theorem normalizedCenterMetric_noncollapse (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w u ρ : ℝ} (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hvol : ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hsec : ∀ y ∈ riemannianBallOf g p u, SectionalBoundedBelowAt g y (-(u ^ 2)⁻¹)) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ≤
        (ballVolume (normalizedCenterMetric g ρ hρ) p 1).toReal := by
  obtain ⟨hpos, hbound⟩ := sectionalThree_volume_lower_at_modified_scale
    g hEnorm hdim p hw hu hρ hρu hvol hsec
  have hs : sqrt ((ρ ^ 2)⁻¹) = ρ⁻¹ := by
    rw [sqrt_inv, sqrt_sq_eq_abs, abs_of_pos hρ]
  have he : sqrt ((ρ ^ 2)⁻¹) * ρ = 1 := by rw [hs, inv_mul_cancel₀ hρ.ne']
  have hv := ballVolume_scaleMetric hdim (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g p ρ
  rw [he] at hv
  have hid : (ballVolume (normalizedCenterMetric g ρ hρ) p 1).toReal =
      (ballVolume g p ρ).toReal / ρ ^ 3 := by
    unfold normalizedCenterMetric
    rw [hv, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (sqrt_nonneg _), hs]
    simp only [div_eq_mul_inv, inv_pow, mul_comm]
  exact ⟨hpos, hid ▸ hbound⟩

theorem normalizedCenterMetric_joint_data (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hdim : Module.finrank ℝ E = 3)
    (K : ℕ) (A : ℝ → ℝ) (p : M) {α w u ρ : ℝ}
    (hα : 4 < α) (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hscale : ENNReal.ofReal (α * u) ≤ curvatureRadius g p)
    (hvol : ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hA : ∀ C, 0 < C → 0 ≤ A C)
    (hcurv : ∀ C, 0 < C → C < α → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf g p (C * u),
        curvatureDerivativeNorm g k y ≤ A C * (u ^ (k + 2))⁻¹) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ≤
        (ballVolume (normalizedCenterMetric g ρ hρ) p 1).toReal ∧
      (∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p (α / 4),
        SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) y (-((α / 4) ^ 2)⁻¹)) ∧
      ∀ R, 0 < R → 2 * R + 2 < α → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k y ≤
            (2 : ℝ) ^ (K + 2) * A (2 * R + 2) := by
  have hαpos : 0 < α := by linarith
  have hlt : ENNReal.ofReal u < curvatureRadius g p :=
    ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hαpos hu)).mpr (by nlinarith)).trans_le hscale
  obtain ⟨hvpos, hv⟩ := normalizedCenterMetric_noncollapse g hEnorm hdim p hw hu hρ hρu hvol
    (fun y hy => sectionalBoundedBelowAt_of_lt_curvatureRadius g hlt hy)
  exact ⟨hvpos, hv, normalizedCenterMetric_sectional_buffer g p hαpos hu hρ hρu hscale,
    normalizedCenterMetric_derivative_bounds g p K A hu hρ hρu hA hcurv⟩

end Analytic

section Support

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompactSpace M]

theorem exists_simultaneous_support_cover (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hdim : Module.finrank ℝ E = 3)
    (S : Set M) {r : M → ℝ} {Λ : NNReal}
    (hr : LipschitzWith Λ r) (hrpos : ∀ p, 0 < r p)
    (hsmall : (Λ : ℝ) * 2000000 ≤ 1 / 100)
    (hsec : ∀ p ∈ S, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * r p),
      SectionalBoundedBelowAt g y (-((2000000 * r p) ^ 2)⁻¹)) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => ball p (r p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, ball p (r p) ⊆ ball i (2 * r i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ ball i (2000000 * r i)}).ncard : ℝ) ≤
        modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
          modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  have hRic : ∀ p ∈ S, ricciBoundedBelowOn g
      (ball p ((3 * 2000000 + 2 * (1 / 3)) * r p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-(((1 / 2000000) / r p) ^ 2))) := by
    intro p hp
    rw [hdim]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    apply ricciBoundedBelowOn_of_sectional_three g hdim
    intro y hy
    have h := hsec p hp y (by convert hy using 1; norm_num)
    have he : -((2000000 * r p) ^ 2)⁻¹ = -(((1 / 2000000) / r p) ^ 2) := by
      field_simp
    simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat, he] using h
  have hselection : (Λ : ℝ) * 1 ≤ 1 / 100 := by
    have hn : (0 : ℝ) ≤ Λ := Λ.property
    nlinarith
  have hoverlap : (Λ : ℝ) * 2000000 ≤ 1 / 4 := by linarith
  obtain ⟨J, hJS, hfin, hdisj, hcover, hmulti⟩ :=
    exists_finite_scale_cover_of_ricci_bound g hEnorm S hr hrpos
      (Δ := 1) (C := 2000000) (q := 1 / 2000000)
      zero_lt_one (by norm_num) (by norm_num) hselection hoverlap hRic
  refine ⟨J, hJS, hfin, ?_, ?_, ?_⟩
  · simpa only [one_mul] using hdisj
  · simpa only [one_mul, mul_one] using hcover
  · convert hmulti using 1; norm_num [hdim]

end Support

end DifferentialGeometry.Geometry.Collapse

namespace GC.MetricGeometry

universe u v w

theorem exists_simultaneous_three_circle_tests :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (A : Type w) [MetricSpace A] (a : A) (σ β : ℝ), σ ≤ η → β ≤ η →
        KleinerLottApprox z c σ →
        ∀ F : Fin 3 → KleinerLottApprox z
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) β,
          ∀ i x, dist x z ≤ 201 → dist ((F i).toFun x).snd a < 1 := by
  obtain ⟨η, hη, hηsmall, htest⟩ := exists_simultaneous_circle_residual_threshold.{u, v, w}
  refine ⟨η, hη, hηsmall, ?_⟩
  intro Z mZ z C mC hcomplete c hcurves hdim hcomp A mA a σ β hσ hβ happrox F i x hx
  exact htest Z z C c hcurves hdim hcomp A a σ β hσ hβ happrox (F i) x hx

end GC.MetricGeometry
