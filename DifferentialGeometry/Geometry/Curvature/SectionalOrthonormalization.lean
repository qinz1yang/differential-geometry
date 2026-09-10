import DifferentialGeometry.Geometry.Curvature.SectionalHomogeneity
import DifferentialGeometry.Geometry.Curvature.UniformSectionalBound
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry

theorem IsAlgCurvForm.pair_shear {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvForm B) (v w : V) (a b : ℝ) :
    B v (a • w - b • v) (a • w - b • v) v = a ^ 2 * B v w w v := by
  have hsmul₂ (x y z t : V) (c : ℝ) : B x (c • y) z t = c * B x y z t := by
    rw [hB.anti_first, hB.smul_left, hB.anti_first y x z t]
    ring
  have hsmul₃ (x y z t : V) (c : ℝ) : B x y (c • z) t = c * B x y z t := by
    rw [hB.pair_swap, hB.smul_left, hB.pair_swap z t x y]
  have hzero₁ (z t : V) : B v v z t = 0 := by
    have h := hB.anti_first v v z t
    linarith
  have hzero₂ (x y : V) : B x y v v = 0 := by
    have h := hB.anti_last x y v v
    linarith
  rw [sub_eq_add_neg, ← neg_smul, hB.add_two, hsmul₂, hsmul₂, hzero₁, mul_zero, add_zero,
    hB.add_three, hsmul₃, hsmul₃, hzero₂, mul_zero, add_zero]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_orthonormal_pair_sectional_quotient (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (hvw : LinearIndependent ℝ ![v, w]) :
    ∃ u q : TangentSpace I x,
      g.inner x u u = 1 ∧ g.inner x q q = 1 ∧ g.inner x u q = 0 ∧
      metricRm04StandardAt g x u q q u = metricRm04StandardAt g x v w w v /
        (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by
  let a := g.inner x v v
  let b := g.inner x v w
  let Δ := a * g.inner x w w - b ^ 2
  let z : TangentSpace I x := a • w - b • v
  have ha : 0 < a := g.pos x v (hvw.ne_zero 0)
  have hΔ : 0 < Δ := gram_determinant_pos g x v w hvw
  have hzz : g.inner x z z = a * Δ := by
    dsimp only [z, Δ]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [g.symm x w v]
    dsimp only [a, b]
    ring
  have hvz : g.inner x v z = 0 := by
    dsimp only [z]
    simp only [map_sub, map_smul, smul_eq_mul]
    dsimp only [a, b]
    ring
  let r := Real.sqrt a
  let s := Real.sqrt (a * Δ)
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos ha hΔ)
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  have hs2 : s ^ 2 = a * Δ := Real.sq_sqrt (mul_pos ha hΔ).le
  let u : TangentSpace I x := r⁻¹ • v
  let q : TangentSpace I x := s⁻¹ • z
  have hshear : metricRm04StandardAt g x v z z v = a ^ 2 * metricRm04StandardAt g x v w w v :=
    IsAlgCurvForm.pair_shear
      (mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x))
      v w a b
  refine ⟨u, q, ?_, ?_, ?_, ?_⟩
  · dsimp only [u]
    simp only [map_smul, smul_apply, smul_eq_mul]
    change r⁻¹ * (r⁻¹ * a) = 1
    rw [← hr2]
    field_simp
  · dsimp only [q]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hzz, ← hs2]
    field_simp
  · dsimp only [u, q]
    simp only [map_smul, smul_apply, smul_eq_mul, hvz, mul_zero]
  · dsimp only [u, q]
    rw [sectional_contraction_smul_pair, hshear, inv_pow, inv_pow, hr2, hs2]
    change a⁻¹ * (a * Δ)⁻¹ * (a ^ 2 * metricRm04StandardAt g x v w w v) =
      metricRm04StandardAt g x v w w v / Δ
    field_simp

theorem HasPositiveSectionalCurvature.exists_uniform_sectional_quotient_bound [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g) :
    ∃ k : ℝ, 0 < k ∧ ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent ℝ ![v, w] → k ≤ metricRm04StandardAt g x v w w v /
        (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by
  obtain ⟨k, hk, hbound⟩ := hg.exists_uniform_orthonormal_bound
  refine ⟨k, hk, ?_⟩
  intro x v w hvw
  obtain ⟨u, q, hu, hq, huq, heq⟩ := exists_orthonormal_pair_sectional_quotient g x v w hvw
  exact le_trans (hbound x u q hu hq huq) heq.le

end DifferentialGeometry.Geometry
