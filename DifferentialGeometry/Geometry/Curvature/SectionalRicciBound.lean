import DifferentialGeometry.Geometry.Curvature.UniformSectionalBound
import DifferentialGeometry.Geometry.Curvature.SectionalHomogeneity
import DifferentialGeometry.Geometry.Curvature.SectionalOrthonormalization
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci



noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Connection

namespace Poincare.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ricciBoundedBelow_of_orthonormal_sectional_bound
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E) {k : ℝ}
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v v = 1 → g.inner x w w = 1 → g.inner x v w = 0 →
        k ≤ metricRm04StandardAt g x v w w v) :
    RicciBoundedBelow g (((Module.finrank ℝ E : ℝ) - 1) * k) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  intro x v
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos := g.pos x v hv
  let s : ℝ := Real.sqrt (g.inner x v v)
  have hs : 0 < s := Real.sqrt_pos.mpr hvpos
  have hs2 : s ^ 2 = g.inner x v v := Real.sq_sqrt hvpos.le
  let u : TangentSpace I x := s⁻¹ • v
  have hu : g.inner x u u = 1 := by
    dsimp only [u]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hs2]
    field_simp
  obtain ⟨e, hON, hperp⟩ := exists_perp_pos g x v hvpos
  have hbound (i : Fin (Module.finrank ℝ E - 1)) :
      k * g.inner x v v ≤ metricRm04StandardAt g x (e i) v v (e i) := by
    have heu : g.inner x (e i) u = 0 := by
      dsimp only [u]
      rw [map_smul, hperp i, smul_zero]
    have h := hsec x (e i) u (by simpa using hON i i) hu heu
    have heq : metricRm04StandardAt g x (e i) u u (e i) =
        s⁻¹ ^ 2 * metricRm04StandardAt g x (e i) v v (e i) := by
      simpa only [one_smul, one_pow, one_mul] using
        sectional_contraction_smul_pair g x (e i) v 1 s⁻¹
    rw [heq] at h
    have hh := mul_le_mul_of_nonneg_right h (sq_nonneg s)
    rw [← hs2]
    calc
      k * s ^ 2 ≤ (s⁻¹ ^ 2 * metricRm04StandardAt g x (e i) v v (e i)) * s ^ 2 := hh
      _ = _ := by field_simp
  rw [← ricci_eq_sum_perp g x v hvpos e hON hperp]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  have hnat : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  calc
    ((Module.finrank ℝ E : ℝ) - 1) * k * g.inner x v v =
        ∑ _i : Fin (Module.finrank ℝ E - 1), k * g.inner x v v := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnat]
      ring
    _ ≤ ∑ i : Fin (Module.finrank ℝ E - 1), metricRm04StandardAt g x (e i) v v (e i) := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rm04_eq_inner_riem, g.symm]

theorem HasPositiveSectionalCurvature.exists_positive_ricci_bound [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ k : ℝ, 0 < k ∧ RicciBoundedBelow g (((Module.finrank ℝ E : ℝ) - 1) * k) := by
  obtain ⟨k, hk, hbound⟩ := hg.exists_uniform_orthonormal_bound
  exact ⟨k, hk, ricciBoundedBelow_of_orthonormal_sectional_bound g hdim hbound⟩

theorem HasPositiveSectionalCurvature.exists_uniform_sectional_and_ricci_bound [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ k : ℝ, 0 < k ∧
      (∀ (x : M) (v w : TangentSpace I x), LinearIndependent ℝ ![v, w] →
        k ≤ metricRm04StandardAt g x v w w v /
          (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) ∧
      RicciBoundedBelow g (((Module.finrank ℝ E : ℝ) - 1) * k) := by
  obtain ⟨k, hk, hbound⟩ := hg.exists_uniform_orthonormal_bound
  refine ⟨k, hk, ?_, ricciBoundedBelow_of_orthonormal_sectional_bound g hdim hbound⟩
  intro x v w hvw
  obtain ⟨u, q, hu, hq, huq, heq⟩ := exists_orthonormal_pair_sectional_quotient g x v w hvw
  exact le_trans (hbound x u q hu hq huq) heq.le

end Poincare.Geometry
