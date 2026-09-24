import DifferentialGeometry.Geometry.Comparison.Toponogov.RemoteTriangle
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

private theorem comparisonAngle_lower_of_perturbed_equal_arms
    {R D a b c : ℝ} (hR : 0 < R) (hRD : 10 * D < R)
    (ha : |a - R| ≤ D) (hb : |b - R| ≤ D) (hc : 3 / 2 * R - D ≤ c) :
    R / 2 < a ∧ R / 2 < b ∧ Real.pi / 3 ≤ comparisonAngle a b c := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have halow : 9 * R / 10 ≤ a := by linarith
  have hblow : 9 * R / 10 ≤ b := by linarith
  have haup : a ≤ 11 * R / 10 := by linarith
  have hbup : b ≤ 11 * R / 10 := by linarith
  have hclow : 14 * R / 10 ≤ c := by linarith
  have hca : a ^ 2 ≤ (11 * R / 10) ^ 2 :=
    (sq_le_sq₀ ha0.le (by positivity)).mpr haup
  have hcb : b ^ 2 ≤ (11 * R / 10) ^ 2 :=
    (sq_le_sq₀ hb0.le (by positivity)).mpr hbup
  have hcc : (14 * R / 10) ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr hclow
  have hab : (9 * R / 10) * (9 * R / 10) ≤ a * b :=
    mul_le_mul halow hblow (by positivity) ha0.le
  have hcos : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a * b)).mpr
    nlinarith [sq_nonneg R]
  refine ⟨by linarith, by linarith, ?_⟩
  have hang := Real.arccos_le_arccos hcos
  rw [← Real.cos_pi_div_three, Real.arccos_cos (by positivity)
    (by nlinarith [Real.pi_pos])] at hang
  exact hang

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem exists_remote_triangle_of_additive_distortion
    (g0 : SmoothRiemannianMetric I M) (hnoncompact : ¬ CompactSpace M)
    (hcomplete : RiemannianMetricComplete g0) (hsec : SectionalBoundedBelow g0 0)
    (p : M) {D : ℝ} (hD : 0 ≤ D) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ g : SmoothRiemannianMetric I M,
      (∀ x z : M, |(riemannianEDistOf g x z).toReal -
        (riemannianEDistOf g0 x z).toReal| ≤ D) →
      ∀ y : M, R0 < (riemannianEDistOf g0 p y).toReal →
      ∃ z : M,
        (riemannianEDistOf g0 p y).toReal < (riemannianEDistOf g0 p z).toReal ∧
        (riemannianEDistOf g0 p y).toReal / 2 < (riemannianEDistOf g y p).toReal ∧
        (riemannianEDistOf g0 p y).toReal / 2 < (riemannianEDistOf g y z).toReal ∧
        Real.pi / 3 ≤ comparisonAngle (riemannianEDistOf g y p).toReal
          (riemannianEDistOf g y z).toReal (riemannianEDistOf g p z).toReal := by
  obtain ⟨R, hR⟩ := remotePointTriangle (I := I) M g0 hnoncompact hcomplete hsec p
  refine ⟨max R (10 * D) + 1, by positivity, ?_⟩
  intro g hdist y hy
  have hyR : R < (riemannianEDistOf g0 p y).toReal := by
    have hh := le_max_left R (10 * D)
    linarith
  have hyD : 10 * D < (riemannianEDistOf g0 p y).toReal := by
    have hh := le_max_right R (10 * D)
    linarith
  obtain ⟨z, hz, hfar⟩ := hR y hyR
  have hypos : 0 < (riemannianEDistOf g0 p y).toReal := by linarith
  have ha := hdist y p
  rw [riemannianEDistOf_comm g0 y p] at ha
  have hb := hdist y z
  rw [hz] at hb
  have hc : 3 / 2 * (riemannianEDistOf g0 p y).toReal - D ≤
      (riemannianEDistOf g p z).toReal := by
    have hh := (abs_le.mp (hdist p z)).1
    linarith
  obtain ⟨hap, hbp, hang⟩ :=
    comparisonAngle_lower_of_perturbed_equal_arms hypos hyD ha hb hc
  exact ⟨z, by linarith, hap, hbp, hang⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
