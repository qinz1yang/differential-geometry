import DifferentialGeometry.Geometry.Comparison.DistanceFamily
import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_compact_distance_cutoff_support
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J)
    (hcomplete : ∀ t ∈ K, RiemannianMetricComplete (I := I) (g t))
    (O : M) {a : ℝ} (ha : 0 < a) :
    ∃ L : Set M, IsCompact L ∧
      ∀ t ∈ K, ∀ x ∉ L, Analysis.CutoffProfile.evalue
        (ENNReal.ofReal a * riemannianEDistOf (I := I) (g t) O x) = 0 := by
  obtain ⟨L, hL, hcover⟩ := exists_compact_riemannianEDistOf_le_of_isCompact
    (I := I) g hg hK hKJ hcomplete O (2 / a)
  refine ⟨L, hL, ?_⟩
  intro t ht x hx
  have hdist : ENNReal.ofReal (2 / a) ≤ riemannianEDistOf (I := I) (g t) O x := by
    by_contra hn
    exact hx (hcover t ht x (le_of_not_ge hn))
  apply Analysis.CutoffProfile.evalue_zero_of_ge
  have hmul := mul_le_mul_right hdist (ENNReal.ofReal a)
  rw [← ENNReal.ofReal_mul ha.le] at hmul
  have hcoef : a * (2 / a) = 2 := by field_simp
  simpa only [hcoef, ENNReal.ofReal_ofNat] using hmul

theorem continuousOn_distance_cutoff
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (hcomplete : ∀ t ∈ J, RiemannianMetricComplete (I := I) (g t))
    (O : M) (a : ℝ) :
    ContinuousOn (fun p : ℝ × M => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (g p.1) O p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  have hd := continuousOn_riemannianEDistOf (I := I) g hJ hg hcomplete O
  have hmul : Continuous (fun r : ENNReal => ENNReal.ofReal a * r) :=
    ENNReal.continuous_const_mul ENNReal.ofReal_ne_top
  exact Analysis.CutoffProfile.continuous_evalue.comp_continuousOn (hmul.comp_continuousOn hd)

end DifferentialGeometry.Geometry.Riemannian
