import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
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

omit [SigmaCompactSpace M] in
open scoped Bundle ENNReal NNReal in
open Geometry.Operator in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem grad_norm_distance_cutoff_le
    (g h : SmoothRiemannianMetric I M) (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (o : M) (a : ℝ≥0) (x : M) :
    Real.sqrt (h.inner x
      (gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x)
      (gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x)) ≤ Analysis.CutoffProfile.derivBound * a := by
  let : LocallyCompactSpace M := _root_.Manifold.locallyCompact_of_finiteDimensional I
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hlip := Analysis.CutoffProfile.lipschitzWith_edist a o
  apply grad_norm_le_lip_all h (L := ⟨Analysis.CutoffProfile.derivBound,
    Analysis.CutoffProfile.derivBound_nonneg⟩ * a)
  intro y z
  exact (hlip y z).trans (mul_le_mul_right (edistOf_mono g h hgh y z) _)

omit [T2Space M] [SigmaCompactSpace M] in
open scoped ENNReal NNReal in
open Geometry.Operator in
theorem support_gradFun_distance_cutoff_subset
    (g h : SmoothRiemannianMetric I M) (o : M) (a : ℝ≥0) :
    Function.support (fun x => gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x) ⊆
      {x | (a : ℝ≥0∞) * riemannianEDistOf g o x ∈ Set.Ioo 1 2} := by
  intro x hx
  let f : M → ℝ := fun y => Analysis.CutoffProfile.evalue
    ((a : ℝ≥0∞) * riemannianEDistOf g o y)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
    by_contra hn
    exact hx (gradFun_eq_zero_of_mfderiv_eq_zero h f (mfderiv_zero_of_not_mdifferentiableAt hn))
  constructor
  · by_contra hn
    have hf : f x = 1 := Analysis.CutoffProfile.evalue_one_of_le (le_of_not_gt hn)
    have hmax : IsLocalMax f x := Filter.Eventually.of_forall fun y => by
      rw [hf]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).2
    exact hx (gradientFun_eq_zero_of_isLocalMax h hmax hd)
  · by_contra hn
    have hf : f x = 0 := Analysis.CutoffProfile.evalue_zero_of_ge (le_of_not_gt hn)
    have hmin : IsLocalMin f x := Filter.Eventually.of_forall fun y => by
      rw [hf]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).1
    exact hx (gradientFun_eq_zero_of_isLocalMin h hmin hd)

end DifferentialGeometry.Geometry.Riemannian
