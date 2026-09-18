import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance comparisonCurvatureSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance comparisonCurvatureModelC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem openPullbackMetric_rm04
    (F : PartialDiffeomorph I3 I3 N M ∞) (U : TopologicalSpace.Opens N)
    (hU : (U : Set N) ⊆ F.source) (g : SmoothRiemannianMetric I3 M)
    (y : U) (a b c d : TangentSpace I3 y) :
    metricRm04StandardAt (openPullbackMetric F U hU g) y a b c d =
      metricRm04StandardAt g (F (y : N)) (mfderiv I3 I3 F (y : N) a)
        (mfderiv I3 I3 F (y : N) b) (mfderiv I3 I3 F (y : N) c)
        (mfderiv I3 I3 F (y : N) d) := by
  rw [openPullbackMetric, metricRm04Standard_pullback, metricRm04StandardAt_restrictOpen]
  simp only [PartialDiffeomorph.mfderiv_toOpensDiffeo]
  rw [mfderiv_subtype_val (I := I3)
    (⟨F '' (U : Set N), image_opens_isOpen F hU⟩ : TopologicalSpace.Opens M)]
  rfl

omit [SigmaCompactSpace M] in
theorem MetricComparisonOn.secLower_image
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {A : Set N} {times : Set ℝ}
    {order : ℕ} {eps c K : ℝ} (P : MetricComparisonOn h g F A times order eps)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (hUA : (U : Set N) ⊆ A) {s : ℝ} (hs : s ∈ times)
    (heps : eps ≤ 1 / 2) (horder : 2 ≤ order) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsec : SecLower (h s) c U)
    (hrm : ∀ y ∈ (U : Set N), normSq0S (h s) y 4 (metricRm04At (h s) y) ≤ K ^ 2) :
    SecLower (g s) (c - 4 * eps * (c + 360 + K)) (F '' (U : Set N)) := by
  rintro _ ⟨y, hy, rfl⟩ v w
  let yU : U := ⟨y, hy⟩
  let G := (h s).restrictOpen U
  let gp := openPullbackMetric F U hU (g s)
  have hsmall : ∀ a : ℕ, a ≤ 2 → metricDerivNorm a gp G G yU ≤ eps := by
    intro a ha
    rw [P.openPullback_metricDerivNorm U hU hUA]
    exact P.close a 0 (by omega) s hs y (hUA hy)
  have hsecG : ∀ a b : TangentSpace I3 yU,
      c * (G.inner yU a a * G.inner yU b b - G.inner yU a b ^ 2) ≤
        metricRm04StandardAt G yU a b b a := by
    intro a b
    dsimp only [G]
    rw [metricRm04StandardAt_restrictOpen]
    simp only [mfderiv_subtype_val_apply]
    exact hsec y hy a b
  have hRmG : ∀ a b d : TangentSpace I3 yU,
      Real.sqrt (G.inner yU (riemannOp (LeviCivita G) yU a b d)
        (riemannOp (LeviCivita G) yU a b d)) ≤ K * Real.sqrt (G.inner yU a a) *
        Real.sqrt (G.inner yU b b) * Real.sqrt (G.inner yU d d) := by
    intro a b d
    have hn : normSq0S G yU 4 (metricRm04At G yU) ≤ K ^ 2 := by
      simpa only [G, rmNormSq_restrictOpen] using hrm y hy
    have hh := riemannOp_normSq_le_of_rmNormSq_le G yU hn a b d
    have heq : K ^ 2 * G.inner yU a a * G.inner yU b b * G.inner yU d d =
        (K * Real.sqrt (G.inner yU a a) * Real.sqrt (G.inner yU b b) *
          Real.sqrt (G.inner yU d d)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (inner_self_nonneg G yU a),
        Real.sq_sqrt (inner_self_nonneg G yU b), Real.sq_sqrt (inner_self_nonneg G yU d)]
    rw [heq] at hh
    exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq (by positivity))
  let D := (F.isLocalDiffeomorphAt I3 I3 ∞ (hU hy)).mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨a, ha⟩ := D.surjective v
  obtain ⟨b, hb⟩ := D.surjective w
  have ha' : mfderiv I3 I3 F y a = v := ha
  have hb' : mfderiv I3 I3 F y b = w := hb
  let aU : TangentSpace I3 yU := a
  let bU : TangentSpace I3 yU := b
  have haU : mfderiv I3 I3 F (yU : N) aU = v := ha'
  have hbU : mfderiv I3 I3 F (yU : N) bU = w := hb'
  have hh := metricRm04_lower_bound_of_small_metric_derivatives gp G yU heps hc hK
    hsmall hsecG hRmG aU bU
  dsimp only [gp] at hh
  rw [openPullbackMetric_inner F U hU (g s) yU aU aU,
    openPullbackMetric_inner F U hU (g s) yU bU bU,
    openPullbackMetric_inner F U hU (g s) yU aU bU,
    openPullbackMetric_rm04 F U hU (g s) yU aU bU bU aU] at hh
  rw [haU, hbU] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
