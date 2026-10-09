import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u

private local instance (U : Opens ThreeSpace) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

theorem exists_uniform_standard_cap_restriction_of_curvature_bound
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P C₀ : ℝ, 0 < P ∧ 0 < C₀ ∧
      ∀ {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless],
      ∀ (K D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧
        ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
          [IsManifold I ∞ M] [T2Space M]
          {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
          {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
          {r : ℝ} {m : ℕ} {ζ : ℝ}
          (w : CanonicalStaticInsertionWitness d A hA r m ζ),
        R ≤ r → m₀ ≤ m → ζ ≤ ζ₀ →
        ∀ (T : ℝ) (hT : 0 < T), T ≤ Θ →
        ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow r)
            (RealTimeInterval.closed 0 T hT.le),
          IsSolutionOn S → S.base.metric 0 = w.windowMetric →
          (∀ (y : standardCapWindow r) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
              (fun z : ℝ × standardCapWindow r =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 i j)
              (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
          (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow r,
            nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
          ∃ hDr : D ≤ r,
          ∃ F : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 T hT.le),
            IsSolutionOn F ∧
            (∀ t : ℝ, F.base.metric t = (S.base.metric t).restrictOpenOfSubset
              (fun _ hx => hx.trans_le (add_le_add hDr (le_refl 1)) :
                standardCapWindow D ≤ standardCapWindow r)) ∧
            F.base.metric 0 = (w.restrictWindow hD hDr).windowMetric ∧
            (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
                (fun z : ℝ × standardCapWindow D =>
                  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (F.base.metric z.1) y z.2 i j)
                (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
            (∀ t ∈ Icc 0 T, ∀ x : standardCapWindow D,
              nablaKRm04NormSqIntrinsic F 0 t x ≤ P ^ 2 ∧ |F.scalar t x| ≤ C₀) ∧
            ∃ Q : StandardSolution, ENNReal.ofReal T < Q.val.lifetime ∧
              ∀ t ∈ Icc 0 T,
                (∀ j : ℕ, j ≤ N → ∀ x : standardCapWindow D,
                  metricDerivNorm j (F.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (metric.restrictOpen (standardCapWindow D)) x < ε) ∧
                (∀ j : ℕ, j ≤ 2 → ∀ x : standardCapWindow D,
                  metricDerivNorm j (F.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (metric.restrictOpen (standardCapWindow D)) x < η) := by
  obtain ⟨εRm, P, hεRm, hP, hRm⟩ :=
    exists_uniform_curvature_bound_of_standard_metric_close_on_opens Θ hΘ.le hΘ1
  refine ⟨P, 9 * P, hP, by positivity, ?_⟩
  intro E H _ _ _ _ _ I _ K D ε η hD hε hη N
  let e := min (ε / 2) (min (η / 2) εRm)
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨R, _, hDR, m₀, ζ₀, hζ₀, hcompare⟩ :=
    exists_uniform_standard_cap_comparison_on_bounded_intervals_of_curvature_bound
      (I := I) Θ K (D + 1) e hΘ hΘ1 he (max N 2)
  refine ⟨R, hDR, max m₀ 4, le_max_right _ _, min ζ₀ (1 / 2),
    lt_min hζ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA r m ζ w hRr hm hζ T hT hTΘ S hS hzero hgram hcurv
  obtain ⟨Q, hQlife, hclose⟩ := hcompare w hRr ((le_max_left _ _).trans hm)
    (hζ.trans (min_le_left _ _)) T hT hTΘ S hS hzero hgram hcurv
  have hDr : D ≤ r := by linarith
  let hsub : standardCapWindow D ≤ standardCapWindow r :=
    fun _ hx => hx.trans_le (add_le_add hDr (le_refl 1))
  let inc : standardCapWindow D → standardCapWindow r := Opens.inclusion hsub
  have hi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      inc (contMDiff_inclusion hsub) _ rfl
    intro y
    change Function.Injective (mfderiv ThreeModel ThreeModel (Opens.inclusion hsub) y)
    rw [mfderiv_opens_incl]
    exact Function.injective_id
  let F := S.localPullback inc hi
  have hFmetric (t : ℝ) : F.base.metric t = (S.base.metric t).restrictOpenOfSubset hsub := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v z
    change (localPullMetric (S.base.metric t) inc hi).inner y v z = _
    rw [localPullMetric_inner]
    simp only [inc, mfderiv_opens_incl]
    rfl
  have hFzero : F.base.metric 0 = (w.restrictWindow hD hDr).windowMetric := by
    rw [hFmetric, hzero, CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
  have hFgram := S.localPullback_chartGramMatrix_joint_contMDiffOn inc hi (Icc 0 T) hgram
  have hcompact : IsCompact {y : standardCapWindow r | ‖y.val‖ ≤ D + 1} := by
    have hc : IsCompact {y : ThreeSpace | ‖y‖ ≤ D + 1} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (D + 1)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro y hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      change ‖y‖ < r + 1
      change ‖y‖ ≤ D + 1 at hy
      linarith)
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) (j : ℕ) (hj : j ≤ max N 2)
      (x : standardCapWindow D) :
      metricDerivNorm j (F.base.metric t)
        ((Q.val.metric t).restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x < e := by
    have hx : inc x ∈ {y : standardCapWindow r | ‖y.val‖ ≤ D + 1} := by
      change ‖x.val‖ ≤ D + 1
      exact x.property.le
    have hp := (derivNorm_le_sup hcompact hj _ _ _ hx).trans_lt (hclose t ht)
    have heq := metricDerivNorm_flat hsub (S.base.metric t)
      ((Q.val.metric t).restrictOpen (standardCapWindow r))
      (metric.restrictOpen (standardCapWindow r)) j x
    rw [SmoothRiemannianMetric.restrictOpen_flat,
      SmoothRiemannianMetric.restrictOpen_flat, ← hFmetric] at heq
    exact heq.trans_lt hp
  refine ⟨hDr, F, hS.localPullback inc hi, hFmetric, hFzero, hFgram, ?_, Q, hQlife, ?_⟩
  · intro t ht x
    have hrm := hRm (standardCapWindow D) (F.base.metric t) Q t
      ⟨ht.1, ht.2.trans hTΘ⟩ x (fun j hj =>
        (hpoint t ht j (hj.trans (le_max_right _ _)) x).le.trans
          ((min_le_right _ _).trans (min_le_right _ _)))
    have hsq := (Real.sqrt_le_iff).mp hrm |>.2
    have hscalar := scalar_abs_le_rm (F.base.metric t) x
    change |F.scalar t x| ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
      Real.sqrt (normSq0S (F.base.metric t) x 4 (metricRm04 (F.base.metric t) x)) at hscalar
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by simp [ThreeSpace]; norm_num
    rw [hdim] at hscalar
    exact ⟨hsq, hscalar.trans (mul_le_mul_of_nonneg_left hrm (by norm_num))⟩
  · intro t ht
    constructor
    · intro j hj x
      exact (hpoint t ht j (hj.trans (le_max_left _ _)) x).trans_le
        ((min_le_left _ _).trans (half_le_self hε.le))
    · intro j hj x
      exact (hpoint t ht j (hj.trans (le_max_right _ _)) x).trans_le
        (((min_le_right _ _).trans (min_le_left _ _)).trans (half_le_self hη.le))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
