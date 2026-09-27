import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ReferenceCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionNorm
import DifferentialGeometry.Tensor.Metric.ScaleNorm
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse
import DifferentialGeometry.Tensor.Metric.IsometryNorm
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Tensor DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

theorem exists_normalizedDatum_insertedMetric_cap_derivative_bounds :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ (A : ℝ) (hA : 0 < A) (m : ℕ),
      ∃ δ₀ > 0, δ₀ < 1 / 2 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, m + 2 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
              (q : insertionBall δ⁻¹), ‖(q : E3)‖ ≤ transitionEnd →
              let G := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
              (∀ j ≤ m, Real.sqrt (normSq0S G q (4 + j) (iterCov G 4 (metricRm04 G) j q)) ≤ C j) ∧
                |metricScalarAt G q| ≤ C 0 := by
  choose K hK hKb using fun j : ℕ =>
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens
      j (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  let C : ℕ → ℝ := fun j => 1 + 9 * K j
  have hC (j : ℕ) : 0 < C j := by dsimp only [C]; linarith [hK j]
  refine ⟨C, hC, ?_⟩
  intro A hA m
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := exists_normalizedDatum_insertedMetric_ball_error_lt
    A hA 0 le_rfl (m + 2) (1 / 2) (by norm_num)
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, _hfit, herror⟩ := hmod δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d q hq
  dsimp only
  let G := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  let G₀ := metric.restrictOpen (insertionBall δ⁻¹)
  have he := herror k hmk g x₀ d
  have hq' : q ∈ {q : insertionBall δ⁻¹ | ‖(q : E3)‖ ≤ transitionEnd + 0} := by simpa using hq
  have hj (s : ℕ) (hs : s ≤ m + 2) : metricDerivNorm s G G₀ G₀ q ≤ 1 / 2 :=
    (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he hs hq').le
  have hl (v : TangentSpace (𝓡 3) q) : (1 / 2 : ℝ) * G₀.inner q v v ≤ G.inner q v v := by
    have h := (inner_bounds_of_metricDerivNorm_le G₀ G q (hj 0 (by omega)) v).1
    norm_num at h ⊢
    exact h
  have hraw (j : ℕ) (hjm : j ≤ m) :
      Real.sqrt (normSq0S G q (4 + j) (iterCov G 4 (metricRm04 G) j q)) ≤ K j :=
    hKb j (insertionBall δ⁻¹) G q hl (fun s hs => hj s (by omega))
  constructor
  · intro j hjm
    exact (hraw j hjm).trans (by dsimp only [C]; linarith [hK j])
  · have hs : |metricScalarAt G q| ≤
        9 * Real.sqrt (normSq0S G q 4 (metricRm04 G q)) := by
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) q) = 3 := by
        change Module.finrank ℝ E3 = 3
        simp
      change |metricScalarAt G q| ≤ 9 * Real.sqrt (normSq0S G q 4 (metricRm04At G q))
      simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using scalar_abs_le_rm G q
    have hb := hraw 0 (Nat.zero_le _)
    change Real.sqrt (normSq0S G q 4 (metricRm04 G q)) ≤ K 0 at hb
    change |metricScalarAt G q| ≤ 1 + 9 * K 0
    linarith only [hs, hb]

private theorem inverse_scale_curvature_norm (U : Opens E3)
    (G : SmoothRiemannianMetric (𝓡 3) U) (Q : ℝ) (hQ : 0 < Q) (j : ℕ) (q : U) :
    Real.sqrt (normSq0S (scaleMetric Q⁻¹ (inv_pos.mpr hQ) G) q (4 + j)
      (iterCov (scaleMetric Q⁻¹ (inv_pos.mpr hQ) G) 4
        (metricRm04 (scaleMetric Q⁻¹ (inv_pos.mpr hQ) G)) j q)) =
      Q ^ (1 + (j : ℝ) / 2) * Real.sqrt (normSq0S G q (4 + j) (iterCov G 4 (metricRm04 G) j q)) := by
  have h := sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq G (Real.sqrt Q)⁻¹
    (inv_pos.mpr (Real.sqrt_pos.mpr hQ)) j q
  have hscale : ((Real.sqrt Q)⁻¹) ^ 2 = Q⁻¹ := by rw [inv_pow, Real.sq_sqrt hQ.le]
  have hpow : (Real.sqrt Q) ^ (2 + j) = Q ^ (1 + (j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hQ.le]
    congr 1
    push_cast
    ring
  have hg : scaleMetric ((Real.sqrt Q)⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hQ))) G =
      scaleMetric Q⁻¹ (inv_pos.mpr hQ) G := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, hscale]
  rw [hg, inv_inv, hpow] at h
  exact h

theorem exists_normalizedDatum_physicalInsertedMetric_cap_derivative_bounds :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ (A : ℝ) (hA : 0 < A) (m : ℕ),
      ∃ δ₀ > 0, δ₀ < 1 / 2 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, m + 2 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
              (q : insertionBall δ⁻¹), ‖(q : E3)‖ ≤ transitionEnd →
              let Q := metricScalarAt g x₀
              let G := scaleMetric Q⁻¹ (inv_pos.mpr d.scalar_pos)
                (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
              (∀ j ≤ m, Real.sqrt (normSq0S G q (4 + j) (iterCov G 4 (metricRm04 G) j q)) ≤
                C j * Q ^ (1 + (j : ℝ) / 2)) ∧ |metricScalarAt G q| ≤ C 0 * Q := by
  obtain ⟨C, hC, hb⟩ := exists_normalizedDatum_insertedMetric_cap_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro A hA m
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := hb A hA m
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hbound⟩ := hmod δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d q hq
  obtain ⟨hj, hs⟩ := hbound k hmk g x₀ d q hq
  dsimp only
  constructor
  · intro j hjm
    rw [inverse_scale_curvature_norm (insertionBall δ⁻¹) _ _ d.scalar_pos]
    exact (mul_le_mul_of_nonneg_left (hj j hjm) (Real.rpow_pos_of_pos d.scalar_pos _).le).trans_eq (mul_comm _ _)
  · rw [metricScalarAt_scaleMetric, inv_inv, abs_mul, abs_of_pos d.scalar_pos]
    exact (mul_le_mul_of_nonneg_left hs d.scalar_pos.le).trans_eq (mul_comm _ _)

section Isometry
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N] [T2Space N]

private theorem actual_isometry_curvature_jets
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (D : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N)
    (hmetric : ∀ (y : M) (v w : TangentSpace (𝓡 3) y),
      g.inner y v w = h.inner (D y) (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y w))
    (j : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) =
      Real.sqrt (normSq0S h (D x) (4 + j) (iterCov h 4 (metricRm04 h) j (D x))) ∧
      metricScalarAt g x = metricScalarAt h (D x) := by
  have hg : g = Diffeomorph.pullbackMetric h D := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact hmetric y v w
  have hRm (y : M) (w : Fin 4 → TangentSpace (𝓡 3) y) :
      metricRm04 g y w = metricRm04 h (D y) (fun i => mfderiv (𝓡 3) (𝓡 3) D y (w i)) := by
    rw [hg]
    have hc := metricRm04Standard_pullback h D y (w 0) (w 1) (w 2) (w 3)
    have hw : vec4 (w 0) (w 1) (w 2) (w 3) = w := by
      funext i
      fin_cases i <;> rfl
    have hdw : vec4 (mfderiv (𝓡 3) (𝓡 3) D y (w 0)) (mfderiv (𝓡 3) (𝓡 3) D y (w 1))
        (mfderiv (𝓡 3) (𝓡 3) D y (w 2)) (mfderiv (𝓡 3) (𝓡 3) D y (w 3)) =
        (fun i => mfderiv (𝓡 3) (𝓡 3) D y (w i)) := by
      funext i
      fin_cases i <;> rfl
    change metricRm04 (Diffeomorph.pullbackMetric h D) y (vec4 (w 0) (w 1) (w 2) (w 3)) =
      metricRm04 h (D y) (vec4 (mfderiv (𝓡 3) (𝓡 3) D y (w 0)) (mfderiv (𝓡 3) (𝓡 3) D y (w 1))
        (mfderiv (𝓡 3) (𝓡 3) D y (w 2)) (mfderiv (𝓡 3) (𝓡 3) D y (w 3))) at hc
    rw [hw, hdw] at hc
    exact hc
  have hjet := iter_cov_of_metric_isometry g h D hmetric (metricRm04 g) (metricRm04 h) hRm j x
  have hn := normSq0S_of_metric_isometry g h D hmetric (4 + j) x _ _ hjet
  refine ⟨congrArg Real.sqrt hn, ?_⟩
  rw [hg]
  exact metricScalarAt_pullback h D x
end Isometry

open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

theorem exists_normalizedDatum_positiveSideInsertionMetric_cap_derivative_bounds :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ (A : ℝ) (hA : 0 < A) (m : ℕ),
      ∃ δ₀ > 0, δ₀ < 1 / 2 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, m + 2 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
              let hB := inv_pos.mpr d.precision_pos
              letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
              ∀ q : InsertionQuotient hB,
                q ∈ range (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) →
                let Q := metricScalarAt g x₀
                let G := d.positiveSideInsertionMetric hA hAB
                (∀ j ≤ m, Real.sqrt (normSq0S G q (4 + j) (iterCov G 4 (metricRm04 G) j q)) ≤
                  C j * Q ^ (1 + (j : ℝ) / 2)) ∧ |metricScalarAt G q| ≤ C 0 * Q := by
  obtain ⟨C, hC, hb⟩ := exists_normalizedDatum_physicalInsertedMetric_cap_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro A hA m
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := hb A hA m
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hbound⟩ := hmod δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  dsimp only
  intro q hq
  let D : InsertionQuotient (inv_pos.mpr d.precision_pos) ≃ₘ⟮𝓡 3, 𝓡 3⟯ insertionBall δ⁻¹ :=
    radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)
  have hx : ‖(D q : E3)‖ ≤ transitionEnd := by
    obtain ⟨x, rfl⟩ := hq
    rw [show (D (adjunctionCell (radialCapBoundary transitionEnd_pos)
      (retainedBoundary (inv_pos.mpr d.precision_pos)) x) : E3) = x.val from
        radialCapAttachmentHomeomorph_cap transitionEnd_pos (inv_pos.mpr d.precision_pos) x]
    exact x.property
  obtain ⟨hj, hs⟩ := hbound k hmk g x₀ d (D q) hx
  let out := d.positiveSideCollapseMetric hA hAB
  have hmetric (y : InsertionQuotient (inv_pos.mpr d.precision_pos))
      (v w : TangentSpace (𝓡 3) y) :
      (d.positiveSideInsertionMetric hA hAB).inner y v w =
        out.inner (D y) (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y w) := by
    rw [d.positiveSideInsertionMetric_eq_pullback_collapseMetric]
    erw [Diffeomorph.pullbackMetricCross_inner]
  constructor
  · intro j hjm
    have hn := actual_isometry_curvature_jets (d.positiveSideInsertionMetric hA hAB) out D hmetric j q
    exact hn.1.le.trans (hj j hjm)
  · have hn := actual_isometry_curvature_jets (d.positiveSideInsertionMetric hA hAB) out D hmetric 0 q
    exact (congrArg abs hn.2).le.trans hs

end DifferentialGeometry.PDE.RicciFlow.StandardCap
