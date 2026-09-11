import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CometricDifference
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Family.SmallC0

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

noncomputable def dirichletCometricDifferenceFormComplOnIcc
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta) :
    ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t => if ht : t ∈ Icc (0 : ℝ) T then
    dirichletCometricDifferenceFormCompl q (g t)
      hdelta_lt hdelta_nn (hdelta t ht)
  else 0

theorem dirichletCometricDifferenceFormComplOnIcc_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceFormComplOnIcc q g
        hdelta_lt hdelta_nn hdelta t
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletCometricDifferenceForm q (g t) u v := by
  rw [dirichletCometricDifferenceFormComplOnIcc, dif_pos ht,
    dirichletCometricDifferenceFormCompl_apply_smooth]

theorem norm_dirichletCometricDifferenceFormComplOnIcc_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta)
    (t : ℝ) :
    ‖dirichletCometricDifferenceFormComplOnIcc q g
      hdelta_lt hdelta_nn hdelta t‖ ≤ delta / (1 - delta) := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · rw [dirichletCometricDifferenceFormComplOnIcc, dif_pos ht]
    exact norm_dirichletCometricDifferenceFormCompl_le q (g t)
      hdelta_lt hdelta_nn (hdelta t ht)
  · rw [dirichletCometricDifferenceFormComplOnIcc, dif_neg ht, norm_zero]
    exact div_nonneg hdelta_nn (by linarith)

theorem dirichletCometricDifferenceFormComplOnIcc_aestronglyMeasurable
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    (q : SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (G.metric t).inner x - q.inner x) delta)
    (u v : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t => dirichletCometricDifferenceFormComplOnIcc q G.metric
        hdelta_lt hdelta_nn hdelta t u v) (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hraw := dirichletCometricDifferenceForm_time_cont
    hG q isCompact_Icc hreg u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (dirichletCometricDifferenceFormComplOnIcc_apply_smooth q G.metric
    hdelta_lt hdelta_nn hdelta ht u₀ v₀).symm

noncomputable def dirichletCometricDifferenceLaplacianOnIcc
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta) :
    ℝ → DirichletHs q 1 →L[ℝ] DirichletHs q (-1) :=
  fun t => dirichletBilinearFormToHs q
    (-dirichletCometricDifferenceFormComplOnIcc q g
      hdelta_lt hdelta_nn hdelta t)

theorem dirichletCometricDifferenceLaplacianOnIcc_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dirichletCometricDifferenceLaplacianOnIcc q g
        hdelta_lt hdelta_nn hdelta t =
      dirichletCometricDifferenceLaplacian q (g t)
        hdelta_lt hdelta_nn (hdelta t ht) := by
  unfold dirichletCometricDifferenceLaplacianOnIcc
  rw [dirichletCometricDifferenceFormComplOnIcc, dif_pos ht]
  unfold dirichletCometricDifferenceLaplacian
  congr

theorem norm_dirichletCometricDifferenceLaplacianOnIcc_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (g t).inner x - q.inner x) delta)
    (t : ℝ) :
    ‖dirichletCometricDifferenceLaplacianOnIcc q g
      hdelta_lt hdelta_nn hdelta t‖ ≤ delta / (1 - delta) := by
  calc
    ‖dirichletCometricDifferenceLaplacianOnIcc q g
        hdelta_lt hdelta_nn hdelta t‖ ≤
        ‖-dirichletCometricDifferenceFormComplOnIcc q g
          hdelta_lt hdelta_nn hdelta t‖ :=
      dirichletBilinearFormToHs_norm_le q
        (-dirichletCometricDifferenceFormComplOnIcc q g
          hdelta_lt hdelta_nn hdelta t)
    _ = ‖dirichletCometricDifferenceFormComplOnIcc q g
          hdelta_lt hdelta_nn hdelta t‖ := norm_neg _
    _ ≤ delta / (1 - delta) :=
      norm_dirichletCometricDifferenceFormComplOnIcc_le q g
        hdelta_lt hdelta_nn hdelta t

theorem dirichletCometricDifferenceLaplacianOnIcc_apply_aestronglyMeasurable
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    (q : SmoothRiemannianMetric (I_half n) M)
    {T delta : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (G.metric t).inner x - q.inner x) delta)
    (u : DirichletHs q 1) :
    AEStronglyMeasurable
      (fun t => dirichletCometricDifferenceLaplacianOnIcc q G.metric
        hdelta_lt hdelta_nn hdelta t u) (timeMeasure T) := by
  let B := dirichletCometricDifferenceFormComplOnIcc q G.metric
    hdelta_lt hdelta_nn hdelta
  let F : ℝ → H1ComplDirichlet q →L[ℝ] ℝ :=
    fun t => -(B t (dirichletHsOneEquivH1Compl q u))
  have hFapply (v : H1ComplDirichlet q) :
      AEStronglyMeasurable (fun t => F t v) (timeMeasure T) := by
    exact (dirichletCometricDifferenceFormComplOnIcc_aestronglyMeasurable
      hG q hreg hdelta_lt hdelta_nn hdelta
      (dirichletHsOneEquivH1Compl q u) v).neg
  have hrep := dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable
    F hFapply
  have hF : AEStronglyMeasurable F (timeMeasure T) := by
    have hdual := (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).continuous.comp_aestronglyMeasurable
      hrep
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hdual
  have hout := (dirichletHsNegOneEquivH1Dual q).symm.continuous.comp_aestronglyMeasurable hF
  change AEStronglyMeasurable
    (fun t => (dirichletHsNegOneEquivH1Dual q).symm
      (-(B t (dirichletHsOneEquivH1Compl q u)))) (timeMeasure T)
  exact hout

theorem exists_dirichletCometricDifferenceLaplacianOnIcc
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    (q : SmoothRiemannianMetric (I_half n) M)
    (hG0 : G.metric 0 = q) (h0reg : (0 : ℝ) ∈ D.regular)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ (T : ℝ)
      (A : ℝ → DirichletHs q 1 →L[ℝ] DirichletHs q (-1)),
      0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
        (∀ u, AEStronglyMeasurable (fun t => A t u) (timeMeasure T)) ∧
        (∀ t, ‖A t‖ ≤ eta) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ u v : SmoothScalarDirichlet q,
          dirichletHsNegOneEquivH1Dual q
              (A t ((dirichletHsOneEquivH1Compl q).symm
                (smoothToH1ComplDirichlet q u)))
              (smoothToH1ComplDirichlet q v) =
            -dirichletCometricDifferenceForm q (G.metric t) u v := by
  obtain ⟨a, b, h0ab, habreg⟩ := D.exists_Icc_regular h0reg
  have h0b : (0 : ℝ) < b := h0ab.2
  have hIco : Ico (0 : ℝ) b ⊆ D.regular := by
    intro t ht
    apply habreg
    constructor
    · linarith [h0ab.1, ht.1]
    · exact ht.2.le
  let delta : ℝ := eta / (1 + eta)
  have hden : 0 < 1 + eta := by linarith
  have hdelta_pos : 0 < delta := div_pos heta hden
  have hdelta_nn : 0 ≤ delta := hdelta_pos.le
  have hdelta_lt : delta < 1 := by
    dsimp only [delta]
    exact (div_lt_one hden).2 (by linarith)
  have hratio : delta / (1 - delta) = eta := by
    dsimp only [delta]
    field_simp
    ring
  obtain ⟨T, hT, hTb, hsmall⟩ := metricDifference_smallC0
    (I := I_half n) (M := M) G.metric q h0b
    (fun x₀ i j => hG.chartGramMatrix_continuousOn hIco x₀ i j)
    hG0 hdelta_pos
  have hreg : Icc (0 : ℝ) T ⊆ D.regular := by
    intro t ht
    exact hIco ⟨ht.1, lt_of_le_of_lt ht.2 (by simpa only [zero_add] using hTb)⟩
  have hmetric : ∀ t ∈ Icc (0 : ℝ) T,
      metricCauchySchwarzBound (I := I_half n) q
        (fun x => (G.metric t).inner x - q.inner x) delta := by
    intro t ht x v w
    simpa only [metricDifference_symVal, sub_apply] using
      hsmall t (by simpa only [zero_add] using ht) x v w
  let A : ℝ → DirichletHs q 1 →L[ℝ] DirichletHs q (-1) :=
    dirichletCometricDifferenceLaplacianOnIcc q G.metric
      hdelta_lt hdelta_nn hmetric
  refine ⟨T, A, hT, hreg, ?_, ?_, ?_⟩
  · intro u
    exact dirichletCometricDifferenceLaplacianOnIcc_apply_aestronglyMeasurable
      hG q hreg hdelta_lt hdelta_nn hmetric u
  · intro t
    rw [← hratio]
    exact norm_dirichletCometricDifferenceLaplacianOnIcc_le q G.metric
      hdelta_lt hdelta_nn hmetric t
  · intro t ht u v
    rw [show A t = dirichletCometricDifferenceLaplacian q (G.metric t)
      hdelta_lt hdelta_nn (hmetric t ht) from
        dirichletCometricDifferenceLaplacianOnIcc_eq q G.metric
          hdelta_lt hdelta_nn hmetric ht]
    rw [dirichletHsNegOneEquivH1Dual_cometricDifferenceLaplacian,
      LinearIsometryEquiv.apply_symm_apply]
    change -(dirichletCometricDifferenceFormCompl q (G.metric t)
      hdelta_lt hdelta_nn (hmetric t ht)
      (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v)) = _
    rw [dirichletCometricDifferenceFormCompl_apply_smooth]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
