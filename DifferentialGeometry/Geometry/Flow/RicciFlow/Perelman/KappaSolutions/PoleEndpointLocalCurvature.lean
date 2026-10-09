import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem ancient_rmNormSq_le_on_backward_ball
    (U : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hU : IsAncientKappaSolution kappa U)
    (p q : U.M) {A r : ℝ} (hr : 0 ≤ r)
    (hbase : redLength U.S 0 p q 1 ≤ A)
    {t : ℝ} (ht : t ≤ -1) (x : U.M)
    (hdist : riemannianEDistOf (U.S.base.metric (-1)) q x ≤ ENNReal.ofReal r) :
    U.rmNormSq (I := I) t x ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2)) ^ 2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hscale : scaleMetric (1 : ℝ)⁻¹ (inv_pos.mpr zero_lt_one)
      (U.S.base.metric (-1)) = U.S.base.metric (-1) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [scaleMetric_inner, inv_one, one_mul]
  have hlength : redLength U.S 0 p x 1 ≤
      (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2 := by
    apply redLength_le_of_rescaled_distance_le U hU p q x zero_lt_one hr hbase
    simpa only [hscale] using hdist
  have hscalarOne : U.S.scalar (-1) x ≤ 3 * redLength U.S 0 p x 1 := by
    simpa only [div_one] using scalar_le_three_mul_redLength_div_of_ancient U hU p x zero_lt_one
  have htzero : t ≤ 0 := ht.trans (by norm_num)
  have hscalar : U.S.scalar t x ≤
      3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2 :=
    (hU.scalar_monotoneOn x htzero (by norm_num) ht).trans
      (hscalarOne.trans (mul_le_mul_of_nonneg_left hlength (by norm_num)))
  have htmem : t ∈ ancientTimeInterval.carrier := by
    simpa only [ancientTimeInterval_carrier, mem_Iic] using htzero
  have hroot : Real.sqrt (U.rmNormSq (I := I) t x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2) :=
    (hU.rmNorm_le_scalar t htmem x).trans
      (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))
  have hnonneg : 0 ≤ U.rmNormSq (I := I) t x := by
    simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
      normSq0S_nonneg (I := I) (U.S.base.metric t) x 4 (U.S.base.rm04 t x)
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (U.rmNormSq (I := I) t x))
    (by positivity : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      (3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2))).2 hroot
  rwa [Real.sq_sqrt hnonneg] at hsq

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

variable (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)

theorem poleEndpointRescaledFlowSeq_rmNormSq_le_of_redLength_le
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (p : F.M) {A r : ℝ} (hr : 0 ≤ r)
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A)
    (i : ℕ) {s : ℝ} (hs : s ≤ 0) (x : F.M)
    (hdist : riemannianEDistOf
      (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
      (q i) x ≤ ENNReal.ofReal r) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).rmNormSq
        (I := I) s x ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2)) ^ 2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U := (poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i
  have hdistU : riemannianEDistOf (U.S.base.metric (-1)) (q i) x ≤ ENNReal.ofReal r := by
    have hmetric :
        ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0 =
          U.S.base.metric (-1) := by
      exact (poleEndpointRescaledFlowSeq_metric_zero F hcar hreg b hbmem tau q hsigma i).trans
        (poleRescaledFlowSeq_metric_neg_one F hcar hreg b hbmem tau q hsigma i).symm
    have htransport := congrArg
      (fun g : SmoothRiemannianMetric I F.M =>
        riemannianEDistOf (I := I) (M := F.M) g (q i) x ≤ ENNReal.ofReal r) hmetric
    apply htransport.mp
    convert hdist using 1
    rfl
  have hbound := ancient_rmNormSq_le_on_backward_ball U (hancient i) p (q i) hr
    (hbase i) (by linarith only [hs] : s - 1 ≤ -1) x hdistU
  change normSq0S
      (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s)
      x 4
      (metricRm04At
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s) x)
      ≤ _
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
  exact hbound

theorem exists_poleEndpointRescaledFlowSeq_local_curvature_bound
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : ℕ, ∀ s ≤ (0 : ℝ), ∀ x : F.M,
      riemannianEDistOf
          (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
          (q i) x ≤ ENNReal.ofReal r →
        ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).rmNormSq
          (I := I) s x ≤ K := by
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 *
    (3 * (Real.sqrt A + Real.sqrt 3 / 2 * r) ^ 2)) ^ 2, sq_nonneg _, ?_⟩
  intro i s hs x hx
  exact poleEndpointRescaledFlowSeq_rmNormSq_le_of_redLength_le
    F hcar hreg b hbmem tau q hsigma kappa hancient p hr hbase i hs x hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
