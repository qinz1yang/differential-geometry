import DifferentialGeometry.Analysis.ODE.Gronwall.SecondOrder
import DifferentialGeometry.Geometry.Comparison.Volume.Intrinsic.Gronwall
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem intrinsicRm04Bound_of_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {R K : ℝ}
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    {z : E} (hz : ‖z‖ < R) :
    IntrinsicRm04Bound (I := I) g hEnorm p (normalFrame (I := I) g p z) K := by
  intro t ht
  apply hRm
  have hdist := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
    (normalFrame (I := I) g p z) (s := 0) (t := t) ht.1
  have hbound : riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p
        (normalFrame (I := I) g p z) t) ≤ ENNReal.ofReal (‖z‖ * t) := by
    simpa only [intrinsicGeodesic_zero, normalFrame_sqrt, sub_zero] using hdist
  have htlen : ‖z‖ * t ≤ ‖z‖ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2.le (norm_nonneg z)
  exact (hbound.trans (ENNReal.ofReal_le_ofReal htlen)).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).2 hz)

private lemma local_quarter_models {A s : ℝ} (hs : 0 ≤ s)
    (herr : gronwallBound 0 (max A 1) A 1 ≤ 1 / 4) :
    s + gronwallBound 0 (max A 1) (A * s) 1 ≤ (5 / 4) * s ∧
      (3 / 4) * s ≤ s - gronwallBound 0 (max A 1) (A * s) 1 := by
  have hscale : gronwallBound 0 (max A 1) (A * s) 1 =
      s * gronwallBound 0 (max A 1) A 1 := by
    rw [mul_comm A s, gronwallBound_zero_mul_eps]
  have hmul := mul_le_mul_of_nonneg_left herr hs
  rw [hscale]
  constructor <;> nlinarith

theorem intrinsicFrameMetric_bounds_of_local_curvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {R K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    {z : E} (hz : ‖z‖ < R)
    (herr : gronwallBound 0
      (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * ‖z‖ ^ 2) 1)
      (Real.sqrt (Module.finrank ℝ E : ℝ) * K * ‖z‖ ^ 2) 1 ≤ 1 / 4)
    (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
      intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ 2 * ‖v‖ ^ 2 := by
  let u : TangentSpace I p := normalFrame (I := I) g p z
  let w : TangentSpace I p := normalFrame (I := I) g p v
  let A : ℝ := Real.sqrt (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) *
    K * g.inner p u u
  have hA : 0 ≤ A := by
    dsimp only [A, u]
    rw [normalFrame_normSq]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) (sq_nonneg _)
  have herror : gronwallBound 0 (max A 1) A 1 ≤ 1 / 4 := by
    simpa only [A, u, normalFrame_normSq, Fintype.card_fin] using herr
  obtain ⟨hmodelLe, hmodelGe⟩ :=
    local_quarter_models (s := ‖v‖) (norm_nonneg _) herror
  have hODE := intrinsicJacobi_ode (I := I) g hEnorm p u w hK
    (intrinsicRm04Bound_of_ball (I := I) g hEnorm p hRm hz)
  obtain ⟨hupper, hlower⟩ := intrinsicJacobi_bounds (I := I) g hEnorm p u w
    hA zero_lt_one (by simpa only [A] using hODE)
  have hupper1 := hupper 1 (by norm_num)
  have hlower1 := hlower 1 (by norm_num)
  have hwNorm : Real.sqrt (g.inner p w w) = ‖v‖ := by
    simpa only [w] using normalFrame_sqrt (I := I) g p v
  simp only [one_mul, hwNorm] at hupper1 hlower1
  let q : M := intrinsicGeodesic (I := I) g hEnorm p u 1
  let J : TangentSpace I q := intrinsicJacobi (I := I) g hEnorm p u w 1
  have hsqrtUpper : Real.sqrt (g.inner q J J) ≤ (5 / 4 : ℝ) * ‖v‖ :=
    hupper1.trans hmodelLe
  have hsqrtLower : (3 / 4 : ℝ) * ‖v‖ ≤ Real.sqrt (g.inner q J J) :=
    hmodelGe.trans hlower1
  have hmetricNonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · simp [hJ]
    · exact (g.pos q J hJ).le
  have hlowerSq : ((3 / 4 : ℝ) * ‖v‖) ^ 2 ≤
      (Real.sqrt (g.inner q J J)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) (norm_nonneg v))
      (Real.sqrt_nonneg _)).2 hsqrtLower
  have hupperSq : (Real.sqrt (g.inner q J J)) ^ 2 ≤
      ((5 / 4 : ℝ) * ‖v‖) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg v))).2 hsqrtUpper
  rw [Real.sq_sqrt hmetricNonneg] at hlowerSq hupperSq
  have hmetric : intrinsicFrameMetric (I := I) g hEnorm p z v v = g.inner q J J := by
    rw [intrinsic_metric_jacobi (I := I) g hEnorm p z v v]
    dsimp only [q, J, u, w, intrinsicFramedExp, expMapIntrinsic]
    rw [intrinsicFrameCLM_apply]
    rfl
  rw [hmetric]
  constructor <;> nlinarith [sq_nonneg ‖v‖]

private lemma local_exists_pos_mul_sq_le {S κ : ℝ} (hκ : 0 < κ) :
    ∃ r : ℝ, 0 < r ∧ S * r ^ 2 ≤ κ := by
  let T : ℝ := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  have hdiv : 0 < κ / T := div_pos hκ hT
  refine ⟨Real.sqrt (κ / T), Real.sqrt_pos.mpr hdiv, ?_⟩
  calc
    S * Real.sqrt (κ / T) ^ 2 ≤ T * Real.sqrt (κ / T) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left S 1) (sq_nonneg _)
    _ = T * (κ / T) := by rw [Real.sq_sqrt hdiv.le]
    _ = κ := by field_simp [hT.ne']

theorem exists_uniform_local_jacobi_scale (n : ℕ) {R K : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∀ s : ℝ, 0 ≤ s → s ≤ r →
      gronwallBound 0 (max (Real.sqrt (n : ℝ) * K * s ^ 2) 1)
        (Real.sqrt (n : ℝ) * K * s ^ 2) 1 ≤ 1 / 4 := by
  obtain ⟨κ, buffer, hκ, hbuffer, hsmall⟩ :=
    exists_gron_smallK (B₀ := (1 / 4 : ℝ)) (D := 1) (by norm_num) (by norm_num)
  let S : ℝ := Real.sqrt (n : ℝ) * K
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) hK
  obtain ⟨r₀, hr₀, hcap⟩ := local_exists_pos_mul_sq_le (S := S) hκ
  refine ⟨min R r₀, lt_min hR hr₀, min_le_left _ _, ?_⟩
  intro s hs hsr
  have hsq : s ^ 2 ≤ r₀ ^ 2 :=
    (sq_le_sq₀ hs hr₀.le).2 (hsr.trans (min_le_right _ _))
  have hnonneg : 0 ≤ S * s ^ 2 := mul_nonneg hS (sq_nonneg _)
  have hle : S * s ^ 2 ≤ κ := (mul_le_mul_of_nonneg_left hsq hS).trans hcap
  have hsmallz := hsmall hnonneg hle
  simp only [mul_one] at hsmallz
  change gronwallBound 0 (max (S * s ^ 2) 1) (S * s ^ 2) 1 ≤ 1 / 4
  linarith

theorem intrinsicFrame_localOn_of_local_curvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {R K r : ℝ} (hK : 0 ≤ K) (hrR : r ≤ R)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    (herror : ∀ s : ℝ, 0 ≤ s → s ≤ r →
      gronwallBound 0 (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * s ^ 2) 1)
        (Real.sqrt (Module.finrank ℝ E : ℝ) * K * s ^ 2) 1 ≤ 1 / 4) :
    IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) (Metric.ball (0 : E) r) := by
  apply intrinsicFrame_localOn (I := I) g hEnorm p
  intro z hz
  have hzr : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hmetric := intrinsicFrameMetric_bounds_of_local_curvature (I := I) g hEnorm p
    hK hRm (hzr.trans_le hrR) (herror ‖z‖ (norm_nonneg _) hzr.le)
  exact branch_of_not_conj (I := I) g hEnorm
    (intrinsicFrame_not_conj (I := I) g hEnorm p z (by norm_num : (0 : ℝ) < 1 / 2)
      (fun v => (hmetric v).1))

theorem exists_uniform_local_intrFrame_control
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∀ p : M,
      (∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04At (I := I) g y)) ≤ K) →
      (∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
        (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
          intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ Metric.ball (0 : E) r,
        ¬ IsConjVec (I := I) g hEnorm p (normalFrame (I := I) g p z : E)) ∧
      (∀ z ∈ Metric.ball (0 : E) r, ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
        (normalFrame (I := I) g p z : E) ∈ B.hom.source) ∧
      IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p) (Metric.ball (0 : E) r) := by
  obtain ⟨r, hr, hrR, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hR hK
  refine ⟨r, hr, hrR, ?_⟩
  intro p hRm
  have hmetric : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
        intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro z hz v
    have hzr : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact intrinsicFrameMetric_bounds_of_local_curvature (I := I) g hEnorm p
      hK hRm (hzr.trans_le hrR) (herror ‖z‖ (norm_nonneg _) hzr.le) v
  have hnot : ∀ z ∈ Metric.ball (0 : E) r,
      ¬ IsConjVec (I := I) g hEnorm p (normalFrame (I := I) g p z : E) := by
    intro z hz
    exact intrinsicFrame_not_conj (I := I) g hEnorm p z (by norm_num : (0 : ℝ) < 1 / 2)
      (fun v => (hmetric z hz v).1)
  have hbranches : ∀ z ∈ Metric.ball (0 : E) r,
      ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
        (normalFrame (I := I) g p z : E) ∈ B.hom.source := by
    intro z hz
    exact branch_of_not_conj (I := I) g hEnorm (hnot z hz)
  exact ⟨hmetric, hnot, hbranches,
    intrinsicFrame_localOn (I := I) g hEnorm p (Metric.ball (0 : E) r) hbranches⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
