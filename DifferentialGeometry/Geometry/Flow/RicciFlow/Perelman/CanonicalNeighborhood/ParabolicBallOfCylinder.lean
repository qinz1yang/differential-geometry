import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_isParabolicallyRmControlled_of_isSpatiallyRmControlled_at_base
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
          ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
            ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
              ∀ (time : (X.interval i).FlowTime), (time : ℝ) = 0 →
              ∀ B : FlowMetricBall (X.term i).S time, B.radius ≤ 1 →
                B.IsSpatiallyRmControlled →
              ∀ B' : FlowMetricBall (X.term i).S time, B'.center = B.center →
                B'.radius ≤ lam * B.radius → B'.IsParabolicallyRmControlled := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hcyl⟩ := exists_local_curvature_cylinder_at_scale hmod
  refine ⟨epsStar, hepsStar, fun Phi hPhi => ?_⟩
  set A : ℝ := C * (3 + 13 * Phi 1) with hA
  have hPhi1 : 0 < Phi 1 := hPhi.pos 1
  have hApos : 0 < A := mul_pos hC (by linarith)
  set lam : ℝ := min 1 (min (c / 14) (2 / (9 * A)))
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamc : lam ≤ c / 14 := (min_le_right _ _).trans (min_le_left _ _)
  have hlamA : lam ≤ 2 / (9 * A) := (min_le_right _ _).trans (min_le_right _ _)
  have hlampos : 0 < lam := lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨lam, hlampos, hlam1, fun eps heps hepsle sigma hsigma X => ?_⟩
  filter_upwards [hcyl eps heps hepsle sigma hsigma Phi hPhi X] with i hi
  intro time htime B hr1 hB B' hcenter hradius
  set r : ℝ := B.radius
  set z : (X.term i).M := B.center
  have hr : 0 < r := B.radius_pos
  have hr' : 0 < B'.radius := B'.radius_pos
  set Q : ℝ := 9 / (2 * r ^ 2) with hQ
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2le : r ^ 2 ≤ 1 := by nlinarith
  have hQ1 : 1 ≤ Q := by
    rw [hQ, le_div_iff₀ (by positivity)]
    linarith
  have hQpos : 0 < Q := by linarith
  have hzB : z ∈ B.set := by
    change riemannianEDistOf ((X.term i).S.base.metric time) B.center B.center <
      ENNReal.ofReal B.radius
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hrmz := hB z hzB
  have hnnz := normSq0S_nonneg ((X.term i).S.base.metric time) z 4
    ((X.term i).S.base.rm04 time z)
  have hρ : FlowMetricBall.rmNormSq (X.term i).S time z ≤ (1 / r ^ 2) ^ 2 := by
    have e : (1 / r ^ 2) ^ 2 = 1 / r ^ 4 := by ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have hsqrtz : Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S time z) ≤ 1 / r ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hρ⟩
  have hscalarz : |(X.term i).S.scalar 0 z| ≤ 2 * Q := by
    have habs := scalar_abs_le_rm (I := I3) ((X.term i).S.base.metric time) z
    have hdimx : Module.finrank ℝ (TangentSpace I3 z) = 3 := by
      change Module.finrank ℝ ThreeSpace = 3
      simp [ThreeSpace]
    rw [hdimx] at habs
    change |(X.term i).S.scalar time z| ≤ ((3 : ℕ) : ℝ) ^ 2 *
      Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S time z) at habs
    rw [htime] at habs
    have h9 : ((3 : ℕ) : ℝ) ^ 2 = 9 := by norm_num
    rw [h9] at habs
    have h2Q : 2 * Q = 9 * (1 / r ^ 2) := by
      rw [hQ]
      field_simp
    rw [h2Q]
    rw [htime] at hsqrtz
    exact habs.trans (mul_le_mul_of_nonneg_left hsqrtz (by norm_num))
  obtain ⟨hwin, hcurv⟩ := hi Q hQ1 z hscalarz
  have hB'r : B'.radius ≤ c / 14 * r :=
    hradius.trans (mul_le_mul_of_nonneg_right hlamc hr.le)
  have hB'sq : B'.radius ^ 2 ≤ c / (3 * Q) := by
    have h1 : B'.radius ^ 2 ≤ (lam * r) ^ 2 := pow_le_pow_left₀ hr'.le hradius 2
    have h2 : lam ^ 2 ≤ lam := by nlinarith
    have h3 : c / (3 * Q) = 2 * c / 27 * r ^ 2 := by
      rw [hQ]
      field_simp
      ring
    rw [h3]
    nlinarith
  have hwindow : Icc ((time : ℝ) - B'.radius ^ 2) time ⊆ Icc (-(c / (3 * Q))) 0 := by
    intro s hs
    rw [htime] at hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hball : B'.set ⊆ riemannianClosedBallOf ((X.term i).S.base.metric 0) z
      (c / Real.sqrt (3 * Q)) := by
    intro x hx
    have hsq : Real.sqrt (3 * Q) ≤ 14 / r := by
      rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ hr2, hQ]
      field_simp
      norm_num
    have hle : c / 14 * r ≤ c / Real.sqrt (3 * Q) := by
      calc c / 14 * r = c / (14 / r) := by field_simp
        _ ≤ c / Real.sqrt (3 * Q) :=
          div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr (by positivity)) hsq
    change riemannianEDistOf ((X.term i).S.base.metric time) B'.center x <
      ENNReal.ofReal B'.radius at hx
    rw [hcenter, htime] at hx
    exact hx.le.trans (ENNReal.ofReal_le_ofReal (hB'r.trans hle))
  refine ⟨fun s hs => hwin (hwindow hs), fun s hs x hx => ?_⟩
  have hbound := (hcurv x s (hwindow hs) (hball hx)).2
  have hnn := normSq0S_nonneg ((X.term i).S.base.metric s) x 4 ((X.term i).S.base.rm04 s x)
  have hrm : FlowMetricBall.rmNormSq (X.term i).S s x ≤ (A * Q) ^ 2 := by
    have h := (Real.sqrt_le_left (by positivity)).mp hbound
    simpa only [hA, mul_assoc] using h
  have hpow : B'.radius ^ 4 ≤ (lam * r) ^ 4 := pow_le_pow_left₀ hr'.le hradius 4
  have hlam4 : lam ^ 4 * A ^ 2 * 81 / 4 ≤ 1 := by
    have h1 : lam * A ≤ 2 / 9 := by
      have h := mul_le_mul_of_nonneg_right hlamA hApos.le
      have e : 2 / (9 * A) * A = 2 / 9 := by field_simp
      linarith
    have h2 : lam ^ 2 ≤ 1 := pow_le_one₀ hlampos.le hlam1
    have h3 : (lam * A) ^ 2 ≤ (2 / 9) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    calc lam ^ 4 * A ^ 2 * 81 / 4 = (lam * A) ^ 2 * lam ^ 2 * (81 / 4) := by ring
      _ ≤ (2 / 9) ^ 2 * 1 * (81 / 4) := by gcongr
      _ = 1 := by norm_num
  have hval : (lam * r) ^ 4 * (A * Q) ^ 2 = lam ^ 4 * A ^ 2 * 81 / 4 := by
    rw [hQ]
    field_simp
    ring
  calc B'.radius ^ 4 * FlowMetricBall.rmNormSq (X.term i).S s x
      ≤ (lam * r) ^ 4 * (A * Q) ^ 2 :=
        mul_le_mul hpow hrm hnn (by positivity)
    _ ≤ 1 := by rw [hval]; exact hlam4

section Restriction

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance parabolicRestrictionC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

open _root_.MeasureTheory in
theorem parabolicallyKappaNoncollapsedBelowScale_restrictOpen_of_isClosed
    {S : SolutionOn (I := I3) (M := M) D}
    {kappa rho : ℝ} (h : ParabolicallyKappaNoncollapsedBelowScale S kappa rho)
    (U : TopologicalSpace.Opens M) (hU : IsClosed (U : Set M)) [SigmaCompactSpace U] :
    ParabolicallyKappaNoncollapsedBelowScale (solutionOnRestrictOpen S U) kappa rho := by
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  refine ⟨h.1, ?_⟩
  intro t B hr hRm
  let B' : FlowMetricBall S t := ⟨B.center.val, B.radius, B.radius_pos⟩
  have hset : B'.set = (Subtype.val : U → M) '' B.set :=
    riemannianBallOf_eq_image_restrictOpen_of_isClosed (S.base.metric t) U hU B.center B.radius
  have hpre : B.set = (Subtype.val : U → M) ⁻¹' B'.set := by
    rw [hset, preimage_image_eq _ Subtype.val_injective]
  have hsubset : B'.set ⊆ U := by
    rw [hset]
    rintro y ⟨x, _, rfl⟩
    exact x.property
  have hnorm : ∀ (s : ℝ) (x : U), FlowMetricBall.rmNormSq (solutionOnRestrictOpen S U) s x =
      FlowMetricBall.rmNormSq S s x.val := by
    intro s x
    have hsec : metricRm04 (I := I3) (M := U) ((S.base.metric s).restrictOpen U) x =
        metricRm04 (I := I3) (M := M) (S.base.metric s) x.val := by
      ext slots
      have heq := metricRm04_restrictOpen_eval (I := I3) (S.base.metric s) U x slots
      simp only [mfderiv_subtype_val_apply] at heq
      exact heq
    change normSq0S ((S.base.metric s).restrictOpen U) x 4
        (metricRm04 ((S.base.metric s).restrictOpen U) x) =
      normSq0S (S.base.metric s) x.val 4 (metricRm04 (S.base.metric s) x.val)
    rw [normSq0S_restrictOpen_apply, hsec]
  have hRm' : B'.IsParabolicallyRmControlled := by
    refine ⟨hRm.1, fun s hs y hy => ?_⟩
    rw [hset] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hnorm s x]
    exact hRm.2 s hs x hx
  have hvol : B.volume = B'.volume := by
    have hmeas : MeasurableSet B'.set := by
      have hd : Continuous (fun y : M ↦
          riemannianEDistOf (S.base.metric t) B'.center y) := by
        simpa only [riemannianEDistOf] using
          Geometry.Riemannian.continuous_riemannianEDist (S.base.metric t) B'.center
      exact (isOpen_lt hd continuous_const).measurableSet
    change DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I3) (M := U)
        ((S.base.metric t).restrictOpen U) B.set =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I3) (M := M)
        (S.base.metric t) B'.set
    rw [hpre]
    exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      (S.base.metric t) U hmeas hsubset
  have hnc := h.2 t B' hr hRm'
  exact ⟨hnc.1, hvol ▸ hnc.2⟩

end Restriction

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
