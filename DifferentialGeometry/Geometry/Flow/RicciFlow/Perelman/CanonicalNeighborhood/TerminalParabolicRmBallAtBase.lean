import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_eventually_curvDerivNormSq_le_at_boundedDistance {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ t ∈ Set.Icc (-(c / 2)) 0, ∀ y : (X.term i).M,
              metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
                ≤ c / Real.sqrt 2 →
              curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ := local_propagation_of_modelBound hmod
  refine ⟨epsStar, c, (3 * C) ^ 2, hepsStar, hc, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  have hscal : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1 := by
    intro i
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar]
      using X.base_one i
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.pinching_error_eventually hPhi (L0 := 2) (eta := 1) one_pos] with i hcyl hpinch
  intro t ht y hy
  have hL : 1 + |(X.term i).S.scalar 0 (X.term i).basepoint| = 2 := by rw [hscal i]; norm_num
  have hmem : (y, t) ∈ frozenBackwardCylinder (X.term i).S (X.term i).basepoint 0 c c
      (1 + |(X.term i).S.scalar 0 (X.term i).basepoint|) := by
    have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact (ENNReal.le_ofReal_iff_toReal_le
        (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0)
          (X.term i).basepoint y) (by positivity)).mpr hy
    · rw [hL]
      exact ⟨by linarith [ht.1, hc], ht.2⟩
  have hs : (0 : ℝ) ∈ Set.Icc (-(X.depth i / 2)) 0 :=
    ⟨by linarith [X.depth_pos i], le_rfl⟩
  obtain ⟨-, hrm⟩ := hcyl 0 hs (X.term i).basepoint
  have hbound := hrm y t hmem
  have heta : (Phi (4 * X.scale i * 2) + Phi 0) / X.scale i < 1 :=
    hpinch 2 ⟨by norm_num, le_rfl⟩
  have hrmle : Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t y) ≤ 3 * C := by
    refine le_trans hbound.2.2 ?_
    rw [hL]
    nlinarith [hC.le, heta]
  have hbridge : FlowMetricBall.rmNormSq (X.term i).S t y =
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y := rfl
  rw [hbridge] at hrmle
  have h3 : Real.sqrt ((3 * C) ^ 2) = 3 * C := Real.sqrt_sq (by positivity)
  exact (Real.sqrt_le_sqrt_iff (by positivity : (0 : ℝ) ≤ (3 * C) ^ 2)).mp (by rw [h3]; exact hrmle)

theorem exists_eventually_scalar_le_at_boundedDistance {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar r C : ℝ, 0 < epsStar ∧ 0 < r ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ y : (X.term i).M,
              metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ r →
              (X.term i).S.scalar 0 y ≤ C := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_eventually_curvDerivNormSq_le_at_boundedDistance hmod
  refine ⟨epsStar, c / Real.sqrt 2,
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C, hepsStar, by positivity, ?_, ?_⟩
  · have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    positivity
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X] with i hb
  intro y hy
  have h0 : curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric 0) y ≤ C :=
    hb 0 ⟨by linarith [hc], le_rfl⟩ y hy
  have hzero : curvCovDeriv (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) 0 =
      metricRm04 (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) := rfl
  have hrm : normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ C := by
    rw [curvDerivNormSq, hzero, metricRm04_apply] at h0
    exact h0
  have hsq : Real.sqrt (normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)) ≤ Real.sqrt C :=
    Real.sqrt_le_sqrt hrm
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I3)
    (M := (X.term i).M) ((X.term i).S.base.metric 0) y
  rw [hdim] at hscal
  exact le_trans (le_abs_self _) (le_trans hscal
    (mul_le_mul_of_nonneg_left hsq (by positivity)))

theorem terminalParabolicRmBallBound_of_rmBoundOnInitialBall
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (start ρ K : ℝ) (hstart : start ≤ 0) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (hregular : ∀ i, Set.Ioo start 0 ⊆ (X.interval i).regular)
    (hric : ∀ i, ∀ s ∈ Set.Icc start 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
      0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
        (X.term i).S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
            ((X.term i).S.base.metric s).inner x v v)
    (hball : ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ ρ →
        curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C) :
    TerminalParabolicRmBallBound X start ρ := by
  obtain ⟨C, hC, hball⟩ := hball
  refine ⟨C, hC, fun i t ht y hy => hball i t ht y ?_⟩
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    norm_num
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hcomplete : ∀ s ∈ Set.Icc start 0, RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric s) := fun s hs => ⟨X.complete i s (hcarrier i hs)⟩
  have hadd := KappaSolutions.ricciFlow_additive_distance_bound_of_ricci_upper (I := I3)
    (S := (X.term i).S) (X.term i).isSolution hdim (X.connected i) hstart hK
    (hcarrier i) (hregular i) hcomplete (hric i) (X.term i).basepoint y
  have hstart_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric start)
      (X.term i).basepoint y).toReal ≤ ρ :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
      ((X.term i).S.base.metric start) (X.term i).basepoint y) hρ).mp hy
  have hzero_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y).toReal ≤ ρ := by
    linarith [hadd.1, hstart_le]
  simpa only [metricDistance] using hzero_le

theorem exists_eventually_terminalParabolicRmBallBound_of_ricciTensorBound
    {kappa K : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hK : 0 ≤ K) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            (∀ i, ∀ s ∈ Set.Icc (-(c / 2)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
              0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
                (X.term i).S.ricciAt s x (vec2 v v) ≤
                  ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                    ((X.term i).S.base.metric s).inner x v v) →
              ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc (-(c / 2)) 0, ∀ y : (X.term i).M,
                riemannianEDistOf (I := I3) ((X.term i).S.base.metric (-(c / 2)))
                  (X.term i).basepoint y ≤ ENNReal.ofReal (c / Real.sqrt 2) →
                curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_eventually_curvDerivNormSq_le_at_boundedDistance hmod
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hric
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    norm_num
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.depth_tendsto.eventually (Filter.eventually_ge_atTop (c / 4))] with i hb hdeep
  intro t ht y hy
  have hcarrier : Set.Icc (-(c / 2)) 0 ⊆ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hregular : Set.Ioo (-(c / 2)) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hcomplete : ∀ s ∈ Set.Icc (-(c / 2)) 0, RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric s) := fun s hs => ⟨X.complete i s (hcarrier hs)⟩
  have hadd := KappaSolutions.ricciFlow_additive_distance_bound_of_ricci_upper (I := I3)
    (S := (X.term i).S) (X.term i).isSolution hdim (X.connected i) (by linarith [hc])
    hK hcarrier hregular hcomplete (hric i) (X.term i).basepoint y
  have hstart_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric (-(c / 2)))
      (X.term i).basepoint y).toReal ≤ c / Real.sqrt 2 :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
      ((X.term i).S.base.metric (-(c / 2))) (X.term i).basepoint y)
      (by positivity)).mp hy
  have hzero_le : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
      ≤ c / Real.sqrt 2 := by
    simpa only [metricDistance] using (by linarith [hadd.1, hstart_le] :
      (riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
        (X.term i).basepoint y).toReal ≤ c / Real.sqrt 2)
  exact hb t ht y hzero_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
