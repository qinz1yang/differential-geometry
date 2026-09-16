import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCurvatureJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactnessLowDimension

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance flowJetsTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance flowJetsCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance flowJetsSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance flowJetsC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance flowJetsC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance flowJetsT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance flowJetsSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance flowJetsTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

private theorem curvDerivNorm_on_window_of_two_le_finrank
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            (X.term i).rmNormSq (I := I) t x ≤ K)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            curvDerivNorm (I := I) p ((X.term i).S.base.metric t) x ≤ C := by
  intro A hA T hT p
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨c, hcpos, hc⟩ := hlower (T + 1) (by linarith)
  obtain ⟨K₀, hK₀, hK⟩ := hlocal (3 * A) (by linarith) (T + 1) (by linarith)
  refine ⟨shiLocalUniformBound (Module.finrank ℝ E) p (max K₀ 1 * (T + 1))
      (2 * A * Real.sqrt (c * max K₀ 1)) * max K₀ 1, ?_, ?_⟩
  · exact mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _)
      (le_trans zero_le_one (le_max_right _ _))
  · filter_upwards [hK, hc] with i hKi hci
    intro t ht x hx
    let K : ℝ := max K₀ 1
    let ρ : ℝ := 2 * A * Real.sqrt c
    let R : ℝ := ρ * Real.sqrt K
    have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
    have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
    have hRpos : 0 < R := by
      have hρ : 0 < ρ := by dsimp only [ρ]; positivity
      exact mul_pos hρ (Real.sqrt_pos.mpr hKpos)
    have hRK : R / Real.sqrt K = ρ := by
      dsimp only [R]
      rw [mul_div_assoc, div_self (Real.sqrt_pos.mpr hKpos).ne', mul_one]
    have hmem : (-(T + 1) : ℝ) ∈ X.D.carrier := by
      simp only [hD, ancientTimeInterval_carrier, Set.mem_Iic]
      linarith
    have hcarrier : Set.Icc (-(T + 1) : ℝ) 0 ⊆ X.D.carrier := by
      intro t ht
      simp only [hD, ancientTimeInterval_carrier, Set.mem_Iic]
      exact ht.2
    have hregular : Set.Ico (-(T + 1) : ℝ) 0 ⊆ X.D.regular := by
      intro t ht
      simp only [hD, ancientTimeInterval_regular, Set.mem_Iio]
      exact ht.2
    have hcompleteMinus : RiemannianMetricComplete (I := I)
        ((X.term i).S.base.metric (-(T + 1))) :=
      ⟨MetricComplete.complete (I := I) ((X.term i).atTime (I := I) (-(T + 1)))
        (hcomplete.complete_on i (-(T + 1)) hmem)⟩
    have hball : IsCompact {y : (X.term i).M |
        riemannianEDistOf (I := I) ((X.term i).S.base.metric (-(T + 1))) x y ≤
          ENNReal.ofReal (R / Real.sqrt K)} := by
      rw [hRK]
      exact hcompleteMinus.closedEBall_isCompact x ρ
    have hcurv : ∀ t ∈ Set.Icc (-(T + 1) : ℝ) 0, ∀ y : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric (-(T + 1))) x y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 ((X.term i).S.base.metric t) y ≤ K ^ 2 := by
      intro t ht y hy
      change (X.term i).rmNormSq (I := I) t y ≤ K ^ 2
      rw [hRK] at hy
      have hquad : ∀ z : (X.term i).M, ∀ v : TangentSpace I z,
          c * (((X.term i).S.base.metric 0).inner z v v) ≤
            ((X.term i).S.base.metric (-(T + 1))).inner z v v :=
        fun z v => hci (-(T + 1)) ⟨le_rfl, by linarith⟩ z v
      have hcmp : ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) x y ≤
          riemannianEDistOf (I := I) ((X.term i).S.base.metric (-(T + 1))) x y :=
        le_edistOf_of_quad (I := I) ((X.term i).S.base.metric 0)
          ((X.term i).S.base.metric (-(T + 1))) hcpos hquad x y
      have hxy : riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) x y ≤
          ENNReal.ofReal (2 * A) := by
        have hall := hcmp.trans hy
        have hρ : ENNReal.ofReal ρ =
            ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (2 * A) := by
          dsimp only [ρ]
          rw [show 2 * A * Real.sqrt c = Real.sqrt c * (2 * A) by ring,
            ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
        rw [hρ] at hall
        have h0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
          ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hcpos))
        have htop : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
        exact (ENNReal.mul_le_mul_iff_right h0 htop).mp hall
      have hpy : riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint y ≤ ENNReal.ofReal (3 * A) := by
        have htri := riemannianEDistOf_triangle (I := I)
          ((X.term i).S.base.metric 0) (X.term i).basepoint x y
        have hsum : ENNReal.ofReal A + ENNReal.ofReal (2 * A) =
            ENNReal.ofReal (3 * A) := by
          rw [← ENNReal.ofReal_add hA.le (by linarith : (0 : ℝ) ≤ 2 * A)]
          congr 1
          ring
        exact htri.trans ((add_le_add hx hxy).trans_eq hsum)
      have hrm : (X.term i).rmNormSq (I := I) t y ≤ K₀ := hKi t ht y hpy
      have hKle : K₀ ≤ K ^ 2 := by
        have h1 : K₀ ≤ K := le_max_left _ _
        nlinarith [hK1, hK₀, h1]
      exact hrm.trans hKle
    have hcenter : riemannianEDistOf (I := I) ((X.term i).S.base.metric (-(T + 1))) x x ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K)) :=
      (riemannianEDistOf_self (I := I) ((X.term i).S.base.metric (-(T + 1))) x).le.trans bot_le
    have hb := shi_local_curvDerivNorm_terminal_of_solution_jets (X.term i).S
      (X.term i).isSolution hdim (a := -(T + 1)) (b := 0) (K := K) (R := R)
      (by linarith) hKpos hRpos hcarrier hregular x hball hcurv p t
      ⟨by linarith [ht.1], ht.2⟩ x hcenter
    have hconst : 2 * A * Real.sqrt c * Real.sqrt K = 2 * A * Real.sqrt (c * K) := by
      rw [Real.sqrt_mul hcpos.le]
      ring
    have helapsed : 1 ≤ t - -(T + 1) := by linarith [ht.1]
    have hsqrt : 1 ≤ Real.sqrt (t - -(T + 1)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt helapsed
    have hdenom : 1 ≤ Real.sqrt (t - -(T + 1)) ^ p := one_le_pow₀ hsqrt
    have hnum : 0 ≤ shiLocalUniformBound (Module.finrank ℝ E) p
        (K * (0 - -(T + 1))) R * K :=
      mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hKpos.le
    have hbound := hb.trans (div_le_self hnum hdenom)
    simpa only [K, R, ρ, hconst, sub_neg_eq_add, zero_add] using hbound


theorem exists_eventually_curvDerivNorm_le_on_window_of_local_curvature_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            (X.term i).rmNormSq (I := I) t x ≤ K)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            curvDerivNorm (I := I) p ((X.term i).S.base.metric t) x ≤ C := by
  by_cases hE : Module.finrank ℝ E ≤ 1
  · intro A _hA T _hT p
    refine ⟨0, le_rfl, Filter.Eventually.of_forall fun i => ?_⟩
    intro _ _ _ t _ht x _hx
    rw [curvDerivNorm_eq_zero_of_finrank_le_one (I := I)
      ((X.term i).S.base.metric t) hE p x]
  · exact curvDerivNorm_on_window_of_two_le_finrank X hD hcomplete (by omega) hlocal hlower

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
