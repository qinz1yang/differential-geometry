import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalShi

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]

private local instance normalizedJetsTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance normalizedJetsCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance normalizedJetsSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance normalizedJetsC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedJetsT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance normalizedJetsSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance normalizedJetsTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

theorem exists_normalized_klim_spatial_jet_constants
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ K : ℝ → ℝ, (∀ A, 0 < K A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, 0 ≤ A → ∀ s : ℝ, s ≤ 0 → ∀ m : ℕ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
            shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants (I := I) hdim kappa
  refine ⟨fun A => 2 * C (A + 1), fun A => mul_pos (by norm_num) (hC (A + 1)), ?_⟩
  intro D F hK hbase A hA s hs m y hy
  let _ : ConnectedSpace F.M := hK.connected
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let K : ℝ := 2 * C (A + 1)
  have hKpos : 0 < K := mul_pos (by norm_num) (hC (A + 1))
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have houter : Real.sqrt K / Real.sqrt K = 1 := div_self hsqrt.ne'
  have ha : s - 1 ≤ 0 := by linarith
  have hspan : s - (s - 1) = 1 := by ring
  have hacar : s - 1 ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using ha
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric (s - 1)) :=
    ⟨MetricComplete.complete (I := I) (F.atTime (I := I) (s - 1))
      (hK.complete (s - 1) hacar)⟩
  have hball : IsCompact {z : F.M |
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K)} := by
    rw [houter]
    exact hcomplete.closedEBall_isCompact y 1
  have hcurv : ∀ q ∈ Set.Icc (s - 1) s, ∀ z : F.M,
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (F.S.base.metric q) z ≤ K ^ 2 := by
    intro q hq z hz
    rw [houter] at hz
    have hterminal := klim_buffered_ball_subset F hK ha hA zero_le_one
      F.basepoint y z hy hz
    have hb := hbound D F hK hbase (A + 1) z hterminal q (hq.2.trans hs)
    change F.rmNormSq (I := I) q z ≤ K ^ 2
    apply hb.2.trans
    dsimp only [K]
    nlinarith [sq_nonneg (C (A + 1))]
  have hcarrier : Set.Icc (s - 1) s ⊆ D.carrier := by
    intro q hq
    simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.trans hs
  have hregular : Set.Ico (s - 1) s ⊆ D.regular := by
    intro q hq
    simpa only [hK.regular_eq, Set.mem_Iio] using hq.2.trans_le hs
  have hcenter : riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y y ≤
      ENNReal.ofReal (Real.sqrt K / (2 * Real.sqrt K)) :=
    (riemannianEDistOf_self (I := I) (F.S.base.metric (s - 1)) y).le.trans bot_le
  have hb := shi_local_curvDerivNorm_terminal_inclusive F.S F.isSolution
    hK.dimension_ge_two (a := s - 1) (b := s) (K := K) (R := Real.sqrt K)
    (by linarith) hKpos hsqrt hcarrier hregular y hball hcurv
    m s ⟨by linarith, le_rfl⟩ y hcenter
  change curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
    shiLocalUniformBound 3 m K (Real.sqrt K) * K
  simpa only [hdim, hspan, mul_one, Real.sqrt_one, one_pow, div_one] using hb

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
