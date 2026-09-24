import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem exists_eventually_curvDerivNorm_le_on_scalar_sublevel
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ A : ℝ, ∀ m : ℕ,
            ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop, ∀ p : (X.term i).M,
              (X.term i).S.scalar 0 p ≤ A →
                curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) p ≤ B := by
  obtain ⟨epsStar, hepsStar, B, hB, hmain⟩ :=
    exists_curvDerivNorm_bound_at_terminal_scalar_scale.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X A m
  refine ⟨B m * max A 1 * Real.sqrt (max A 1) ^ m,
    mul_nonneg (mul_nonneg (hB m) (by positivity)) (by positivity), ?_⟩
  filter_upwards [hmain eps heps hle sigma hsigma Phi hPhi X] with i hi
  exact fun p hp => hi (max A 1) (le_max_right _ _) p (hp.trans (le_max_left _ _)) m

private theorem exists_source_curvDerivNorm_bound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : (X.term i).M,
      curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) p ≤ B := by
  obtain ⟨C, hC⟩ := X.source_bound i
  let K : ℝ := max C 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hCK : C ≤ K ^ 2 := by
    have hCK : C ≤ K := le_max_left _ _
    nlinarith
  have hcarrier : Icc (-X.depth i) 0 ⊆ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    intro t ht
    exact ⟨by linarith [ht.1, X.depth_pos i], ht.2⟩
  have hregular : Ico (-X.depth i) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro t ht
    exact ⟨by linarith [ht.1, X.depth_pos i], ht.2⟩
  have hcomplete : RiemannianMetricComplete ((X.term i).S.base.metric 0) :=
    ⟨X.complete i 0 (hcarrier ⟨by linarith [X.depth_pos i], le_rfl⟩)⟩
  refine ⟨shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * (0 - -X.depth i))
      (Real.sqrt K / (4 * Real.exp
        ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * (0 - -X.depth i)))) *
      K / Real.sqrt (0 - -X.depth i) ^ m,
    div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
      (pow_nonneg (Real.sqrt_nonneg _) _), fun p => ?_⟩
  have hb := shi_curvDerivNorm_terminal_of_terminal_ball (X.term i).S (X.term i).isSolution
    (a := -X.depth i) (b := 0) (K := K) (R := 1) (by linarith [X.depth_pos i]) hK
    one_pos hcarrier hregular p (hcomplete.closedEBall_isCompact p 1) (by
      intro t ht y _
      exact (hC t (hcarrier ht) y).trans hCK) m
  simpa only [one_mul] using hb

private theorem exists_prefix_curvDerivNorm_bound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (N m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i, i < N → ∀ p : (X.term i).M,
      curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) p ≤ B := by
  induction N with
  | zero => exact ⟨0, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨B, hB, hb⟩ := ih
    obtain ⟨C, _, hc⟩ := exists_source_curvDerivNorm_bound X N m
    refine ⟨max B C, hB.trans (le_max_left _ _), fun i hi p => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact (hb i hlt p).trans (le_max_left _ _)
    · subst i
      exact (hc p).trans (le_max_right _ _)

theorem exists_curvDerivNorm_le_on_scalar_sublevel {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ A : ℝ, ∀ m : ℕ,
            ∃ B : ℝ, 0 ≤ B ∧ ∀ i, ∀ p : (X.term i).M,
              (X.term i).S.scalar 0 p ≤ A →
                curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) p ≤ B := by
  obtain ⟨epsStar, hepsStar, htail⟩ :=
    exists_eventually_curvDerivNorm_le_on_scalar_sublevel hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X A m
  obtain ⟨B, hB, hb⟩ := htail eps heps hle sigma hsigma Phi hPhi X A m
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  obtain ⟨C, _, hc⟩ := exists_prefix_curvDerivNorm_bound X N m
  refine ⟨max B C, hB.trans (le_max_left _ _), fun i p hp => ?_⟩
  by_cases hi : i < N
  · exact (hc i hi p).trans (le_max_right _ _)
  · exact (hN i (le_of_not_gt hi) p hp).trans (le_max_left _ _)

theorem exists_terminalDerivativeBounds_of_boundedAtDistance {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            BoundedAtDistance X → TerminalDerivativeBounds X := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := exists_curvDerivNorm_le_on_scalar_sublevel hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hb rho hrho m
  obtain ⟨A, hA⟩ := hb rho hrho
  obtain ⟨B, _, hB⟩ := hbound eps heps hle sigma hsigma Phi hPhi X A m
  exact ⟨B, fun i p hp => hB i p (hA i p hp)⟩

theorem exists_curvDerivNorm_bound_on_terminal_ball {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar rho : ℝ, 0 < epsStar ∧ 0 < rho ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ m : ℕ,
            ∃ B : ℝ, 0 ≤ B ∧ ∀ i, ∀ y : (X.term i).M,
              metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
                curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ B := by
  obtain ⟨e₁, he₁, hsublevel⟩ := exists_curvDerivNorm_le_on_scalar_sublevel hkappa
  obtain ⟨e₂, c, _, he₂, hc, _, hprop⟩ := canonical_neighborhood_local_propagation hkappa
  refine ⟨min e₁ e₂, c / Real.sqrt 2, lt_min he₁ he₂, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X m
  obtain ⟨B, hB, hb⟩ := hsublevel eps heps (hle.trans (min_le_left _ _))
    sigma hsigma Phi hPhi X 8 m
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hprop eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X)
  obtain ⟨C, _, hC⟩ := exists_prefix_curvDerivNorm_bound X N m
  refine ⟨max B C, hB.trans (le_max_left _ _), fun i y hy => ?_⟩
  by_cases hi : i < N
  · exact (hC i hi y).trans (le_max_right _ _)
  have hL : 1 + |(X.term i).S.scalar 0 (X.term i).basepoint| = 2 := by
    have hbase : (X.term i).S.scalar 0 (X.term i).basepoint = 1 := X.base_one i
    rw [hbase]
    norm_num
  have hmem : (y, (0 : ℝ)) ∈ frozenBackwardCylinder (X.term i).S (X.term i).basepoint 0 c c
      (1 + |(X.term i).S.scalar 0 (X.term i).basepoint|) := by
    rw [hL]
    have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
    refine ⟨?_, ⟨by linarith, le_rfl⟩⟩
    exact (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top ((X.term i).S.base.metric 0) (X.term i).basepoint y)
      (by positivity)).mpr hy
  have hs := (hN i (le_of_not_gt hi) 0
    ⟨by linarith [X.depth_pos i], le_rfl⟩ (X.term i).basepoint).2 y 0 hmem
  have hscalar : (X.term i).S.scalar 0 y ≤ 8 := by
    have hh := hs.2.1
    rw [hL] at hh
    norm_num at hh ⊢
    exact hh
  exact (hb i y hscalar).trans (le_max_left _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
