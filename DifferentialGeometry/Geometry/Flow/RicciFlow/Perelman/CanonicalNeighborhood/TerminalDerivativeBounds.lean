import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalScalarDerivatives

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem NormalizedSequence.exists_terminal_curvDerivNorm_bound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (i m : ℕ) : ∃ C : ℝ, ∀ y : (X.term i).M,
      curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ C := by
  obtain ⟨K0, hK0⟩ := X.source_bound i
  let T := X.depth i
  let K := max K0 1
  have hT : 0 < T := X.depth_pos i
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right _ _)
  have hcarrier : Icc (-T) 0 ⊆ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    intro t ht
    exact ⟨by dsimp [T] at *; linarith [ht.1], ht.2⟩
  have hregular : Ioo (-T) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro t ht
    exact ⟨by dsimp [T] at *; linarith [ht.1], ht.2⟩
  have hcomplete : RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric (-(T / 2))) :=
    ⟨X.complete i _ (hcarrier ⟨by linarith, by linarith⟩)⟩
  have hrm : ∀ t ∈ Icc (-T) 0, ∀ y : (X.term i).M,
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ K ^ 2 := by
    intro t ht y
    have hbound : curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ K0 :=
      hK0 t (hcarrier ht) y
    have hK0le : K0 ≤ K := le_max_left _ _
    have hKone : 1 ≤ K := le_max_right _ _
    nlinarith
  refine ⟨shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * (T / 2))
    (Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * T / 2)) *
      ((1 : ℝ) / 4) * Real.sqrt K) * K / Real.sqrt (T / 4) ^ m, ?_⟩
  intro y
  exact curvDerivNorm_le_on_terminal_ball_of_curvature_bound (X.term i).S (X.term i).isSolution
    (by simp [ThreeSpace]) hT one_pos hK hcarrier hregular hcomplete y
    (fun t ht z _ => hrm t ht z) m 0 ⟨by linarith, le_rfl⟩ y (by
      change riemannianEDistOf ((X.term i).S.base.metric 0) y y ≤ ENNReal.ofReal (1 / 2)
      rw [riemannianEDistOf_self]
      exact bot_le)

private theorem exists_terminal_derivative_bound_on_prefix
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (N m : ℕ) : ∃ C : ℝ, ∀ i, i < N → ∀ y : (X.term i).M,
      curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ C := by
  induction N with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨K, hK⟩ := X.exists_terminal_curvDerivNorm_bound N m
    refine ⟨max C K, fun i hi y => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact (hC i hlt y).trans (le_max_left _ _)
    · exact (hK y).trans (le_max_right _ _)

theorem terminalDerivativeBounds_of_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          BoundedAtDistance X → TerminalDerivativeBounds X := by
  obtain ⟨epsStar, hepsStar, hprop⟩ :=
    exists_eventually_curvDerivNorm_le_of_terminal_scalar_le hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hscalar rho hrho m
  obtain ⟨A, hA⟩ := hscalar rho hrho
  obtain ⟨C, hC⟩ := hprop eps heps hle sigma hsigma Phi hPhi A m
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hC X)
  obtain ⟨K, hK⟩ := exists_terminal_derivative_bound_on_prefix X N m
  refine ⟨max C K, fun i y hy => ?_⟩
  by_cases hi : i < N
  · exact (hK i hi y).trans (le_max_right _ _)
  · exact (hN i (le_of_not_gt hi) y (hA i y hy)).trans (le_max_left _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
