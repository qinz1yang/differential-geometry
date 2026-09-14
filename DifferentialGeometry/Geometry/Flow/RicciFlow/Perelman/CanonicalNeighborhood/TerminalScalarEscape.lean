import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformScalarBoundProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

abbrev TerminalScalarBoundedAbove {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ C : ℝ, ∀ i : ℕ, ∀ x : (X.term i).M, (X.term i).S.scalar 0 x ≤ C

abbrev BoundedDistanceToBasepoint {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ R : ℝ, ∀ i : ℕ, ∀ x : (X.term i).M,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤ R

abbrev TerminalScalarEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  BoundedAtDistance X ∧
    ∀ C : ℝ, ∃ i : ℕ, ∃ x : (X.term i).M, C < (X.term i).S.scalar 0 x

abbrev ExhaustedWithinRadius {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (r : ℝ) : Prop :=
  ∃ R : ℝ, R < r ∧ ∀ i : ℕ, ∀ x : (X.term i).M,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤ R

abbrev NoTerminalScalarEscapeShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ¬ TerminalScalarEscape X

abbrev BoundedDistanceToBasepointShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, BoundedDistanceToBasepoint X

theorem terminalScalarEscape_iff_boundedAtDistance_and_not_boundedAbove
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    TerminalScalarEscape X ↔ BoundedAtDistance X ∧ ¬ TerminalScalarBoundedAbove X := by
  constructor
  · rintro ⟨hbdd, hunbounded⟩
    refine ⟨hbdd, fun habove => ?_⟩
    obtain ⟨C, hC⟩ := habove
    obtain ⟨i, x, hx⟩ := hunbounded C
    exact absurd (hC i x) (not_le.mpr hx)
  · rintro ⟨hbdd, habove⟩
    refine ⟨hbdd, fun C => ?_⟩
    by_contra hcon
    exact habove ⟨C, fun i x => le_of_not_gt fun hlt => hcon ⟨i, x, hlt⟩⟩

theorem terminalScalarBoundedAbove_of_boundedAtDistance_and_boundedDistanceToBasepoint
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hbdd : BoundedAtDistance X) (hdiam : BoundedDistanceToBasepoint X) :
    TerminalScalarBoundedAbove X := by
  obtain ⟨R, hR⟩ := hdiam
  obtain ⟨C, hC⟩ := hbdd (max R 0 + 1) (by positivity)
  exact ⟨C, fun i x => hC i x (le_trans (hR i x) (by linarith [le_max_left R 0]))⟩

theorem boundedAtDistance_of_terminalScalarBoundedAbove
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : TerminalScalarBoundedAbove X) : BoundedAtDistance X := by
  obtain ⟨C, hC⟩ := h
  exact fun _ _ => ⟨C, fun i y _ => hC i y⟩

theorem noTerminalScalarEscapeShell_of_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    NoTerminalScalarEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X hesc => ?_⟩
  obtain ⟨C, _hC, hCbound⟩ := hbound eps heps hle X
  obtain ⟨i, x, hx⟩ := hesc.2 C
  exact absurd (hCbound i x) (not_le.mpr hx)

theorem noTerminalScalarEscapeShell_of_uniformScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarUpperBoundShell.{u} kappa sigma Phi) :
    NoTerminalScalarEscapeShell.{u} kappa sigma Phi :=
  noTerminalScalarEscapeShell_of_uniformTerminalScalarUpperBoundShell
    (uniformTerminalScalarUpperBoundShell_of_uniformScalarUpperBoundShell h)

theorem noTerminalScalarEscapeShell_of_boundedDistanceToBasepointShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : BoundedDistanceToBasepointShell.{u} kappa sigma Phi) :
    NoTerminalScalarEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hdiam⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X hesc => ?_⟩
  obtain ⟨C, hC⟩ :=
    terminalScalarBoundedAbove_of_boundedAtDistance_and_boundedDistanceToBasepoint X
      hesc.1 (hdiam eps heps hle X)
  obtain ⟨i, x, hx⟩ := hesc.2 C
  exact absurd (hC i x) (not_le.mpr hx)

theorem uniformTerminalScalarUpperBoundShell_iff_boundedAtDistanceShell_and_noTerminalScalarEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi ↔
      BoundedAtDistanceShell.{u} kappa sigma Phi ∧
        NoTerminalScalarEscapeShell.{u} kappa sigma Phi := by
  constructor
  · intro h
    exact ⟨boundedAtDistanceShell_of_uniformTerminalScalarUpperBoundShell h,
      noTerminalScalarEscapeShell_of_uniformTerminalScalarUpperBoundShell h⟩
  · rintro ⟨⟨e₁, he₁, h₁⟩, ⟨e₂, he₂, h₂⟩⟩
    refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X => ?_⟩
    have hbdd : BoundedAtDistance X := h₁ eps heps (le_trans hle (min_le_left e₁ e₂)) X
    have hno : ¬ TerminalScalarEscape X := h₂ eps heps (le_trans hle (min_le_right e₁ e₂)) X
    have habove : TerminalScalarBoundedAbove X := by
      by_contra hcon
      exact hno ((terminalScalarEscape_iff_boundedAtDistance_and_not_boundedAbove X).mpr
        ⟨hbdd, hcon⟩)
    obtain ⟨C, hC⟩ := habove
    exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1),
      fun i x => le_trans (hC i x) (le_max_left C 1)⟩

theorem uniformTerminalScalarUpperBoundShell_of_boundedAtDistanceShell_and_boundedDistanceToBasepointShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hshell : BoundedAtDistanceShell.{u} kappa sigma Phi)
    (hdiam : BoundedDistanceToBasepointShell.{u} kappa sigma Phi) :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, h₁⟩ := hshell
  obtain ⟨e₂, he₂, h₂⟩ := hdiam
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X => ?_⟩
  obtain ⟨C, hC⟩ :=
    terminalScalarBoundedAbove_of_boundedAtDistance_and_boundedDistanceToBasepoint X
      (h₁ eps heps (le_trans hle (min_le_left e₁ e₂)) X)
      (h₂ eps heps (le_trans hle (min_le_right e₁ e₂)) X)
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1),
    fun i x => le_trans (hC i x) (le_max_left C 1)⟩

theorem noSubsequenceCurvatureEscapeShell_of_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi :=
  noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell
    (boundedAtDistanceShell_of_uniformTerminalScalarUpperBoundShell h)

theorem uniformTerminalScalarUpperBoundShell_of_boundedDistanceToBasepointShell_and_smallScale_and_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hdiam : BoundedDistanceToBasepointShell.{u} kappa sigma Phi)
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (hesc : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi) :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi :=
  uniformTerminalScalarUpperBoundShell_of_boundedAtDistanceShell_and_boundedDistanceToBasepointShell
    (boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell hsmall hesc) hdiam

theorem terminalScalarBoundedAbove_of_curvatureBoundedWithin_and_exhaustedWithinRadius
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {r : ℝ} (hbdd : CurvatureBoundedWithin X r) (hexh : ExhaustedWithinRadius X r) :
    TerminalScalarBoundedAbove X := by
  obtain ⟨R, hRr, hR⟩ := hexh
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun i x => hC i x (lt_of_le_of_lt (hR i x) hRr)⟩

theorem boundedAtDistance_of_curvatureBoundedWithin_and_exhaustedWithinRadius
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {r : ℝ} (hbdd : CurvatureBoundedWithin X r) (hexh : ExhaustedWithinRadius X r) :
    BoundedAtDistance X :=
  boundedAtDistance_of_terminalScalarBoundedAbove X
    (terminalScalarBoundedAbove_of_curvatureBoundedWithin_and_exhaustedWithinRadius X hbdd hexh)

theorem uniformTerminalScalarUpperBoundShell_of_smallScale_and_exhaustion
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          CurvatureBoundedWithin X r ∧ ExhaustedWithinRadius X r) :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, r, hepsStar, _hr, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨hbdd, hexh⟩ := hb eps heps hle X
  obtain ⟨C, hC⟩ :=
    terminalScalarBoundedAbove_of_curvatureBoundedWithin_and_exhaustedWithinRadius X hbdd hexh
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1),
    fun i x => le_trans (hC i x) (le_max_left C 1)⟩

theorem boundedAtDistanceShell_of_smallScale_and_exhaustion
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          CurvatureBoundedWithin X r ∧ ExhaustedWithinRadius X r) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_uniformTerminalScalarUpperBoundShell
    (uniformTerminalScalarUpperBoundShell_of_smallScale_and_exhaustion h)

private theorem exists_forall_inv_le_of_tendsto_atTop (Q : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ i : ℕ, 0 < Q i) (htend : Filter.Tendsto Q Filter.atTop Filter.atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, (Q i)⁻¹ ≤ C := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (Filter.eventually_ge_atTop c))
  have hprefix : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i < n → (Q i)⁻¹ ≤ C := by
    intro n
    induction n with
    | zero => exact ⟨1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ n ih =>
      obtain ⟨C, hC, hle⟩ := ih
      refine ⟨max C (Q n)⁻¹, lt_max_of_lt_right (inv_pos.mpr (hQ n)), fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact le_trans (hle i hlt) (le_max_left _ _)
      · exact le_max_right _ _
  obtain ⟨C, hC, hle⟩ := hprefix N
  refine ⟨max C c⁻¹, lt_max_of_lt_left hC, fun i => ?_⟩
  rcases lt_or_ge i N with hi | hi
  · exact le_trans (hle i hi) (le_max_left C c⁻¹)
  · exact le_trans (by simpa [one_div] using one_div_le_one_div_of_le hc (hN i hi))
      (le_max_right C c⁻¹)

theorem exists_terminalScalarLowerBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    ∃ c : ℝ, ∀ i : ℕ, ∀ x : (X.term i).M, c ≤ (X.term i).S.scalar 0 x := by
  obtain ⟨C, _hC, hle⟩ :=
    exists_forall_inv_le_of_tendsto_atTop X.scale one_pos (fun i => X.scale_pos i)
      X.scale_tendsto
  refine ⟨-6 * Phi 0 * C, fun i x => ?_⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hmem : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hlow := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
    (X.pinching i) hdim hmem x
  have hval : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
    simp only [rescalePinchingFunction, mul_zero]
  rw [hval] at hlow
  have hPhi0 : 0 < Phi 0 := hPhi.pos 0
  have hstep : (X.scale i)⁻¹ * Phi 0 ≤ C * Phi 0 :=
    mul_le_mul_of_nonneg_right (hle i) (le_of_lt hPhi0)
  nlinarith [hlow, hstep]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
