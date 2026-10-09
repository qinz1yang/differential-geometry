import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBallVolumeLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAvrZero

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private local instance flowMeasurable
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    MeasurableSpace F.M := borel F.M
private local instance flowBorel
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    BorelSpace F.M := ⟨rfl⟩

theorem exists_normalized_ancient_kappa_volume_collapse_radius
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        riemannianVolumeMeasure (I := I3) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I3) (F.S.base.metric 0) F.basepoint A) ≤
          ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  by_contra hfailure
  push Not at hfailure
  let a : ℕ → ℝ := fun i => (i : ℝ) + 1
  have ha (i : ℕ) : 1 ≤ a i := by
    dsimp only [a]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hcounter : ∀ i : ℕ,
      ∃ F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution kappa F ∧ PointedFlowScalarAtBase F 1 ∧
        ENNReal.ofReal epsilon * ENNReal.ofReal ((a i) ^ 3) <
          riemannianVolumeMeasure (I := I3) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I3) (F.S.base.metric 0) F.basepoint (a i)) := by
    intro i
    exact hfailure (a i) (ha i)
  choose X hX hbase hvolume using hcounter
  have hexpand : Tendsto a atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ))
    intro i
    dsimp only [a]
    linarith
  obtain ⟨L, phi, hphi, Phi, hL, _, _, hconv, _⟩ :=
    exists_ancientKappa_fixed_kappa_compactness X hX hbase
  obtain ⟨C, hcanonical⟩ := hconv 0 le_rfl
  have hsourceComplete : SeqMetricComplete (I := I3) ((ancientPointedFlowSeq X).atTime 0) :=
    ⟨fun i => (hX i).complete 0 (by simp)⟩
  have hRic : ∀ i : ℕ, RicciBoundedBelow (I := I3) ((X i).S.base.metric 0) 0 := by
    intro i z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I3) ((X i).S.base.metric 0) z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      (hX i).nonnegativeCurvatureOperator 0 (by simp) z n c u w
  have hsourceVolume : ∀ i : ℕ,
      ENNReal.ofReal epsilon * ENNReal.ofReal ((a i) ^ Module.finrank ℝ ThreeSpace) ≤
        riemannianVolumeMeasure (I := I3) (M := (X i).M) ((X i).S.base.metric 0)
          (riemannianBallOf (I := I3) ((X i).S.base.metric 0) (X i).basepoint (a i)) := by
    intro i
    simpa only [hdim] using (hvolume i).le
  obtain ⟨_, havr, hnoncompact⟩ := pointed_ball_volume_lower_of_expanding_radii
    C hcanonical (hL.complete 0 (by simp)) hsourceComplete
      (fun i => (hX i).connected) hRic hphi a hexpand
      (ENNReal.ofReal epsilon) hsourceVolume
  have heps0 : ENNReal.ofReal epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr hepsilon).ne'
  have hzero := ancientKappaThree_terminal_avr_eq_zero L hL hdim
    (hnoncompact heps0) L.basepoint
  change ENNReal.ofReal epsilon / euclideanUnitBallVolume (Module.finrank ℝ ThreeSpace) ≤
    asymptoticVolumeRatio (I := I3) (L.S.base.metric 0) L.basepoint at havr
  rw [hzero] at havr
  exact (ENNReal.div_pos heps0 (euclideanUnitBallVolume_ne_top _)).not_ge havr

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
