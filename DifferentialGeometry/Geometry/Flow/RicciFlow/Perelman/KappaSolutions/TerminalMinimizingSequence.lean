import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance minimizingSequenceTopology : TopologicalSpace F.M := F.topology
local instance minimizingSequenceCharted : ChartedSpace H F.M := F.charted
local instance minimizingSequenceSmooth : IsManifold I ∞ F.M := F.smooth
local instance minimizingSequenceT2 : T2Space F.M := F.t2
local instance minimizingSequenceSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_tendstoUniformly_minimizing_sequence_of_ancient
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    letI : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
    letI : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
    ∃ (beta : ℕ → ℝ → F.M) (gamma : ℝ → F.M) (K : Set F.M),
      (∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (beta n)) ∧
      (∀ n, beta n 0 = x) ∧ (∀ n, beta n (Real.sqrt tau) = y) ∧
      Antitone (fun n => lRegularizedAction F.S 0 (beta n) 0 (Real.sqrt tau)) ∧
      Tendsto (fun n => lRegularizedAction F.S 0 (beta n) 0 (Real.sqrt tau)) atTop
        (𝓝 (lCost F.S 0 x y tau)) ∧
      Continuous gamma ∧ gamma 0 = x ∧ gamma (Real.sqrt tau) = y ∧
      IsCompact K ∧ (∀ n, beta n '' Icc 0 (Real.sqrt tau) ⊆ K) ∧
      gamma '' Icc 0 (Real.sqrt tau) ⊆ K ∧
      TendstoUniformly (fun n (s : Icc 0 (Real.sqrt tau)) => beta n s.1)
        (fun s => gamma s.1) atTop := by
  classical
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  let : ConnectedSpace F.M := hF.connected
  let costs : Set ℝ := {r | ∃ alpha : ℝ → F.M,
    ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lLength F.S 0 (squareRootReparametrization alpha) 0 tau = r}
  obtain ⟨alpha0, halpha0, h0a, h0b, _⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected F.S 0 x y tau htau
      (lCost F.S 0 x y tau + 1) (by linarith)
  have hcosts : costs.Nonempty :=
    ⟨_, alpha0, halpha0, h0a, h0b, rfl⟩
  have hscalar : ∀ s ∈ Icc 0 tau, ∀ z : F.M, 0 ≤ F.S.scalar (0 - s) z := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs z
    apply (hC (0 - s) _ z).1
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr hs.1
  have hcosts_bdd : BddBelow costs := by
    refine ⟨0, ?_⟩
    rintro r ⟨alpha, _, _, _, rfl⟩
    exact lLength_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar _
  obtain ⟨v, hvanti, hvlim, hv⟩ := exists_seq_tendsto_sInf hcosts hcosts_bdd
  choose alpha halpha hstart hend hval using fun n => hv n
  have haction (n : ℕ) : lRegularizedAction F.S 0 (alpha n) 0 (Real.sqrt tau) = v n := by
    rw [← lLength_squareRootReparametrization_eq_lRegularizedAction F.S 0 (alpha n) tau htau.le]
    exact hval n
  have hbound (n : ℕ) : lRegularizedAction F.S 0 (alpha n) 0 (Real.sqrt tau) ≤ v 0 := by
    rw [haction]
    exact hvanti (Nat.zero_le n)
  obtain ⟨K, phi, g, hK, hphi, hKalpha, hconv, hKg, hga, hgb⟩ :=
    exists_uniform_subseq_of_ancient_action_le F hF alpha halpha x y (Real.sqrt_nonneg tau)
      hstart hend hbound
  let gamma : ℝ → F.M := IccExtend (Real.sqrt_nonneg tau) g
  have hgamma : Continuous gamma := g.continuous.comp continuous_projIcc
  have heq (s : Icc 0 (Real.sqrt tau)) : gamma s.1 = g s :=
    IccExtend_of_mem (Real.sqrt_nonneg tau) g s.2
  have hga' : gamma 0 = x := (heq ⟨0, le_rfl, Real.sqrt_nonneg tau⟩).trans hga
  have hgb' : gamma (Real.sqrt tau) = y :=
    (heq ⟨Real.sqrt tau, Real.sqrt_nonneg tau, le_rfl⟩).trans hgb
  refine ⟨fun n => alpha (phi n), gamma, K, (fun n => halpha (phi n)),
    (fun n => hstart (phi n)), (fun n => hend (phi n)), ?_, ?_, hgamma,
    hga', hgb', hK, hKalpha, ?_, ?_⟩
  · intro n m hnm
    simpa only [haction] using hvanti (hphi.monotone hnm)
  · have h := hvlim.comp hphi.tendsto_atTop
    change Tendsto (fun n => lRegularizedAction F.S 0 (alpha (phi n)) 0 (Real.sqrt tau))
      atTop (𝓝 (sInf costs))
    rw [show (fun n => lRegularizedAction F.S 0 (alpha (phi n)) 0 (Real.sqrt tau)) =
      (fun n => v (phi n)) by
        funext n
        exact haction (phi n)]
    exact h
  · rintro z ⟨s, hs, rfl⟩
    rw [heq ⟨s, hs⟩]
    exact hKg ⟨s, hs⟩
  · convert hconv using 1
    funext s
    exact heq s

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
