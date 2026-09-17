import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance normalizedSourceTopology : TopologicalSpace F.M := F.topology
local instance normalizedSourceCharted : ChartedSpace H F.M := F.charted
local instance normalizedSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance normalizedSourceT2 : T2Space F.M := F.t2
local instance normalizedSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancient_reducedVolume_antitone
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  intro tau₁ h₁ tau₂ h₂ h₁₂
  apply le_of_tendsto_of_tendsto
    (ancient_reducedVolume_tendsto_terminal F hF h₂ p)
    (ancient_reducedVolume_tendsto_terminal F hF h₁ p)
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (ancient_reducedVolume_antitone_of_regular_base F hF p
    (T := T) hT) h₁ h₂ h₁₂


theorem exists_samePole_normalized_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  sorry

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
theorem ancient_reducedVolume_antitone_of_redVolume_antitone
    (hgap : ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := F.M) D)
      (T : ℝ) (x : F.M) {tau1 tau2 : ℝ},
      IsSolutionOn (I := I) S →
      0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
      Set.Ico (T - tau2) T ⊆ D.regular →
      redVolume S T x tau2 ≤ redVolume S T x tau1)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  exact hgap ancientTimeInterval F.S 0 p F.isSolution h1 h12 (by simp)
    (fun t ht => ht.2)

section IcoSlab

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] in
def redVolumeIcoSlabAntitone {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  ∀ (T : ℝ) (x : M) {tau1 tau2 : ℝ},
    IsSolutionOn (I := I) S →
    0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
    Set.Ico (T - tau2) T ⊆ D.regular →
    redVolume S T x tau2 ≤ redVolume S T x tau1

end IcoSlab

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_icoSlabAntitone
    (h : ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := F.M) D),
      redVolumeIcoSlabAntitone (I := I) (D := D) S)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) :=
  ancient_reducedVolume_antitone_of_redVolume_antitone F
    (fun D S T x => h D S T x) p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
