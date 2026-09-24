import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTerminalSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section TerminalReducedVolume

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance asymptoticShrinkerFrontierTopology : TopologicalSpace F.M := F.topology
local instance asymptoticShrinkerFrontierCharted : ChartedSpace H F.M := F.charted
local instance asymptoticShrinkerFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance asymptoticShrinkerFrontierT2 : T2Space F.M := F.t2
local instance asymptoticShrinkerFrontierTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance asymptoticShrinkerFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact

omit [I.Boundaryless] in
theorem terminalReducedVolume_semicontinuous_of_tendsto {p : F.M} {tau : ℝ}
    (h : Tendsto (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ))
      (𝓝 (intrinsicReducedVolume F.S 0 p tau))) :
    intrinsicReducedVolume F.S 0 p tau ≤
        liminf (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)) ∧
      limsup (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)) ≤
        intrinsicReducedVolume F.S 0 p tau :=
  ⟨h.liminf_eq.ge, h.limsup_eq.le⟩

omit [I.Boundaryless] in
theorem terminalReducedVolume_semicontinuous_of_terminal_tendsto {p : F.M}
    (h : ∀ tau ∈ Set.Ioi (0 : ℝ),
      Tendsto (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ))
        (𝓝 (intrinsicReducedVolume F.S 0 p tau))) :
    TerminalReducedVolumeLowerSemicontinuous F p ∧
      TerminalReducedVolumeUpperSemicontinuous F p :=
  ⟨fun tau htau => (terminalReducedVolume_semicontinuous_of_tendsto F (h tau htau)).1,
    fun tau htau => (terminalReducedVolume_semicontinuous_of_tendsto F (h tau htau)).2⟩

omit [I.Boundaryless] in
theorem not_Iic_zero_subset_ancientTimeInterval_regular :
    ¬ (Set.Iic (0 : ℝ) ⊆ ancientTimeInterval.regular) :=
  fun h => not_ancientTimeInterval_zero_mem_regular (h (Set.mem_Iic.mpr le_rfl))

omit [I.Boundaryless] in
theorem terminalReducedVolume_semicontinuous_of_metric_eq_const {p : F.M}
    (g : SmoothRiemannianMetric I F.M) (hconst : F.S.base.metric = fun _ => g) :
    TerminalReducedVolumeLowerSemicontinuous F p ∧
      TerminalReducedVolumeUpperSemicontinuous F p := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  exact terminalReducedVolume_semicontinuous_of_terminal_tendsto F
    (fun tau _ => tendsto_intrinsicReducedVolume_of_metric_eq_const F.S g hconst p tau)

def HasSamePoleNormalizedShrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → F.M,
    (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2) ∧
    backwardSliceApproximateMetricCompactness F hF tau htau q ∧
    ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
      StrictMono phi →
      ∀ (Phi : PointedRiemannianConvergenceMaps (I := I)
        (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) →
      MetricComplete (I := I) L →
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace H L.M := L.charted
       let _ : IsManifold I ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       let _ : SigmaCompactSpace L.M := L.sigmaCompact
       ConnectedSpace L.M →
       (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
       (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
         0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯,
         gradientRicciSoliton L.metric f 1 ∧
         IsHamiltonNormalizedPotential L.metric f ∧
         Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
           atTop (𝓝 (normalizedShrinkerMass L.metric f)))

theorem exists_samePole_normalized_asymptotic_shrinker_of_input [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hinput : HasSamePoleNormalizedShrinkerInput F hF p tau htau) :
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
  obtain ⟨q, hcost, hcompact, hlimit⟩ := hinput
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q hcompact
  exact ⟨q, L, phi, hphi, hcost, Phi, C, hdomain, hcomplete,
    hconnected, hlimit phi L hphi Phi C hdomain hcomplete hconnected⟩

end TerminalReducedVolume

section BackwardSlice

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance backwardSliceFrontierTopology : TopologicalSpace F.M := F.topology
local instance backwardSliceFrontierCharted : ChartedSpace H F.M := F.charted
local instance backwardSliceFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance backwardSliceFrontierT2 : T2Space F.M := F.t2
local instance backwardSliceFrontierTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance backwardSliceFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact

def HasBackwardSliceShrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : F.M) : Prop :=
  ∃ q : ℕ → F.M, backwardSliceApproximateMetricCompactness F hF tau htau q ∧
    backwardSliceLimitGradientShrinker F tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_shrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : F.M)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0))
    (hinput : HasBackwardSliceShrinkerInput F hF tau htau p) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  obtain ⟨q, hcompact, hlimit⟩ := hinput
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker_of_blowdownInput F hF tau htau q p hmono
      hcompact hlimit
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩

end BackwardSlice

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
