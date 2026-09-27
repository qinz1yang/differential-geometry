import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

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

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reductionSourceTopology : TopologicalSpace F.M := F.topology
local instance reductionSourceCharted : ChartedSpace H F.M := F.charted
local instance reductionSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance reductionSourceT2 : T2Space F.M := F.t2
local instance reductionSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one
    (hE : Module.finrank ℝ E ≤ 1) (t : ℝ) (x : F.M) :
    F.rmNormSq t x = 0 := by
  have hzero : F.S.base.rm04 t x = 0 := by
    simpa only [SolutionFamily.rm04, metricRm04_apply] using
      metricRm04At_eq_zero_of_finrank_le_one (I := I) (M := F.M) (F.S.base.metric t) hE x
  rw [PointedFlowData.rmNormSq, hzero]
  simp only [SolutionOn.family_metric]
  simp [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S,
    Tensor0SBundle.MetricFiberData.inner]

theorem not_isAncientKappaSolution_of_finrank_le_one
    {kappa : ℝ} (hE : Module.finrank ℝ E ≤ 1) :
    ¬ IsAncientKappaSolution kappa F := by
  intro hF
  obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
  exact hx (ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one F hE t x)

theorem two_le_finrank_of_isAncientKappaSolution
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    2 ≤ Module.finrank ℝ E := by
  by_contra h
  exact not_isAncientKappaSolution_of_finrank_le_one F (by omega) hF

theorem neZero_finrank_of_isAncientKappaSolution
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    NeZero (Module.finrank ℝ E) :=
  ⟨by have h := two_le_finrank_of_isAncientKappaSolution F hF; omega⟩

theorem ancient_reducedVolume_antitone_of_finrank_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hE : Module.finrank ℝ E ≤ 1) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) :=
  (not_isAncientKappaSolution_of_finrank_le_one F hE hF).elim

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_terminalLimits
    (p : F.M)
    (hregular : ∀ T : ℝ, T < 0 →
      AntitoneOn (intrinsicReducedVolume F.S T p) (Ioi 0))
    (hlower : ∀ tau ∈ Ioi 0,
      intrinsicReducedVolume F.S 0 p tau ≤
        liminf (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)))
    (hupper : ∀ tau ∈ Ioi 0,
      limsup (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)) ≤
        intrinsicReducedVolume F.S 0 p tau) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  have hcompare : ∀ᶠ T in 𝓝[<] (0 : ℝ),
      intrinsicReducedVolume F.S T p tau2 ≤ intrinsicReducedVolume F.S T p tau1 := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact (hregular T hT) h1 h2 h12
  have hliminf := Filter.liminf_le_liminf hcompare
  have hlimsup := Filter.liminf_le_limsup (f := 𝓝[<] (0 : ℝ))
    (u := fun T : ℝ => intrinsicReducedVolume F.S T p tau1)
  exact (hlower tau2 h2).trans (hliminf.trans (hlimsup.trans (hupper tau1 h1)))

section NormalizedShrinker

variable [NeZero (Module.finrank ℝ E)]

theorem exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hcost : ∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2)
    (hcompact : backwardSliceApproximateMetricCompactness F hF tau htau q)
    (hlimit : ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
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
       (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ)
           (v w : Fin n → TangentSpace I x),
         0 ≤ ∑ i, ∑ j,
           c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯,
         gradientRicciSoliton L.metric f 1 ∧
         IsHamiltonNormalizedPotential L.metric f ∧
         Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
           atTop (𝓝 (normalizedShrinkerMass L.metric f)))) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
            (backwardSliceSequence F tau htau q) L phi)
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
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ)
             (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j,
             c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q hcompact
  obtain ⟨hnonflat, hnco, hlimit⟩ := hlimit phi L hphi Phi C hdomain hcomplete hconnected
  exact ⟨q, L, phi, hphi, hcost, Phi, C, hdomain, hcomplete,
    hconnected, hnonflat, hnco, hlimit⟩

end NormalizedShrinker

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
