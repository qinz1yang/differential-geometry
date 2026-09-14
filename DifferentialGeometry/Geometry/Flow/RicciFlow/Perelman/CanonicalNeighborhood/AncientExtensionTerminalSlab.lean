import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitFrontierInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformScalarBoundProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalScalarEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalShiDerivativeBounds

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem terminalLimitScalarBoundFrontier_of_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X _ _ P hcanon _ _ _ _ _ _ _ => ?_⟩
  obtain ⟨C, _hC, hCbound⟩ := hbound eps heps hle X
  refine ⟨C, fun x => metricScalarAt_limit_le_of_eventually_le P.maps P.convergence.metrics
    hcanon C (fun x => Filter.Eventually.of_forall fun i => ?_) x⟩
  exact hCbound (P.subseq i) (P.maps.partialDiffeomorph i x)

theorem terminal_limit_global_bound_of_compactnessFrontier_and_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hcompact : TerminalLimitCompactnessFrontier.{u} kappa sigma Phi)
    (hscal : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontiers hPhi hcompact
    (terminalLimitScalarBoundFrontier_of_uniformTerminalScalarUpperBoundShell hscal)

theorem uniformTerminalScalarUpperBoundShell_of_harnackCollapseBound_and_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi)
    (hdiam : BoundedDistanceToBasepointShell.{u} kappa sigma Phi)
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (hescape : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi) :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi :=
  uniformTerminalScalarUpperBoundShell_of_boundedDistanceToBasepointShell_and_smallScale_and_noSubsequenceCurvatureEscapeShell
    hdiam (exists_curvatureBoundedWithin_of_harnackCollapseBound hsigma hPhi h) hescape

theorem window_subset_carrier_of_le_modelDepth {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {depthBound : ℝ}
    (hdepth : depthBound ≤ 2 * modelDepth eps) (i : ℕ) :
    Set.Icc (-depthBound) 0 ⊆ (X.interval i).carrier := by
  rw [X.carrier_eq i]
  intro s hs
  have hbuffer := X.depth_buffer i
  exact ⟨by linarith [hs.1], hs.2⟩

theorem terminalSlabBounds_of_uniformRmNormSqBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit X) {depthBound : ℝ}
    (hdepth : depthBound ≤ 2 * modelDepth eps) (h : UniformRmNormSqBound.{u} X) :
    TerminalSlabBounds L depthBound := by
  obtain ⟨K, hK⟩ := h
  intro _K _hKc width _hwidth hwide
  refine ⟨K, ?_⟩
  filter_upwards with i
  intro t ht y _hy
  have hcarrier : t ∈ (X.interval (L.subseq i)).carrier :=
    window_subset_carrier_of_le_modelDepth X hdepth (L.subseq i)
      (Set.Icc_subset_Icc (by linarith : -depthBound ≤ -width) le_rfl ht)
  exact hK (L.subseq i) t hcarrier ((L.maps.partialDiffeomorph i) y)

def TerminalSlabAnalyticShell (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
      ∃ (depthBound : ℝ) (hdepth : depthBound ≤ 2 * modelDepth eps),
        0 < depthBound ∧ ∀ hb : TerminalSlabBounds L depthBound,
          TerminalSlabAnalyticInputs (L.toStatic hdepth hb)

theorem terminalSlabAnalyticShell_of_slabInputShell {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalSlabInputShell.{u} kappa sigma Phi) :
    TerminalSlabAnalyticShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hI⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, hdepth, hb, hdpos, han⟩ := hI eps heps hle X L
  exact ⟨depthBound, hdepth, hdpos, fun hb' => by
    rw [Subsingleton.elim hb' hb]
    exact han⟩

theorem terminalSlabInputShell_iff_terminalSlabAnalyticShell_of_uniformRmNormSqBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi) :
    TerminalSlabInputShell.{u} kappa sigma Phi ↔ TerminalSlabAnalyticShell.{u} kappa sigma Phi := by
  refine ⟨terminalSlabAnalyticShell_of_slabInputShell, fun h => ?_⟩
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  obtain ⟨e₂, he₂, hana⟩ := h
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, hdepth, hdpos, hall⟩ :=
    hana eps heps (le_trans hle (min_le_right e₁ e₂)) X L
  refine ⟨depthBound, hdepth,
    terminalSlabBounds_of_uniformRmNormSqBound L hdepth
      (hrm₁ eps heps (le_trans hle (min_le_left e₁ e₂)) X), hdpos, ?_⟩
  exact hall _

theorem first_backward_slab_of_uniformRmNormSqBoundProducer_and_terminalSlabAnalyticShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (h : TerminalSlabAnalyticShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  obtain ⟨e₂, he₂, hana⟩ := h
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, hdepth, _hdpos, hall⟩ :=
    hana eps heps (le_trans hle (min_le_right e₁ e₂)) X L
  have hb : TerminalSlabBounds L depthBound :=
    terminalSlabBounds_of_uniformRmNormSqBound L hdepth
      (hrm₁ eps heps (le_trans hle (min_le_left e₁ e₂)) X)
  exact first_backward_slab_of_terminal L hdepth hb (hall hb)

theorem not_forall_window_subset_all_carriers {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    ¬ ∀ depthBound : ℝ, 0 < depthBound →
      ∀ i : ℕ, Set.Icc (-depthBound) 0 ⊆ (X.interval i).carrier := by
  intro h
  have hmem : -(4 * X.depth 0 + 1) ∈ (X.interval 0).carrier :=
    h (4 * X.depth 0 + 1) (by linarith [X.depth_pos 0]) 0
      ⟨by linarith, by linarith [X.depth_pos 0]⟩
  rw [X.carrier_eq 0] at hmem
  linarith [hmem.1, X.depth_pos 0]

theorem terminalSlabAnalyticShell_of_uniformRmNormSqBoundProducer_and_terminalSlabJetInputs
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (h : TerminalSlabJetInputs.{u} kappa sigma Phi) :
    TerminalSlabAnalyticShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  obtain ⟨e₂, he₂, hjet⟩ := h
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, delta, hdepth, hb, hd, hdpos, hdle, hexists, hjets, hgeom, hcurv⟩ :=
    hjet eps heps (le_trans hle (min_le_right e₁ e₂)) X L
  refine ⟨depthBound, hdepth, hdpos, fun hb' => ?_⟩
  rw [Subsingleton.elim hb' hb]
  exact ⟨delta, hd, hdle, hexists, slabLimit_isSolutionOn_of_spatialJets _ hdle hjets,
    hgeom, hcurv⟩

theorem exists_terminalLimit_and_backwardExtension_of_frontiers
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hcompact : TerminalLimitCompactnessFrontier.{u} kappa sigma Phi)
    (hscal : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi)
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (hslab : TerminalSlabAnalyticShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X →
          ∃ L : TerminalLimit X, ∃ delta : ℝ, ∃ _hd : 0 < delta,
            Nonempty (BackwardExtension L
              (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨e₁, he₁, h₁⟩ :=
    terminal_limit_global_bound_of_compactnessFrontier_and_uniformTerminalScalarUpperBoundShell
      hPhi hcompact hscal
  obtain ⟨e₂, he₂, h₂⟩ :=
    first_backward_slab_of_uniformRmNormSqBoundProducer_and_terminalSlabAnalyticShell hrm hslab
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X hb hderiv => ?_⟩
  obtain ⟨L⟩ := h₁ eps heps (le_trans hle (min_le_left e₁ e₂)) X hb hderiv
  obtain ⟨delta, hdpos, hB⟩ := h₂ eps heps (le_trans hle (min_le_right e₁ e₂)) X L
  exact ⟨L, delta, hdpos, hB⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
