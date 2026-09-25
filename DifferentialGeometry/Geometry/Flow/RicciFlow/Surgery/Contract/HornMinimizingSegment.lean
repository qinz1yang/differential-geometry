import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornEndpointRadius
import DifferentialGeometry.Geometry.Metric.Distance.SeparatingMinimizer

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.SphereSeparation

universe u
variable {D : OneStepIncoming.{u}} {eps Lambda : ℝ} (P : TerminalCorePresentation D eps Lambda)

theorem exists_minimizing_segment_across_horn_sides
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set positiveHornDomain} (d : ComplementPair S)
    (hleft : S ⊆ closure d.left) (hright : S ⊆ closure d.right)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ S)
    {A Tlo Thi : ℝ} (hA : 0 < A) (hTlo : 0 < Tlo)
    (hcompact : IsCompact (riemannianClosedBallOf D.terminal.metric
      (P.horn c e (y, s)) (3 * A + 1)))
    (hcapture : riemannianClosedBallOf D.terminal.metric
      (P.horn c e (y, s)) (3 * A) ⊆ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hbase : ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, 0)))
    (hlow : ∀ z : positiveHornDomain, z.val.2 < Tlo → z ∈ d.left)
    (hhigh : ∀ z : positiveHornDomain, Thi < z.val.2 → z ∈ d.right) :
    ∃ a b : positiveHornDomain, a ∈ d.left ∧ b ∈ d.right ∧
      riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
        (P.positiveHornMap c e a) = ENNReal.ofReal A ∧
      riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
        (P.positiveHornMap c e b) = ENNReal.ofReal A ∧
      ∃ gamma : ℝ → D.slab.terminalRegularOpen,
        let length := (riemannianEDistOf D.terminal.metric
          (P.positiveHornMap c e a) (P.positiveHornMap c e b)).toReal
        gamma 0 = P.positiveHornMap c e a ∧ gamma length = P.positiveHornMap c e b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ gamma (Icc 0 length) ∧
        (∀ t ∈ Icc 0 length, gamma t ∈ riemannianClosedBallOf D.terminal.metric
          (P.horn c e (y, s)) (3 * A)) ∧
        (∀ t ∈ Icc 0 length, ∀ u ∈ Icc 0 length,
          riemannianEDistOf D.terminal.metric (gamma t) (gamma u) = ENNReal.ofReal |t - u|) ∧
        ∃ t ∈ Icc 0 length, gamma t ∈ P.positiveHornMap c e '' S := by
  have hKsmall : IsCompact (riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) A) :=
    hcompact.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist D.terminal.metric _) continuous_const)
      (riemannianClosedBallOf_mono _ _ (by linarith))
  obtain ⟨a, b, ha, hb, hdistA, hdistB⟩ := P.exists_horn_side_points_at_distance
    c e d hleft hright y hs hcenter hA hTlo hKsmall hbase hlow hhigh
  let _ : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)
  have hU : riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) (3 * A) ⊆
      (P.positiveHornMap_local c e).image := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hcapture hz
    exact ⟨⟨w, hw⟩, hwz⟩
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hmin, hcross⟩ :=
    exists_minimizing_segment_across_open_embedding_sides D.terminal.metric
      (P.positiveHornMap_local c e).image (P.positiveHornDiffeomorph c e).toHomeomorph
      d (P.horn c e (y, s)) a b ha hb hA.le hdistA.le hdistB.le hcompact hU
  exact ⟨a, b, ha, hb, hdistA, hdistB, gamma, hstart, hend, hsmooth, hmem, hmin, hcross⟩

theorem exists_minimizing_segment_across_scaled_horn_sides
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set positiveHornDomain} (d : ComplementPair S)
    (hleft : S ⊆ closure d.left) (hright : S ⊆ closure d.right)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ S)
    (Q : ℝ) (hQ : 0 < Q) {A Tlo Thi : ℝ} (hA : 0 < A) (hTlo : 0 < Tlo)
    (hcompact : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) (3 * A + 1)))
    (hcapture : riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) (3 * A) ⊆ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hbase : ENNReal.ofReal A < riemannianEDistOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) (P.horn c e (y, 0)))
    (hlow : ∀ z : positiveHornDomain, z.val.2 < Tlo → z ∈ d.left)
    (hhigh : ∀ z : positiveHornDomain, Thi < z.val.2 → z ∈ d.right) :
    ∃ a b : positiveHornDomain, a ∈ d.left ∧ b ∈ d.right ∧
      riemannianEDistOf (scaleMetric Q hQ D.terminal.metric) (P.horn c e (y, s))
        (P.positiveHornMap c e a) = ENNReal.ofReal A ∧
      riemannianEDistOf (scaleMetric Q hQ D.terminal.metric) (P.horn c e (y, s))
        (P.positiveHornMap c e b) = ENNReal.ofReal A ∧
      ∃ gamma : ℝ → D.slab.terminalRegularOpen,
        let length := (riemannianEDistOf (scaleMetric Q hQ D.terminal.metric)
          (P.positiveHornMap c e a) (P.positiveHornMap c e b)).toReal
        gamma 0 = P.positiveHornMap c e a ∧ gamma length = P.positiveHornMap c e b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ gamma (Icc 0 length) ∧
        (∀ t ∈ Icc 0 length, gamma t ∈ riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
          (P.horn c e (y, s)) (3 * A)) ∧
        (∀ t ∈ Icc 0 length, ∀ u ∈ Icc 0 length,
          riemannianEDistOf (scaleMetric Q hQ D.terminal.metric) (gamma t) (gamma u) =
            ENNReal.ofReal |t - u|) ∧
        ∃ t ∈ Icc 0 length, gamma t ∈ P.positiveHornMap c e '' S := by
  have hKsmall : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) A) :=
    hcompact.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist (scaleMetric Q hQ D.terminal.metric) _) continuous_const)
      (riemannianClosedBallOf_mono _ _ (by linarith))
  obtain ⟨a, b, ha, hb, hdistA, hdistB⟩ := P.exists_horn_side_points_at_scaled_distance
    c e d hleft hright y hs hcenter Q hQ hA hTlo hKsmall hbase hlow hhigh
  let _ : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)
  have hU : riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) (3 * A) ⊆ (P.positiveHornMap_local c e).image := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hcapture hz
    exact ⟨⟨w, hw⟩, hwz⟩
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hmin, hcross⟩ :=
    exists_minimizing_segment_across_open_embedding_sides (scaleMetric Q hQ D.terminal.metric)
      (P.positiveHornMap_local c e).image (P.positiveHornDiffeomorph c e).toHomeomorph
      d (P.horn c e (y, s)) a b ha hb hA.le hdistA.le hdistB.le hcompact hU
  exact ⟨a, b, ha, hb, hdistA, hdistB, gamma, hstart, hend, hsmooth, hmem, hmin, hcross⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
