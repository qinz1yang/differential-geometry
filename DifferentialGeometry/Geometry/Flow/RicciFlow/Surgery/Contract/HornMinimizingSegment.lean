import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornEndpointRadius
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer

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
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hmin⟩ :=
    exists_distance_parametrized_minimizer_in_closedBall D.terminal.metric
      (P.horn c e (y, s)) (P.positiveHornMap c e a) (P.positiveHornMap c e b)
      hA.le hdistA.le hdistB.le hcompact
  refine ⟨a, b, ha, hb, hdistA, hdistB, gamma, hstart, hend, hsmooth, hmem, hmin, ?_⟩
  let length := (riemannianEDistOf D.terminal.metric
    (P.positiveHornMap c e a) (P.positiveHornMap c e b)).toReal
  have hlength : 0 ≤ length := ENNReal.toReal_nonneg
  let E := P.positiveHornDiffeomorph c e
  have hmemImage (t : ℝ) (ht : t ∈ Icc 0 length) :
      gamma t ∈ (P.positiveHornMap_local c e).image := by
    obtain ⟨z, hz, heq⟩ := hcapture (hmem t ht)
    exact ⟨⟨z, hz⟩, heq⟩
  let G : ℝ → (P.positiveHornMap_local c e).image := fun t =>
    ⟨gamma (projIcc 0 length hlength t), hmemImage _ (projIcc 0 length hlength t).property⟩
  let lifted : ℝ → positiveHornDomain := fun t => E.symm (G t)
  have hGc : Continuous G :=
    (((hsmooth.continuousOn.domRestrict).comp continuous_projIcc).subtype_mk _)
  have hcont : Continuous lifted := E.symm.continuous.comp hGc
  have hround (t : ℝ) (ht : t ∈ Icc 0 length) : P.positiveHornMap c e (lifted t) = gamma t := by
    have hh := congrArg Subtype.val (E.apply_symm_apply (G t))
    change P.positiveHornMap c e (lifted t) = gamma (projIcc 0 length hlength t) at hh
    simpa only [projIcc_of_mem hlength ht] using hh
  have hstartLift : lifted 0 = a :=
    (P.horn_interior_embedding c e).isEmbedding.injective
      ((hround 0 ⟨le_rfl, hlength⟩).trans hstart)
  have hendLift : lifted length = b :=
    (P.horn_interior_embedding c e).isEmbedding.injective
      ((hround length ⟨hlength, le_rfl⟩).trans hend)
  have hcross : ∃ t ∈ Icc 0 length, lifted t ∈ S := by
    by_contra hnone
    have havoid : lifted '' Icc 0 length ⊆ Sᶜ := by
      rintro z ⟨t, ht, rfl⟩ hS
      exact hnone ⟨t, ht, hS⟩
    rcases d.subset_left_or_subset_right
      (isPreconnected_Icc.image lifted hcont.continuousOn) havoid with hl | hr
    · exact disjoint_left.mp d.disjoint
        (hendLift ▸ hl ⟨length, ⟨hlength, le_rfl⟩, rfl⟩) hb
    · exact disjoint_left.mp d.disjoint ha
        (hstartLift ▸ hr ⟨0, ⟨le_rfl, hlength⟩, rfl⟩)
  obtain ⟨t, ht, htS⟩ := hcross
  exact ⟨t, ht, lifted t, htS, hround t ht⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
