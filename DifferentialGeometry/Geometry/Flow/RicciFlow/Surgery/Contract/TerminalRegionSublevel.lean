import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalNeckFrontierProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegionSigned
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAllLowBridge

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology (SmoothTwoSidedCollar symmetricOpenInterval)
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
universe u

theorem exists_smoothSphericalRegion_covering_scalar_sublevel_noncompact
    (D : OneStepIncoming.{u}) {ε A : ℝ} (hε : 0 < ε) (hA : 0 < A)
    (y : D.slab.terminalRegularOpen) (hyA : metricScalarAt D.terminal.metric y ≤ A)
    (hnoncompact : ¬ IsCompact (connectedComponent y)) :
    ∃ B : ℝ, A < B ∧ ∃ S : SmoothSphericalRegion D.stage,
      Nonempty (TerminalNeckFrontier D S ε) ∧
      S.region ⊆ Subtype.val '' connectedComponent y ∧
      (∀ x : D.slab.terminalRegularOpen, x ∈ connectedComponent y →
        metricScalarAt D.terminal.metric x ≤ A → x.val ∈ interior S.region) ∧
      (∀ x : D.slab.terminalRegularOpen, x.val ∈ S.region →
        metricScalarAt D.terminal.metric x ≤ B) := by
  obtain ⟨η, hη, hregion⟩ :=
    D.terminal.exists_smoothSphericalRegion_terminal_component_with_signed_collar
  let δ := min η (ε / 2)
  have hδ : 0 < δ := lt_min hη (half_pos hε)
  have hδη : δ ≤ η := min_le_left _ _
  have hδε : δ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  obtain ⟨U, A', hUopen, hUconn, hUcompact, hUcomponent, hUlow, hAA', hApos⟩ :=
    D.terminal.exists_connected_compact_neighborhood_scalar_sublevel_component_with_bound
      (B := q + 1) y hyA
  have hA'pos : 0 < A' := lt_trans hA hAA'
  have hqA' : q < 4 * C2 * A' := by
    have hC2pos : 0 < C2 := lt_of_lt_of_le zero_lt_one hC2
    nlinarith
  obtain ⟨ι, v, neck, level, b, C, S, label, hb, hinteriorconn,
    hyint, hyambient, hcomponent, hSregion, hscalar, hfrontier,
    hfrontierscalar, hSsphere, hnecks⟩ :=
      hregion A' y hA'pos hqA' (hyA.trans hAA'.le) hnoncompact
  have hUscalar : ∀ x ∈ U, metricScalarAt D.terminal.metric x ≤ A' :=
    fun x hx => hApos.2 x (subset_closure hx)
  have hyU : y ∈ U := hUlow ⟨rfl, hyA⟩
  have hyC : y ∈ C := interior_subset hyint
  have hdisj : Disjoint U (frontier C) := by
    apply disjoint_left.mpr
    intro x hxU hxfront
    nlinarith [hUscalar x hxU, hfrontierscalar x hxfront]
  have hUint : U ⊆ interior C :=
    DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      hUconn.isPreconnected ⟨y, hyU, hyC⟩ hdisj
  have hC2sq : 1 ≤ C2 ^ 2 := by nlinarith
  have hAB : A < 8 * C2 ^ 2 * A' := by
    apply hAA'.trans_le
    exact le_mul_of_one_le_left hA'pos.le (by nlinarith)
  have hF : Nonempty (TerminalNeckFrontier D S ε) := by
    classical
    refine ⟨TerminalNeckFrontier.ofSmoothRegion ?_⟩
    intro j
    let i := label.symm j
    obtain ⟨hl, _, _, hclose, hdomain, r, σ, _, hr1, hσ, _, _, _, c, hcr, hcollar⟩ :=
      hnecks i.val i.property
    have hj (z : Sphere 2) :
        (S.sphere j z).val = ((neck i.val).map (z, level i.val)).val := by
      simpa only [i, label.apply_symm_apply] using hSsphere i z
    let c' : SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun z : Sphere 2 => (S.sphere j z).val) :=
      { c with zero_eq := fun z => (c.zero_eq z).trans (hj z).symm }
    have hlower : -3 ≤ level i.val := (abs_le.mp hl).1
    have hupper : level i.val ≤ 3 := (abs_le.mp hl).2
    refine ⟨(neck i.val).cylindricalChart, level i.val, ⟨by linarith, by linarith⟩,
      hdomain, ?_, δ, hδε, hclose, σ, hσ, c', ?_, ?_⟩
    · intro z
      refine ⟨hdomain z (level i.val) ⟨by linarith, by linarith⟩, ?_⟩
      exact (hj z).symm
    · intro p
      have ht := p.2.property
      have hp : level i.val + σ * (p.2 : ℝ) ∈ Icc (-101 : ℝ) 101 := by
        change -c.radius < (p.2 : ℝ) ∧ (p.2 : ℝ) < c.radius at ht
        rcases hσ with rfl | rfl <;> constructor <;> nlinarith
      refine ⟨hdomain p.1 _ hp, ?_⟩
      exact (hcollar p).1
    · intro p
      exact (hcollar p).2.1
  refine ⟨8 * C2 ^ 2 * A', hAB, S, hF, ?_, ?_, ?_⟩
  · rw [hSregion]
    exact image_mono hcomponent
  · intro x hx hxA
    have hxU := hUlow ⟨ConnectedComponents.coe_eq_coe'.mpr hx, hxA⟩
    rw [hSregion, DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
      D.slab.terminalRegularOpen.isOpenEmbedding']
    exact mem_image_of_mem Subtype.val (hUint hxU)
  · intro x hx
    have hxC : x ∈ C := by
      rw [hSregion, Subtype.val_injective.mem_set_image] at hx
      exact hx
    exact hscalar x hxC

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
