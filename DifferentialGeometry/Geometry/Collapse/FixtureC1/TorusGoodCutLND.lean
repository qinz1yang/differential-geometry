import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterRows
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGoodCutOCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGoodCutOCL

/-!
# The produced cut choice `D_R` on the register chain over the flat torus (circle stage non-empty)

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G7. Lane O-FIXTURE-C1 (G7, G8) runs register V4's
enhanced chain with (JA) on the flat T³ with a NON-EMPTY circle stage
(`exists_torus_register_chainEJA_OFC`, `torRegChain_*_OFC`). This file applies the chain kernel of
the closed row lane (O-CL0, `Gaf02ChainEJA.goodCutOn_OCL`, the `D_R` consumed by the heads of
S-LANDING G5) to that chain, for every orientation parameter `oM`:

* the cut choice `D_R` EXISTS on the torus chain (its numerics are those of the register,
  `cut_numerics_OCL`, and `ε_r < 1/2`);
* its facts hold: `Z = ∅` (the zero family of C1 is empty), `slimSet ∪ M₂ = univ`, `M₃ ⊆ X₁`,
  the circle base is `W₁ ∩ R₁`;
* that circle base is NON-EMPTY (the chart of GAF07's base piece at the origin centre maps it onto
  `B(0, 4)`, `gaf07_circle_piece_GAFD`);
* GAF07 over EVERY point of that circle base: the whole fibre `q₀⁻¹(w)` is a smooth embedded
  circle of the torus (`goodCutOn_circle_fibre_OCL`, numerics `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`);
* the circle source of `D_R` is FDC03's circle-bundle domain `circleDomain_EFE`.

What this does NOT cover: the exits records themselves. `ClosedExitsOverU74` needs a source
`S : ClosedChainEZRowsSource_RGC` (a `ClosedModel` of a `CompactCarrier` with the family instance
`ClosedFamilyInstanceC14ZV4`, i.e. the LPA02 joint witness on the torus: layer (iii)), and the plain
data kernel `ExitsKernelU_LND` needs `A0` stages over a `CompactCarrier` (a smooth base surface
for the circle stage); neither exists for `Tor_FXC1` yet.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

section Torus

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  (R : ClosedRegisterV4 (earlyDataSharedV4 K) T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) {Kf : ℕ} {δ εr Λz : ℝ}
  (C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc Kf δ εr Λz) K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage) (registerCadj_RGC K))

/-- **The produced cut choice `D_R` on the register chain over the flat torus**, for every
orientation parameter: it exists (register numerics + `ε_r < 1/2`), the zero region is empty,
`slimSet ∪ M₂ = univ`, `M₃ ⊆ X₁`, the circle base is `W₁ ∩ R₁`, the circle source is the domain of
FDC03's circle bundle, the circle base is NON-EMPTY (GAF07's chart `κ_{j₀}` maps the base piece
onto `B(0, 4)`), and over EVERY point of the circle base the whole fibre `q₀⁻¹(w)` is a smooth
embedded circle of the torus. -/
theorem torRegChain_goodCut_LND (hεr : εr < 1 / 2)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) :
    ∃ D : CutChoiceOn74 C.toGaf02ChainE,
      C.toGaf02ChainE.zeroUnion_ZSP35 = ∅ ∧ D.slimSet ∪ D.M₂ = univ ∧
      D.M₃ ⊆ {x | C.toGaf02ChainE.cutQ_R74 0 x ∈ C.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 (torRegPackets_OFC R hT hlc Kf δ εr Λz).toLocalChartPackets} ∧
      D.circleBaseOpen = gaf07CircleRatio_G47
        (torRegPackets_OFC R hT hlc Kf δ εr Λz).toLocalChartPackets ∩
        C.toChain.finalBase_BAS 0 ∧ D.circleBaseOpen.Nonempty ∧
      D.circleSource = (C.circleDomain_EFE : Set (torRegTorus_OFC R)) ∧
      ∀ w ∈ D.circleBaseOpen, ∃ f : Circle → torRegTorus_OFC R,
        IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧ range f = C.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w} := by
  have hn := R.cut_numerics_OCL hT
  have hrow := R.torus_row_numbers_OFC hT
  have hz : C.toGaf02ChainE.zeroUnion_ZSP35 = ∅ := by
    unfold Gaf02ChainE.zeroUnion_ZSP35
    refine iUnion_eq_empty.2 fun k => ?_
    have hk := (Set.Finite.mem_toFinset _).1 k.2
    exact absurd hk (notMem_empty _)
  have hf := C.goodCutOn_facts_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr hn.1
    hn.2.1 hn.2.2
  have hj := (Set.Finite.mem_toFinset
    (torRegPackets_OFC R hT hlc Kf δ εr Λz).circle.finite_centres
    (a := torRegOrigin_OFC R)).mpr (torRegPackets_origin_mem_OFC R hT hlc)
  have hpc := C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hrow.1 hrow.2 ⟨_, hj⟩
  obtain ⟨w₀, hw₀, -⟩ := hpc.2.surjOn (mem_ball_self (by norm_num) : (0 : ℝ²) ∈ ball 0 4)
  refine ⟨C.goodCutOn_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr hn.1 hn.2.1
    hn.2.2, hz, ?_, hf.2.2.2, rfl, ⟨w₀, mem_iUnion.2 ⟨_, hw₀.2⟩, hw₀.1⟩,
    (C.goodCutOn_circleSource_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr hn.1
      hn.2.1 hn.2.2 hrow.1 hrow.2).1, fun w hw => ?_⟩
  · have key : ∀ Z : Set (torRegTorus_OFC R), Z = ∅ →
        Z ∪ (C.goodCutOn_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr hn.1 hn.2.1
          hn.2.2).slimSet ∪ (C.goodCutOn_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM)
          hεr hn.1 hn.2.1 hn.2.2).M₂ = univ →
        (C.goodCutOn_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr hn.1 hn.2.1
          hn.2.2).slimSet ∪ (C.goodCutOn_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM)
          hεr hn.1 hn.2.1 hn.2.2).M₂ = univ :=
      fun Z hZ h => by rwa [hZ, empty_union] at h
    exact key _ hz hf.2.2.1
  · exact C.goodCutOn_circle_fibre_OCL (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) hεr
      hn.1 hn.2.1 hn.2.2 hrow.1 hrow.2 hw

end Torus

/-- **Consumer on an existing register chain over the torus** (`K_f = 5`, `ε_r = 0`): at the
register of `exists_closedRegisterV4`, on the chain of `exists_torus_register_chainEJA_OFC`, the
produced cut choice `D_R` exists as soon as the torus carries an orientation (the orientation
parameter `oM` of the closed family; none is constructed yet), with a NON-EMPTY circle base over
whose every point the whole fibre of `q₀` is a smooth embedded circle. -/
theorem torC1_goodCut_LND (K : ℕ) :
    ∃ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
      (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T),
        ∃ C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc 5 R.later.circle.γ 0
              (T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
                R.later.split.b R.later.split.β₁ / 20))
              K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
              R.stage.e R.stage.c (stageCwAt_V4C R.stage) (registerCadj_RGC K),
            C.x₀ = torRegOrigin_OFC R ∧
            (Nonempty (ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) →
              ∃ D : CutChoiceOn74 C.toGaf02ChainE, D.circleBaseOpen.Nonempty ∧
                ∀ w ∈ D.circleBaseOpen, ∃ f : Circle → torRegTorus_OFC R,
                  IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
                    range f = C.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w}) := by
  have h0 := exists_torus_register_chainEJA_OFC K
  obtain ⟨T, h1⟩ := h0
  obtain ⟨hT, h2⟩ := h1
  obtain ⟨hlc, h⟩ := h2
  have R : ClosedRegisterV4 (earlyDataSharedV4 K) T :=
    Classical.choice (exists_closedRegisterV4 (earlyDataSharedV4 K) T)
  refine ⟨T, hT, hlc, R, ?_⟩
  have hΛz : 20 * (T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ / 20) ≤ T.T₀Low R.stage R.later.circle R.later.excl
      R.later.err R.later.scale R.later.split.b R.later.split.β₁ := le_of_eq (by ring)
  have hR := h R 5 R.later.circle.γ 0 _ le_rfl R.later.ε₀_pos hΛz (torRegOrigin_OFC R)
  obtain ⟨C, hC, -⟩ := hR
  refine ⟨C, hC, fun ⟨oM⟩ => ?_⟩
  obtain ⟨D, -, -, -, -, hne, -, hf⟩ := torRegChain_goodCut_LND R hT hlc C (by norm_num) oM
  exact ⟨D, hne, hf⟩

end DifferentialGeometry.Geometry.Collapse
