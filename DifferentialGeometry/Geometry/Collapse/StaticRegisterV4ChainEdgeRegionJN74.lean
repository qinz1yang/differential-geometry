import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSaturationJN74

/-!
# Draft 74, FDC03's `edge_region` at `D_R` (field `edge_region` of `JunctionRimFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G9 part 1 (suffix `_JN74`). From the raw FDC03 set geometry
(`mem_relInt_iff_JN74`: `int_{M₂} M^edge = M^edge ∩ {T < 4Δ}`), with no corner record:

* `goodCut_edgeSet_inter_M₃_JN74`: on the actual chain, `M^edge ∩ M₃ = M^edge ∩ {T = 4Δ}`;
* `cut_M₃_at_JN74`: the carried `M₃` is `M.ψ(M₃(D_R))` (the first half of G8's `hsat`);
* **`cut_edgeSet_inter_M₃_eq_vertical_JN74`**: `edge_region` of the rim facts, i.e.
  `P.cut.edgeSet ∩ P.cut.M₃ = (edgeBundle74 P.A P.cut F).vertical` for the produced stage geometry
  `P`, for any edge facts `F` (the vertical face does not depend on the proof fields).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **On the actual chain, `M^edge ∩ M₃ = M^edge ∩ {T = 4Δ}`** (FDC03 (Last): the points of
`M^edge` below the level are in `int_{M₂} M^edge`, the rim points are not). -/
theorem goodCut_edgeSet_inter_M₃_JN74 (A : SmoothStageBases74 S) (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) :
    (S.goodCut_OCL B hT hεr).edgeSet ∩ (S.goodCut_OCL B hT hεr).M₃ =
      {x | x ∈ (S.goodCut_OCL B hT hεr).edgeSet ∧
        S.toE_RGC.toRowsSource_RGC.height x = R.edgeLevel_R74} := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hiff := fun {x : M.X} => Gaf02ChainEJA.mem_relInt_iff_JN74 (C := S.chain) (x := x) A hεr
    R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.2.2.2.1 hE.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2 (S.goodCut_OCL B hT hεr).D₃_eq
    (S.goodCut_OCL B hT hεr).K₃_req (S.goodCut_OCL B hT hεr).K₃_faces
    (S.goodCut_D₃_reg_OCL B hT hεr) (S.goodCut_D₃_bdry_OCL B hT hεr)
  ext x
  constructor
  · rintro ⟨hxE, hx3⟩
    refine ⟨hxE, ?_⟩
    rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74]
    refine le_antisymm (S.chain.cutEdgeSet_height_le_JN74 R.two_le_Δ_EDP23 _ hxE).1
      (not_lt.mp fun hlt => hx3.2 ((hiff).mpr ⟨hxE, hlt⟩))
  · rintro ⟨hxE, hxT⟩
    refine ⟨hxE, hxE.1, fun hrel => ?_⟩
    have h := ((hiff).mp hrel).2
    rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74] at hxT
    exact absurd hxT (ne_of_lt h)

/-- **The carried `M₃` is `M.ψ(M₃(D_R))`** (`M₂_at_OCL`, `edgeSet_at_OCL`, `relInt_image_R74`). -/
theorem cut_M₃_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ = M.ψ '' (S.goodCut_OCL B hT hεr).M₃ := by
  have hE := S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw
  change (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ \
    relInt (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet = _
  rw [S.M₂_at_OCL B hT hεr A zero, S.edgeSet_at_OCL B hT hεr A zero hE,
    relInt_image_R74 M.ψ, ← image_sdiff (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective]
  rfl

/-- **`edge_region` of the rim facts at `D_R`**: `M^edge ∩ M₃ = V_e` for the carried cut, where
`V_e = {x ∈ source | f₂ x ∈ C₂, T x = 4Δ}` is the vertical face of the rows' edge bundle (which
does not depend on the proof fields `F` of the edge facts). -/
theorem cut_edgeSet_inter_M₃_eq_vertical_JN74 (A : SmoothStageBases74 S)
    (zero : ZSP02SmoothExit74 S) (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet ∩
        (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).vertical := by
  have hE := S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw
  have hES := S.edgeSet_at_OCL B hT hεr A zero hE
  rw [hES, S.cut_M₃_at_JN74 B hT hεr A zero hNb hcw,
    ← image_inter (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective,
    S.goodCut_edgeSet_inter_M₃_JN74 B hT hεr A hNb hcw]
  ext y
  constructor
  · rintro ⟨x, ⟨hxE, hxH⟩, rfl⟩
    have hy : M.ψ x ∈ (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet := by
      rw [hES]
      exact ⟨x, hxE, rfl⟩
    obtain ⟨hpar, hproj, hhgt⟩ := hy
    have hsrc : M.ψ x ∈ (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource :=
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet_subset_edgeSource ⟨hpar, hproj, hhgt⟩
    refine ⟨⟨M.ψ x, hsrc⟩, ⟨hproj, ?_⟩, rfl⟩
    change (S.closedStagesAt_OCL B hT hεr A zero).A.edge.height ⟨M.ψ x, hpar⟩ =
      (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level
    rw [(S.closedStagesAt_OCL B hT hεr A zero).edge_level,
      (S.closedStagesAt_OCL B hT hεr A zero).edge_height ⟨M.ψ x, hpar⟩, M.ψ.symm_apply_apply]
    exact hxH
  · rintro ⟨⟨y, hsrc⟩, ⟨hproj, hh⟩, rfl⟩
    have hy : y ∈ (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet := by
      refine ⟨(S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictParent_le _ hsrc, hproj, ?_⟩
      exact le_of_eq hh
    rw [hES] at hy
    obtain ⟨x, hxE, rfl⟩ := hy
    refine ⟨x, ⟨hxE, ?_⟩, rfl⟩
    have h2 := (S.closedStagesAt_OCL B hT hεr A zero).edge_height
      ⟨M.ψ x, (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictParent_le _ hsrc⟩
    rw [M.ψ.symm_apply_apply] at h2
    rw [← h2, ← (S.closedStagesAt_OCL B hT hεr A zero).edge_level]
    exact hh

/-- **The rim facts of the produced stage geometry from the three remaining primitives**
(`rimBase` with its smoothness and the whole-fibre equality, and the corner model `local_faces`
of `C₁`): the field `edge_region` is PRODUCED by `cut_edgeSet_inter_M₃_eq_vertical_JN74`
(O-CL1's head `rims`, with the explicit primitives listed as the remaining gaps h1 / h2 / h3 /
h5 of the residual table). -/
def junctionRimFacts_ofPrimitives_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (rimBase : Rw.edge.Base → Rw.circle.Base)
    (rimBase_smooth : ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase Rw.edge.cbase)
    (rim_fibre : ∀ c ∈ Rw.edge.cbase, Rw.edge.rim c = Rw.circle.fibre (rimBase c))
    (local_faces : ∀ c ∈ frontier Rw.circle.cbase, ∃ U : TopologicalSpace.Opens Rw.circle.Base,
      c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel Rw.slimPieces.ResidualFace Rw.edge.EdgeBaseComponent →
          Rw.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧
              Rw.circle.fibre c' ⊆ circleFaceSet Rw.slimPieces Rw.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        Rw.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}) :
    JunctionRimFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut Rw where
  rimBase := rimBase
  rimBase_smooth := rimBase_smooth
  rim_fibre := rim_fibre
  edge_region := S.cut_edgeSet_inter_M₃_eq_vertical_JN74 B hT hεr A zero hNb hcw Rw.edgeFacts
  local_faces := local_faces

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
