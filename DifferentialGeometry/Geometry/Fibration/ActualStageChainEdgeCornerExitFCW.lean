import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# EDP05 / FDC03: a regular horizontal-vertical corner is a limit of points of `M₂` above the rim

Lane S-FC-WRAP3, group G11 (suffix `_FCW`). Blueprint `master207B.tex`, EDP05 (B:7040–7090) and
FDC03 (B:7341–7344): "for a point of `M^edge` the relative interior in (Last) is characterized by
`T < 4Δ`". Away from `∂M₂` this is `height_lt_of_mem_interior_EFC`; at the horizontal faces it
needs EDP05's face charts. This module is the face case:

* `exists_nonneg_gt_near_FCW` (kernel, boundaryless model): if `(dF, dT)` is onto `ℝ²` at `x` and
  `F x ≥ 0`, every neighbourhood of `x` contains `y` with `F y ≥ 0` and `T y > T x`
  (a submersion maps neighbourhoods to neighbourhoods);
* `Gaf02ChainEJA.edge_corner_exit_FCW` (binding): at a point `x ∈ ∂M₂` of the edge source with
  `T x = 4Δ`, every neighbourhood of `x` contains a point of `M₂` of the edge source with
  `T > 4Δ` (EDP05's descended defining function `F = hh ∘ π₂E` with `M₂ = {F ≥ 0}` over
  `{π₂E ∈ N}` and `edge_corner_independence_EFE`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **A regular corner point is a limit of points with `0 ≤ F` and larger `T`** (generic,
boundaryless model): if `(dF, dT)` is onto `ℝ²` at `x` and `F x ≥ 0`, every neighbourhood of `x`
contains `y` with `F y ≥ 0` and `T y > T x`. -/
theorem exists_nonneg_gt_near_FCW {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] {F T : M → ℝ} {x : M}
    (hF : ContMDiffAt I 𝓘(ℝ, ℝ) 1 F x) (hT : ContMDiffAt I 𝓘(ℝ, ℝ) 1 T x)
    (hs : Surjective (fun v : TangentSpace I x =>
      (mfderiv I 𝓘(ℝ, ℝ) F x v, mfderiv I 𝓘(ℝ, ℝ) T x v)))
    (hF0 : 0 ≤ F x) {O : Set M} (hO : O ∈ 𝓝 x) : ∃ y ∈ O, 0 ≤ F y ∧ T x < T y := by
  have hf : ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 1 (fun y => (F y, T y)) x := hF.prodMk hT
  have hd : mfderiv I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (fun y => (F y, T y)) x =
      (mfderiv I 𝓘(ℝ, ℝ) F x).prod (mfderiv I 𝓘(ℝ, ℝ) T x) :=
    mfderiv_prodMk (hF.mdifferentiableAt one_ne_zero) (hT.mdifferentiableAt one_ne_zero)
  have hsurj : Surjective (mfderiv I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (fun y => (F y, T y)) x) := by
    rw [hd]
    exact hs
  have hmap := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at hf hsurj
  have hS : (fun y => (F y, T y)) '' O ∈ 𝓝 (F x, T x) := by
    rw [← hmap]
    exact image_mem_map hO
  have hc : Tendsto (fun t : ℝ => (F x + t, T x + t)) (𝓝 0) (𝓝 (F x, T x)) := by
    have : Continuous (fun t : ℝ => (F x + t, T x + t)) := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨t, ht, htp⟩ := (((hc.eventually hS).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  obtain ⟨y, hyO, hy⟩ := ht
  have h1 : F y = F x + t := congrArg Prod.fst hy
  have h2 : T y = T x + t := congrArg Prod.snd hy
  exact ⟨y, hyO, by rw [h1]; linarith [htp], by rw [h2]; linarith [htp]⟩


variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Exit

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **A corner point of `∂M₂` at the rim is a limit of points of `M₂` above the rim** (see the
module docstring). -/
theorem edge_corner_exit_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    {x : X} (hxF : x ∈ frontier (edgeM2_EFE C K₃)) (hxs : x ∈ C.edgeSource_EFE)
    (hxT : C.edgeHeight_EFE ⟨x, hxs⟩ = 4 * Δ) {O : Set X} (hO : O ∈ 𝓝 x) :
    ∃ y ∈ O, y ∈ edgeM2_EFE C K₃ ∧ ∃ hys : y ∈ C.edgeSource_EFE,
      4 * Δ < C.edgeHeight_EFE ⟨y, hys⟩ := by
  obtain ⟨hxM, N, hN, hxN, hh, hhN, hdef, F, hF, hFne, hFeq⟩ :=
    C.edge_face_data_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hxF
  have hzero := eq_zero_of_mem_frontier_of_descended_EFE
    C.toGaf02ChainE.continuous_edgeBlockProj_EFE hN hhN.continuousOn hdef hxF hxM hxN
  have hreg := C.toGaf02ChainE.edge_regular_face_base_EFE A _ hN hhN hdef hFeq ⟨x, hxs⟩ hxN hFne
    hzero
  have hci := C.toGaf02ChainE.edge_corner_independence_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1
    ⟨x, hxs⟩ hxT
  have hdesc := C.toGaf02ChainE.edge_descended_mfderiv_EFE A hN hhN hFeq ⟨x, hxs⟩ hxN
  let _ := A.edgeChartedSpace1
  have hbsm := hdesc.1
  have hsurj := hci (fun cc => hh (C.edgeValB_EFE cc)) (hbsm.mdifferentiableAt (by simp))
    hreg.1
  have hFsm : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) 1
      ((fun cc => hh (C.edgeValB_EFE cc)) ∘ C.edgeProj_EFE) ⟨x, hxs⟩ :=
    (hbsm.comp (⟨x, hxs⟩ : C.edgeSource_EFE)
      ((C.edgeProj_contMDiff_EFE A) (⟨x, hxs⟩ : C.edgeSource_EFE))).of_le
      (by exact_mod_cast le_top)
  have hTsm : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) 1 C.edgeHeight_EFE ⟨x, hxs⟩ :=
    ((C.toGaf02ChainE.contMDiff_edgeHeightGlobal_EFE.comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, E3))))
        (⟨x, hxs⟩ : C.edgeSource_EFE)).of_le (by exact_mod_cast le_top)
  have hO' : Subtype.val ⁻¹' (O ∩ {z | C.toGaf02ChainE.edgeBlockProj_EFE z ∈ N}) ∈
      𝓝 (⟨x, hxs⟩ : C.edgeSource_EFE) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hO
      (C.toGaf02ChainE.continuous_edgeBlockProj_EFE.continuousAt.preimage_mem_nhds
        (hN.mem_nhds hxN)))
  obtain ⟨y, hyO, hy0, hyT⟩ := exists_nonneg_gt_near_FCW hFsm hTsm hsurj (le_of_eq hzero.symm) hO'
  exact ⟨y.1, hyO.1, (hdef y.1 hyO.2).mpr hy0, y.2, lt_of_eq_of_lt hxT.symm hyT⟩

end Exit

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
