import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseEFE
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube

/-!
# EDP06: saturation of `M₂ ∩ X₁`, the corner descent on the circle base and the rim, group G10

Lane S-EDP-FDC4, group G10. Blueprint `master207B.tex`, EDP06 (B:7092–7133). On the final-family
chain `C : Gaf02ChainEJA …` with the abstract circle base `B₁ = W₁ ∩ R₁` (`circleBaseOpens_EFE`,
projection `circleProj_EFE = π₁E`, G6) and the edge data of G9 / G11:

* `edp06_saturation_EFE` (B:7118–7122, "`M₂ ∩ X₁` is saturated by whole connected circle fibers"):
  a point of `X₁` on a circle fibre meeting `M₂` lies in `M₂` (connected fibre meets `∂M₂`; the
  whole `π₂E`-fibre through a point of `∂M₂` lies in `M₂`);
* `edge_rim_point_EFE`: over every point of `B₂` the rim `{T = 4Δ}` is nonempty (the boundary
  circle of the whole disk);
* `circle_descent_EFE` (**layer 1 of D74-14, the field `desc` of `CornerDescent74`**): `T − 4Δ` and
  `F = hh ∘ π₂E` descend to smooth `Tb`, `hb` on a patch `V` of `B₁` around `π₁E q₀`, on the WHOLE
  preimage of `V`, which lies in the edge source;
* `edge_corner_rank_raw_EFE` (**field `rank` of `CornerRank74`**, generic form): at a rim point
  with `db ≠ 0` the pair `(T − 4Δ, F)` has onto differential into `ℝ × ℝ`;
* `edge_rim_fibre_in_source_EFE`: the whole circle fibre through a rim point lies in the edge
  source;
* `edp06_corner_EFE`: at an endpoint `c₀` of `C₂` and a rim point `q₀ ∈ X₁` over it, the face data
  of G11, the rank, and the descent with `Tb = hb = 0` at `π₁E q₀`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- A preconnected set meeting `t` and `tᶜ` meets the frontier of `t`. -/
theorem inter_frontier_nonempty_of_isPreconnected_EFE {Y : Type*} [TopologicalSpace Y]
    {s t : Set Y} (hs : IsPreconnected s) (h1 : (s ∩ t).Nonempty) (h2 : (s ∩ tᶜ).Nonempty) :
    (s ∩ frontier t).Nonempty := by
  have hcov : s ⊆ closure t ∪ closure tᶜ := fun y _ => by
    by_cases hy : y ∈ t
    · exact Or.inl (subset_closure hy)
    · exact Or.inr (subset_closure hy)
  obtain ⟨y, hys, hyt⟩ := isPreconnected_closed_iff.mp hs _ _ isClosed_closure isClosed_closure hcov
    (h1.mono (inter_subset_inter_right _ subset_closure))
    (h2.mono (inter_subset_inter_right _ subset_closure))
  exact ⟨y, hys, by rw [frontier_eq_closure_inter_closure]; exact hyt⟩

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **The rim is nonempty over every point of `B₂`**: the boundary circle of the whole disk
(`edgeBase_fibre_disk_EDP23`) lies in `{T = 4Δ}`. -/
theorem edge_rim_point_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (cc : Ĉ.edgeBaseOpens_EFE) :
    ∃ x : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE x = cc ∧ Ĉ.edgeHeight_EFE x = 4 * Δ := by
  have hw : (cc : Ĉ.toChain.finalBase_BAS 1).1 ∈ Ĉ.edgeBase_EDP23 := ⟨cc.1.2, cc.2⟩
  obtain ⟨φ, -, -, hbd⟩ := Ĉ.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
    hβc1 hw
  have hx : (φ ∘ cellBoundaryInclusion 2) ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), by simp⟩ ∈
      range (φ ∘ cellBoundaryInclusion 2) := mem_range_self _
  rw [hbd] at hx
  obtain ⟨h1, h2⟩ := hx
  have hys : (φ (cellBoundaryInclusion 2 ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), by simp⟩)) ∈
      Ĉ.edgeSource_EFE := Ĉ.mem_edgeSource_EFE hΔ2 (h1 ▸ cc.2) h2.le
  refine ⟨⟨_, hys⟩, Subtype.ext (Subtype.ext h1), h2⟩

/-- **The rank of `(T − 4Δ, F)` at a rim point, ambient form** (field `rank` of `CornerRank74`;
EDP04's rank two + `db ≠ 0`): for `F = hh ∘ π₂E` with `hh` smooth on `N ∋ π₂E x`, `T x = 4Δ` and
`d(hh ∘ ι)(f₂ x) ≠ 0`, the differential of `y ↦ (T y − 4Δ, F y)` at `x` is onto `ℝ × ℝ`. -/
theorem edge_corner_rank_raw_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N) (x : Ĉ.edgeSource_EFE) (hxN : Ĉ.edgeBlockProj_EFE x.1 ∈ N)
    (hT : Ĉ.edgeHeight_EFE x = 4 * Δ) :
    let _ := A.edgeChartedSpace1
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x) ≠ 0 →
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
      (fun y : X => (Ĉ.edgeHeightGlobal_EFE y - 4 * Δ, hh (Ĉ.edgeBlockProj_EFE y))) x.1) := by
  intro _ hdb
  obtain ⟨hbsm, -⟩ := Ĉ.edge_descended_mfderiv_EFE A hN hhN
    (F := fun y => hh (Ĉ.edgeBlockProj_EFE y)) (fun _ => rfl) x hxN
  have hpair := Ĉ.edge_corner_independence_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hT _
    (hbsm.mdifferentiableAt (by simp)) hdb
  have hTg := Ĉ.contMDiff_edgeHeightGlobal_EFE
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => hh (Ĉ.edgeBlockProj_EFE y)) x.1 :=
    ((hhN.contDiffAt (hN.mem_nhds hxN)).contMDiffAt).comp x.1
      ((Ĉ.contMDiff_edgeBlockProj_EFE A) x.1)
  have hT' : ∀ w, mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeight_EFE x w =
      mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 w := fun w => by
    have h1 : mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeight_EFE x =
        mvfderiv 𝓘(ℝ, E3) Ĉ.edgeHeightGlobal_EFE x.1 :=
      mvfderiv_comp_subtype_val_EFE Ĉ.edgeSource_EFE (fun _ => rfl) x
        (hTg.contMDiffAt.mdifferentiableAt (by simp))
    rw [h1]
    rfl
  have hF' : ∀ w, mvfderiv 𝓘(ℝ, E3) ((fun cc => hh (Ĉ.edgeValB_EFE cc)) ∘ Ĉ.edgeProj_EFE) x w =
      mvfderiv 𝓘(ℝ, E3) (fun y => hh (Ĉ.edgeBlockProj_EFE y)) x.1 w := fun w => by
    have h1 : mvfderiv 𝓘(ℝ, E3) (fun z : Ĉ.edgeSource_EFE => hh (Ĉ.edgeBlockProj_EFE z.1)) x =
        mvfderiv 𝓘(ℝ, E3) (fun y => hh (Ĉ.edgeBlockProj_EFE y)) x.1 :=
      mvfderiv_comp_subtype_val_EFE Ĉ.edgeSource_EFE (fun _ => rfl) x
        (hF.mdifferentiableAt (by simp))
    rw [← h1]
    rfl
  refine surjective_mfderiv_pair_EFE (hTg.contMDiffAt.sub contMDiffAt_const) hF (fun y => ?_)
  obtain ⟨v, hv⟩ := hpair (y.2, y.1)
  refine ⟨v, ?_, ?_⟩
  · rw [mvfderiv_sub_const_EFE (hTg.contMDiffAt.mdifferentiableAt (by simp))]
    exact (hT' v).symm.trans (congrArg Prod.snd hv)
  · exact (hF' v).symm.trans (congrArg Prod.fst hv)

end Gaf02ChainE

namespace Gaf02ChainEJA

section Rim

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **EDP06: `M₂ ∩ X₁` is saturated by whole circle fibres** (B:7118–7122). -/
theorem edp06_saturation_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (hεr : εr < 1 / 2)
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
    (x y : C.circleDomain_EFE) (hxy : C.circleProj_EFE y = C.circleProj_EFE x)
    (hx : (x : X) ∈ edgeM2_EFE C K₃) : (y : X) ∈ edgeM2_EFE C K₃ := by
  by_contra hy
  have hFc : IsPreconnected (Subtype.val '' {z : C.circleDomain_EFE |
      C.circleProj_EFE z = C.circleProj_EFE x}) :=
    ((C.circleProj_connected_EFE hβ hd (C.circleProj_EFE x)).isPreconnected).image _
      continuous_subtype_val.continuousOn
  obtain ⟨x', ⟨z, hz, rfl⟩, hx'fr⟩ := inter_frontier_nonempty_of_isPreconnected_EFE hFc
    ⟨x, ⟨x, rfl, rfl⟩, hx⟩ ⟨y, ⟨y, hxy, rfl⟩, hy⟩
  have hπ0 : ∀ w, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection w = w :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  have hE : C.toChain.E y.1 = C.toChain.E z.1 := by
    have h1 : C.circleProj_EFE y = C.circleProj_EFE z := hxy.trans hz.symm
    have h2 := congrArg (fun v : C.circleBaseOpens_EFE => ((v : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) h1
    change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y.1) =
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E z.1) at h2
    rwa [hπ0, hπ0] at h2
  have hyz : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E y.1) =
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z.1) := by
    rw [hE]
  have hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier :=
    (C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).1
  rcases C.frontier_cutM2_cases_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hx'fr with
    ⟨k, hk, hK⟩ | ⟨y₀, hy₀, hyC, hxy₀⟩
  · exact hy (C.toGaf02ChainE.edge_zero_fibre_subset_M2_EFE hεr K₃.carrier k hk hK hyz).2
  · exact hy ((C.edge_slim_face_descent_EFE hεr K₃ D₃ hSD hy₀ hyC hxy₀).1 y.1 hyz)

/-- **Corner descent on the circle base (layer 1 of D74-14)**: let `F = hh ∘ π₂E` with `hh` smooth
on an open `N ∋ π₂E q₀`, and let the whole circle fibre through `q₀ ∈ X₁` lie in the edge source.
Then on a patch `V ∋ π₁E q₀` of `B₁` the functions `Tb = T̃ − 4Δ` and `hb = hh ∘ π₂` are smooth,
the WHOLE preimage of `V` lies in the edge source and in `{π₂E ∈ N}`, and
`T − 4Δ = Tb ∘ π₁E`, `F = hb ∘ π₁E` on it. -/
theorem circle_descent_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    {N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N) (x₀ : C.circleDomain_EFE)
    (hx₀N : C.edgeBlockProj_EFE x₀.1 ∈ N)
    (hfib : ∀ y : C.circleDomain_EFE, C.circleProj_EFE y = C.circleProj_EFE x₀ →
      (y : X) ∈ C.edgeSource_EFE) :
    let _ := A.circleChartedSpace
    ∃ V : TopologicalSpace.Opens C.circleBaseOpens_EFE, C.circleProj_EFE x₀ ∈ V ∧
      ∃ Tb hb : C.circleBaseOpens_EFE → ℝ,
        ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ Tb V ∧ ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ hb V ∧
        (∀ y : C.circleDomain_EFE, C.circleProj_EFE y ∈ V →
          (y : X) ∈ C.edgeSource_EFE ∧ C.edgeBlockProj_EFE y.1 ∈ N ∧
          C.edgeHeightGlobal_EFE y.1 - 4 * Δ = Tb (C.circleProj_EFE y) ∧
          hh (C.edgeBlockProj_EFE y.1) = hb (C.circleProj_EFE y)) ∧
        Tb (C.circleProj_EFE x₀) = C.edgeHeightGlobal_EFE x₀.1 - 4 * Δ ∧
        hb (C.circleProj_EFE x₀) = hh (C.edgeBlockProj_EFE x₀.1) := by
  intro _
  have hπ0 : ∀ w, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection w = w :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  let valB1 : C.circleBaseOpens_EFE →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
    fun cc => ((cc : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
  have hval : ContMDiff 𝓘(ℝ, ℝ²)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ valB1 :=
    (A.circle_isManifold.2.1).comp (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ²)))
  have hvc : ∀ y : C.circleDomain_EFE, valB1 (C.circleProj_EFE y) = C.toChain.E y.1 := fun y =>
    (hπ0 _)
  let sc := gafScaleMarker P.toLocalChartFamily P.zero
  let Q2 := (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
  let O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
    {w | sc w ≠ 0} ∩ Q2 ⁻¹' N
  have hOo : IsOpen O :=
    (isOpen_ne_fun sc.continuous continuous_const).inter (hN.preimage Q2.continuous)
  have hV₀ : IsOpen (valB1 ⁻¹' O) := hOo.preimage hval.continuous
  have hx₀O : valB1 (C.circleProj_EFE x₀) ∈ O := by
    rw [hvc]
    exact ⟨(C.toChain.scale_pos x₀.1).2.ne', hx₀N⟩
  have hfc : IsClosedMap C.circleProj_EFE := C.circleProj_isProper_EFE.isClosedMap
  have hN' : IsOpen {y : C.circleDomain_EFE | (y : X) ∈ C.edgeSource_EFE} :=
    C.edgeSource_EFE.isOpen.preimage continuous_subtype_val
  obtain ⟨U, hU, hxU, hUV, hUN⟩ := EdgeDisk.exists_open_tube_subset_EFC hfc hN' (c₀ :=
    C.circleProj_EFE x₀) (fun y hy => hfib y hy) hV₀ hx₀O
  have hTsm : ContDiffOn ℝ ∞ (fun w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²) => EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero w) /
        sc w) {w | sc w ≠ 0} :=
    ((((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafHeightVector P.toLocalChartFamily P.zero)).contDiff).contDiffOn).div
      sc.contDiff.contDiffOn (fun w hw => hw)
  refine ⟨⟨U, hU⟩, hxU, fun cc => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (valB1 cc)) / sc (valB1 cc) - 4 * Δ,
    fun cc => hh (Q2 (valB1 cc)), ?_, ?_, ?_, ?_, ?_⟩
  · refine ((hTsm.sub contDiffOn_const).contMDiffOn.comp hval.contMDiffOn ?_)
    intro cc hcc
    exact (hUV hcc).1
  · refine ((hhN.comp Q2.contDiff.contDiffOn (fun w hw => hw)).contMDiffOn.comp
      hval.contMDiffOn ?_)
    intro cc hcc
    exact (hUV hcc).2
  · intro y hy
    have hyO : valB1 (C.circleProj_EFE y) ∈ O := hUV hy
    rw [hvc] at hyO
    refine ⟨hUN hy, hyO.2, ?_, ?_⟩
    · beta_reduce
      rw [hvc]
      rfl
    · beta_reduce
      rw [hvc]
      rfl
  · beta_reduce
    rw [hvc]
    rfl
  · beta_reduce
    rw [hvc]
    rfl

/-- **The whole circle fibre through a rim point lies in the edge source** (EDP06's equality of
circles `edp06_rim_eq_whole_fibre_EFE` + (ELoc)). -/
theorem edge_rim_fibre_in_source_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (q₀ : C.edgeSource_EFE) (hT : C.edgeHeight_EFE q₀ = 4 * Δ)
    (hX₁ : (q₀ : X) ∈ C.circleDomain_EFE) :
    ∀ y : C.circleDomain_EFE, C.circleProj_EFE y = C.circleProj_EFE ⟨q₀.1, hX₁⟩ →
      (y : X) ∈ C.edgeSource_EFE := by
  intro y hy
  have hX₁' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q₀.1) ∈
      C.toChain.circleBase_BAS := by
    have h := C.circleDomain_eq_EFE hβ hd
    have hq : (q₀ : X) ∈ (C.circleDomain_EFE : Set X) := hX₁
    rw [h] at hq
    exact hq
  have hfib := C.edp06_rim_eq_whole_fibre_EFE hβ hd hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
    (q₀ := q₀.1) (C.toGaf02ChainE.edgeSource_mem_EFE q₀.2).2 hT hX₁'
  have hyF : (y : X) ∈ {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (C.toChain.E x) = (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q₀.1) ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          P.toLocalChartFamily P.zero (C.toChain.E x)) / C.toChain.scale x = 4 * Δ} := by
    rw [hfib]
    exact congrArg (fun v : C.circleBaseOpens_EFE => ((v : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) hy
  have hR : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E y.1) ∈
      edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 := by
    rw [hyF.1]
    exact (C.toGaf02ChainE.edgeSource_mem_EFE q₀.2).2
  exact C.toGaf02ChainE.mem_edgeSource_EFE hΔ2 hR hyF.2.le

/-- **EDP06 / FDC03, the corner at an endpoint** (fields `desc` of `CornerDescent74` and `rank` of
`CornerRank74`): at an endpoint `c₀` of `C₂` and a rim point `q₀ ∈ X₁` over it, the face data of
EDP05 (`hh`, `d(hh ∘ ι)(c₀) ≠ 0`), the rank two of `(T − 4Δ, F)` at `q₀` (ambient, onto `ℝ × ℝ`),
and the descent of `T − 4Δ` and `F = hh ∘ π₂E` to smooth functions `Tb`, `hb` of `B₁` on the
WHOLE preimage of a patch `V ∋ π₁E q₀`, vanishing at `π₁E q₀`. -/
theorem edp06_corner_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
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
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}))
    {c₀ : C.edgeBaseOpens_EFE} (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃))
    (q₀ : C.edgeSource_EFE) (hq₀c : C.edgeProj_EFE q₀ = c₀) (hT : C.edgeHeight_EFE q₀ = 4 * Δ)
    (hX₁ : (q₀ : X) ∈ C.circleDomain_EFE) :
    let _ := A.edgeChartedSpace1
    let _ := A.circleChartedSpace
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.edgeBlockProj_EFE q₀.1 ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiffOn ℝ ∞ hh N ∧ hh (C.edgeBlockProj_EFE q₀.1) = 0 ∧
        (∀ y : X, C.edgeBlockProj_EFE y ∈ N →
          (y ∈ edgeM2_EFE C K₃ ↔ 0 ≤ hh (C.edgeBlockProj_EFE y))) ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (C.edgeValB_EFE cc)) c₀ ≠ 0 ∧
        Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
          (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) q₀.1) ∧
        ∃ V : TopologicalSpace.Opens C.circleBaseOpens_EFE,
          C.circleProj_EFE ⟨q₀.1, hX₁⟩ ∈ V ∧
          ∃ Tb hb : C.circleBaseOpens_EFE → ℝ,
            ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ Tb V ∧ ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ hb V ∧
            (∀ y : C.circleDomain_EFE, C.circleProj_EFE y ∈ V →
              (y : X) ∈ C.edgeSource_EFE ∧ C.edgeBlockProj_EFE y.1 ∈ N ∧
              C.edgeHeightGlobal_EFE y.1 - 4 * Δ = Tb (C.circleProj_EFE y) ∧
              hh (C.edgeBlockProj_EFE y.1) = hb (C.circleProj_EFE y)) ∧
            Tb (C.circleProj_EFE ⟨q₀.1, hX₁⟩) = 0 ∧ hb (C.circleProj_EFE ⟨q₀.1, hX₁⟩) = 0 := by
  intro _ _
  have hH := C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs
    hKF hDreg hdD hcpt
  have hfr : (q₀ : X) ∈ frontier (edgeM2_EFE C K₃) := by
    have : (q₀ : X) ∈ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ ∧
        C.edgeProj_EFE x ∈ frontier (edgeC2_EFE C K₃)} := ⟨q₀, ⟨hT.le, hq₀c ▸ hc₀⟩, rfl⟩
    rw [← hH] at this
    exact this.1
  obtain ⟨N, hN, hq₀N, hh, hhN, hzero, hdef, hdb⟩ :=
    C.edge_regular_data_EFE A hεr K₃ D₃ hD hKs hKF hDreg hdD q₀ hfr
  have hfib := C.edge_rim_fibre_in_source_EFE hβ hd hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
    q₀ hT hX₁
  obtain ⟨V, hxV, Tb, hb', hTb, hhb, hdes, hTc, hbc⟩ := C.circle_descent_EFE A hN hhN ⟨q₀.1, hX₁⟩
    hq₀N hfib
  refine ⟨N, hN, hq₀N, hh, hhN, hzero, hdef, ?_, ?_, V, hxV, Tb, hb', hTb, hhb, hdes, ?_, ?_⟩
  · rw [← hq₀c]
    exact hdb
  · exact C.toGaf02ChainE.edge_corner_rank_raw_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hN hhN q₀
      hq₀N hT hdb
  · rw [hTc]
    change C.edgeHeight_EFE q₀ - 4 * Δ = 0
    rw [hT, sub_self]
  · rw [hbc]
    exact hzero

/-- **EDP06's base coordinates** (B:7124–7131, "`(g_i, T)` are actual local base coordinates",
D74-14 layer 2, R0 bound to the circle bundle): from the descent data and the rank two of
`(T − 4Δ, F)` at `q₀` (the output of `edp06_corner_EFE`), the descended pair `(Tb, hb)` is a
partial diffeomorphism of `B₁` onto an open set of `ℝ × ℝ` on a neighbourhood of `π₁E q₀` inside
the patch (`exists_rankTwo_descended_chart74` with `f = circleProj_EFE`). -/
theorem edp06_base_chart_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    {N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N) (x₀ : C.circleDomain_EFE)
    (hx₀N : C.edgeBlockProj_EFE x₀.1 ∈ N)
    (V : TopologicalSpace.Opens C.circleBaseOpens_EFE) (hxV : C.circleProj_EFE x₀ ∈ V)
    (Tb hb : C.circleBaseOpens_EFE → ℝ)
    (hTb : let _ := A.circleChartedSpace
      ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ Tb V)
    (hhb : let _ := A.circleChartedSpace
      ContMDiffOn 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ) ∞ hb V)
    (hdes : ∀ y : C.circleDomain_EFE, C.circleProj_EFE y ∈ V →
      (y : X) ∈ C.edgeSource_EFE ∧ C.edgeBlockProj_EFE y.1 ∈ N ∧
      C.edgeHeightGlobal_EFE y.1 - 4 * Δ = Tb (C.circleProj_EFE y) ∧
      hh (C.edgeBlockProj_EFE y.1) = hb (C.circleProj_EFE y))
    (hrank : Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
      (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) x₀.1)) :
    let _ := A.circleChartedSpace
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ × ℝ) C.circleBaseOpens_EFE (ℝ × ℝ) ∞,
      C.circleProj_EFE x₀ ∈ Φ.source ∧ Φ.source ⊆ V ∧ ∀ c ∈ Φ.source, Φ c = (Tb c, hb c) := by
  intro _
  have : IsManifold 𝓘(ℝ, ℝ²) ∞ (C.toChain.finalBase_BAS 0) := A.circle_isManifold.1
  have hf := C.circleProj_contMDiff_EFE A
  have hTg := C.contMDiff_edgeHeightGlobal_EFE
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => hh (C.edgeBlockProj_EFE y)) x₀.1 :=
    ((hhN.contDiffAt (hN.mem_nhds hx₀N)).contMDiffAt).comp x₀.1
      ((C.contMDiff_edgeBlockProj_EFE A) x₀.1)
  have hpair : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
      (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) x₀.1 :=
    ((hTg.contMDiffAt.sub contMDiffAt_const).prodMk_space hF).mdifferentiableAt (by simp)
  have hrank' : Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ)
      (fun z : C.circleDomain_EFE => (C.edgeHeightGlobal_EFE z.1 - 4 * Δ,
        hh (C.edgeBlockProj_EFE z.1))) x₀) := by
    have h1 := mfderiv_comp_subtype_val_R74 C.circleDomain_EFE (I := 𝓘(ℝ, E3))
      (f := fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y)))
      (g := fun z : C.circleDomain_EFE => (C.edgeHeightGlobal_EFE z.1 - 4 * Δ,
        hh (C.edgeBlockProj_EFE z.1))) (fun _ => rfl) x₀ hpair
    rw [h1]
    exact hrank
  have hev : (fun z : C.circleDomain_EFE => (C.edgeHeightGlobal_EFE z.1 - 4 * Δ,
      hh (C.edgeBlockProj_EFE z.1))) =ᶠ[nhds x₀] fun z => (Tb (C.circleProj_EFE z),
        hb (C.circleProj_EFE z)) := by
    filter_upwards [(V.isOpen.preimage hf.continuous).mem_nhds hxV] with z hz
    obtain ⟨-, -, h1, h2⟩ := hdes z hz
    exact Prod.ext h1 h2
  exact EdgeDisk.exists_rankTwo_descended_chart74 (I := 𝓘(ℝ, E3)) (IB := 𝓘(ℝ, ℝ²))
    (by simp) ((hf x₀).mdifferentiableAt (by simp)) hxV hTb hhb hev hrank'

/-- **The EDP06 row on the actual chain** (blueprint B:7092–7133), for a chain whose rim lies in
`X₁` (`hX₁`, the first clause of EDP06, `eventually_edp06_rim_mem_X₁_C14Z_EFC`): (1) `M₂ ∩ X₁` is
saturated by the whole circle fibres (`edp06_saturation_EFE`); (2) every point of `B₂` carries a
rim point (`edge_rim_point_EFE`; the rim is the whole circle fibre by G5's
`edp06_rim_eq_whole_fibre_EFE`); (3) at every endpoint of `C₂` and every rim point over it: the
face data, the rank two of `(T − 4Δ, F)`, and the descent of `T − 4Δ`, `F` to the circle base on the
whole preimage of a patch (`edp06_corner_EFE`; the base chart is `edp06_base_chart_EFE`). -/
theorem edp06_row_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
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
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    type_of% (C.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD) ∧
    (∀ cc : C.edgeBaseOpens_EFE, type_of% (C.toGaf02ChainE.edge_rim_point_EFE hΔ2 hc hϑ hε0 hε hμ
      hτ hσc hb hγc hγc1 hβc1 cc)) ∧
    (∀ (c₀ : C.edgeBaseOpens_EFE) (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃)) (q₀ : C.edgeSource_EFE)
      (hq₀c : C.edgeProj_EFE q₀ = c₀) (hT : C.edgeHeight_EFE q₀ = 4 * Δ)
      (hX₁ : (q₀ : X) ∈ C.circleDomain_EFE),
      type_of% (C.edp06_corner_EFE A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃
        hD hKs hKF hDreg hdD hcpt hc₀ q₀ hq₀c hT hX₁)) :=
  ⟨C.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD,
    fun cc => C.toGaf02ChainE.edge_rim_point_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 cc,
    fun _ hc₀ q₀ hq₀c hT hX₁ => C.edp06_corner_EFE A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt hc₀ q₀ hq₀c hT hX₁⟩

end Rim

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
