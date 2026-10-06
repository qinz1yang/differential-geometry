import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgePiecesFD4

/-!
# FDC04, clause "horizontal edge disks" (G2)

Lane S-FDC04 (`_FD4`), group G2. Blueprint `master207B.tex`, FDC04 (B:7367-7435): "Every horizontal
edge disk is a whole `f₂` fiber in one component of `∂M₂`, hence in an actual zero or slim
boundary by (RF) and EDP05. Distinct disks are disjoint as fibers. Their boundary circles are the
actual vertical-circle fibers by EDP06." With `H = ∂M₂ ∩ X₂` (the horizontal face of (EF)), `D(y)`
the whole low fibre `{π₂E = π₂E y, T ≤ 4Δ}` of EDP04 and `R(y)` its rim `{π₂E = π₂E y, T = 4Δ}`:

* `edge_horizontal_disks_FD4`, for the admissible `K₃, D₃` and `hcpt` (FDC02's compactness, the
  tail of G3 discharges it): (a) over every `y ∈ H` the fibre `D(y)` is the image of a smooth
  embedding of the closed 2-disk whose boundary circle is exactly `R(y)` (EDP04, whole disk with
  its rim); (b) `D(y) ⊆ H` (`edge_frontier_H_EFE`: `H = f₂⁻¹(∂C₂) ∩ X₂`, so the whole disk lies in
  `∂M₂`); (c) `H ⊆ M^edge`; (d) two disks are equal or disjoint (fibres of `π₂E`); (e) `D(y)` lies
  in the ONE component of `∂M₂` through `y` (connectedness of the disk); (f) `H = ⋃_{y ∈ H} D(y)`.
  NOT here: that the disk lies in a single zero face or slim fibre (`edge_disk_in_face_EFE`, group
  G11 of S-EDP-FDC4: not delivered when this file was written) and that `R(y)` is an `E`-fibre of
  the circle region (EDP06, `edp06_rim_eq_whole_fibre_EFE`, its own row).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0

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

namespace Gaf02ChainEJA

section Disks

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- The horizontal face `H = ∂M₂ ∩ X₂` of (EF) (low part of the edge source). -/
abbrev edgeHorizontal_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (Δ : ℝ) : Set X :=
  frontier (C.edgeM2_EFE K₃) ∩ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}

/-- The whole low fibre `D(y) = {π₂E = π₂E y, T ≤ 4Δ}` through `y`. -/
abbrev edgeDisk_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (Δ : ℝ) (y : X) : Set X :=
  {z | C.toGaf02ChainE.cutQ_R74 1 z = C.toGaf02ChainE.cutQ_R74 1 y ∧
    C.toGaf02ChainE.edgeHeightGlobal_EFE z ≤ 4 * Δ}

/-- The rim `R(y) = {π₂E = π₂E y, T = 4Δ}` of the disk through `y`. -/
abbrev edgeRim_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (Δ : ℝ) (y : X) : Set X :=
  {z | C.toGaf02ChainE.cutQ_R74 1 z = C.toGaf02ChainE.cutQ_R74 1 y ∧
    C.toGaf02ChainE.edgeHeightGlobal_EFE z = 4 * Δ}

/-- **The horizontal edge disks** (see the module docstring). -/
theorem edge_horizontal_disks_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
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
    (hcpt : IsCompact (C.edgeA_FD4 K₃ Δ)) :
    (∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, ∃ φ : ClosedCell 2 → X,
      IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧ range φ = C.edgeDisk_FD4 Δ y ∧
        range (φ ∘ cellBoundaryInclusion 2) = C.edgeRim_FD4 Δ y) ∧
    (∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, C.edgeDisk_FD4 Δ y ⊆ C.edgeHorizontal_FD4 K₃ Δ) ∧
    C.edgeHorizontal_FD4 K₃ Δ ⊆ C.edgeA_FD4 K₃ Δ ∧
    (∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, ∀ y' ∈ C.edgeHorizontal_FD4 K₃ Δ,
      C.edgeDisk_FD4 Δ y = C.edgeDisk_FD4 Δ y' ∨
        Disjoint (C.edgeDisk_FD4 Δ y) (C.edgeDisk_FD4 Δ y')) ∧
    (∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ,
      C.edgeDisk_FD4 Δ y ⊆ connectedComponentIn (frontier (C.edgeM2_EFE K₃)) y) ∧
    C.edgeHorizontal_FD4 K₃ Δ = ⋃ y ∈ C.edgeHorizontal_FD4 K₃ Δ, C.edgeDisk_FD4 Δ y := by
  let _ := A.edgeChartedSpace1
  have _ : IsManifold (𝓡 1) ∞ (C.toChain.finalBase_BAS 1) := A.edge_isManifold1.1
  have hH := C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs
    hKF hDreg hdD hcpt
  have hE1 := C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
    hKs hKF hDreg hdD hcpt
  have hHeq : C.edgeHorizontal_FD4 K₃ Δ = Subtype.val '' {x : C.edgeSource_EFE |
      C.edgeHeight_EFE x ≤ 4 * Δ ∧ C.edgeProj_EFE x ∈ frontier (C.edgeC2_EFE K₃)} := hH
  -- every point of `H` is a source point over a frontier point of `C₂`
  have hpt : ∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, ∃ x : C.edgeSource_EFE, (x : X) = y ∧
      C.edgeHeight_EFE x ≤ 4 * Δ ∧ C.edgeProj_EFE x ∈ frontier (C.edgeC2_EFE K₃) := by
    intro y hy
    rw [hHeq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, rfl, hx.1, hx.2⟩
  -- the whole disk through a source point
  have hdisk : ∀ (x : C.edgeSource_EFE), C.edgeDisk_FD4 Δ (x : X) =
      Subtype.val '' {x' : C.edgeSource_EFE | C.edgeProj_EFE x' = C.edgeProj_EFE x ∧
        C.edgeHeight_EFE x' ≤ 4 * Δ} := fun x =>
    (C.toGaf02ChainE.edgeDisk_eq_EFE hΔ2 (C.edgeProj_EFE x)).symm
  have hdisk_sub : ∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ,
      C.edgeDisk_FD4 Δ y ⊆ C.edgeHorizontal_FD4 K₃ Δ := by
    intro y hy
    obtain ⟨x, rfl, -, hxf⟩ := hpt y hy
    intro z hz
    rw [hdisk x] at hz
    obtain ⟨x', ⟨hx'1, hx'2⟩, rfl⟩ := hz
    rw [hHeq]
    exact ⟨x', ⟨hx'2, hx'1 ▸ hxf⟩, rfl⟩
  have hself : ∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, y ∈ C.edgeDisk_FD4 Δ y := by
    intro y hy
    obtain ⟨x, rfl, hxT, -⟩ := hpt y hy
    exact ⟨rfl, hxT⟩
  have hdiskmap : ∀ y ∈ C.edgeHorizontal_FD4 K₃ Δ, ∃ φ : ClosedCell 2 → X,
      IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧ range φ = C.edgeDisk_FD4 Δ y ∧
        range (φ ∘ cellBoundaryInclusion 2) = C.edgeRim_FD4 Δ y := by
    intro y hy
    obtain ⟨x, rfl, -, -⟩ := hpt y hy
    have hw : ((C.edgeProj_EFE x : C.edgeBaseOpens_EFE) : C.toChain.finalBase_BAS 1).1 ∈
        C.edgeBase_EDP23 := ⟨(C.edgeProj_EFE x).1.2, (C.edgeProj_EFE x).2⟩
    obtain ⟨φ, hφ, hr, hrim⟩ := C.toGaf02ChainE.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ
      hσc hb hγc hγc1 hβc1 hw
    exact ⟨φ, hφ, hr, hrim⟩
  refine ⟨hdiskmap, hdisk_sub, ?_, ?_, ?_, ?_⟩
  · -- `H ⊆ M^edge` (saturation of E1 and closedness of `C₂`)
    intro y hy
    obtain ⟨x, rfl, hxT, hxf⟩ := hpt y hy
    have hsat : C.edgeA_FD4 K₃ Δ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈
        C.edgeC2_EFE K₃ ∧ C.edgeHeight_EFE x ≤ 4 * Δ} := hE1.2.1
    rw [hsat]
    exact ⟨x, ⟨hE1.1.isClosed.frontier_subset hxf, hxT⟩, rfl⟩
  · intro y hy y' hy'
    by_cases hq : C.toGaf02ChainE.cutQ_R74 1 y = C.toGaf02ChainE.cutQ_R74 1 y'
    · left
      ext z
      simp only [Set.mem_ofPred_eq, hq]
    · right
      refine Set.disjoint_left.mpr fun z hz hz' => hq ?_
      exact hz.1.symm.trans hz'.1
  · intro y hy
    obtain ⟨φ, hφ, hr, -⟩ := hdiskmap y hy
    have hpre := (isPreconnected_range_closedCell_EFE hφ.isEmbedding.continuous).1
    rw [hr] at hpre
    exact hpre.subset_connectedComponentIn (hself y hy)
      (fun z hz => (hdisk_sub y hy hz).1)
  · refine Subset.antisymm (fun y hy => mem_iUnion₂.mpr ⟨y, hy, hself y hy⟩) ?_
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
    exact hdisk_sub y hy hzy

end Disks

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
