import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeFibreDiskEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseEFE
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FibreSaturation

/-!
# EDP06: the boundary circle of the whole edge disk is a whole circle fibre of `E`

Lane S-EDP-FDC2, group G5 (EDP06, second clause; draft 74 D74-14 layers 1–2; binding of the
kernel `EdgeDisk.range_eq_of_range_subset_of_isEmbedding`). Blueprint `master207B.tex`, EDP06
(B:7092–7133): "A whole circle fiber through this point has the same value of the GLOBAL `E`. It
therefore has the same edge base point and the same `T = 4Δ` ... This inclusion of a compact
connected smooth circle into the disk's connected smooth boundary circle is open ... and closed by
compactness. It is the entire boundary circle."

* `Gaf02Chain.edgeRim_data_eq_of_E_eq_EFE`: `E x = E y` gives the same `π₂E` and the same height
  `T = A/s` (`s = ℓ_ρ ∘ E`);
* `cellBoundaryInclusion_isEmbedding_EFE`, `circle_range_eq_boundary_EFE`: the kernel bound to
  `Circle` and `CellBoundary 2` (a topological embedding of the circle inside the boundary circle
  of an embedded disk fills it);
* `Gaf02ChainEJA.circleFibre_circle_EFE`: over `w ∈ B₁ = circleBase_BAS` the whole fibre
  `(π₁E)⁻¹(w)` is the range of a smooth embedding of the circle (G6);
* **`Gaf02ChainEJA.edp06_rim_eq_whole_fibre_EFE`**: for `q₀ ∈ X₂` with `T q₀ = 4Δ` in `X₁`, the
  rim `{π₂E = π₂E q₀, T = 4Δ}` (the boundary circle of the whole disk of EDP04,
  `edp04_fibre_disk_of_mem_EFE`) is EXACTLY the whole circle fibre `(π₁E)⁻¹(π₁E q₀)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold cellBoundaryChartedSpace

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- The inclusion of the boundary sphere into the closed cell is an embedding. -/
theorem cellBoundaryInclusion_isEmbedding_EFE (n : ℕ) :
    Topology.IsEmbedding (cellBoundaryInclusion n) := by
  refine Topology.IsEmbedding.of_comp ?_ continuous_subtype_val
    (g := (Subtype.val : ClosedCell n → EuclideanSpace ℝ (Fin n))) ?_
  · exact continuous_induced_rng.2 continuous_subtype_val
  · exact Topology.IsEmbedding.subtypeVal

/-- **EDP06's kernel, bound to `Circle` and the boundary circle of the cell**: a topological
embedding of the circle whose range lies in the boundary circle `d(∂ClosedCell 2)` of an embedded
disk fills it. -/
theorem circle_range_eq_boundary_EFE {Y : Type*} [TopologicalSpace Y] {f : Circle → Y}
    {d : CellBoundary 2 → Y} (hf : Topology.IsEmbedding f) (hd : Topology.IsEmbedding d)
    (hsub : range f ⊆ range d) : range f = range d := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (CellBoundary 2) :=
    DifferentialGeometry.Topology.Handle.cellBoundaryChartedSpace 2
  have hconn : ConnectedSpace (CellBoundary 2) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
      norm_num
    have h : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isConnected_sphere hrank 0 zero_le_one
    have h' : IsConnected {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ = 1} := by
      convert h using 1
      ext x
      simp
    exact isConnected_iff_connectedSpace.mp h'
  exact EdgeDisk.range_eq_of_range_subset_of_isEmbedding (F := EuclideanSpace ℝ (Fin 1))
    (P := Circle) (Q := CellBoundary 2) hf.continuous hf.injective hd hsub

namespace Gaf02Chain

/-- `E` determines the second-stage projection and the height `T`. -/
theorem edgeRim_data_eq_of_E_eq_EFE {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b'
    s' ε γc βc Lmax τ γ δ εr e T V} (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {x y : X}
    (h : C.E x = C.E y) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E x) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E y) ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E x)) /
          C.scale x =
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E y)) /
          C.scale y := by
  refine ⟨by rw [h], ?_⟩
  have hs : C.scale x = C.scale y := by
    change gafScaleMarker P.toLocalChartFamily P.zero (C.E x) =
      gafScaleMarker P.toLocalChartFamily P.zero (C.E y)
    rw [h]
  rw [h, hs]

end Gaf02Chain

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **The whole circle fibre over a point of `B₁`** (G6): a smooth embedded circle. -/
theorem circleFibre_circle_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.circleBase_BAS) :
    ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w} := by
  have hW : w ∈ C.toChain.finalBase_BAS 0 := ((C.gaf07_circle_row_GAFD hβ hd).1.1 ▸ hw).1
  have hmem : (⟨w, hW⟩ : C.toChain.finalBase_BAS 0) ∈ C.circleBaseOpens_EFE :=
    (Set.ext_iff.mp (C.circleBaseOpens_eq_EFE hβ hd) ⟨w, hW⟩).mpr hw
  obtain ⟨f, hf, hrf⟩ := C.circleProj_circle_EFE hβ hd ⟨⟨w, hW⟩, hmem⟩
  exact ⟨f, hf, hrf.trans (C.circleProj_fibre_EFE _)⟩

/-- **EDP06, the circles agree** (B:7092–7133): for a point `q₀` of the actual `X₂` with `T q₀ = 4Δ`
which lies in `X₁` (the first clause of EDP06, `eventually_edp06_rim_mem_X₁_C14Z_EFC`), the boundary
circle of the whole edge disk `{π₂E = π₂E q₀, T ≤ 4Δ}` is EXACTLY the whole circle fibre of
`π₁E = E : X₁ → B₁` through `q₀`. -/
theorem edp06_rim_eq_whole_fibre_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {q₀ : X}
    (hwit : ∃ k : P.edge.finite_centres.toFinset,
      9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q₀)) ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q₀))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E q₀)))
    (hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
      (C.toChain.E q₀)) / C.toChain.scale q₀ = 4 * Δ)
    (hX₁ : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q₀) ∈
      C.toChain.circleBase_BAS) :
    {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E q₀) ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
          (C.toChain.E x)) / C.toChain.scale x = 4 * Δ} =
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        {(gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q₀)} := by
  have hπ0 : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  obtain ⟨f, hf, hrf⟩ := C.circleFibre_circle_EFE hβ hd hX₁
  obtain ⟨φ, hφ, -, hbd⟩ := C.toGaf02ChainE.edp04_fibre_disk_of_mem_EFE hΔ2 hc hϑ hε0 hε hμ hτ
    hσc hb hγc hγc1 hβc1 hwit hT.le
  have hfibE : ∀ y : X, y ∈ range f →
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E y) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E q₀) ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
        (C.toChain.E y)) / C.toChain.scale y = 4 * Δ := by
    intro y hy
    rw [hrf] at hy
    have hy' : C.toChain.E y = C.toChain.E q₀ := by
      have h : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y) =
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q₀) := hy
      rwa [hπ0, hπ0] at h
    exact ⟨(C.toChain.edgeRim_data_eq_of_E_eq_EFE hy').1,
      (C.toChain.edgeRim_data_eq_of_E_eq_EFE hy').2.trans hT⟩
  have hdemb : Topology.IsEmbedding (φ ∘ cellBoundaryInclusion 2) :=
    hφ.isEmbedding.comp (cellBoundaryInclusion_isEmbedding_EFE 2)
  have hkern := circle_range_eq_boundary_EFE hf.isEmbedding hdemb (by
    rw [hbd]
    exact fun y hy => hfibE y hy)
  rw [← hbd, ← hkern, hrf]

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
