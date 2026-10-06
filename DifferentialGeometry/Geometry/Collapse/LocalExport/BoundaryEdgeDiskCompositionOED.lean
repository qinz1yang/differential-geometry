import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskChartOED
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorEmbedding
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph

/-!
# The cross-model argument `hιc` of the edge disk chart, discharged (lane O-EDGEDISK, G1c)

`smoothDiskChartAt_of_localRecord_OED` (G1b) takes the composition of the disk chart with the
interior embedding `ι : N → M` as an explicit argument `hιc`. Here it is discharged:

* `isImmersionAtOfComplement_localDiffeomorph_comp_toHalfSpace_OED`,
  `IsImmersion.localDiffeomorph_comp_toHalfSpace_OED`,
  `IsSmoothEmbedding.localDiffeomorph_comp_toHalfSpace_OED`: an immersion into a manifold modelled
  on `𝓘(ℝ, ℝⁿ)` followed by a LOCAL diffeomorphism into a manifold modelled on `𝓡∂ n` is an
  immersion (the local twin of O-CROSS's `IsImmersion.diffeomorph_comp_toHalfSpace_OCX`: the vector
  chart is `Φ⁻¹` followed by the code chart, on a restricted source chart; the source model needs a
  nonzero range-preserving translation `s₀`);
* `isSmoothEmbedding_comp_diskChart_toHalfSpace_OED`: the instance for disk charts
  `ℝ¹ × D² → N₀` (`s₀ = (e₀, 0)`);
* **`isSmoothEmbedding_val_comp_diskChart_OED`**: the PRODUCTION instance of `hιc` for the inclusion
  `W° → W.Carrier` of the interior of a carrier of either kind (closed: the boundaryless composition
  `IsImmersion.isLocalDiffeomorphOn_comp`; with boundary: the half-space composition above), with
  `isLocalDiffeomorph_pieceInterior_val`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

section LocalDiffeomorph

variable {n : ℕ} [NeZero n]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
  [IsManifold I ∞ M] [IsManifold (𝓡∂ n) ∞ N]

/-- **An immersion followed by a local diffeomorphism into a half-space manifold** (at a point). -/
theorem isImmersionAtOfComplement_localDiffeomorph_comp_toHalfSpace_OED
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s₀ : E) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I)
    {f : M → N₀} {g : N₀ → N} {x : M}
    (hf : IsImmersionAtOfComplement F I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f x)
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) ∞ g (f x)) :
    IsImmersionAtOfComplement F I (𝓡∂ n) ∞ (g ∘ f) x := by
  classical
  obtain ⟨Φ, hΦx, hΦeq⟩ := hg
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hΦx))
  let φ := hf.domChart.restr s
  have hφsource : φ.source = hf.domChart.source ∩ s :=
    hf.domChart.restr_source' s hsopen
  have hxφ : x ∈ φ.source := by
    rw [hφsource]
    exact ⟨hf.mem_domChart_source, hxs⟩
  let β := Φ.symm.trans (chartPartialDiffeomorph_OCX hf.codChart hf.codChart_mem_maximalAtlas)
  have htarget : (φ.extend I).target ⊆ (hf.domChart.extend I).target := by
    intro y hy
    rw [OpenPartialHomeomorph.extend_target] at hy ⊢
    exact ⟨hy.1.1, hy.2⟩
  refine isImmersionAtOfComplement_halfSpace_of_affine_OCX s₀ hs₀ hs₀I φ
    (restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hf.domChart_mem_maximalAtlas hsopen) hxφ β
    ?_ hf.equiv 0 ?_
  · intro y hy
    rw [hφsource] at hy
    have hyΦ : f y ∈ Φ.source := hs hy.2
    change g (f y) ∈ β.source
    rw [hΦeq hyΦ]
    refine ⟨Φ.map_source hyΦ, ?_⟩
    change Φ.symm (Φ (f y)) ∈ hf.codChart.source
    have hcancel : Φ.symm (Φ (f y)) = f y := Φ.left_inv hyΦ
    rw [hcancel]
    exact hf.source_subset_preimage_source hy.1
  · intro u hu
    have huφ := (φ.extend I).map_target hu
    rw [OpenPartialHomeomorph.extend_source, hφsource] at huφ
    have huΦ : f ((φ.extend I).symm u) ∈ Φ.source := hs huφ.2
    change hf.codChart (Φ.symm (g (f ((φ.extend I).symm u)))) = hf.equiv (u, 0) + 0
    have hcancel : Φ.symm (Φ (f ((φ.extend I).symm u))) = f ((φ.extend I).symm u) :=
      Φ.left_inv huΦ
    rw [hΦeq huΦ, hcancel, add_zero]
    exact hf.writtenInCharts (htarget hu)

/-- Global form. -/
theorem isImmersion_localDiffeomorph_comp_toHalfSpace_OED
    (s₀ : E) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I)
    {f : M → N₀} {g : N₀ → N} (hf : IsImmersion I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hg : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) ∞ g) :
    IsImmersion I (𝓡∂ n) ∞ (g ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  exact IsImmersionOfComplement.isImmersion (F := F) (fun x =>
    isImmersionAtOfComplement_localDiffeomorph_comp_toHalfSpace_OED s₀ hs₀ hs₀I (hF x)
      (hg (f x)))

/-- Smooth-embedding form (the local diffeomorphism is moreover a topological embedding). -/
theorem isSmoothEmbedding_localDiffeomorph_comp_toHalfSpace_OED
    (s₀ : E) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I)
    {f : M → N₀} {g : N₀ → N} (hf : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hg : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) ∞ g)
    (hge : IsEmbedding g) :
    IsSmoothEmbedding I (𝓡∂ n) ∞ (g ∘ f) :=
  ⟨isImmersion_localDiffeomorph_comp_toHalfSpace_OED s₀ hs₀ hs₀I hf.isImmersion hg,
    hge.comp hf.isEmbedding⟩

end LocalDiffeomorph

section DiskChart

theorem diskChart_shift_ne_zero_OED :
    ((EuclideanSpace.single 0 1 : ℝ¹), (0 : ℝ²)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : ℝ¹ × ℝ² => v.1 0) h
  simp at h1

theorem diskChart_shift_range_OED {v : ℝ¹ × ℝ²} :
    v + ((EuclideanSpace.single 0 1 : ℝ¹), (0 : ℝ²)) ∈ range ((𝓡 1).prod (𝓡∂ 2)) ↔
      v ∈ range ((𝓡 1).prod (𝓡∂ 2)) :=
  prod_shift_range_OCX (fun _ => modelWithCornersSelf_shift_range_OCX _)

/-- **A disk chart into an `𝓘(ℝ, ℝⁿ)`-manifold followed by a local diffeomorphism and embedding
into an `𝓡∂ n`-manifold** is a smooth embedding. -/
theorem isSmoothEmbedding_comp_diskChart_toHalfSpace_OED {n : ℕ} [NeZero n]
    {N₀ : Type*} [TopologicalSpace N₀] (cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) N₀)
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ N] {ι : N₀ → N}
    (hι : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) ∞ ι) (hιe : IsEmbedding ι)
    (Φ : ℝ¹ × ClosedCell 2 → N₀)
    (hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Φ) :
    IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ n) ∞ (ι ∘ Φ) :=
  isSmoothEmbedding_localDiffeomorph_comp_toHalfSpace_OED _ diskChart_shift_ne_zero_OED
    (fun _ => diskChart_shift_range_OED) hΦ hι hιe

/-- The same through a local diffeomorphism and embedding between BOUNDARYLESS models (the source
manifold's charted space is an explicit argument, to avoid clashes with other instances). -/
theorem isSmoothEmbedding_comp_diskChart_of_localDiffeomorph_OED {F' G₀ G₁ : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace G₀] [TopologicalSpace G₁]
    {J₀ : ModelWithCorners ℝ F' G₀} {J₁ : ModelWithCorners ℝ F' G₁} [J₀.Boundaryless]
    [J₁.Boundaryless] {N₀ : Type*} [TopologicalSpace N₀] (cs : ChartedSpace G₀ N₀)
    {N : Type*} [TopologicalSpace N] [ChartedSpace G₁ N] [IsManifold J₁ ∞ N] {ι : N₀ → N}
    (hι : IsLocalDiffeomorph J₀ J₁ ∞ ι) (hιe : IsEmbedding ι) (Φ : ℝ¹ × ClosedCell 2 → N₀)
    (hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) J₀ ∞ Φ) :
    IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) J₁ ∞ (ι ∘ Φ) :=
  ⟨hΦ.isImmersion.isLocalDiffeomorphOn_comp_of_boundaryless (fun p => hι p.1),
    hιe.comp hΦ.isEmbedding⟩

end DiskChart

section Production

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- **The production instance of `hιc`**: for the inclusion `W° → W.Carrier` of the interior of a
compact carrier (either kind), a smooth disk chart `ℝ¹ × D² → W°` (interior atlas, model `𝓡 3`)
stays a smooth embedding into `W.Carrier` (model `W.model`). -/
theorem isSmoothEmbedding_val_comp_diskChart_OED (W : CompactCarrier.{0})
    (Φ : ℝ¹ × ClosedCell 2 → W.pieceInterior ⊤)
    (hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) (𝓡 3) ∞ Φ) :
    IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) W.model ∞
      ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ∘ Φ) := by
  have hloc := isLocalDiffeomorph_pieceInterior_val W ⊤
  cases W with
  | mk k C o =>
    cases k
    · exact isSmoothEmbedding_comp_diskChart_of_localDiffeomorph_OED (interiorCharted_BDRY1 _)
        hloc IsEmbedding.subtypeVal Φ hΦ
    · exact isSmoothEmbedding_comp_diskChart_toHalfSpace_OED (interiorCharted_BDRY1 _) hloc
        IsEmbedding.subtypeVal Φ hΦ

end Production

end DifferentialGeometry.Geometry.Collapse
