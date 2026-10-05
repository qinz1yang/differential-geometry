import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBasesV2

/-!
# Boundary route interfaces v2, part 2: the whole-fibre layer as smooth proper restrictions
(lane BIFACEc, re-freeze after review 69)

External review 69 §1.5 and lead disposition D69-1 (binding). v1's `BoundaryWholeFiberSpec` stores
only fibrewise TOPOLOGICAL types and allows only TORUS slim fibres; the blueprint (BCG07 / BCF01 and
the closed route) keeps whole slim fibres `S²` OR `T²` (an interior `S² × I` slim cylinder is not
excluded by a non-empty boundary), and the consumers need the actual smooth proper restriction.

* `SmoothProductChartAt_BIFc IM IF k f X B y` (generic, any manifold `M`): a smooth local product
  chart of `f : M → H` over the `k`-dimensional base `B` at `y` with fibre model `F`: a smooth
  immersed topological embedding `σ : ℝᵏ → H` onto a relatively open piece `B ∩ O` of the base
  with `σ 0 = y`, and a smooth embedding `φ : ℝᵏ × F → M` onto the WHOLE preimage
  `X ∩ f⁻¹(range σ)` with `f ∘ φ = σ ∘ pr₁` (the restriction COMMUTES with `f`).
* `SmoothDiskChartAt_BIFc IM k f T a X B y`: the same with fibre `ClosedCell 2` (model `𝓡∂ 2`)
  and the vertical rim `T ∘ φ = a ⟺ ‖w‖ = 1` (the two-stratum structure of the edge source).
* Derived exits (generic): `SmoothProductChartAt_BIFc.fibre_eq_range` (the whole fibre over `y`
  is the image of the smooth embedding `φ(0, ·)`), `.nonempty_fibre_homeomorph` (fibre `≃ₜ F`);
  `SmoothDiskChartAt_BIFc.fibre_disk_rim` (fibre `≃ₜ ClosedCell 2` with the unit circle onto the
  vertical rim).
* `BoundaryWholeFiberSpecV2 C Bs` (D69-1) on ONE chain `C` and ONE v2 BASES exit `Bs`: circle
  charts (`k = 2`, fibre `Circle`), slim charts (`k = 1`, fibre `ClosureSphere` (`𝓡 2`) OR
  `Circle × Circle` (`(𝓡 1).prod (𝓡 1)`)), edge disk charts (`k = 1`, fibre `ClosedCell 2`, rim at
  `T = C.heightRatio = 4Δ`), all with the SAME final stage maps `C.stageMap st`, and the buffered
  sources `D > 10`. Derived (D69-1 "types as derived exits"): `circle_fibre_BIFc`,
  `slim_fibre_BIFc` (`≃ₜ S²` OR `≃ₜ T²`), `edge_fibre_BIFc` (v1's form), and the conditional
  projection `toV1_BIFc` (v1's object when every slim fibre is a torus).
* Inhabitants: the empty family (`BoundaryGaf02Chain.emptyWholeFiberSpecV2_BIFc`), and NON-EMPTY
  model instances of the generic charts: the `S² × ℝ` slim cylinder (`sphereCylinder_chart_BIFc`,
  the case v1 excluded), the `T² × ℝ` slim cylinder (`torusCylinder_chart_BIFc`) and the circle
  bundle `ℝ² × S¹` (`circleBundle_chart_BIFc`), with their derived fibre types.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc

/-- The slice `φ(0, ·)` of a chart commuting with `f` over an injective base parametrization `σ`
is exactly the whole fibre over `σ 0`. -/
theorem range_slice_eq_fibre_BIFc {M H G : Type*} {k : ℕ} {f : M → H} {X : Set M}
    {σ : EuclideanSpace ℝ (Fin k) → H} {φ : EuclideanSpace ℝ (Fin k) × G → M} {y : H}
    (h0 : σ 0 = y) (hσ : Injective σ) (hr : range φ = X ∩ f ⁻¹' range σ)
    (hf : ∀ x z, f (φ (x, z)) = σ x) : range (fun z => φ (0, z)) = X ∩ f ⁻¹' {y} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    have hmem : φ (0, z) ∈ range φ := mem_range_self _
    rw [hr] at hmem
    exact ⟨hmem.1, by rw [mem_preimage, mem_singleton_iff, hf, h0]⟩
  · rintro ⟨hX, hy⟩
    rw [mem_preimage, mem_singleton_iff] at hy
    have hmem : p ∈ X ∩ f ⁻¹' range σ := ⟨hX, ⟨0, by rw [h0, hy]⟩⟩
    rw [← hr] at hmem
    obtain ⟨⟨x, z⟩, rfl⟩ := hmem
    have hx : x = 0 := hσ (by rw [← hf x z, hy, h0])
    subst hx
    exact ⟨z, rfl⟩

section Generic

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace M] [ChartedSpace HM M] (IM : ModelWithCorners ℝ EM HM)
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  [TopologicalSpace F] [ChartedSpace HF F] (IF : ModelWithCorners ℝ EF HF)
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A smooth local product chart of `f` over the base `B` at `y`** with fibre model `F`: a smooth
immersed topological embedding `σ : ℝᵏ → H` onto the relatively open piece `B ∩ O` with `σ 0 = y`,
and a smooth embedding `φ : ℝᵏ × F → M` onto the WHOLE preimage `X ∩ f⁻¹(range σ)` with
`f (φ (x, z)) = σ x`. -/
def SmoothProductChartAt_BIFc (k : ℕ) (f : M → H) (X : Set M) (B : Set H) (y : H) : Prop :=
  ∃ (σ : EuclideanSpace ℝ (Fin k) → H) (φ : EuclideanSpace ℝ (Fin k) × F → M) (O : Set H),
    σ 0 = y ∧ ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧ (∀ x, Injective (fderiv ℝ σ x)) ∧
    IsOpen O ∧ range σ = B ∩ O ∧ IsSmoothEmbedding ((𝓡 k).prod IF) IM ∞ φ ∧
    range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x

variable {IM IF}

/-- **The whole fibre over `y` is the image of the smooth embedding `φ(0, ·)`.** -/
theorem SmoothProductChartAt_BIFc.fibre_eq_range {k : ℕ} {f : M → H} {X : Set M} {B : Set H}
    {y : H} (h : SmoothProductChartAt_BIFc IM IF (F := F) k f X B y) :
    ∃ φ₀ : F → M, IsEmbedding φ₀ ∧ range φ₀ = X ∩ f ⁻¹' {y} := by
  obtain ⟨σ, φ, -, h0, -, hσ, -, -, -, hφ, hr, hf⟩ := h
  exact ⟨fun z => φ (0, z), hφ.isEmbedding.comp (isEmbedding_prodMkRight _),
    range_slice_eq_fibre_BIFc h0 hσ.injective hr hf⟩

/-- **Derived fibre type**: the whole fibre over `y` is homeomorphic to the fibre model `F`. -/
theorem SmoothProductChartAt_BIFc.nonempty_fibre_homeomorph {k : ℕ} {f : M → H} {X : Set M}
    {B : Set H} {y : H} (h : SmoothProductChartAt_BIFc IM IF (F := F) k f X B y) :
    Nonempty ((X ∩ f ⁻¹' {y} : Set M) ≃ₜ F) := by
  obtain ⟨φ₀, hφ₀, hr⟩ := h.fibre_eq_range
  exact ⟨((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hr)).symm⟩

end Generic

section Disk

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace M] [ChartedSpace HM M] (IM : ModelWithCorners ℝ EM HM)
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A smooth local disk-bundle chart** (fibre `ClosedCell 2`, model `𝓡∂ 2`) of `f` over the base
`B` at `y`, with the vertical rim at the level `a` of `T`: the chart of
`SmoothProductChartAt_BIFc` together with `T (φ (x, w)) = a ⟺ ‖w‖ = 1`. -/
def SmoothDiskChartAt_BIFc (k : ℕ) (f : M → H) (T : M → ℝ) (a : ℝ) (X : Set M) (B : Set H)
    (y : H) : Prop :=
  ∃ (σ : EuclideanSpace ℝ (Fin k) → H) (φ : EuclideanSpace ℝ (Fin k) × ClosedCell 2 → M)
    (O : Set H),
    σ 0 = y ∧ ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧ (∀ x, Injective (fderiv ℝ σ x)) ∧
    IsOpen O ∧ range σ = B ∩ O ∧ IsSmoothEmbedding ((𝓡 k).prod (𝓡∂ 2)) IM ∞ φ ∧
    range φ = X ∩ f ⁻¹' range σ ∧ (∀ x w, f (φ (x, w)) = σ x) ∧
    ∀ x w, T (φ (x, w)) = a ↔ ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1

variable {IM}

/-- A disk chart is a product chart with fibre `ClosedCell 2`. -/
theorem SmoothDiskChartAt_BIFc.toProductChart {k : ℕ} {f : M → H} {T : M → ℝ} {a : ℝ}
    {X : Set M} {B : Set H} {y : H} (h : SmoothDiskChartAt_BIFc IM k f T a X B y) :
    SmoothProductChartAt_BIFc IM (𝓡∂ 2) (F := ClosedCell 2) k f X B y := by
  obtain ⟨σ, φ, O, h0, hs, he, hd, hO, hrσ, hφ, hr, hf, -⟩ := h
  exact ⟨σ, φ, O, h0, hs, he, hd, hO, hrσ, hφ, hr, hf⟩

/-- **Derived disk fibre with its rim** (v1's `edge_fibre` form): the whole fibre over `y` is
`≃ₜ ClosedCell 2` with the unit circle going onto the vertical rim `fibre ∩ {T = a}`. -/
theorem SmoothDiskChartAt_BIFc.fibre_disk_rim {k : ℕ} {f : M → H} {T : M → ℝ} {a : ℝ}
    {X : Set M} {B : Set H} {y : H} (h : SmoothDiskChartAt_BIFc IM k f T a X B y) :
    ∃ ed : (X ∩ f ⁻¹' {y} : Set M) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = X ∩ f ⁻¹' {y} ∩ {p | T p = a} := by
  obtain ⟨σ, φ, O, h0, -, hσ, -, -, -, hφ, hr, hf, hT⟩ := h
  have hφ₀ : IsEmbedding fun w : ClosedCell 2 => φ (0, w) :=
    hφ.isEmbedding.comp (isEmbedding_prodMkRight _)
  have hrange : range (fun w : ClosedCell 2 => φ (0, w)) = X ∩ f ⁻¹' {y} :=
    range_slice_eq_fibre_BIFc h0 hσ.injective hr hf
  refine ⟨((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm, ?_⟩
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, ?_⟩
    set w := ((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm q with hw
    have hq' : (q : M) = φ (0, w) := by
      have := congrArg Subtype.val
        (((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hrange)).apply_symm_apply q)
      rw [← this]
      rfl
    change T q = a
    rw [hq', hT]
    exact hq
  · rintro ⟨hp, hTa⟩
    refine ⟨⟨p, hp⟩, ?_, rfl⟩
    obtain ⟨w, hw⟩ : (p : M) ∈ range (fun w : ClosedCell 2 => φ (0, w)) := by rw [hrange]; exact hp
    have hsymm : ((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm ⟨p, hp⟩ = w := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext hw.symm
    change ‖(((hφ₀.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm ⟨p, hp⟩).1‖ = 1
    rw [hsymm, ← hT 0 w]
    rw [show φ (0, w) = p from hw]
    exact hTa

end Disk

/-! ## Non-empty model instances of the generic charts -/

section Models

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-- `fderiv id` is injective. -/
theorem injective_fderiv_id_BIFc {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    Injective (fderiv ℝ (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) x) := by
  rw [fderiv_id]
  exact fun _ _ h => h

/-- **The `S² × ℝ` slim cylinder** (review 69 §5.2, D69-11: the case v1's torus-only slim field
excluded): the projection `ℝ¹ × S² → ℝ¹` has a smooth product chart with fibre `ClosureSphere` over
the base point `0`. -/
theorem sphereCylinder_chart_BIFc :
    SmoothProductChartAt_BIFc ((𝓡 1).prod (𝓡 2)) (𝓡 2) (F := GC.GraphManifold.ClosureSphere.{0}) 1
      (Prod.fst : EuclideanSpace ℝ (Fin 1) × GC.GraphManifold.ClosureSphere.{0} →
        EuclideanSpace ℝ (Fin 1)) univ univ 0 :=
  ⟨id, id, univ, rfl, contDiff_id, IsEmbedding.id, injective_fderiv_id_BIFc, isOpen_univ,
    by rw [univ_inter, range_id], IsSmoothEmbedding.id, by rw [range_id, range_id, preimage_univ, inter_univ],
    fun _ _ => rfl⟩

/-- **The `T² × ℝ` slim cylinder**: the projection `ℝ¹ × T² → ℝ¹` has a smooth product chart with
fibre `Circle × Circle` over the base point `0`. -/
theorem torusCylinder_chart_BIFc :
    SmoothProductChartAt_BIFc ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))) ((𝓡 1).prod (𝓡 1))
      (F := Circle × Circle) 1
      (Prod.fst : EuclideanSpace ℝ (Fin 1) × (Circle × Circle) → EuclideanSpace ℝ (Fin 1)) univ univ
      0 :=
  ⟨id, id, univ, rfl, contDiff_id, IsEmbedding.id, injective_fderiv_id_BIFc, isOpen_univ,
    by rw [univ_inter, range_id], IsSmoothEmbedding.id, by rw [range_id, range_id, preimage_univ, inter_univ],
    fun _ _ => rfl⟩

/-- **The circle bundle `ℝ² × S¹ → ℝ²`**: a smooth product chart with fibre `Circle` over the
base point `0`. -/
theorem circleBundle_chart_BIFc :
    SmoothProductChartAt_BIFc ((𝓡 2).prod (𝓡 1)) (𝓡 1) (F := Circle) 2
      (Prod.fst : EuclideanSpace ℝ (Fin 2) × Circle → EuclideanSpace ℝ (Fin 2)) univ univ 0 :=
  ⟨id, id, univ, rfl, contDiff_id, IsEmbedding.id, injective_fderiv_id_BIFc, isOpen_univ,
    by rw [univ_inter, range_id], IsSmoothEmbedding.id, by rw [range_id, range_id, preimage_univ, inter_univ],
    fun _ _ => rfl⟩

/-- **The edge disk bundle `ℝ¹ × D² → ℝ¹`** with the rim at `‖w‖ = 1`: a smooth disk chart over
the base point `0`. -/
theorem diskBundle_chart_BIFc :
    SmoothDiskChartAt_BIFc ((𝓡 1).prod (𝓡∂ 2)) 1
      (Prod.fst : EuclideanSpace ℝ (Fin 1) × ClosedCell 2 → EuclideanSpace ℝ (Fin 1))
      (fun p => ‖(p.2 : EuclideanSpace ℝ (Fin 2))‖) 1 univ univ 0 :=
  ⟨id, id, univ, rfl, contDiff_id, IsEmbedding.id, injective_fderiv_id_BIFc, isOpen_univ,
    by rw [univ_inter, range_id], IsSmoothEmbedding.id, by rw [range_id, range_id, preimage_univ, inter_univ],
    fun _ _ => rfl,
    fun _ _ => Iff.rfl⟩

/-- **Consumer on the models**: the whole fibres of the `S² × ℝ` and `T² × ℝ` slim cylinders are
`≃ₜ S²` and `≃ₜ T²`, the circle-bundle fibre is `≃ₜ S¹`, the disk-bundle fibre is a closed disk
with its rim at `‖w‖ = 1`. -/
theorem model_fibres_BIFc :
    Nonempty ((univ ∩ (Prod.fst : EuclideanSpace ℝ (Fin 1) × GC.GraphManifold.ClosureSphere.{0} →
        EuclideanSpace ℝ (Fin 1)) ⁻¹' {0} : Set _) ≃ₜ GC.GraphManifold.ClosureSphere.{0}) ∧
      Nonempty ((univ ∩ (Prod.fst : EuclideanSpace ℝ (Fin 1) × (Circle × Circle) →
        EuclideanSpace ℝ (Fin 1)) ⁻¹' {0} : Set _) ≃ₜ Circle × Circle) ∧
      Nonempty ((univ ∩ (Prod.fst : EuclideanSpace ℝ (Fin 2) × Circle →
        EuclideanSpace ℝ (Fin 2)) ⁻¹' {0} : Set _) ≃ₜ Circle) ∧
      ∃ ed : (univ ∩ (Prod.fst : EuclideanSpace ℝ (Fin 1) × ClosedCell 2 →
          EuclideanSpace ℝ (Fin 1)) ⁻¹' {0} : Set _) ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          univ ∩ (Prod.fst : EuclideanSpace ℝ (Fin 1) × ClosedCell 2 → EuclideanSpace ℝ (Fin 1)) ⁻¹'
            {0} ∩ {p | ‖(p.2 : EuclideanSpace ℝ (Fin 2))‖ = 1} :=
  ⟨(sphereCylinder_chart_BIFc).nonempty_fibre_homeomorph,
    (torusCylinder_chart_BIFc).nonempty_fibre_homeomorph,
    (circleBundle_chart_BIFc).nonempty_fibre_homeomorph,
    (diskBundle_chart_BIFc).fibre_disk_rim⟩

end Models

/-! ## The boundary whole-fibre layer v2 -/

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The whole-fibre layer v2** (review 69 §1.5, D69-1) on ONE chain `C` and ONE v2 BASES exit
`Bs`: the actual smooth proper restrictions of the SAME final stage maps `f_j = C.stageMap j` as
smooth local product charts — circle (`k = 2`, fibre `Circle`), slim (`k = 1`, fibre `S²`
(`ClosureSphere`) OR `T²` (`Circle × Circle`)), edge (`k = 1`, fibre `ClosedCell 2`, rim at
`T = C.heightRatio = 4Δ`) — and the buffered sources. Fibre types are DERIVED
(`circle_fibre_BIFc`, `slim_fibre_BIFc`, `edge_fibre_BIFc`); properness and ranks are `Bs`'s. -/
structure BoundaryWholeFiberSpecV2 (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (Bs : BoundaryGaf02BasesV2 C) : Prop where
  /-- Circle stage: smooth `ℝ² × S¹` charts of `f₁` over `B₁`. -/
  circle_chart : ∀ y ∈ Bs.base 0, SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2
    (C.stageMap 0) (Bs.source 0) (Bs.base 0) y
  /-- Slim stage: smooth `ℝ × S²` OR `ℝ × T²` charts of `f₃` over `B₃` (S² OR T², D69-1). -/
  slim_chart : ∀ y ∈ Bs.base 2,
    SmoothProductChartAt_BIFc W.model (𝓡 2) (F := GC.GraphManifold.ClosureSphere.{0}) 1
        (C.stageMap 2) (Bs.source 2) (Bs.base 2) y ∨
      SmoothProductChartAt_BIFc W.model ((𝓡 1).prod (𝓡 1)) (F := Circle × Circle) 1
        (C.stageMap 2) (Bs.source 2) (Bs.base 2) y
  /-- Edge stage: smooth `ℝ × D²` charts of `f₂` over `B₂` with the rim at `T = 4Δ`. -/
  edge_chart : ∀ y ∈ Bs.base 1, SmoothDiskChartAt_BIFc W.model 1 (C.stageMap 1) C.heightRatio
    (4 * Δ) (Bs.source 1) (Bs.base 1) y
  /-- The whole source domains lie in the buffered interior domain `{D > 10}`. -/
  source_buffered : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}

namespace BoundaryWholeFiberSpecV2

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (WF : BoundaryWholeFiberSpecV2 C Bs)
include WF

/-- **Derived: whole circle fibres** `≃ₜ S¹`. -/
theorem circle_fibre_BIFc : ∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle) :=
  fun y hy => (WF.circle_chart y hy).nonempty_fibre_homeomorph

/-- **Derived: whole slim fibres** `≃ₜ S²` OR `≃ₜ T²` (D69-1). -/
theorem slim_fibre_BIFc : ∀ y ∈ Bs.base 2,
    Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle) := by
  intro y hy
  rcases WF.slim_chart y hy with h | h
  · obtain ⟨e⟩ := h.nonempty_fibre_homeomorph
    exact Or.inl ⟨e.trans Homeomorph.ulift⟩
  · exact Or.inr h.nonempty_fibre_homeomorph

/-- **Derived: whole edge disk fibres** in v1's form: `≃ₜ ClosedCell 2` with the unit circle onto
the vertical part `fibre ∩ {T = 4Δ}` of the SAME chain's `T = C.heightRatio`. -/
theorem edge_fibre_BIFc : ∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
    Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
      Bs.fibre 1 y ∩ {p | C.heightRatio p = 4 * Δ} :=
  fun y hy => (WF.edge_chart y hy).fibre_disk_rim

/-- **Conditional projection to v1** (`BoundaryWholeFiberSpec`) on a v1 BASES object with the
same sources and bases, when every slim fibre is a torus (v1 has no sphere branch). -/
theorem toV1_BIFc (Bs₁ : BoundaryGaf02Bases C) (hs : Bs₁.source = Bs.source)
    (hb : Bs₁.base = Bs.base)
    (htor : ∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) :
    BoundaryWholeFiberSpec C Bs₁ where
  circle_fibre := fun y hy => by
    have hf : Bs₁.fibre 0 y = Bs.fibre 0 y := by
      simp only [BoundaryGaf02Bases.fibre, BoundaryGaf02BasesV2.fibre, hs]
    rw [hf]
    exact WF.circle_fibre_BIFc y (hb ▸ hy)
  slim_fibre := fun y hy => by
    have hf : Bs₁.fibre 2 y = Bs.fibre 2 y := by
      simp only [BoundaryGaf02Bases.fibre, BoundaryGaf02BasesV2.fibre, hs]
    rw [hf]
    exact htor y (hb ▸ hy)
  edge_fibre := fun y hy => by
    have hf : Bs₁.fibre 1 y = Bs.fibre 1 y := by
      simp only [BoundaryGaf02Bases.fibre, BoundaryGaf02BasesV2.fibre, hs]
    rw [hf]
    exact WF.edge_fibre_BIFc y (hb ▸ hy)
  source_buffered := fun st => by
    rw [hs]
    exact WF.source_buffered st

end BoundaryWholeFiberSpecV2

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **The whole-fibre layer v2 of the empty v2 bases** (vacuous: no base point). -/
theorem emptyWholeFiberSpecV2_BIFc (hc : ∀ st, S.stageCentres_BIF st = ∅)
    (hF : Continuous S.boundaryOriginalMap) :
    BoundaryWholeFiberSpecV2 C (C.emptyBasesV2_BIFc hc hF) where
  circle_chart := fun y hy => (notMem_empty y hy).elim
  slim_chart := fun y hy => (notMem_empty y hy).elim
  edge_chart := fun y hy => (notMem_empty y hy).elim
  source_buffered := fun _ => empty_subset _

end BoundaryGaf02Chain


end DifferentialGeometry.Geometry.Collapse
