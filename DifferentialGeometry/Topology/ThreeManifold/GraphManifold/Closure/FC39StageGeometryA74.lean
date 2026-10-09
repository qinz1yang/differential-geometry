import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# Draft 74, package A0, part 1: the actual stage geometry `A` and its restriction to open bases

Lane S-JUNCTIONS (suffix `_JN74`). Draft 74 §4.1 / D74-15: the shared assembler
`rows_of_smooth_stage_geometry74 (A) (D) (H)` has three inputs. This module defines the first one,
**`SmoothStageGeometry74 W E`** (the ACTUAL smooth stage maps before any cut: the zero and cusp core
models, the slim, edge and circle stages `parent ⊆ W`, `proj : parent → Base`, height, level), and
the restriction of a stage to an open base `V`, which is what the rows' `Base = ↥V` of D74-3 /
D74-11 / D74-13 is:

* `StageProj74 W k`: a smooth proper-type stage of base dimension `k` (an open parent inside the
  interior, a continuous map, smooth, a submersion);
* `StageProj74.restrictParent V = q⁻¹(V)` (open in `W`), `restrictProj V : q⁻¹(V) → ↥V` (smooth,
  submersion), through the tree's open-subtype calculus (`contMDiff_subtypeVal_comp_iff`,
  `mfderiv_subtypeVal_comp`, `mfderiv_opens_incl`);
* `SlimStage74`, `EdgeStage74` (extra data of the slim and edge stages), `SmoothStageGeometry74`.

Nothing here is a rows record: the zero and cusp families are the actual `ZeroDomains` /
`CuspCores` (the cut-independent selected core models, packages Z2 / BD0); the cut-dependent row
structures are produced by the assembler from `A`, the cut choice `D` and the cut geometry `H`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **A smooth stage of base dimension `k`** (draft 74 §4.1, `A`): an open parent inside the
interior of `W`, the actual final map `proj : parent → Base` onto a smooth `k`-manifold, smooth and
a submersion. The cut-dependent properties (properness, whole fibres, trivializations) are NOT here:
they live over the chosen good open base in `StageCutGeometry74`. -/
structure StageProj74 (W : CompactCarrier.{u}) (k : ℕ) where
  Base : Type u
  [baseTop : TopologicalSpace Base]
  [baseCharts : ChartedSpace (EuclideanSpace ℝ (Fin k)) Base]
  [baseSmooth : IsManifold (𝓡 k) ∞ Base]
  [baseT2 : T2Space Base]
  parent : TopologicalSpace.Opens W.Carrier
  parent_interior : (parent : Set W.Carrier) ⊆ W.interior
  proj : C(parent, Base)
  proj_smooth : ContMDiff W.model (𝓡 k) ∞ proj
  proj_submersion : ∀ x, Surjective (mfderiv W.model (𝓡 k) proj x)

attribute [instance] StageProj74.baseTop StageProj74.baseCharts StageProj74.baseSmooth
  StageProj74.baseT2

namespace StageProj74

variable {k : ℕ} (P : StageProj74 W k)

/-- The restriction of the parent to the whole preimage of an open base `V`. -/
def restrictParent (V : TopologicalSpace.Opens P.Base) : TopologicalSpace.Opens W.Carrier :=
  ⟨Subtype.val '' (P.proj ⁻¹' (V : Set P.Base)),
    P.parent.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage P.proj.continuous)⟩

theorem mem_restrictParent {P : StageProj74 W k} {V : TopologicalSpace.Opens P.Base}
    {x : W.Carrier} : x ∈ P.restrictParent V ↔ ∃ h : x ∈ P.parent, P.proj ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem exists_of_mem_restrictParent {V : TopologicalSpace.Opens P.Base} {x : W.Carrier}
    (hx : x ∈ P.restrictParent V) : ∃ h : x ∈ P.parent, P.proj ⟨x, h⟩ ∈ V :=
  mem_restrictParent.1 hx

theorem mem_restrictParent_of {V : TopologicalSpace.Opens P.Base} {x : W.Carrier}
    (h : x ∈ P.parent) (hx : P.proj ⟨x, h⟩ ∈ V) : x ∈ P.restrictParent V :=
  mem_restrictParent.2 ⟨h, hx⟩

theorem restrictParent_le (V : TopologicalSpace.Opens P.Base) : P.restrictParent V ≤ P.parent :=
  fun _ hx => (P.exists_of_mem_restrictParent hx).1

/-- The inclusion of the restricted parent into the parent. -/
def restrictIncl (V : TopologicalSpace.Opens P.Base) : P.restrictParent V → P.parent :=
  TopologicalSpace.Opens.inclusion (P.restrictParent_le V)

theorem proj_restrictIncl_mem (V : TopologicalSpace.Opens P.Base) (x : P.restrictParent V) :
    P.proj (P.restrictIncl V x) ∈ V := by
  obtain ⟨h, hx⟩ := P.exists_of_mem_restrictParent x.2
  exact hx

/-- The restricted projection `q⁻¹(V) → ↥V`. -/
def restrictProj (V : TopologicalSpace.Opens P.Base) : C(P.restrictParent V, V) where
  toFun x := ⟨P.proj (P.restrictIncl V x), P.proj_restrictIncl_mem V x⟩
  continuous_toFun :=
    (P.proj.continuous.comp (continuous_inclusion (P.restrictParent_le V))).subtype_mk _

@[simp] theorem restrictProj_val (V : TopologicalSpace.Opens P.Base) (x : P.restrictParent V) :
    ((P.restrictProj V x : V) : P.Base) = P.proj (P.restrictIncl V x) :=
  rfl

theorem restrictProj_smooth (V : TopologicalSpace.Opens P.Base) :
    ContMDiff W.model (𝓡 k) ∞ (P.restrictProj V) := by
  refine (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff V (P.restrictProj V)).1 ?_
  exact P.proj_smooth.comp (contMDiff_inclusion (P.restrictParent_le V))

theorem restrictProj_submersion (V : TopologicalSpace.Opens P.Base) (x : P.restrictParent V) :
    Surjective (mfderiv W.model (𝓡 k) (P.restrictProj V) x) := by
  intro v
  obtain ⟨u, hu⟩ := P.proj_submersion (P.restrictIncl V x) v
  refine ⟨u, ?_⟩
  have h1 := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := W.model) (J := 𝓡 k) V
    (P.restrictProj V) x
  have hid : mfderiv W.model W.model (P.restrictIncl V) x = ContinuousLinearMap.id ℝ _ :=
    DifferentialGeometry.mfderiv_opens_incl (P.restrictParent_le V) x
  have h2 : mfderiv W.model (𝓡 k) (P.proj ∘ P.restrictIncl V) x =
      (mfderiv W.model (𝓡 k) P.proj (P.restrictIncl V x)).comp
        (mfderiv W.model W.model (P.restrictIncl V) x) :=
    mfderiv_comp x (P.proj_smooth.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (n := ∞) (P.restrictParent_le V)).mdifferentiableAt (by simp))
  rw [hid] at h2
  have h3 := congrArg (fun L => L u) h2
  exact (congrArg (fun L => L u) h1).symm.trans (h3.trans hu)

end StageProj74

/-- **The slim stage** (`f₃ : parent → B₃`, ZSP04): the actual slim base with the stage map and the
three base sets the cut choice `K₃` is measured against: `C₃` (the slim base domain after the zero
removal), the required slab image `Q_req` and the face points `F₃ = ∂C₃`. -/
structure SlimStage74 (W : CompactCarrier.{u}) extends StageProj74 W 1 where
  C₃ : Set Base
  slabImage : Set Base
  facePoints : Set Base

/-- **The edge stage** (`q₁ : parent → B₂`, `T = A/s`, level `4Δ`): the actual edge base, the open
ambient parent, the final edge map, the actual height and the level. -/
structure EdgeStage74 (W : CompactCarrier.{u}) extends StageProj74 W 1 where
  height : parent → ℝ
  height_smooth : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ height
  level : ℝ

/-- **`A` (draft 74 §4.1, package A0): the actual smooth stage geometry** — the selected zero and
cusp core models (the cut-independent pieces) and the three actual stages (slim `f₃`, edge `q₁`
with its height, circle `q₀`) before any cut. -/
structure SmoothStageGeometry74 (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  zero : ZeroDomains W
  cusp : CuspCores W E
  slim : SlimStage74 W
  edge : EdgeStage74 W
  circle : StageProj74 W 2

/-- **`D` (draft 74 §1.3, D74-3): the explicit cut choice.** `K₃` (the compact slim base domain,
`slab ∪ F₃ ⊆ int K₃`, `∂K₃ ∩ F₃ = ∅`), `D₃ = K₃ ∩ C₃`, the actual compact edge / remaining circle
bases `C₂`, `C₁` and the good open base neighbourhoods `edgeBaseOpen ⊇ C₂`, `circleBaseOpen ⊇ C₁`
(`edgeBaseOpen = ⊥` when `C₂ = ∅`). Its accessors (`slimSet`, `edgeSource`, `circleSource`,
`edgeSet`, `circleRegion`, `M₂`, `M₃`; `M₁` is `regionM1 A.zero A.cusp`) are definitions, not
fields; `M₁ / M₂ / M₃` use the RELATIVE interiors of §5.7. -/
structure StageCutChoice74 {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    (A : SmoothStageGeometry74 W E) where
  K₃ : Set A.slim.Base
  D₃ : Set A.slim.Base
  C₂ : Set A.edge.Base
  C₁ : Set A.circle.Base
  edgeBaseOpen : TopologicalSpace.Opens A.edge.Base
  circleBaseOpen : TopologicalSpace.Opens A.circle.Base
  K₃_compact : IsCompact K₃
  D₃_compact : IsCompact D₃
  D₃_eq : D₃ = K₃ ∩ A.slim.C₃
  K₃_req : A.slim.slabImage ∪ A.slim.facePoints ⊆ interior K₃
  K₃_faces : Disjoint (frontier K₃) A.slim.facePoints
  C₂_sub : C₂ ⊆ edgeBaseOpen
  C₁_sub : C₁ ⊆ circleBaseOpen
  edgeBaseOpen_empty : C₂ = ∅ → edgeBaseOpen = ⊥

namespace StageCutChoice74

variable {A : SmoothStageGeometry74 W E} (D : StageCutChoice74 A)

/-- `slimSet = f₃⁻¹(D₃)`: the WHOLE inverse image of the compact slim base domain. -/
def slimSet : Set W.Carrier :=
  {x | ∃ h : x ∈ A.slim.parent, A.slim.proj ⟨x, h⟩ ∈ D.D₃}

/-- The edge source: the open ambient parent restricted to the whole `q₁`-preimage of the open
edge base. -/
abbrev edgeSource : TopologicalSpace.Opens W.Carrier :=
  A.edge.restrictParent D.edgeBaseOpen

/-- The circle source: the whole `q₀`-preimage of the open circle base (whole fibres). -/
abbrev circleSource : TopologicalSpace.Opens W.Carrier :=
  A.circle.restrictParent D.circleBaseOpen

/-- `M^edge = q₁⁻¹(C₂) ∩ {T ≤ 4Δ}` (FDC02). -/
def edgeSet : Set W.Carrier :=
  {x | ∃ h : x ∈ A.edge.parent, A.edge.proj ⟨x, h⟩ ∈ D.C₂ ∧ A.edge.height ⟨x, h⟩ ≤ A.edge.level}

/-- `M₃`'s expected circle description `q₀⁻¹(C₁)` (FDC03). -/
def circleRegion : Set W.Carrier :=
  {x | ∃ h : x ∈ A.circle.parent, A.circle.proj ⟨x, h⟩ ∈ D.C₁}

/-- `M₂ = M₁ \ int_{M₁} slimSet` (relative interior). -/
def M₂ : Set W.Carrier :=
  regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet

/-- `M₃ = M₂ \ int_{M₂} M^edge` (relative interior, FDC03 (Last)). -/
def M₃ : Set W.Carrier :=
  D.M₂ \ relInt D.M₂ D.edgeSet

/-- The restricted edge height `T` on the edge source. -/
def edgeHeight (x : D.edgeSource) : ℝ :=
  A.edge.height (A.edge.restrictIncl D.edgeBaseOpen x)

theorem edgeHeight_smooth : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ D.edgeHeight :=
  A.edge.height_smooth.comp (contMDiff_inclusion (n := ∞) (A.edge.restrictParent_le _))

theorem edgeSet_subset_edgeSource : D.edgeSet ⊆ D.edgeSource := fun _ ⟨h, hc, _⟩ =>
  A.edge.mem_restrictParent_of h (D.C₂_sub hc)

theorem circleRegion_subset_circleSource : D.circleRegion ⊆ D.circleSource := fun _ ⟨h, hc⟩ =>
  A.circle.mem_restrictParent_of h (D.C₁_sub hc)

theorem M₃_subset_M₂ : D.M₃ ⊆ D.M₂ := fun _ hx => hx.1

theorem M₂_subset_M₁ : D.M₂ ⊆ regionM1 A.zero A.cusp := fun _ hx => hx.1

end StageCutChoice74

end GC.GraphManifold.Assembly.FC39P0
