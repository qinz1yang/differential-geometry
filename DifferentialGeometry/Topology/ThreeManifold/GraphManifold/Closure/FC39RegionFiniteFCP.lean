import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39LocalFacesFiniteFCP
import DifferentialGeometry.Topology.Connected.FibreComponentsFCP

/-!
# FC39: the finite list of components of `M₃` (the FDC04 list), from `local_faces`

Lane S-FINCOMP, group G3 (suffix `_FCP`). With the circle bundle `R.circle` of the rows
(`M₃ = D.M₃ = R.circle.region = proj⁻¹(C₁)`, whole connected circle fibres, compact by the
properness field of `CircleCutFacts74`): the components of `M₃` are the preimages of the components
of `C₁`, hence open, hence finite in number.

* `JunctionRimFacts74.circle_region_finite_components_FCP`: for every
  `G : JunctionRimFacts74 A D R`, `D.M₃` is the disjoint union of finitely many compact connected
  subsets of the ambient carrier (the FDC04 list for the two-stratum piece).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **The finite list of components of `M₃`** (see the module docstring): finitely many pairwise
disjoint compact connected sets of the carrier with union `M₃`. -/
theorem JunctionRimFacts74.circle_region_finite_components_FCP (G : JunctionRimFacts74 A D R) :
    ∃ (m : ℕ) (Bm : Fin m → Set W.Carrier), (∀ i, IsCompact (Bm i)) ∧
      (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧ D.M₃ = ⋃ i, Bm i := by
  have hlc : LocallyConnectedSpace R.circle.cbase :=
    locallyConnectedSpace_of_local_faces_FCP fun c hc => by
      obtain ⟨U, hcU, L, φ, -, -, hφ, hsurj, hcb⟩ := G.local_faces c hc
      exact ⟨U, hcU, L, φ, fun f hf => (hφ f hf).1, hsurj, hcb⟩
  let T := {x : R.circle.domain // R.circle.proj x ∈ R.circle.cbase}
  let g : T → W.Carrier := fun x => ((x.1 : R.circle.domain) : W.Carrier)
  have hg : Topology.IsEmbedding g :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : range g = R.circle.region := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcomp : IsCompact R.circle.region :=
    R.circleFacts.proper R.circle.cbase R.circle.cbase_compact
  have : CompactSpace T := by
    rw [← isCompact_univ_iff, hg.isCompact_iff, image_univ, hrange]
    exact hcomp
  let f : T → R.circle.cbase := fun x => ⟨R.circle.proj x.1, x.2⟩
  have hf : Continuous f := (R.circle.proj.continuous.comp continuous_subtype_val).subtype_mk _
  have hfs : Surjective f := fun z => by
    obtain ⟨x, hx⟩ := R.circle.proj_surjective_GGFF z.1
    exact ⟨⟨x, hx ▸ z.2⟩, Subtype.ext hx⟩
  have hfib : ∀ z : R.circle.cbase, IsConnected (f ⁻¹' {z}) := by
    intro z
    have hc := R.circle.isConnected_fibre_GRIM z.1
    have himg : g '' (f ⁻¹' {z}) = R.circle.fibre z.1 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.1, congrArg Subtype.val hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy ▸ z.2⟩, Subtype.ext hy, rfl⟩
    rw [← himg] at hc
    exact ⟨hc.nonempty.of_image,
      hg.isInducing.isPreconnected_image.mp hc.isPreconnected⟩
  have hopen : ∀ x : T, IsOpen (connectedComponent x) :=
    isOpen_connectedComponent_of_fibres_FCP hf hfs hfib fun z => isOpen_connectedComponent
  obtain ⟨m, Bm, hc, hcon, -, hd, hU⟩ := exists_finite_components_of_embedding_FCP hg hopen
  refine ⟨m, Bm, hc, hcon, hd, ?_⟩
  rw [← StageCutChoice74.region_circleBundle74_eq_M₃ D R.circleFacts]
  exact hrange.symm.trans hU

/-- **Shape example (the FDC04 finite-list clause for the two-stratum piece)**: the circle base
`C₁` and `M₃` are finite disjoint unions of compact connected pieces, from the gate fact
`G : JunctionRimFacts74 A D R` alone. -/
example (G : JunctionRimFacts74 A D R) :
    (∃ (m : ℕ) (Bc : Fin m → Set R.circle.Base), (∀ i, IsCompact (Bc i)) ∧
      (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧ R.circle.cbase = ⋃ i, Bc i) ∧
    (∃ (m : ℕ) (Bm : Fin m → Set W.Carrier), (∀ i, IsCompact (Bm i)) ∧
      (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧ D.M₃ = ⋃ i, Bm i) := by
  obtain ⟨m, Bc, h1, h2, -, -, -, h6, h7⟩ := G.circle_cbase_finite_components_FCP
  exact ⟨⟨m, Bc, h1, h2, h6, h7⟩, G.circle_region_finite_components_FCP⟩

end GC.GraphManifold.Assembly.FC39P0
