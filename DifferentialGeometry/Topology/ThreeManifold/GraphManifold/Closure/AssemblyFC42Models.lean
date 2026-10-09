import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BasicModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces

/-!
# FC42 pieces B13 and B8: model changes for `T² × I` pieces and reversed handles

* **B13** `annulusCircleCarrierDiffeomorphTorusInterval`: B3's raw `T² × I` carrier
  `annulusCircleCarrier` (`productCarrier 2`) is diffeomorphic to the certificate's product model
  `Torus × Icc 0 1` with the product corner model `torusModel.prod (𝓡∂ 1)` — this is the tree's
  `torusMonodromyPolarDiffeomorph` (`Closure/TorusMonodromy.lean`). Consequently the vertex models
  `SlimModel.torusInterval` and `Vertex.cuspCore` land in the `hpiece` format of
  `exists_rawGraphPresentation_of_regularCutData` (`rawPiece_of_torusInterval`).
* **B8** `iccReflect` (the tree's `torusMonodromyIntervalReflection`, `t ↦ 1 − t`) and
  `EdgeHandle.reverse`: a product disk handle run backwards, with all five fields of `EdgeHandle`;
  `EdgeHandle.orient σ` reverses when `σ = true`. The end disks and the image are as expected
  (`orient_map_iccEnd`, `orient_endDisk`, `orient_range`, `orient_vertical`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASMV3M : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMV3M : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## B13 -/

/-- **B13.** The raw `T² × I` carrier is the certificate's product `Torus × Icc 0 1`. -/
def annulusCircleCarrierDiffeomorphTorusInterval :
    annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, torusModel.prod (𝓡∂ 1)⟯
      (Torus × Icc (0 : ℝ) 1) :=
  torusMonodromyPolarDiffeomorph.{u}

theorem nonempty_annulusCircleCarrier_diffeomorph_torusInterval :
    Nonempty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model,
      torusModel.prod (𝓡∂ 1)⟯ (Torus × Icc (0 : ℝ) 1)) :=
  ⟨annulusCircleCarrierDiffeomorphTorusInterval⟩

/-- A piece diffeomorphic to the product `Torus × Icc 0 1` is in the `hpiece` format of B3. -/
theorem rawPiece_of_torusInterval {W : CompactCarrier.{u}} (P : PieceFold W)
    (e : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ P.Piece) :=
  ⟨annulusCircleCarrier.{u}, ⟨annulusRawPresentation.{u}⟩,
    ⟨annulusCircleCarrierDiffeomorphTorusInterval.trans e⟩⟩

/-! ## B8 -/

/-- **B8.** The smooth reflection `t ↦ 1 − t` of `[0, 1]` in the `𝓡∂ 1` model. -/
def iccReflect : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1 :=
  torusMonodromyIntervalReflection

theorem iccReflect_val (t : Icc (0 : ℝ) 1) : (iccReflect t : ℝ) = 1 - t := rfl

theorem iccReflect_iccEnd (b : Bool) : iccReflect (iccEnd b) = iccEnd (!b) := by
  cases b <;> ext <;> simp [iccReflect_val, iccEnd]

theorem iccReflect_iccReflect (t : Icc (0 : ℝ) 1) : iccReflect (iccReflect t) = t := by
  ext
  simp [iccReflect_val]

/-- The reflection of the interval factor of `ClosedCell 2 × Icc 0 1`. -/
def handleReflect :
    (ClosedCell 2 × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡∂ 2).prod (𝓡∂ 1), (𝓡∂ 2).prod (𝓡∂ 1)⟯
      (ClosedCell 2 × Icc (0 : ℝ) 1) :=
  (Diffeomorph.refl (𝓡∂ 2) (ClosedCell 2) ∞).prodCongr iccReflect

theorem handleReflect_apply (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    handleReflect p = (p.1, iccReflect p.2) := rfl

/-- **B8.** A product disk handle run backwards: `(x, t) ↦ H (x, 1 − t)`. -/
def EdgeHandle.reverse {W : CompactCarrier.{u}} (H : EdgeHandle W) : EdgeHandle W where
  map := H.map ∘ handleReflect
  smooth := H.smooth.comp handleReflect.contMDiff
  mfderiv_bijective p :=
    GC.Seifert.mfderiv_comp_diffeomorph_symm_bijective handleReflect H.smooth p
      (H.mfderiv_bijective _)
  injective := H.injective.comp handleReflect.injective
  interior := by
    rintro _ ⟨p, rfl⟩
    exact H.interior ⟨_, rfl⟩

theorem EdgeHandle.reverse_map {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (p : ClosedCell 2 × Icc (0 : ℝ) 1) : H.reverse.map p = H.map (p.1, iccReflect p.2) := rfl

/-- A handle with a traversal orientation: reversed when `σ = true`. -/
def EdgeHandle.orient {W : CompactCarrier.{u}} (σ : Bool) (H : EdgeHandle W) : EdgeHandle W :=
  cond σ H.reverse H

theorem EdgeHandle.orient_map_iccEnd {W : CompactCarrier.{u}} (σ : Bool) (H : EdgeHandle W)
    (x : ClosedCell 2) (b : Bool) :
    (H.orient σ).map (x, iccEnd b) = H.map (x, iccEnd (xor b σ)) := by
  cases σ
  · simp [EdgeHandle.orient]
  · simp [EdgeHandle.orient, EdgeHandle.reverse_map, iccReflect_iccEnd]

theorem EdgeHandle.orient_endDisk {W : CompactCarrier.{u}} (σ : Bool) (H : EdgeHandle W)
    (b : Bool) : (H.orient σ).endDisk b = H.endDisk (xor b σ) := by
  ext z
  simp only [EdgeHandle.endDisk, mem_range, EdgeHandle.orient_map_iccEnd]

theorem EdgeHandle.orient_range {W : CompactCarrier.{u}} (σ : Bool) (H : EdgeHandle W) :
    range (H.orient σ).map = range H.map := by
  cases σ
  · rfl
  · change range (H.map ∘ handleReflect) = range H.map
    have hs : range (handleReflect : ClosedCell 2 × Icc (0 : ℝ) 1 → ClosedCell 2 × Icc (0 : ℝ) 1) =
        univ :=
      handleReflect.toEquiv.surjective.range_eq
    rw [range_comp, hs, image_univ]

theorem EdgeHandle.orient_vertical {W : CompactCarrier.{u}} (σ : Bool) (H : EdgeHandle W) :
    (H.orient σ).vertical = H.vertical := by
  cases σ
  · rfl
  · change (H.map ∘ handleReflect) '' (diskRim ×ˢ univ) = H.map '' (diskRim ×ˢ univ)
    rw [image_comp]
    congr 1
    ext p
    constructor
    · rintro ⟨q, ⟨hq, -⟩, rfl⟩
      exact ⟨hq, mem_univ _⟩
    · rintro ⟨hp, -⟩
      exact ⟨(p.1, iccReflect p.2), ⟨hp, mem_univ _⟩, by
        simp [handleReflect_apply, iccReflect_iccReflect]⟩

end GC.GraphManifold.Assembly
