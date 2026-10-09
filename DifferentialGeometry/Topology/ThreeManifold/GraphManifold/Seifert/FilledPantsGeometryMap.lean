import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Geometry.Thurston.FoldDescent
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product

/-!
# Folds through the product chart of a charted Seifert block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3,
with the errata after review 21). For charts `C` of a Seifert block, `C.chartProductMap` is the
product chart `planarOpen d.k × S¹ → W.pieceInterior ⊤`, read in the interior atlas of the block
(model `𝓡 3`): a local diffeomorphism, injective, with range the product region. A map
`G : X → ℂ × S¹` whose first coordinate stays in `planarOpen d.k` is pushed into the block as
`C.throughProduct G hG`; it is a local diffeomorphism as soon as `G` is one
(`isLocalDiffeomorph_throughProduct`), and two points have the same image iff they have the same
`G`-value. On an open `N` of a model manifold `X` this gives the fold `C.foldThroughProduct N G hG`,
and a same-image normal form for `G` (an ambient isometry `γ` carrying `y` to `y'` and preserving
`G` near `y`) gives the fibre compatibility required by `GeometricStructure.ofFold`
(`metricFiberCompatible_foldThroughProduct`, through `metricFiberCompatible_of_foldPairs`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

namespace SeifertBlockCharts

variable (C : SeifertBlockCharts W d)

theorem productRegion_le_pieceInterior : C.productRegion ≤ W.pieceInterior ⊤ :=
  fun _ hx => ⟨trivial, C.productRegion_interior hx⟩

def chartProductMap (x : planarOpen d.k × Circle) : W.pieceInterior ⊤ :=
  ⟨(C.product x : W.Carrier), C.productRegion_le_pieceInterior (C.product x).2⟩

theorem chartProductMap_val (x : planarOpen d.k × Circle) :
    (C.chartProductMap x : W.Carrier) = C.product x :=
  rfl

theorem chartProductMap_injective : Function.Injective C.chartProductMap := by
  intro x y h
  have h' := congrArg (fun z : W.pieceInterior ⊤ => (z : W.Carrier)) h
  exact C.product.injective (Subtype.ext h')

theorem exists_chartProductMap_eq {x : W.pieceInterior ⊤}
    (hx : (x : W.Carrier) ∈ C.productRegion) : ∃ y, C.chartProductMap y = x := by
  obtain ⟨y, hy⟩ := C.product.surjective ⟨x, hx⟩
  have hy' : (C.product y : W.Carrier) = x := congrArg Subtype.val hy
  exact ⟨y, Subtype.ext hy'⟩

theorem isLocalDiffeomorph_chartProductMap :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph PlaneCircleModel (𝓡 3) ∞ C.chartProductMap := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hinc : IsLocalDiffeomorph W.model W.model ∞
      (TopologicalSpace.Opens.inclusion C.productRegion_le_pieceInterior) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict
      (fun z : C.productRegion => C.productRegion_le_pieceInterior z.property)
      (isLocalDiffeomorph_subtype_val C.productRegion y)
  exact isLocalDiffeomorph_comp
    (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.pieceInterior ⊤)).isLocalDiffeomorph
    (isLocalDiffeomorph_comp hinc C.product.isLocalDiffeomorph)

section Through

variable {X : Type*}

def throughProduct (G : X → ℂ × Circle) (hG : ∀ x, (G x).1 ∈ planarOpen d.k) (x : X) :
    W.pieceInterior ⊤ :=
  C.chartProductMap (⟨(G x).1, hG x⟩, (G x).2)

theorem throughProduct_val (G : X → ℂ × Circle) (hG : ∀ x, (G x).1 ∈ planarOpen d.k) (x : X) :
    (C.throughProduct G hG x : W.Carrier) = C.product (⟨(G x).1, hG x⟩, (G x).2) :=
  rfl

theorem throughProduct_congr {G G' : X → ℂ × Circle} (hG : ∀ x, (G x).1 ∈ planarOpen d.k)
    (hG' : ∀ x, (G' x).1 ∈ planarOpen d.k) {x y : X} (h : G x = G' y) :
    C.throughProduct G hG x = C.throughProduct G' hG' y := by
  have h1 : (⟨(G x).1, hG x⟩ : planarOpen d.k) = ⟨(G' y).1, hG' y⟩ :=
    Subtype.ext (congrArg Prod.fst h)
  unfold throughProduct
  rw [h1, show (G x).2 = (G' y).2 from congrArg Prod.snd h]

theorem throughProduct_eq_iff (G : X → ℂ × Circle) (hG : ∀ x, (G x).1 ∈ planarOpen d.k)
    {x y : X} : C.throughProduct G hG x = C.throughProduct G hG y ↔ G x = G y := by
  constructor
  · intro h
    have h' := C.chartProductMap_injective h
    have h1 : (G x).1 = (G y).1 := congrArg (fun z : planarOpen d.k × Circle => z.1.val) h'
    have h2 : (G x).2 = (G y).2 := congrArg (fun z : planarOpen d.k × Circle => z.2) h'
    exact Prod.ext h1 h2
  · intro h
    exact C.throughProduct_congr hG hG h

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

omit C in
theorem isLocalDiffeomorph_planarRestrict (G : X → ℂ × Circle)
    (hG : ∀ x, (G x).1 ∈ planarOpen d.k) (hGl : IsLocalDiffeomorph I PlaneCircleModel ∞ G) :
    IsLocalDiffeomorph I PlaneCircleModel ∞
      (fun x => ((⟨(G x).1, hG x⟩ : planarOpen d.k), (G x).2)) := by
  intro x
  have hc : Continuous G := hGl.contMDiff.continuous
  have hcont : Continuous fun x => ((⟨(G x).1, hG x⟩ : planarOpen d.k), (G x).2) :=
    (hc.fst.subtype_mk hG).prodMk hc.snd
  have he : IsLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞
      (Prod.map (Subtype.val : planarOpen d.k → ℂ) (id : Circle → Circle))
      ((⟨(G x).1, hG x⟩ : planarOpen d.k), (G x).2) :=
    (isLocalDiffeomorph_subtype_val (planarOpen d.k) _).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _)
  exact IsLocalDiffeomorphAt.of_comp_left he (hGl x) hcont.continuousAt

theorem isLocalDiffeomorph_throughProduct (G : X → ℂ × Circle)
    (hG : ∀ x, (G x).1 ∈ planarOpen d.k) (hGl : IsLocalDiffeomorph I PlaneCircleModel ∞ G) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph I (𝓡 3) ∞ (C.throughProduct G hG) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact isLocalDiffeomorph_comp C.isLocalDiffeomorph_chartProductMap
    (isLocalDiffeomorph_planarRestrict G hG hGl)

end Through

section Fold

variable {X : Type*} [TopologicalSpace X]

def foldThroughProduct (N : TopologicalSpace.Opens X) (G : X → ℂ × Circle)
    (hG : ∀ p ∈ N, (G p).1 ∈ planarOpen d.k) : N → W.pieceInterior ⊤ :=
  C.throughProduct (fun p : N => G p) (fun p => hG p p.2)

theorem foldThroughProduct_eq_iff (N : TopologicalSpace.Opens X) (G : X → ℂ × Circle)
    (hG : ∀ p ∈ N, (G p).1 ∈ planarOpen d.k) {y y' : N} :
    C.foldThroughProduct N G hG y = C.foldThroughProduct N G hG y' ↔ G y = G y' :=
  C.throughProduct_eq_iff _ _

theorem isLocalDiffeomorph_foldThroughProduct [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (N : TopologicalSpace.Opens X)
    (G : X → ℂ × Circle) (hG : ∀ p ∈ N, (G p).1 ∈ planarOpen d.k)
    (hGl : IsLocalDiffeomorph (𝓡 3) PlaneCircleModel ∞ (fun p : N => G p)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.foldThroughProduct N G hG) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact C.isLocalDiffeomorph_throughProduct _ _ hGl

theorem metricFiberCompatible_foldThroughProduct [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] (g : SmoothRiemannianMetric (𝓡 3) X)
    (N : TopologicalSpace.Opens X) (G : X → ℂ × Circle)
    (hG : ∀ p ∈ N, (G p).1 ∈ planarOpen d.k)
    (hF : letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.foldThroughProduct N G hG))
    (hpair : ∀ y y' : N, G y = G y' → ∃ γ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X,
      Diffeomorph.pullbackMetric g γ = g ∧ γ (y : X) = (y' : X) ∧
        ∃ U : TopologicalSpace.Opens X, (y : X) ∈ U ∧ (U : Set X) ⊆ N ∧
          Set.MapsTo γ (U : Set X) N ∧ ∀ z ∈ U, G (γ z) = G z) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    metricFiberCompatible (g.restrictOpen N) (C.foldThroughProduct N G hG) hF := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  let _ := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  refine metricFiberCompatible_of_foldPairs g N _ hF fun y y' hyy => ?_
  obtain ⟨γ, hγg, hγy, U, hyU, hUN, hmaps, hGU⟩ :=
    hpair y y' ((C.foldThroughProduct_eq_iff N G hG).1 hyy)
  refine ⟨γ, hγg, hγy, U, hyU, hUN, hmaps, fun z => ?_⟩
  exact (C.foldThroughProduct_eq_iff N G hG).2 (hGU z z.property)

end Fold

end SeifertBlockCharts

end GC.Seifert
