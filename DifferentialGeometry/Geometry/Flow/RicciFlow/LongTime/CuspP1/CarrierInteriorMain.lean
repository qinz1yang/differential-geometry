import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CarrierInteriorPush
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.GluingInjectionTheorem

/-!
# CP1-C2: carrier pieces of a torus presentation are `π₁`-injective into `W`

`interiorImage = cutOpen ∅` (closed `W`), and every carrier piece `G.components.piece i` of the cut
carrier, boundary tori included, maps `π₁`-injectively into `W` at every basepoint
(`injective_pieceMap_CPC2`); so does the whole cut carrier (`injective_cutMap_CPC2`).
Route: the inward collar push of `CarrierInteriorPush` (`id ≃ r`, `r` into the interior) transports
the tree's K19 piece-interior injectivity (`injective_pieceInterior_of_ports`) to the piece.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace GC.LongTime.CuspP1
open GC.Seifert

variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

/-- The cut map as a continuous map. -/
def cutMapC_CPC2 : C(G.cutCarrier.Carrier, W.Carrier) :=
  ⟨G.cutMap, (G.reconstruction.continuous.comp G.pairing.quotientMap.continuous)⟩

/-- The actual carrier piece (with its boundary tori) mapped into `W`. -/
def pieceMap_CPC2 (i : Fin G.components.count) : C(↥(G.components.piece i), W.Carrier) :=
  (cutMapC_CPC2 G).comp ⟨Subtype.val, continuous_subtype_val⟩

variable {G}

theorem interiorImage_eq_cutOpen_CPC2 (hext : G.externalCount = 0) :
    (G.interiorImage : Set W.Carrier) = G.cutOpen ∅ := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := G.interiorDiffeomorph.surjective ⟨y, hy⟩
    have h : y = G.cutMap x.val := by
      have := congrArg Subtype.val hx
      exact this.symm.trans (G.interior_map x)
    rw [h]
    exact G.cutMap_mem_cutOpen_empty x.2
  · exact fun hy => G.mem_interiorImage hext hy


/-- Frozen statement (CP1-C2): every actual carrier piece, boundary tori included, is
`π₁`-injective into `W` at every basepoint, given injective ports and no external ports. -/
theorem injective_pieceMap_CPC2 (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (i : Fin G.components.count)
    (x : G.components.piece i) :
    Function.Injective (FundamentalGroup.map (pieceMap_CPC2 G i) x) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := exists_inward_homotopy_CPC2 (G.pieceBoundaryTori i)
    (G.pieceBoundaryTori_image i)
  have hr' : ∀ p, (r p).val ∈ G.cutCarrier.interior := fun p =>
    (G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val (u := G.components.piece i)).mp
      (hr p)
  let ρ : C(↥(G.components.piece i), G.cutCarrier.pieceInterior (G.components.piece i)) :=
    ⟨fun p => ⟨(r p).val, (r p).2, hr' p⟩, by fun_prop⟩
  let ι : C(G.cutCarrier.pieceInterior (G.components.piece i), ↥(G.components.piece i)) :=
    ⟨fun y => ⟨y.1, y.2.1⟩, by fun_prop⟩
  have hιρ : ι.comp ρ = r := ContinuousMap.ext fun _ => rfl
  have hid : Function.Injective (FundamentalGroup.map
      (ContinuousMap.id (↥(G.components.piece i))) x) :=
    injective_fundamentalGroup_map_of_leftInverse _ (ContinuousMap.id _) (fun _ => rfl) x
  have hrinj : Function.Injective (FundamentalGroup.map r x) :=
    (GC.Topology.homotopic_injective_iff _ _ H x).mp hid
  have hρ : Function.Injective (FundamentalGroup.map ρ x) := by
    apply GC.Topology.injective_inner_of_composite ρ ι x
    rw [hιρ]
    exact hrinj
  have hint := G.injective_pieceInterior_of_ports hext hports i (ρ x)
  have hcomp : Function.Injective (FundamentalGroup.map
      ((G.pieceInteriorToCarrier i).comp ρ) x) := by
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact hint.comp hρ
  have he : (G.pieceInteriorToCarrier i).comp ρ = (pieceMap_CPC2 G i).comp r :=
    ContinuousMap.ext fun _ => rfl
  rw [he] at hcomp
  let hF : ((pieceMap_CPC2 G i).comp (ContinuousMap.id _)).Homotopy ((pieceMap_CPC2 G i).comp r) :=
    { toFun := fun y => pieceMap_CPC2 G i (H y)
      continuous_toFun := (pieceMap_CPC2 G i).continuous.comp H.continuous
      map_zero_left := fun p => congrArg (pieceMap_CPC2 G i) (H.apply_zero p)
      map_one_left := fun p => congrArg (pieceMap_CPC2 G i) (H.apply_one p) }
  have := (GC.Topology.homotopic_injective_iff _ _ hF x).mpr hcomp
  rwa [ContinuousMap.comp_id] at this

open Classical in
/-- Retraction of the cut carrier onto a clopen piece. -/
def pieceRetraction_CPC2 (i : Fin G.components.count) (z : ↥(G.components.piece i)) :
    C(G.cutCarrier.Carrier, ↥(G.components.piece i)) := by
  refine ⟨fun y => ⟨if y ∈ (G.components.piece i : Set G.cutCarrier.Carrier) then y else z.val,
    ?_⟩, ?_⟩
  · split_ifs with hy
    exacts [hy, z.2]
  · refine Continuous.subtype_mk (Continuous.if (fun a ha => ?_) continuous_id continuous_const) _
    have hcl : IsClopen (G.components.piece i : Set G.cutCarrier.Carrier) :=
      ⟨G.components.closed i, (G.components.piece i).isOpen⟩
    rw [show {y : G.cutCarrier.Carrier | y ∈ (G.components.piece i : Set G.cutCarrier.Carrier)} =
      (G.components.piece i : Set G.cutCarrier.Carrier) from rfl, hcl.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty _)

open Classical in
/-- The whole cut carrier is `π₁`-injective into `W` at every basepoint. -/
theorem injective_cutMap_CPC2 (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (x : G.cutCarrier.Carrier) :
    Function.Injective (FundamentalGroup.map (cutMapC_CPC2 G) x) := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ G.components.piece i := by
    have := G.components.covers
    have hx : x ∈ ⋃ i, (G.components.piece i : Set G.cutCarrier.Carrier) := this ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩
  let v : C(↥(G.components.piece i), G.cutCarrier.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  let z : ↥(G.components.piece i) := ⟨x, hi⟩
  have hr : Function.LeftInverse (pieceRetraction_CPC2 (G := G) i z) v := fun p => by
    apply Subtype.ext
    change (if p.val ∈ (G.components.piece i : Set G.cutCarrier.Carrier) then p.val else z.val) = p.val
    exact if_pos p.2
  have hcl : IsClopen (G.components.piece i : Set G.cutCarrier.Carrier) :=
    ⟨G.components.closed i, (G.components.piece i).isOpen⟩
  have hsurj : Function.Surjective (FundamentalGroup.map v z) :=
    surjective_fundamentalGroup_map_of_clopen v (pieceRetraction_CPC2 (G := G) i z) hr _ hcl
      (fun y hy => by
        change (if y ∈ (G.components.piece i : Set G.cutCarrier.Carrier) then y else z.val) = y
        exact if_pos hy) z hi
  exact injective_fundamentalGroup_map_of_comp v (cutMapC_CPC2 G) z hsurj
    (injective_pieceMap_CPC2 hext hports i z)

end GC.LongTime.CuspP1
