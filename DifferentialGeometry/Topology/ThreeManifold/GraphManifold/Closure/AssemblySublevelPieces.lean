import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevel
import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSlice
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Chapter-14 assembly, bridge B1-relative: regular sublevels of a carrier as pieces

Let `W` be a carrier (either model kind) and `f : W → ℝ` smooth with regular level `{f = c}` inside
the interior of `W`. The sublevel `{f ≤ c}` carries slice charts for both kinds at once: at level
points and at interior points the ambient-model producers `exists_sliceChart_of_zero` /
`exists_sliceChart_of_pos` (`RegularLevel/HalfSpaceSliceCharts.lean:143, 191`) apply to any model,
and only at physical boundary points (kind `withBoundary`) the restricted ambient chart
(`:260`) is used. The generic slice manifold (`RegularLevel/HalfSpaceSlice.lean:300`) then gives an
`𝓡∂ 3` structure with boundary `(∂W ∩ {f ≤ c}) ∪ {f = c}` and a smooth inclusion with bijective
differential. The sublevel is compact and locally connected, so its connected components are
finitely many open pieces; each is a `PieceEmbedding`.

* `carrierSublevelChartedSpace`, `carrierSublevel_isBoundaryPoint_iff`: the sublevel structure;
* `carrierSublevelPiece`: the piece of one connected component;
* `exists_pieces_of_regular_sublevel`: B1-relative, the frozen statement of the assembly design
  (`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §4 row §2).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry GC.Endpoint Manifold
open DifferentialGeometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The model half-space `ℍ³` is locally connected. -/
theorem locallyConnectedSpace_euclideanHalfSpace_three :
    LocallyConnectedSpace (EuclideanHalfSpace 3) := by
  have : LocallyPathConnectedSpace (range (𝓡∂ 3)) :=
    (𝓡∂ 3).convex_range.locallyPathConnectedSpace
  exact (𝓡∂ 3).isClosedEmbedding.isEmbedding.toHomeomorph.locallyConnectedSpace

section Sublevel

variable (W : CompactCarrier.{u})

/-- At a physical boundary point, a restricted chart of the carrier, written as an `ℍ³ × ℝ⁰`
slice chart of height `0`. Only kind `withBoundary` has such points. -/
theorem exists_boundary_sliceChart_carrier (x : W.Carrier) (hb : W.model.IsBoundaryPoint x)
    {U : Set W.Carrier} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph W.model ((𝓡∂ 3).prod 𝓘(ℝ, Fin 0 → ℝ)) W.Carrier
        (EuclideanHalfSpace 3 × (Fin 0 → ℝ)) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ ((Φ x).1.1 0 = 0 ↔ W.model.IsBoundaryPoint x) := by
  cases W with
  | mk k M =>
  cases k with
  | closed =>
    exfalso
    change (𝓡 3).IsBoundaryPoint x at hb
    exact ((𝓡 3).isInteriorPoint_iff_not_isBoundaryPoint x).mp
      BoundarylessManifold.isInteriorPoint hb
  | withBoundary =>
    exact exists_sliceChart_restrict (m := 2) x hU hxU

variable (f : W.Carrier → ℝ) (c : ℝ)

/-- Slice charts of the sublevel `{f ≤ c}` of a carrier, both kinds. -/
theorem carrierSublevel_sliceCharts (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x, f x = c → x ∈ W.interior) :
    ∀ x, f x ≤ c → ∃ p : PartialDiffeomorph W.model ((𝓡∂ 3).prod 𝓘(ℝ, Fin 0 → ℝ)) W.Carrier
        (EuclideanHalfSpace 3 × (Fin 0 → ℝ)) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, f y ≤ c ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ (W.model.IsBoundaryPoint x ∨ f x = c)) := by
  intro x hx
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      2 + 1 + Module.finrank ℝ (Fin 0 → ℝ) := by
    simp
  have hΨ : ContMDiff W.model 𝓘(ℝ, Fin 0 → ℝ) ∞ (fun _ : W.Carrier => (0 : Fin 0 → ℝ)) :=
    contMDiff_const
  have hB : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun y => c - f y) :=
    (contDiff_const.sub contDiff_id).contMDiff.comp hf
  have hiff : ∀ y, ((0 : Fin 0 → ℝ) = 0 ∧ 0 ≤ c - f y) ↔ f y ≤ c := fun y => by
    simp [sub_nonneg]
  by_cases hxr : f x = c
  · have hne : mfderiv W.model 𝓘(ℝ, ℝ) (fun y => c - f y) x ≠ 0 := by
      intro h0
      apply hreg x hxr
      have h := DifferentialGeometry.Manifold.mfderiv_const_sub_real
        ((hf x).mdifferentiableAt (by simp)) c
      have h' : -(show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from
          mfderiv W.model 𝓘(ℝ, ℝ) f x) = 0 := h.symm.trans h0
      exact neg_eq_zero.mp h'
    have hxint : W.model.IsInteriorPoint x := hint x hxr
    obtain ⟨Φ, hxΦ, hΦ1, hΦ⟩ := exists_sliceChart_of_zero (d := 2) hdim hΨ hB hxint
      (by rw [hxr, sub_self])
      (DifferentialGeometry.Topology.Manifold.surjective_mfderiv_zero_prod
        ((hB x).mdifferentiableAt (by simp)) hne)
    exact ⟨(Φ, 1), zero_le_one, hxΦ, fun y hy => (hiff y).symm.trans (hΦ y hy),
      iff_of_true hΦ1 (Or.inr hxr)⟩
  · have hlt : f x < c := lt_of_le_of_ne hx hxr
    by_cases hb : W.model.IsBoundaryPoint x
    · obtain ⟨Φ, hxΦ, hsub, hbd⟩ := exists_boundary_sliceChart_carrier W x hb
        (isOpen_lt hf.continuous continuous_const) hlt
      refine ⟨(Φ, 0), le_rfl, hxΦ, fun y hy => ?_, ?_⟩
      · exact iff_of_true (le_of_lt (hsub hy)) ⟨Subsingleton.elim _ _, (Φ y).1.2⟩
      · exact hbd.trans (or_iff_left hxr).symm
    · have hint' : W.model.IsInteriorPoint x :=
        (W.model.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hb
      obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos (d := 2) hdim hΨ hB hint'
        (sub_pos.mpr hlt) (fun _ => ⟨0, Subsingleton.elim (α := Fin 0 → ℝ) _ _⟩)
      exact ⟨(Φ, 0), le_rfl, hxΦ, fun y hy => (hiff y).symm.trans (hΦ y hy),
        iff_of_false (hΦpos x hxΦ).ne' (fun h => h.elim hb hxr)⟩

variable (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
  (hint : ∀ x, f x = c → x ∈ W.interior)

/-- The `𝓡∂ 3` structure on the sublevel `{f ≤ c}` of a carrier. -/
@[reducible]
def carrierSublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // f x ≤ c} :=
  sliceChartedSpace (d := 2) (fun x => f x ≤ c) (fun x => W.model.IsBoundaryPoint x ∨ f x = c)
    (carrierSublevel_sliceCharts W f c hf hreg hint)

theorem carrierSublevel_isManifold :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // f x ≤ c} :=
  slice_isManifold (d := 2) _ _ (carrierSublevel_sliceCharts W f c hf hreg hint)

theorem carrierSublevel_contMDiff_val :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    ContMDiff (𝓡∂ 3) W.model ∞ (Subtype.val : {x : W.Carrier // f x ≤ c} → W.Carrier) :=
  slice_contMDiff_val (d := 2) _ _ (carrierSublevel_sliceCharts W f c hf hreg hint)

theorem carrierSublevel_mfderiv_val_bijective (x : {x : W.Carrier // f x ≤ c}) :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    Bijective (mfderiv (𝓡∂ 3) W.model
      (Subtype.val : {x : W.Carrier // f x ≤ c} → W.Carrier) x) :=
  slice_mfderiv_val_bijective (d := 2) _ _ (carrierSublevel_sliceCharts W f c hf hreg hint)
    (by simp) x

variable {W f c} in
theorem carrierSublevel_isBoundaryPoint_iff {x : {x : W.Carrier // f x ≤ c}} :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    (𝓡∂ 3).IsBoundaryPoint x ↔ (W.model.IsBoundaryPoint x.1 ∨ f x.1 = c) :=
  slice_isBoundaryPoint_iff (d := 2) (carrierSublevel_sliceCharts W f c hf hreg hint)

theorem compactSpace_carrierSublevel (hfc : Continuous f) :
    CompactSpace {x : W.Carrier // f x ≤ c} :=
  isCompact_iff_compactSpace.mp (isClosed_le hfc continuous_const).isCompact

include hf hreg hint in
theorem locallyConnectedSpace_carrierSublevel :
    LocallyConnectedSpace {x : W.Carrier // f x ≤ c} := by
  let _ := carrierSublevelChartedSpace W f c hf hreg hint
  have := locallyConnectedSpace_euclideanHalfSpace_three
  exact ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) _

include hf hreg hint in
/-- The connected component `i` of the sublevel, as an open subset. -/
def carrierSublevelComponent (i : ConnectedComponents {x : W.Carrier // f x ≤ c}) :
    TopologicalSpace.Opens {x : W.Carrier // f x ≤ c} := by
  have := locallyConnectedSpace_carrierSublevel W f c hf hreg hint
  exact ⟨ConnectedComponents.mk ⁻¹' {i},
    (isOpen_discrete {i}).preimage ConnectedComponents.continuous_coe⟩

theorem coe_carrierSublevelComponent (i : ConnectedComponents {x : W.Carrier // f x ≤ c}) :
    (carrierSublevelComponent W f c hf hreg hint i : Set {x : W.Carrier // f x ≤ c}) =
      ConnectedComponents.mk ⁻¹' {i} :=
  rfl

include hf hreg hint in
/-- The piece of the connected component `i` of a regular sublevel. -/
def carrierSublevelPiece (i : ConnectedComponents {x : W.Carrier // f x ≤ c}) :
    PieceEmbedding W :=
  letI := carrierSublevelChartedSpace W f c hf hreg hint
  haveI := carrierSublevel_isManifold W f c hf hreg hint
  haveI := compactSpace_carrierSublevel W f c hf.continuous
  haveI := locallyConnectedSpace_carrierSublevel W f c hf hreg hint
  { Piece := carrierSublevelComponent W f c hf hreg hint i
    secondCountable := (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal :
      Topology.IsInducing (fun q : carrierSublevelComponent W f c hf hreg hint i =>
        ((q : {x : W.Carrier // f x ≤ c}) : W.Carrier))).secondCountableTopology
    compact := isCompact_iff_compactSpace.mp
      ((isClosed_discrete {i}).preimage ConnectedComponents.continuous_coe).isCompact
    connected := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
      apply Subtype.connectedSpace
      change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
      rw [connectedComponents_preimage_singleton]
      exact isConnected_connectedComponent
    map := fun q => ((q : {x : W.Carrier // f x ≤ c}) : W.Carrier)
    smooth := (carrierSublevel_contMDiff_val W f c hf hreg hint).comp contMDiff_subtype_val
    mfderiv_bijective := by
      intro q
      have h1 : MDifferentiableAt (𝓡∂ 3) W.model
          (Subtype.val : {x : W.Carrier // f x ≤ c} → W.Carrier) q :=
        (carrierSublevel_contMDiff_val W f c hf hreg hint).mdifferentiableAt (by simp)
      have h2 : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
          (Subtype.val : carrierSublevelComponent W f c hf hreg hint i →
            {x : W.Carrier // f x ≤ c}) q :=
        (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp q h1 h2
      change Bijective (mfderiv (𝓡∂ 3) W.model
        ((Subtype.val : {x : W.Carrier // f x ≤ c} → W.Carrier) ∘
          (Subtype.val : carrierSublevelComponent W f c hf hreg hint i →
            {x : W.Carrier // f x ≤ c})) q)
      rw [hcomp, DifferentialGeometry.mfderiv_subtype_val]
      exact carrierSublevel_mfderiv_val_bijective W f c hf hreg hint q
    injective := Subtype.val_injective.comp Subtype.val_injective }

theorem range_carrierSublevelPiece (i : ConnectedComponents {x : W.Carrier // f x ≤ c}) :
    range (carrierSublevelPiece W f c hf hreg hint i).map =
      Subtype.val '' (ConnectedComponents.mk ⁻¹' {i}) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

variable {W f c hf hreg hint} in
theorem carrierSublevelPiece_isBoundaryPoint_iff
    {i : ConnectedComponents {x : W.Carrier // f x ≤ c}}
    {q : (carrierSublevelPiece W f c hf hreg hint i).Piece} :
    (𝓡∂ 3).IsBoundaryPoint q ↔
      (W.model.IsBoundaryPoint ((carrierSublevelPiece W f c hf hreg hint i).map q) ∨
        f ((carrierSublevelPiece W f c hf hreg hint i).map q) = c) := by
  let _ := carrierSublevelChartedSpace W f c hf hreg hint
  exact (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
    (u := carrierSublevelComponent W f c hf hreg hint i) (x := q)).trans
    (carrierSublevel_isBoundaryPoint_iff hf hreg hint (x := q.1))

end Sublevel

/-- **B1-relative (regular domain, global defining function).** Kernel:
`RegularLevel/BoundarySublevel.lean:153` (kind `withBoundary`) and `RegularLevel/Sublevel.lean:212–256`
(kind `closed`, after the linear rechart to `MorseModel 3`). The sublevel may be empty or
disconnected; the output is its finite family of connected components, each a `PieceEmbedding`,
with the boundary formula `∂P = (∂W ∩ P) ∪ {f = c}`. -/
theorem exists_pieces_of_regular_sublevel (W : CompactCarrier.{u}) (f : W.Carrier → ℝ) (c : ℝ)
    (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x, f x = c → x ∈ W.interior) :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | f x ≤ c} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      ∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔
        (W.model.IsBoundaryPoint ((P k).map q) ∨ f ((P k).map q) = c) := by
  have := locallyConnectedSpace_carrierSublevel W f c hf hreg hint
  have := compactSpace_carrierSublevel W f c hf.continuous
  let e := Finite.equivFin (ConnectedComponents {x : W.Carrier // f x ≤ c})
  refine ⟨Nat.card (ConnectedComponents {x : W.Carrier // f x ≤ c}),
    fun k => carrierSublevelPiece W f c hf hreg hint (e.symm k), ?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion, range_carrierSublevelPiece, mem_ofPred_eq]
    constructor
    · rintro ⟨k, y, -, rfl⟩
      exact y.2
    · intro hx
      refine ⟨e (ConnectedComponents.mk ⟨x, hx⟩), ⟨x, hx⟩, ?_, rfl⟩
      simp
  · intro k k' hkk'
    rw [range_carrierSublevelPiece, range_carrierSublevelPiece]
    refine (Set.disjoint_image_iff Subtype.val_injective).mpr (Disjoint.preimage _ ?_)
    exact disjoint_singleton.mpr (fun h => hkk' (e.symm.injective h))
  · intro k q
    exact carrierSublevelPiece_isBoundaryPoint_iff (i := e.symm k) (q := q)

end GC.GraphManifold.Assembly
