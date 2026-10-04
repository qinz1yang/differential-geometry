import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPieces
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# Consumer of B1-relative: the `external_local` shape

The field `EmbeddedCutSystem.external_local` (`Seifert/EmbeddedPieces.lean:292`) asks that a piece
map be a local diffeomorphism at the physical boundary points of the piece. For a B1-relative piece
this holds at every point off the level `{f = c}`: there the sublevel is the open set
`{f < c}` of `W`, and the slice structure agrees with the open-subset structure of `W`.

* `isLocalDiffeomorphAt_carrierSublevel_val`: the inclusion of the sublevel is a local
  diffeomorphism at every point with `f < c`;
* `carrierSublevelPiece_isLocalDiffeomorphAt`: the same for each component piece;
* `exists_pieces_of_regular_sublevel_isLocalDiffeomorphAt`: B1-relative with the extra conclusion
  that every piece map is a local diffeomorphism at every point over `∂W` (the `external_local`
  shape) and, more generally, at every point with `f < c`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry GC.Endpoint Manifold
open DifferentialGeometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Local

variable (W : CompactCarrier.{u}) (f : W.Carrier → ℝ) (c : ℝ)
  (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
  (hint : ∀ x, f x = c → x ∈ W.interior)

/-- The open part `{f < c}` of the sublevel. -/
def carrierSublevelOpenPart (hfc : Continuous f) : TopologicalSpace.Opens {x : W.Carrier // f x ≤ c} :=
  ⟨{y | f y.1 < c}, isOpen_lt (hfc.comp continuous_subtype_val) continuous_const⟩

/-- The open set `{f < c}` of `W`. -/
def carrierStrictSublevel (hfc : Continuous f) : TopologicalSpace.Opens W.Carrier :=
  ⟨{x | f x < c}, isOpen_lt hfc continuous_const⟩

/-- The open part of the sublevel, with the slice structure, is diffeomorphic to the open set
`{f < c}` of `W` by the identity. -/
def carrierSublevelOpenPartDiffeomorph :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    carrierSublevelOpenPart W f c hf.continuous ≃ₘ⟮𝓡∂ 3, W.model⟯
      carrierStrictSublevel W f c hf.continuous := by
  letI := carrierSublevelChartedSpace W f c hf hreg hint
  exact
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun x => ⟨⟨x.1, le_of_lt x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun := by
        apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
          (carrierStrictSublevel W f c hf.continuous) _).mp
        exact (carrierSublevel_contMDiff_val W f c hf hreg hint).comp contMDiff_subtype_val
      contMDiff_invFun := by
        apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
          (carrierSublevelOpenPart W f c hf.continuous) _).mp
        apply (slice_contMDiff_iff (d := 2) (carrierSublevel_sliceCharts W f c hf hreg hint)
          le_rfl).mpr
        exact contMDiff_subtype_val }

/-- The inclusion of a regular sublevel is a local diffeomorphism at every point with `f < c`. -/
theorem isLocalDiffeomorphAt_carrierSublevel_val (y : {x : W.Carrier // f x ≤ c})
    (hy : f y.1 < c) :
    letI := carrierSublevelChartedSpace W f c hf hreg hint
    IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞
      (Subtype.val : {x : W.Carrier // f x ≤ c} → W.Carrier) y := by
  let _ := carrierSublevelChartedSpace W f c hf hreg hint
  let V := carrierSublevelOpenPart W f c hf.continuous
  let O := carrierStrictSublevel W f c hf.continuous
  have hV : Nonempty V := ⟨⟨y, hy⟩⟩
  have hO : Nonempty O := ⟨⟨y.1, hy⟩⟩
  let φ := carrierSublevelOpenPartDiffeomorph W f c hf hreg hint
  let Ψ := (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3) V hV).symm.trans
    (φ.toPartialDiffeomorph.trans
      (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph W.model O hO))
  have hsource : ∀ z, z ∈ Ψ.source ↔ z ∈ (V : Set {x : W.Carrier // f x ≤ c}) := by
    intro z
    constructor
    · intro hz
      have hz1 : z ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3) V
          hV).target := hz.1
      rwa [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target] at hz1
    · intro hz
      refine ⟨?_, mem_univ _, mem_univ _⟩
      change z ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3) V hV).target
      rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
      exact hz
  refine ⟨Ψ, (hsource y).mpr hy, ?_⟩
  intro z hz
  have hzV := (hsource z).mp hz
  change z.1 = ((φ ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3) V
    hV).symm z) : W.Carrier))
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply (𝓡∂ 3) V hV hzV]
  rfl

/-- A B1-relative piece map is a local diffeomorphism at every point with `f < c`. -/
theorem carrierSublevelPiece_isLocalDiffeomorphAt
    (i : ConnectedComponents {x : W.Carrier // f x ≤ c})
    (q : (carrierSublevelPiece W f c hf hreg hint i).Piece)
    (hq : f ((carrierSublevelPiece W f c hf hreg hint i).map q) < c) :
    IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ (carrierSublevelPiece W f c hf hreg hint i).map q := by
  let _ := carrierSublevelChartedSpace W f c hf hreg hint
  let C := carrierSublevelComponent W f c hf hreg hint i
  let q' : C := q
  have h1 : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞
      (Subtype.val : C → {x : W.Carrier // f x ≤ c}) q' :=
    ⟨DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3) C ⟨q'⟩, mem_univ _,
      fun _ _ => rfl⟩
  exact h1.comp W.model W.Carrier (isLocalDiffeomorphAt_carrierSublevel_val W f c hf hreg hint q'.1 hq)

end Local

/-- **B1-relative with the `external_local` shape.** The pieces of `exists_pieces_of_regular_sublevel`
can be chosen so that every piece map is a local diffeomorphism at every point with `f < c`, in
particular at every point over the physical boundary `∂W`. -/
theorem exists_pieces_of_regular_sublevel_isLocalDiffeomorphAt (W : CompactCarrier.{u})
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x, f x = c → x ∈ W.interior) :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | f x ≤ c} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      (∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔
        (W.model.IsBoundaryPoint ((P k).map q) ∨ f ((P k).map q) = c)) ∧
      (∀ k q, f ((P k).map q) < c → IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ (P k).map q) ∧
      ∀ k q, W.model.IsBoundaryPoint ((P k).map q) →
        IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ (P k).map q := by
  have := locallyConnectedSpace_carrierSublevel W f c hf hreg hint
  have := compactSpace_carrierSublevel W f c hf.continuous
  let e := Finite.equivFin (ConnectedComponents {x : W.Carrier // f x ≤ c})
  have hlt : ∀ k q, f ((carrierSublevelPiece W f c hf hreg hint (e.symm k)).map q) < c →
      IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞
        (carrierSublevelPiece W f c hf hreg hint (e.symm k)).map q :=
    fun k q hq => carrierSublevelPiece_isLocalDiffeomorphAt W f c hf hreg hint (e.symm k) q hq
  refine ⟨Nat.card (ConnectedComponents {x : W.Carrier // f x ≤ c}),
    fun k => carrierSublevelPiece W f c hf hreg hint (e.symm k), ?_, ?_, ?_, hlt, ?_⟩
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
  · intro k q hb
    refine hlt k q (lt_of_le_of_ne ?_ ?_)
    · exact (show carrierSublevelComponent W f c hf hreg hint (e.symm k) from q).1.2
    · intro heq
      have hi : W.model.IsInteriorPoint ((carrierSublevelPiece W f c hf hreg hint (e.symm k)).map q) :=
        hint _ heq
      exact ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi) hb

end GC.GraphManifold.Assembly
