import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K0, the gate G4 part 2): the edge slab and the transport hypotheses

Lane FC39-G-RIMBOX, dispositions D62-3 (a), D62-6. For an open set `V` of the edge base and a smooth regular
coordinate `φ` on `V` (the axial coordinate of an interval component, `FC39GRimAxialCoordinate.lean`),
the edge slab `edgeSlab_GRIM P V` (the edge-source points over `V`) lies in `W.interior`; with the
boundaryless interior charts (`interiorChartedSpace W.model ∞`, model `𝓘(ℝ, ℝ³)`) the axial coordinate
`g = φ ∘ proj` and `B = level − height` satisfy the hypotheses of the side-boundary transport
(`exists_sideBoundary_interval_trivialization_preserving`): smooth, `g` a submersion (`proj_submersion`
and `dφ` onto), `(g, B)` a submersion on the wall (`rank_two`), `g` proper on `{B ≥ 0}` over the window
(`EdgeBundle.proper` on `V ∩ φ⁻¹ K`). Derivatives are transported from the carrier model by
`mfderiv_interiorAtlas`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- The edge slab over an open set `V` of the edge base: the points of the edge source over `V`. -/
def edgeSlab_GRIM (P : EdgeBundle W) (V : Set P.Base) (hV : IsOpen V) :
    TopologicalSpace.Opens W.Carrier :=
  ⟨{x | ∃ h : x ∈ P.source, P.proj ⟨x, h⟩ ∈ V}, by
    have hset : {x | ∃ h : x ∈ P.source, P.proj ⟨x, h⟩ ∈ V} = Subtype.val '' (P.proj ⁻¹' V) := by
      ext x
      constructor
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
    rw [hset]
    exact P.source.isOpen.isOpenMap_subtype_val _ (hV.preimage P.proj.continuous)⟩

theorem pieceInterior_edgeSlab_le_GRIM (P : EdgeBundle W) (V : Set P.Base) (hV : IsOpen V) :
    W.pieceInterior (edgeSlab_GRIM P V hV) ≤ P.source :=
  fun _ hx => hx.1.fst

/-- The edge-source point of a point of the slab interior. -/
abbrev edgeSlabIncl_GRIM (P : EdgeBundle W) (V : Set P.Base) (hV : IsOpen V) :
    W.pieceInterior (edgeSlab_GRIM P V hV) → P.source :=
  TopologicalSpace.Opens.inclusion (pieceInterior_edgeSlab_le_GRIM P V hV)

/-- **The side-boundary transport hypotheses on the edge slab** (sheet §3 K0): on the boundaryless
recharted slab interior, the axial coordinate `g = φ ∘ proj` and `B = level − height` are smooth,
`g` is a submersion, `(g, B)` is a submersion on the wall `B = 0`, and `g` is proper on `{B ≥ 0}`
over the axial window. -/
theorem edgeSlab_transportHypotheses_GRIM (P : EdgeBundle W) {V : Set P.Base} (hV : IsOpen V)
    {φ : P.Base → ℝ} (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V)
    (hφs : ∀ c ∈ V, Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c)) {ε : ℝ}
    (hK : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-ε) (1 + ε) → IsCompact (V ∩ φ ⁻¹' K)) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
      (M := W.pieceInterior (edgeSlab_GRIM P V hV))
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ) ∞
        (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ) ∞
        (fun y => P.level - P.height (edgeSlabIncl_GRIM P V hV y)) ∧
      (∀ y, Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ)
        (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y)) ∧
      (∀ y, P.level - P.height (edgeSlabIncl_GRIM P V hV y) = 0 →
        Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ × ℝ)
          (fun y => (φ (P.proj (edgeSlabIncl_GRIM P V hV y)),
            P.level - P.height (edgeSlabIncl_GRIM P V hV y))) y)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-ε) (1 + ε) →
        IsCompact ((fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) ⁻¹' K ∩
          {y | 0 ≤ P.level - P.height (edgeSlabIncl_GRIM P V hV y)}) := by
  intro _
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hι : ContMDiff W.model W.model ∞ (edgeSlabIncl_GRIM P V hV) := contMDiff_inclusion _
  have hpV : ∀ y : W.pieceInterior (edgeSlab_GRIM P V hV),
      P.proj (edgeSlabIncl_GRIM P V hV y) ∈ V := fun y => y.2.1.snd
  set g : W.pieceInterior (edgeSlab_GRIM P V hV) → ℝ :=
    fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y)) with hgdef
  set B : W.pieceInterior (edgeSlab_GRIM P V hV) → ℝ :=
    fun y => P.level - P.height (edgeSlabIncl_GRIM P V hV y) with hBdef
  have hgW : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ g := fun y =>
    (hφ.contMDiffAt (hV.mem_nhds (hpV y))).comp y ((P.proj_smooth.comp hι) y)
  have hBW : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ B := contMDiff_const.sub (P.height_smooth.comp hι)
  have hid := DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id W.model ∞
    (M := W.pieceInterior (edgeSlab_GRIM P V hV))
  -- the derivative of g in the carrier model
  have hdg : ∀ y, mfderiv W.model 𝓘(ℝ, ℝ) g y =
      (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (P.proj (edgeSlabIncl_GRIM P V hV y))).comp
        (mfderiv W.model (𝓡 1) P.proj (edgeSlabIncl_GRIM P V hV y)) := by
    intro y
    have hφd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ (P.proj (edgeSlabIncl_GRIM P V hV y)) :=
      (hφ.contMDiffAt (hV.mem_nhds (hpV y))).mdifferentiableAt hn
    have hpd : MDifferentiableAt W.model (𝓡 1) P.proj (edgeSlabIncl_GRIM P V hV y) :=
      (P.proj_smooth _).mdifferentiableAt hn
    have hιd : MDifferentiableAt W.model W.model (edgeSlabIncl_GRIM P V hV) y :=
      (hι y).mdifferentiableAt hn
    change mfderiv W.model 𝓘(ℝ, ℝ) (φ ∘ P.proj ∘ edgeSlabIncl_GRIM P V hV) y = _
    rw [mfderiv_comp y hφd (hpd.comp y hιd), mfderiv_comp y hpd hιd,
      DifferentialGeometry.mfderiv_opens_incl]
    rfl
  have hdB : ∀ y v, mfderiv W.model 𝓘(ℝ, ℝ) B y v =
      -(mfderiv W.model 𝓘(ℝ, ℝ) P.height (edgeSlabIncl_GRIM P V hV y) v) := by
    intro y v
    have hhd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) P.height (edgeSlabIncl_GRIM P V hV y) :=
      (P.height_smooth _).mdifferentiableAt hn
    have hιd : MDifferentiableAt W.model W.model (edgeSlabIncl_GRIM P V hV) y :=
      (hι y).mdifferentiableAt hn
    have h1 : HasMFDerivAt W.model 𝓘(ℝ, ℝ) (P.height ∘ edgeSlabIncl_GRIM P V hV) y
        (mfderiv W.model 𝓘(ℝ, ℝ) P.height (edgeSlabIncl_GRIM P V hV y)) := by
      have := (hhd.comp y hιd).hasMFDerivAt
      rwa [mfderiv_comp y hhd hιd, DifferentialGeometry.mfderiv_opens_incl] at this
    have h2 := (hasMFDerivAt_const (I := W.model) (I' := 𝓘(ℝ, ℝ)) P.level y).sub h1
    have hB' : B = (fun _ => P.level) - P.height ∘ edgeSlabIncl_GRIM P V hV := rfl
    rw [hB', h2.mfderiv]
    exact zero_sub _
  refine ⟨hgW.comp hid, hBW.comp hid, ?_, ?_, ?_⟩
  · intro y
    have h := DifferentialGeometry.Manifold.mfderiv_interiorAtlas W.model hgW y
    have h' : ∀ v : EuclideanSpace ℝ (Fin 3), mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ) g y v =
        mfderiv W.model 𝓘(ℝ, ℝ) g y v := fun v =>
      congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L v) h
    have hs : Surjective (mfderiv W.model 𝓘(ℝ, ℝ) g y) := by
      rw [hdg]
      exact (hφs _ (hpV y)).comp (P.proj_submersion _)
    intro r
    obtain ⟨v, hv⟩ := hs r
    exact ⟨v, (h' v).trans hv⟩
  · intro y hy0
    have hpairW : ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (fun y => (g y, B y)) := hgW.prodMk_space hBW
    have h := DifferentialGeometry.Manifold.mfderiv_interiorAtlas W.model hpairW y
    have h' : ∀ v : EuclideanSpace ℝ (Fin 3),
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y v =
          mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y v := fun v =>
      congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ => L v) h
    suffices hs : Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y) by
      intro r
      obtain ⟨v, hv⟩ := hs r
      exact ⟨v, (h' v).trans hv⟩
    -- components of the pair derivative
    have hpd : MDifferentiableAt W.model 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y :=
      (hpairW y).mdifferentiableAt hn
    have hfst : ∀ v, (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y v).1 =
        mfderiv W.model 𝓘(ℝ, ℝ) g y v := by
      intro v
      have hfd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × ℝ → ℝ) (g y, B y) :=
        ((contDiff_fst.contMDiff) (g y, B y)).mdifferentiableAt hn
      have := mfderiv_comp y hfd hpd
      have hc : (Prod.fst ∘ fun y => (g y, B y)) = g := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_fst] at this
      rw [this]
      rfl
    have hsnd : ∀ v, (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, B y)) y v).2 =
        mfderiv W.model 𝓘(ℝ, ℝ) B y v := by
      intro v
      have hsd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ) (g y, B y) :=
        ((contDiff_snd.contMDiff) (g y, B y)).mdifferentiableAt hn
      have := mfderiv_comp y hsd hpd
      have hc : (Prod.snd ∘ fun y => (g y, B y)) = B := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_snd] at this
      rw [this]
      rfl
    rintro ⟨s, u⟩
    obtain ⟨w, hw⟩ := hφs _ (hpV y) s
    have hlev : P.height (edgeSlabIncl_GRIM P V hV y) = P.level := by
      have : P.level - P.height (edgeSlabIncl_GRIM P V hV y) = 0 := hy0
      linarith
    obtain ⟨v, hv⟩ := P.rank_two _ hlev (w, -u)
    obtain ⟨hv1, hv2⟩ := Prod.mk.inj hv
    have hg1 : mfderiv W.model 𝓘(ℝ, ℝ) g y v = s := by
      rw [hdg]
      change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ _ (mfderiv W.model (𝓡 1) P.proj _ v) = s
      rw [hv1, hw]
    have hB1 : mfderiv W.model 𝓘(ℝ, ℝ) B y v = u :=
      (hdB y v).trans (by rw [hv2]; exact neg_neg u)
    exact ⟨v, Prod.ext ((hfst v).trans hg1) ((hsnd v).trans hB1)⟩
  · intro K hKc hKsub
    have himg : Subtype.val '' (g ⁻¹' K ∩ {y | 0 ≤ B y}) =
        Subtype.val '' {x : P.source | P.proj x ∈ V ∩ φ ⁻¹' K ∧ P.height x ≤ P.level} := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyK, hyB⟩, rfl⟩
        refine ⟨edgeSlabIncl_GRIM P V hV y, ⟨⟨hpV y, hyK⟩, ?_⟩, rfl⟩
        change 0 ≤ P.level - P.height _ at hyB
        linarith
      · rintro ⟨z, ⟨⟨hzV, hzK⟩, hzl⟩, rfl⟩
        refine ⟨⟨z.val, ⟨z.2, hzV⟩, P.source_interior z.2⟩, ⟨hzK, ?_⟩, rfl⟩
        change 0 ≤ P.level - P.height z
        linarith
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have hc := P.proper _ (hK K hKc hKsub)
    rw [← himg] at hc
    exact hc

end GC.GraphManifold.Assembly.FC39P0
