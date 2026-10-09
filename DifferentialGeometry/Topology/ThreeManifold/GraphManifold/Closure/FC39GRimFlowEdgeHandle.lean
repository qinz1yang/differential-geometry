import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimSlabEndDisk
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimFlowHandleApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAxialCoordinateApplications

/-!
# FC39 GROUP G, RIMBOX route B (sheet §4, binding G5c part 2): the new flow edge handle

Lane FC39-G-RIMBOX (successor FC39-G-RIMBOXc), dispositions D62-1, D62-3 (a), (c), (f), D62-6. For an
interval component `i` of the edge export, on the boundaryless edge-slab interior `Y`
(`edgeSlab_GRIM`, interior charts `𝓘(ℝ, ℝ³)`), the flow handle `Hm (w, t) = Fl_t (D w)`
(`exists_flowHandle_polar_GRIM`) of the polar new end disk `D` (`edgeSlab_polarEndDisk_GRIM`, `κ = 1`)
is a NEW `EdgeHandle` (`map = val ∘ Hm`) which satisfies the four link clauses of
`EdgeComponentsLink` for the component (`handle_whole`, `handle_proj`, `handle_disk`, `handle_rim`, all
as set equalities; the rim reverse inclusion by the inverse flow and the group law, D62-3 (f)). The
flow, its two-sided axial window `(-ε/2, 1 + ε/2)` from the `g = 0` slice (D62-3 (a)) and the
two-sided collar `C` (shrunk so that `C (annulus) ⊆ U`, tube lemma) are exported JOINTLY with the
handle for the rim charts (D62-3 (c): both ends use the same flow).

* `exists_edgeHandle_of_immersion_GRIM` — an injective immersion of `D² × [0, 1]` through an immersed
  boundaryless 3-manifold is an `EdgeHandle`; `pieceInterior_val_immersion_GRIM` — the inclusion of a
  piece interior (interior charts) is such an immersion;
* `EdgeComponentModels.exists_flowEdgeHandle_GRIM` — the binding.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsFEH_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothFEH_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}}

/-- **An injective immersion of `D² × [0, 1]` through an immersed boundaryless 3-manifold is an
edge handle** (`map = ι ∘ Hm`; the differential is injective, hence bijective by dimension). -/
theorem exists_edgeHandle_of_immersion_GRIM {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] (ι : Y → W.Carrier) (hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ∞ ι)
    (hιinj : Injective ι)
    (hιd : ∀ y, Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ι y))
    (hιint : range ι ⊆ W.interior)
    (Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y)
    (hHm : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ Hm)
    (hinj : Injective Hm)
    (himm : ∀ p, Injective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) Hm p)) :
    ∃ H : EdgeHandle W, ∀ p, H.map p = ι (Hm p) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨{ map := ι ∘ Hm
            smooth := hι.comp hHm
            mfderiv_bijective := fun p => ?_
            injective := hιinj.comp hinj
            interior := (range_comp_subset_range Hm ι).trans hιint }, fun p => rfl⟩
  have hHmd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) Hm p :=
    (hHm p).mdifferentiableAt hn
  have hιdd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ι (Hm p) :=
    (hι (Hm p)).mdifferentiableAt hn
  have hinjd : Injective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model (ι ∘ Hm) p) := by
    rw [mfderiv_comp p hιdd hHmd]
    exact (hιd (Hm p)).comp (himm p)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp
  exact ⟨hinjd, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinjd⟩

/-- The inclusion of a piece interior, with its interior (`𝓘(ℝ, ℝ³)`) charts, is a smooth injective
immersion into the carrier. -/
theorem pieceInterior_val_immersion_GRIM (O : TopologicalSpace.Opens W.Carrier) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior O)
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ∞ (Subtype.val : W.pieceInterior O → W.Carrier) ∧
      ∀ y, Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model
        (Subtype.val : W.pieceInterior O → W.Carrier) y) := by
  intro _
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let Ψ := (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞
    (M := W.pieceInterior O)).symm
  have hfac : (Subtype.val : W.pieceInterior O → W.Carrier) =
      (Subtype.val : W.pieceInterior O → W.Carrier) ∘ Ψ := rfl
  refine ⟨contMDiff_subtype_val.comp Ψ.contMDiff, fun y => ?_⟩
  have hΨd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model Ψ y :=
    (Ψ.contMDiff y).mdifferentiableAt hn
  have hvald : MDifferentiableAt W.model W.model (Subtype.val : W.pieceInterior O → W.Carrier)
      (Ψ y) := (contMDiff_subtype_val (Ψ y)).mdifferentiableAt hn
  have hΨinj : Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model Ψ y) :=
    ((Ψ.isLocalDiffeomorph y).mfderivToContinuousLinearEquiv hn).injective
  rw [hfac, mfderiv_comp y hvald hΨd, DifferentialGeometry.mfderiv_subtype_val]
  exact hΨinj

/-- **The new flow edge handle of an interval component** (sheet §4, binding G5c part 2): an
`EdgeHandle` `H = val ∘ Hm` with the four link clauses of the component as set equalities, exported
jointly with the slab flow (two-sided axial window from the `g = 0` slice, `B` kept on `{|B| < r'}`,
group law) and the two-sided rim collar `C` (inside the flow domain), with `Hm (w, t) = Fl_t (C w)`
near the rim. -/
theorem EdgeComponentModels.exists_flowEdgeHandle_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) (i : Fin M.intervalCount) :
    ∃ (V : Set P.Base) (hV : IsOpen V) (φ : P.Base → ℝ) (ε : ℝ), 0 < ε ∧
      range (M.intervalBase i) ⊆ V ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V ∧
      (∀ t, φ (M.intervalBase i t) = t) ∧ InjOn φ V ∧
      (∀ c ∈ V, Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c)) ∧ φ '' V = Ioo (-ε) (1 + ε) ∧
      let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
        (M := W.pieceInterior (edgeSlab_GRIM P V hV))
      ∃ (H : EdgeHandle W)
        (Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → W.pieceInterior (edgeSlab_GRIM P V hV)),
        (∀ p, H.map p = (Hm p : W.Carrier)) ∧
        range H.map = P.wholeComponent (M.componentEquiv (.inl i)) ∧
        (∀ w t, ∃ hx : H.map (w, t) ∈ P.source,
          P.proj ⟨H.map (w, t), hx⟩ = M.intervalBase i t) ∧
        (∀ t, range (fun w => H.map (w, t)) = P.disk (M.intervalBase i t)) ∧
        (∀ t, (fun w => H.map (w, t)) '' diskRim = P.rim (M.intervalBase i t)) ∧
        ∃ (δ r' : ℝ) (U : TopologicalSpace.Opens (W.pieceInterior (edgeSlab_GRIM P V hV)))
          (Fl : ℝ → U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ U)
          (C : EuclideanSpace ℝ (Fin 2) → W.pieceInterior (edgeSlab_GRIM P V hV)),
          0 < δ ∧ δ < 1 ∧ δ ≤ r' ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            ∞ (fun q : ℝ × U => Fl q.1 q.2) ∧
          Fl 0 = Diffeomorph.refl _ U ∞ ∧ (∀ s t, (Fl s).trans (Fl t) = Fl (s + t)) ∧
          (∀ z : U, φ (P.proj (edgeSlabIncl_GRIM P V hV z)) = 0 →
            -r' ≤ P.level - P.height (edgeSlabIncl_GRIM P V hV z) →
            ∀ t ∈ Ioo (-(ε / 2)) (1 + ε / 2),
              φ (P.proj (edgeSlabIncl_GRIM P V hV (Fl t z))) = t) ∧
          (∀ (z : U) (t : ℝ), |P.level - P.height (edgeSlabIncl_GRIM P V hV z)| < r' →
            P.level - P.height (edgeSlabIncl_GRIM P V hV (Fl t z)) =
              P.level - P.height (edgeSlabIncl_GRIM P V hV z)) ∧
          ContMDiffOn (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ C {z | |‖z‖ - 1| < δ} ∧
          InjOn C {z | |‖z‖ - 1| < δ} ∧
          (∀ z, |‖z‖ - 1| < δ →
            Injective (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C z)) ∧
          (∀ z, |‖z‖ - 1| < δ → φ (P.proj (edgeSlabIncl_GRIM P V hV (C z))) = 0 ∧
            P.level - P.height (edgeSlabIncl_GRIM P V hV (C z)) = 1 - ‖z‖) ∧
          (∀ z, |‖z‖ - 1| < δ → C z ∈ U) ∧
          ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1), 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
            ∃ hw : C w ∈ U,
              Hm (w, t) = ((Fl (t : ℝ) ⟨C w, hw⟩ : U) : W.pieceInterior (edgeSlab_GRIM P V hV)) := by
  obtain ⟨V, φ, ε, hV, hε, hrange, hφ, hφβ, hφinj, hφs, hφV, hK⟩ :=
    M.exists_intervalBase_twoSidedCoordinate_GRIM i
  refine ⟨V, hV, φ, ε, hε, hrange, hφ, hφβ, hφinj, hφs, hφV, ?_⟩
  intro _
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior (edgeSlab_GRIM P V hV)) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  obtain ⟨hP, hB, hreg, hregb, hprop⟩ := edgeSlab_transportHypotheses_GRIM P hV hφ hφs hK
  obtain ⟨δ, hδ0, -, D, hD, hDinj, hDimm, hD0, hDsurj, hpol, hrim, C, hC, hCinj, hCimm, hCP,
    hDC⟩ :=
    edgeSlab_polarEndDisk_GRIM M i hV hφ hφs hφinj hφβ hrange one_pos
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 1 + 1 + Module.finrank ℝ ℝ := by
    simp
  have hDr : range D = {y | φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = 0 ∧ 0 ≤ (P.level - P.height (edgeSlabIncl_GRIM P V hV y))} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(hD0 w).1, by linarith [(hD0 w).2]⟩
    · rintro ⟨hy0, hyB⟩
      exact hDsurj y hy0 (by linarith)
  have hpolB : ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
      (P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))) = 1 * (1 - ‖(w : EuclideanSpace ℝ (Fin 2))‖) := by
    intro w hw
    rw [hpol w hw]
    ring
  obtain ⟨Hm, hHm, hinj, himm, hPB, hrangeHm, -, -, -, -, -, r', hr', U, Fl, hFl, hFl0, hgrp,
    hDU, hHmFl, hFlP, hFlB⟩ :=
    exists_flowHandle_polar_GRIM hdim hP hB (a := -ε) (b := 1 + ε) (fun y _ _ => hreg y)
      (fun y _ hy => hregb y hy) hprop (a₀ := -(ε / 2)) (b₀ := 1 + ε / 2) (by linarith)
      (by linarith) (by linarith) (by linarith) D hD hDinj hDimm hDr one_pos hδ0 hpolB
  obtain ⟨hvalsm, hvalimm⟩ := pieceInterior_val_immersion_GRIM (edgeSlab_GRIM P V hV)
  obtain ⟨H, hH⟩ := exists_edgeHandle_of_immersion_GRIM
    (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier) hvalsm Subtype.val_injective
    hvalimm (by rintro _ ⟨y, rfl⟩; exact y.2.2) Hm hHm hinj himm
  -- the axial coordinate recovers the base point
  have hpV : ∀ y : (W.pieceInterior (edgeSlab_GRIM P V hV)), P.proj (edgeSlabIncl_GRIM P V hV y) ∈ V := fun y => y.2.1.snd
  have hβV : ∀ t, M.intervalBase i t ∈ V := fun t => hrange (mem_range_self t)
  have hbase : ∀ (y : (W.pieceInterior (edgeSlab_GRIM P V hV))) (t : Icc (0 : ℝ) 1), φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = t →
      P.proj (edgeSlabIncl_GRIM P V hV y) = M.intervalBase i t := fun y t hy =>
    hφinj (hpV y) (hβV t) (by rw [hφβ]; exact hy)
  -- points of the source over the component lie in the slab
  have hslab : ∀ (x : P.source) (t : Icc (0 : ℝ) 1), P.proj x = M.intervalBase i t →
      ∃ y : (W.pieceInterior (edgeSlab_GRIM P V hV)), (y : W.Carrier) = x ∧ edgeSlabIncl_GRIM P V hV y = x ∧ φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = t := by
    intro x t hx
    have hxV : P.proj x ∈ V := hx ▸ hβV t
    refine ⟨⟨x.1, ⟨x.2, hxV⟩, P.source_interior x.2⟩, rfl, rfl, ?_⟩
    change φ (P.proj x) = t
    rw [hx, hφβ]
  have hHmap : ∀ p, H.map p = (Hm p : W.Carrier) := hH
  -- the projection clause
  have hproj : ∀ w t, ∃ hx : H.map (w, t) ∈ P.source,
      P.proj ⟨H.map (w, t), hx⟩ = M.intervalBase i t := by
    intro w t
    rw [hHmap]
    exact ⟨(Hm (w, t)).2.1.fst, hbase (Hm (w, t)) t (hPB (w, t)).1⟩
  -- the disk clause
  have hdisk : ∀ t, range (fun w => H.map (w, t)) = P.disk (M.intervalBase i t) := by
    intro t
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨hx, hxp⟩ := hproj w t
      refine ⟨⟨_, hx⟩, ⟨hxp, ?_⟩, rfl⟩
      have h := (hPB (w, t)).2
      have hc : (⟨H.map (w, t), hx⟩ : P.source) = edgeSlabIncl_GRIM P V hV (Hm (w, t)) :=
        Subtype.ext (hHmap _)
      rw [hc]
      linarith
    · rintro ⟨x, ⟨hxc, hxl⟩, rfl⟩
      obtain ⟨y, hyx, hyi, hyg⟩ := hslab x t hxc
      have hyr : y ∈ range Hm := by
        rw [hrangeHm]
        refine ⟨by rw [hyg]; exact t.2, ?_⟩
        rw [hyi]
        linarith
      obtain ⟨⟨w, t'⟩, hwt⟩ := hyr
      have ht' : t' = t := Subtype.ext (by
        have := (hPB (w, t')).1
        rw [hwt] at this
        rw [← this, hyg])
      subst ht'
      refine ⟨w, ?_⟩
      change H.map (w, t') = x
      rw [hHmap, hwt, hyx]
  refine ⟨H, Hm, hHmap, ?_, hproj, hdisk, ?_, ?_⟩
  · -- the whole component
    ext x
    constructor
    · rintro ⟨⟨w, t⟩, rfl⟩
      have hx : H.map (w, t) ∈ P.disk (M.intervalBase i t) := by
        rw [← hdisk t]
        exact ⟨w, rfl⟩
      obtain ⟨x', ⟨hx'c, hx'l⟩, hx'e⟩ := hx
      refine ⟨x', ⟨?_, hx'l⟩, hx'e⟩
      have hR := M.intervalBase_range i
      change P.proj x' ∈ (M.componentEquiv (.inl i)).1
      rw [← hR, hx'c]
      exact mem_range_self t
    · rintro ⟨x, ⟨hxc, hxl⟩, rfl⟩
      have hR := M.intervalBase_range i
      have hxc' : P.proj x ∈ (M.componentEquiv (.inl i)).1 := hxc
      rw [← hR] at hxc'
      obtain ⟨t, ht⟩ := hxc'
      have hx : (x : W.Carrier) ∈ P.disk (M.intervalBase i t) := ⟨x, ⟨ht.symm, hxl⟩, rfl⟩
      rw [← hdisk t] at hx
      obtain ⟨w, hw⟩ := hx
      exact ⟨(w, t), hw⟩
  · -- the rim clause
    intro t
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hx, hxp⟩ := hproj w t
      refine ⟨⟨_, hx⟩, ⟨hxp, ?_⟩, rfl⟩
      obtain ⟨hDw, hHw⟩ := hHmFl (w, t)
      have hn1 : ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 := mem_diskRim_iff.mp hw
      have hBD : (P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))) = 0 := by
        rw [hpolB w (by rw [hn1]; linarith), hn1]
        ring
      have hBHm : (P.level - P.height (edgeSlabIncl_GRIM P V hV (Hm (w, t)))) = 0 := by
        rw [hHw]
        rw [show ((Fl ((w, t).2 : ℝ) ⟨D (w, t).1, hDw⟩ : U) : (W.pieceInterior (edgeSlab_GRIM P V hV))) =
          ((Fl (t : ℝ) ⟨D w, hDw⟩ : U) : (W.pieceInterior (edgeSlab_GRIM P V hV))) from rfl]
        have h := hFlB ⟨D w, hDw⟩ t (by
          change |(P.level - P.height (edgeSlabIncl_GRIM P V hV (D w)))| < r'
          rw [hBD, abs_zero]
          exact hr')
        change (P.level - P.height (edgeSlabIncl_GRIM P V hV ((Fl (t : ℝ) ⟨D w, hDw⟩ : U) : (W.pieceInterior (edgeSlab_GRIM P V hV))))) = 0
        rw [show (P.level - P.height (edgeSlabIncl_GRIM P V hV ((Fl (t : ℝ) ⟨D w, hDw⟩ : U) : (W.pieceInterior (edgeSlab_GRIM P V hV))))) = (P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))) from h, hBD]
      have hc : (⟨H.map (w, t), hx⟩ : P.source) = edgeSlabIncl_GRIM P V hV (Hm (w, t)) :=
        Subtype.ext (hHmap _)
      rw [hc]
      linarith
    · rintro ⟨x, ⟨hxc, hxl⟩, rfl⟩
      have hx : (x : W.Carrier) ∈ P.disk (M.intervalBase i t) := ⟨x, ⟨hxc, hxl.le⟩, rfl⟩
      rw [← hdisk t] at hx
      obtain ⟨w, hw⟩ := hx
      refine ⟨w, ?_, hw⟩
      -- the inverse flow: (P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))) = (P.level - P.height (edgeSlabIncl_GRIM P V hV (Hm (w, t)))) = 0
      obtain ⟨hDw, hHw⟩ := hHmFl (w, t)
      have hBy : (P.level - P.height (edgeSlabIncl_GRIM P V hV (Hm (w, t)))) = 0 := by
        have hc : edgeSlabIncl_GRIM P V hV (Hm (w, t)) = x := Subtype.ext ((hHmap _).symm.trans hw)
        rw [hc, hxl, sub_self]
      set z : U := Fl (t : ℝ) ⟨D w, hDw⟩ with hz
      have hzB : (P.level - P.height (edgeSlabIncl_GRIM P V hV z)) = 0 := by
        rw [← hBy, hHw]
      have hback : Fl (-(t : ℝ)) z = ⟨D w, hDw⟩ := by
        have h := congrArg (fun F : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)),
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ U => F ⟨D w, hDw⟩) (hgrp (t : ℝ) (-(t : ℝ)))
        simp only [Diffeomorph.coe_trans, comp_apply, add_neg_cancel, hFl0, Diffeomorph.coe_refl, id_eq] at h
        exact h
      have hBD : (P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))) = 0 := by
        have h := hFlB z (-(t : ℝ)) (by
          rw [hzB, abs_zero]
          exact hr')
        change (P.level - P.height (edgeSlabIncl_GRIM P V hV ((Fl (-(t : ℝ)) z : U) : (W.pieceInterior (edgeSlab_GRIM P V hV))))) = (P.level - P.height (edgeSlabIncl_GRIM P V hV z)) at h
        rw [hback, hzB] at h
        exact h
      have hlev : P.height (edgeSlabIncl_GRIM P V hV (D w)) = P.level := by
        linarith
      exact mem_diskRim_iff.mpr (hrim w hlev)
  · -- the flow and the collar, jointly with the handle
    -- shrink the collar so that it lies in the flow domain (tube lemma)
    have hann_open : ∀ η : ℝ, IsOpen {z : EuclideanSpace ℝ (Fin 2) | |‖z‖ - 1| < η} := fun η =>
      isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const
    have hOopen : IsOpen ({z : EuclideanSpace ℝ (Fin 2) | |‖z‖ - 1| < δ} ∩
        C ⁻¹' ((Subtype.val : U → (W.pieceInterior (edgeSlab_GRIM P V hV))) '' univ)) := by
      have hUY : (Subtype.val : U → (W.pieceInterior (edgeSlab_GRIM P V hV))) '' univ = (U : Set (W.pieceInterior (edgeSlab_GRIM P V hV))) := by
        rw [image_univ, Subtype.range_coe]
      rw [hUY]
      exact hC.continuousOn.isOpen_inter_preimage (hann_open δ) U.isOpen
    have hsph : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
        {z : EuclideanSpace ℝ (Fin 2) | |‖z‖ - 1| < δ} ∩
          C ⁻¹' ((Subtype.val : U → (W.pieceInterior (edgeSlab_GRIM P V hV))) '' univ) := by
      intro z hz
      have hz1 : ‖z‖ = 1 := by simpa using hz
      refine ⟨by simp [hz1, hδ0], ?_⟩
      let w : ClosedCell 2 := ⟨z, by simp [hz1]⟩
      have hw : 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ := by
        change 1 - δ < ‖z‖
        rw [hz1]
        linarith
      have hCz : C z = D w := (hDC w hw).symm
      exact ⟨⟨D w, hDU w⟩, mem_univ _, hCz.symm⟩
    obtain ⟨η, hη, hηsub⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_thickening_subset_open
      hOopen hsph
    set δ₁ : ℝ := min (min δ η) (min r' (1 / 2)) with hδ₁
    have hδ₁0 : 0 < δ₁ := lt_min (lt_min hδ0 hη) (lt_min hr' (by norm_num))
    have hδ₁δ : δ₁ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
    have hδ₁η : δ₁ ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have hδ₁r : δ₁ ≤ r' := (min_le_right _ _).trans (min_le_left _ _)
    have hδ₁h : δ₁ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hsubδ : ∀ z : EuclideanSpace ℝ (Fin 2), |‖z‖ - 1| < δ₁ → |‖z‖ - 1| < δ :=
      fun z hz => lt_of_lt_of_le hz hδ₁δ
    have hCU : ∀ z, |‖z‖ - 1| < δ₁ → C z ∈ U := by
      intro z hz
      have hzpos : 0 < ‖z‖ := by
        have := (abs_lt.mp hz).1
        linarith
      have hmem : z ∈ Metric.thickening η (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
        rw [Metric.mem_thickening_iff]
        refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
        · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ hzpos.ne']
        · rw [dist_eq_norm]
          have h1 : z - ‖z‖⁻¹ • z = (1 - ‖z‖⁻¹) • z := by
            rw [sub_smul, one_smul]
          rw [h1, norm_smul, Real.norm_eq_abs]
          have h2 : |1 - ‖z‖⁻¹| * ‖z‖ = |‖z‖ - 1| := by
            rw [← abs_of_pos hzpos, ← abs_mul]
            congr 1
            rw [abs_of_pos hzpos]
            field_simp
          rw [h2]
          exact lt_of_lt_of_le hz hδ₁η
      obtain ⟨-, ⟨u, -, hu⟩⟩ := hηsub hmem
      rw [← hu]
      exact u.2
    refine ⟨δ₁, r', U, Fl, C, hδ₁0, by linarith, hδ₁r, hFl, hFl0, hgrp, hFlP, hFlB,
      hC.mono fun z hz => hsubδ z hz, hCinj.mono fun z hz => hsubδ z hz,
      fun z hz => hCimm z (hsubδ z hz), fun z hz => ⟨(hCP z (hsubδ z hz)).1, ?_⟩, hCU,
      fun w t hw => ?_⟩
    · rw [(hCP z (hsubδ z hz)).2]
      ring
    · have hwδ : 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ := lt_of_le_of_lt (by linarith) hw
      have hCw : C w = D w := (hDC w hwδ).symm
      obtain ⟨hDw, hHw⟩ := hHmFl (w, t)
      refine ⟨hCw ▸ hDw, ?_⟩
      rw [hHw]
      congr 2
      exact Subtype.ext hCw.symm

end GC.GraphManifold.Assembly.FC39P0
