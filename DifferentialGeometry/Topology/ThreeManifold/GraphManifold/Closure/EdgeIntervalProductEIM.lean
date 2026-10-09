import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimFlowEdgeHandle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeIntervalSublevelEIM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeIntervalLiftEIM

/-!
# E3: the boundary-preserving product over an interval component of the edge base (lane
# S-EDGE-INT2)

Draft 74, package E3 (`edge_interval_product74`). For an edge bundle `P` over a closed edge
base, a smooth embedding `β : [0, 1] → P.Base` whose range is an actual component `C` of the
edge base, there is a whole `D² × [0, 1]` (an `EdgeHandle`) onto the whole inverse image of `C`
below the level, projecting to `β t` over the slice `t`, whose slices are the whole disks and whose
slice rims are the whole rims (the four interval fields of `EdgeComponentModels`).

Route: the axial coordinate of `β` and the edge slab of RIMBOX (`FC39GRimEdgeSlab`), the end disk
`D` over `β 0` taken from `P.fibre_disk` and lifted into the slab (`EdgeIntervalLiftEIM`), the
plain flow handle `exists_flowHandle_GRIM`, and the rim of the end disk read off the regular
sublevel `{axial = 0, 0 ≤ level - height}` (`EdgeIntervalSublevelEIM`: the boundary of an
embedded copy of the sublevel is `{level - height = 0}`). No old end disk of an
`EdgeComponentModels` is used (the earlier flow edge handle took the polar end disk of the old
product as input).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsEIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothEIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance diskChartsAddEIM : ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell 2) :=
  diskChartsEIM

variable {W : CompactCarrier.{u}}

/-- **E3, interval component product.** -/
theorem EdgeBundle.edge_interval_product_EIM (P : EdgeBundle W) (β : Icc (0 : ℝ) 1 → P.Base)
    (hβ : IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ β) (C : P.EdgeBaseComponent)
    (hC : range β = C.1) :
    ∃ H : EdgeHandle W, range H.map = P.wholeComponent C ∧
      (∀ w t, ∃ hx : H.map (w, t) ∈ P.source, P.proj ⟨H.map (w, t), hx⟩ = β t) ∧
      (∀ t, range (fun w => H.map (w, t)) = P.disk (β t)) ∧
      (∀ t, (fun w => H.map (w, t)) '' diskRim = P.rim (β t)) := by
  obtain ⟨V, φ, ε, hV, hε, hrange, hφ, hφβ, hφinj, hφs, hφV, hK⟩ :=
    exists_axialCoordinate_GRIM β hβ.contMDiff hβ.isEmbedding.injective
      (fun t => hβ.isImmersion.mfderiv_injective (by simp) t)
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
    (M := W.pieceInterior (edgeSlab_GRIM P V hV))
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior (edgeSlab_GRIM P V hV)) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  obtain ⟨hP, hB, hreg, hregb, hprop⟩ := edgeSlab_transportHypotheses_GRIM P hV hφ hφs hK
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 1 + 1 + Module.finrank ℝ ℝ := by
    simp
  have hpV : ∀ y : (W.pieceInterior (edgeSlab_GRIM P V hV)),
      P.proj (edgeSlabIncl_GRIM P V hV y) ∈ V := fun y => y.2.1.snd
  have hβV : ∀ t, β t ∈ V := fun t => hrange (mem_range_self t)
  have hβ0 : φ (β (iccEnd false)) = 0 := by
    rw [hφβ]
    simp [iccEnd]
  -- the end disk over `β 0`, lifted into the slab
  obtain ⟨φ₀, hφ₀, hφ₀r⟩ := P.fibre_disk (β (iccEnd false))
  have hφ₀Y : ∀ w, φ₀ w ∈ W.pieceInterior (edgeSlab_GRIM P V hV) := by
    intro w
    have hw : φ₀ w ∈ range φ₀ := mem_range_self w
    rw [hφ₀r] at hw
    obtain ⟨x, ⟨hxc, -⟩, hx⟩ := hw
    rw [← hx]
    exact ⟨⟨x.2, by rw [hxc]; exact hβV _⟩, P.source_interior x.2⟩
  obtain ⟨D, hDφ, hDemb⟩ :=
    exists_interiorLift_isSmoothEmbedding_EIM W (edgeSlab_GRIM P V hV) hφ₀ hφ₀Y
  have hDsm : ContMDiff (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ D := hDemb.contMDiff
  have hDinj : Injective D := hDemb.isEmbedding.injective
  have hDimm : ∀ w, Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) D w) :=
    fun w => hDemb.isImmersion.mfderiv_injective (by simp) w
  have hDr : range D = {y | φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = 0 ∧
      0 ≤ P.level - P.height (edgeSlabIncl_GRIM P V hV y)} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      have hw : φ₀ w ∈ range φ₀ := mem_range_self w
      rw [hφ₀r] at hw
      obtain ⟨x, ⟨hxc, hxl⟩, hx⟩ := hw
      have hxe : edgeSlabIncl_GRIM P V hV (D w) = x := Subtype.ext ((hDφ w).trans hx.symm)
      change φ (P.proj (edgeSlabIncl_GRIM P V hV (D w))) = 0 ∧
        0 ≤ P.level - P.height (edgeSlabIncl_GRIM P V hV (D w))
      rw [hxe, hxc]
      exact ⟨hβ0, by linarith⟩
    · rintro ⟨hy0, hyB⟩
      have hpy : P.proj (edgeSlabIncl_GRIM P V hV y) = β (iccEnd false) :=
        hφinj (hpV y) (hβV _) (hy0.trans hβ0.symm)
      have hmem : (y : W.Carrier) ∈ range φ₀ := by
        rw [hφ₀r]
        exact ⟨edgeSlabIncl_GRIM P V hV y, ⟨hpy, by linarith⟩, rfl⟩
      obtain ⟨w, hw⟩ := hmem
      exact ⟨w, Subtype.ext ((hDφ w).trans hw)⟩
  -- the rim of the end disk
  have hrimiff : ∀ w : ClosedCell 2,
      w ∈ diskRim ↔ P.level - P.height (edgeSlabIncl_GRIM P V hV (D w)) = 0 := fun _ =>
    isBoundaryPoint_iff_of_range_eq_regularSublevel_EIM (d := 1) hdim hP hB
      (fun y _ _ => hreg y) (fun y _ hy => hregb y hy) hDemb hDr
  -- the flow handle
  obtain ⟨Hm, hHm, hinj, himm, hPB, hrangeHm, -, r', hr', hBHm, U, Fl, hFl, hFl0, hgrp, hDU,
    hHmFl, hFlP, hFlB⟩ :=
    exists_flowHandle_GRIM hdim hP hB (a := -ε) (b := 1 + ε) (fun y _ _ => hreg y)
      (fun y _ hy => hregb y hy) hprop (a₀ := -(ε / 2)) (b₀ := 1 + ε / 2) (by linarith)
      (by linarith) (by linarith) (by linarith) D hDsm hDinj hDimm hDr
  obtain ⟨hvalsm, hvalimm⟩ := pieceInterior_val_immersion_GRIM (edgeSlab_GRIM P V hV)
  obtain ⟨H, hH⟩ := exists_edgeHandle_of_immersion_GRIM
    (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier) hvalsm
    Subtype.val_injective hvalimm (by rintro _ ⟨y, rfl⟩; exact y.2.2) Hm hHm hinj himm
  have hbase : ∀ (y : (W.pieceInterior (edgeSlab_GRIM P V hV))) (t : Icc (0 : ℝ) 1),
      φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = t →
      P.proj (edgeSlabIncl_GRIM P V hV y) = β t := fun y t hy =>
    hφinj (hpV y) (hβV t) (by rw [hφβ]; exact hy)
  have hslab : ∀ (x : P.source) (t : Icc (0 : ℝ) 1), P.proj x = β t →
      ∃ y : (W.pieceInterior (edgeSlab_GRIM P V hV)), (y : W.Carrier) = x ∧
        edgeSlabIncl_GRIM P V hV y = x ∧ φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = t := by
    intro x t hx
    have hxV : P.proj x ∈ V := hx ▸ hβV t
    refine ⟨⟨x.1, ⟨x.2, hxV⟩, P.source_interior x.2⟩, rfl, rfl, ?_⟩
    change φ (P.proj x) = t
    rw [hx, hφβ]
  have hHmap : ∀ p, H.map p = (Hm p : W.Carrier) := hH
  have hproj : ∀ w t, ∃ hx : H.map (w, t) ∈ P.source,
      P.proj ⟨H.map (w, t), hx⟩ = β t := by
    intro w t
    rw [hHmap]
    exact ⟨(Hm (w, t)).2.1.fst, hbase (Hm (w, t)) t (hPB (w, t)).1⟩
  have hdisk : ∀ t, range (fun w => H.map (w, t)) = P.disk (β t) := by
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
  refine ⟨H, ?_, hproj, hdisk, ?_⟩
  · -- the whole component
    ext x
    constructor
    · rintro ⟨⟨w, t⟩, rfl⟩
      have hx : H.map (w, t) ∈ P.disk (β t) := by
        rw [← hdisk t]
        exact ⟨w, rfl⟩
      obtain ⟨x', ⟨hx'c, hx'l⟩, hx'e⟩ := hx
      refine ⟨x', ⟨?_, hx'l⟩, hx'e⟩
      rw [show P.proj x' ∈ C.1 ↔ P.proj x' ∈ range β by rw [hC], hx'c]
      exact mem_range_self t
    · rintro ⟨x, ⟨hxc, hxl⟩, rfl⟩
      have hxc' : P.proj x ∈ C.1 := hxc
      rw [← hC] at hxc'
      obtain ⟨t, ht⟩ := hxc'
      have hx : (x : W.Carrier) ∈ P.disk (β t) := ⟨x, ⟨ht.symm, hxl⟩, rfl⟩
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
      have hBD : P.level - P.height (edgeSlabIncl_GRIM P V hV (D w)) = 0 := (hrimiff w).mp hw
      have hBHm' : P.level - P.height (edgeSlabIncl_GRIM P V hV (Hm (w, t))) = 0 := by
        have h := hBHm (w, t) (by
          change P.level - P.height (edgeSlabIncl_GRIM P V hV (D w)) < r'
          rw [hBD]
          exact hr')
        exact h.trans hBD
      have hc : (⟨H.map (w, t), hx⟩ : P.source) = edgeSlabIncl_GRIM P V hV (Hm (w, t)) :=
        Subtype.ext (hHmap _)
      rw [hc]
      linarith
    · rintro ⟨x, ⟨hxc, hxl⟩, rfl⟩
      have hx : (x : W.Carrier) ∈ P.disk (β t) := ⟨x, ⟨hxc, hxl.le⟩, rfl⟩
      rw [← hdisk t] at hx
      obtain ⟨w, hw⟩ := hx
      refine ⟨w, ?_, hw⟩
      obtain ⟨hDw, hHw⟩ := hHmFl (w, t)
      have hBy : P.level - P.height (edgeSlabIncl_GRIM P V hV (Hm (w, t))) = 0 := by
        have hc : edgeSlabIncl_GRIM P V hV (Hm (w, t)) = x :=
          Subtype.ext ((hHmap _).symm.trans hw)
        rw [hc, hxl, sub_self]
      set z : U := Fl (t : ℝ) ⟨D w, hDw⟩ with hz
      have hzB : P.level - P.height (edgeSlabIncl_GRIM P V hV z) = 0 := by
        rw [← hBy, hHw]
      have hback : Fl (-(t : ℝ)) z = ⟨D w, hDw⟩ := by
        have h := congrArg (fun F : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)),
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ U => F ⟨D w, hDw⟩) (hgrp (t : ℝ) (-(t : ℝ)))
        simp only [Diffeomorph.coe_trans, comp_apply, add_neg_cancel, hFl0,
          Diffeomorph.coe_refl, id_eq] at h
        exact h
      have hBD : P.level - P.height (edgeSlabIncl_GRIM P V hV (D w)) = 0 := by
        have h := hFlB z (-(t : ℝ)) (by
          rw [hzB, abs_zero]
          exact hr')
        change P.level - P.height (edgeSlabIncl_GRIM P V hV
          ((Fl (-(t : ℝ)) z : U) : (W.pieceInterior (edgeSlab_GRIM P V hV)))) =
          P.level - P.height (edgeSlabIncl_GRIM P V hV z) at h
        rw [hback, hzB] at h
        exact h
      exact (hrimiff w).mpr hBD

end GC.GraphManifold.Assembly.FC39P0
