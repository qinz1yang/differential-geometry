import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlug
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSphere
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
Actual signed split tubes in bounded carriers, with retained external collars avoiding the tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

private instance plugInteriorBoundaryless (W : CompactCarrier.{u}) :
    BoundarylessManifold W.model W.interior where
  isInteriorPoint' x := W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property

def boundedSplitInterior (W : CompactCarrier.{u}) : Type u := W.interior

private instance plugInteriorTopology (W : CompactCarrier.{u}) :
    TopologicalSpace (boundedSplitInterior W) := inferInstanceAs (TopologicalSpace W.interior)

instance boundedSplitInteriorCharts (W : CompactCarrier.{u}) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (boundedSplitInterior W) :=
  DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞ (M := W.interior)

instance boundedSplitInteriorSmooth (W : CompactCarrier.{u}) :
    IsManifold (𝓡 3) ∞ (boundedSplitInterior W) :=
  DifferentialGeometry.Manifold.interiorIsManifold W.model ∞ (M := W.interior)

private def plugInteriorIdentity (W : CompactCarrier.{u}) :
    W.interior ≃ₘ⟮W.model, 𝓡 3⟯ boundedSplitInterior W :=
  DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.interior)

def boundedSplitInteriorVal (W : CompactCarrier.{u}) : boundedSplitInterior W → W.Carrier :=
  fun x => x.val

private theorem boundedSplitInteriorVal_local (W : CompactCarrier.{u}) :
    IsLocalDiffeomorph (𝓡 3) W.model ∞ (boundedSplitInteriorVal W) := by
  intro x
  exact ((plugInteriorIdentity W).symm.isLocalDiffeomorph x).comp _ _
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val W.interior _)

private def plugInteriorClamp {W : CompactCarrier.{u}} (a : W.interior)
    (x : W.Carrier) : boundedSplitInterior W := by
  classical
  exact if hx : x ∈ W.interior then ⟨x, hx⟩ else a

private theorem plugInteriorClamp_val {W : CompactCarrier.{u}} (a : W.interior)
    {x : W.Carrier} (hx : x ∈ W.interior) :
    boundedSplitInteriorVal W (plugInteriorClamp a x) = x := by
  classical
  change (if hz : x ∈ W.interior then (⟨x, hz⟩ : W.interior) else a).val = x
  rw [dite_eq_left hx]

private theorem plugInteriorClamp_local
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [BoundarylessManifold I M] {W : CompactCarrier.{u}} (a : W.interior)
    {f : M → W.Carrier} {x : M} (hf : IsLocalDiffeomorphAt I W.model ∞ f x) :
    IsLocalDiffeomorphAt I (𝓡 3) ∞ (plugInteriorClamp a ∘ f) x := by
  have hx : f x ∈ W.interior :=
    (hf.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint
  have heq : (boundedSplitInteriorVal W ∘ plugInteriorClamp a ∘ f) =ᶠ[𝓝 x] f := by
    filter_upwards [hf.contMDiffAt.continuousAt.preimage_mem_nhds
      (W.interior.isOpen.mem_nhds hx)] with y hy
    exact plugInteriorClamp_val a hy
  have hloc := IsLocalDiffeomorphAt.of_eventuallyEq heq hf
  have hgV : ∀ y, (boundedSplitInteriorVal W ∘ plugInteriorClamp a ∘ f) y ∈ W.interior :=
    fun y => (plugInteriorClamp a (f y)).property
  have hlift := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hgV hloc
  exact hlift.comp _ _ ((plugInteriorIdentity W).isLocalDiffeomorph _)

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool}

private def plugSolid (h : E.IsSplitSeam j b) : ℂ × Circle → W.Carrier :=
  E.toTorus.pieceChart (E.seamPiece j b) (discPlanarBase 1) (E.splitData h).ΘV clampDisc

private def plugHost (h : E.IsSplitSeam j b) : ℂ × Circle → W.Carrier :=
  E.toTorus.pieceChart (E.hostPiece j b) pantsPlanarBase (E.splitData h).ΘH clampPants

private def plugSeam (j : Fin E.toTorus.pairing.count) (b : Bool) (q : Torus × ℝ) :
    W.Carrier := E.toTorus.seam j (E.seamCoord j b q)

private def plugHostSide (h : E.IsSplitSeam j b) : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩

private theorem plugCross_zero (h : E.IsSplitSeam j b) :
    (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
  have h0 := h.2.2
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  exact h0

private theorem plugSeam_zero (j : Fin E.toTorus.pairing.count) (b : Bool) (t : Torus) :
    E.plugSeam j b (t, 0) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (t, halfZero)) := by
  rw [plugSeam, seamCoord_apply, neg_zero]
  exact (E.cutMap_sideCollar_eq_seam j b t 0 le_rfl zero_lt_one).symm

private theorem plugSeam_local (j : Fin E.toTorus.pairing.count) (b : Bool) {q : Torus × ℝ}
    (hq : |q.2| < 1) :
    IsLocalDiffeomorphAt signedCollarModel W.model ∞ (E.plugSeam j b) q := by
  have hmem : E.seamCoord j b q ∈ (E.toTorus.seam j).source := by
    rw [E.toTorus.seam_source, seamCoord_apply]
    have h1 := abs_lt.mp hq
    cases b <;> simp only [sideHeight, neg_neg, id] <;> constructor <;> linarith
  exact ((E.seamCoord j b).isLocalDiffeomorph q).comp _ _
    ((E.toTorus.seam j).isLocalDiffeomorphAt _ _ ∞ hmem)

private theorem plugSeam_inj (j : Fin E.toTorus.pairing.count) (b : Bool) {t t' : Torus}
    (h : E.plugSeam j b (t, 0) = E.plugSeam j b (t', 0)) : t = t' := by
  have hmem : ∀ x : Torus, E.seamCoord j b (x, 0) ∈ (E.toTorus.seam j).source := by
    intro x
    rw [E.toTorus.seam_source, seamCoord_apply, neg_zero]
    change -1 < sideHeight b 0 ∧ sideHeight b 0 < 1
    cases b <;> simp [sideHeight]
  have := (E.toTorus.seam j).toPartialEquiv.injOn (hmem t) (hmem t') h
  exact congrArg Prod.fst ((E.seamCoord j b).injective this)

private theorem plugPort_solid (h : E.IsSplitSeam j b) (l : Fin 1) :
    E.standardPort (E.seamPiece j b) h.1 l = ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
  have hs : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
  exact Subsingleton.elim _ _

private theorem plugPort_host (h : E.IsSplitSeam j b) :
    E.standardPort (E.hostPiece j b) h.2.1 (E.plugHostSide h) =
      ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩ :=
  Equiv.apply_symm_apply _ _

private theorem plugSeam_neg (h : E.IsSplitSeam j b) (t : Torus) {r : ℝ}
    (hr : -min ((E.splitData h).δ / 2) (1 / 2) < r) (hr0 : r < 0) :
    E.plugSeam j b (t, r) = E.plugSolid h ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ), t.2) := by
  have hδ := (E.splitData h).hδ
  have hm1 := min_le_left ((E.splitData h).δ / 2) (1 / 2)
  have hm2 := min_le_right ((E.splitData h).δ / 2) (1 / 2)
  have hs0 : 0 ≤ -r := by linarith
  have hs1 : -r < 1 := by linarith
  rw [plugSeam, seamCoord_apply, ← E.cutMap_sideCollar_eq_seam j b t (-r) hs0 hs1]
  have hp : (t, halfPoint (-r) hs0) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.seamPiece j b)
    ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ hp
  have e2 := (E.splitData h).hV 0 (t, halfPoint (-r) hs0) hp (by
    change -r < (E.splitData h).δ
    linarith)
  rw [E.plugPort_solid h] at e2
  rw [← e1, e2]
  change E.toTorus.cutMap ((E.splitData h).ΘV ((discPlanarBase.{u} 1).collar 0
    (t.1, halfPoint (-r) hs0), t.2) : E.toTorus.cutCarrier.Carrier) =
    E.toTorus.cutMap ((E.splitData h).ΘV (clampDisc ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ)), t.2) :
      E.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq hs0 hs1]
  congr 4
  ring_nf

private theorem plugSeam_pos (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) (t : Torus) {r : ℝ}
    (hr0 : 0 < r) (hr : r < min ((E.splitData h).δ / 2) (1 / 2)) :
    E.plugSeam j b (t, r) = E.plugHost h (planarCollarFormula 3 (E.plugHostSide h)
      (((t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : Circle) : ℂ), r),
      t.1 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
  have hδ := (E.splitData h).hδ
  have hm1 := min_le_left ((E.splitData h).δ / 2) (1 / 2)
  have hm2 := min_le_right ((E.splitData h).δ / 2) (1 / 2)
  have hs1 : r < 1 := by linarith
  have hcross : E.crossMap j b t = (t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
      t.1 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    rw [hlin.crossMap_apply b t]
    simp [linearTorusMap, plugCross_zero E h]
  have e0 := E.cutMap_sideCollar_eq_seam j (!b) (E.crossMap j b t) r hr0.le hs1
  rw [leftOfSide_not_crossMap, sideHeight_not] at e0
  rw [plugSeam, seamCoord_apply, sideHeight_neg, ← e0]
  have hp : (E.crossMap j b t, halfPoint r hr0.le) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩ hp
  have e2 := (E.splitData h).hH (E.plugHostSide h) (E.crossMap j b t, halfPoint r hr0.le) hp (by
    change r < (E.splitData h).δ
    linarith)
  rw [E.plugPort_host h] at e2
  rw [← e1, e2]
  change E.toTorus.cutMap ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar (E.plugHostSide h)
    ((E.crossMap j b t).1, halfPoint r hr0.le), (E.crossMap j b t).2) :
      E.toTorus.cutCarrier.Carrier) = _
  rw [pantsCollar_eq _ hr0.le hs1, hcross]
  rfl

private theorem plugHost_local (h : E.IsSplitSeam j b) {q : ℂ × Circle}
    (hq : q.1 ∈ SplitTube.pantsInterior) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞ (E.plugHost h) q :=
  E.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampPants hq)

private theorem plugSolid_local (h : E.IsSplitSeam j b) {q : ℂ × Circle} (hq : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞ (E.plugSolid h) q :=
  E.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq)

private theorem plugInteriorClamp_eq_of_mem (a : W.interior) {x y : W.Carrier}
    (hx : x ∈ W.interior) (hy : y ∈ W.interior)
    (heq : plugInteriorClamp a x = plugInteriorClamp a y) : x = y := by
  have he := congrArg (boundedSplitInteriorVal W) heq
  rwa [plugInteriorClamp_val a hx, plugInteriorClamp_val a hy] at he

private theorem plugInterior_mem_of_local
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [BoundarylessManifold I M] {f : M → W.Carrier} {x : M}
    (hf : IsLocalDiffeomorphAt I W.model ∞ f x) : f x ∈ W.interior :=
  (hf.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint

private def plugFallback (h : E.IsSplitSeam j b) : W.interior :=
  ⟨E.plugSolid h (0, 1), plugInterior_mem_of_local _
    (E.plugSolid_local h (q := (0, 1)) (by simp))⟩

def boundedSplitCharts (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    SplitTube.SplitCharts (boundedSplitInterior W) where
  host := E.plugHostSide h
  e₀ := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  e₁ := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  d := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  he₀ := (units_entries_of_zero _ (plugCross_zero E h)).2
  he₁ := (units_entries_of_zero _ (plugCross_zero E h)).1
  δ := min ((E.splitData h).δ / 2) (1 / 2)
  hδ := lt_min (half_pos (E.splitData h).hδ) (by norm_num)
  hδ1 := min_le_right _ _
  solid := plugInteriorClamp (E.plugFallback h) ∘ E.plugSolid h
  hostMap := plugInteriorClamp (E.plugFallback h) ∘ E.plugHost h
  seam := plugInteriorClamp (E.plugFallback h) ∘ E.plugSeam j b
  solid_local q hq := plugInteriorClamp_local _ _ (E.plugSolid_local h hq)
  host_local q hq := plugInteriorClamp_local _ _ (E.plugHost_local h hq)
  seam_local q hq := plugInteriorClamp_local _ _ (E.plugSeam_local j b
    (lt_of_lt_of_le hq ((min_le_right _ _).trans (by norm_num))))
  solid_inj q q' hq hq' heq := by
    have he := plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugSolid_local h hq))
      (plugInterior_mem_of_local _ (E.plugSolid_local h hq')) heq
    refine E.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq) ?_ he
    intro he
    have h1 := clampDisc_val.{u} hq.le
    have h2 := clampDisc_val.{u} hq'.le
    have he' := congrArg
      (fun x : (discPlanarBase.{u} 1).surface.Carrier => (x : discSet.{u}).val) he
    change (clampDisc.{u} q.1 : discSet.{u}).val =
      (clampDisc.{u} q'.1 : discSet.{u}).val at he'
    rw [h1, h2] at he'
    exact congrArg ULift.down he'
  host_inj q q' hq hq' heq := by
    have he := plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugHost_local h hq))
      (plugInterior_mem_of_local _ (E.plugHost_local h hq')) heq
    refine E.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampPants hq) ?_ he
    intro he
    have h1 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq)
    have h2 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq')
    have he' := congrArg
      (fun x : pantsPlanarBase.{u}.surface.Carrier => (x : planarSet.{u} 3).val) he
    change (clampPants.{u} q.1 : planarSet.{u} 3).val =
      (clampPants.{u} q'.1 : planarSet.{u} 3).val at he'
    rw [h1, h2] at he'
    exact congrArg ULift.down he'
  seam_inj t t' heq := E.plugSeam_inj j b
    (plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugSeam_local j b (q := (t, 0)) (by simp)))
      (plugInterior_mem_of_local _ (E.plugSeam_local j b (q := (t', 0)) (by simp))) heq)
  solid_ne_host q q' hq hq' heq := by
    have he := plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugSolid_local h hq))
      (plugInterior_mem_of_local _ (E.plugHost_local h hq')) heq
    exact E.toTorus.pieceChart_ne _ _ _ _ (E.seamPiece_ne_hostPiece h) _ _ _
      (isLocalDiffeomorphAt_clampDisc hq) he
  seam_ne_solid t q hq heq := by
    have he := plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugSeam_local j b (q := (t, 0)) (by simp)))
      (plugInterior_mem_of_local _ (E.plugSolid_local h hq)) heq
    rw [E.plugSeam_zero] at he
    exact E.toTorus.cutMap_ne_pieceChart _ _ _ _
      (E.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampDisc hq) he
  seam_ne_host t q hq heq := by
    have he := plugInteriorClamp_eq_of_mem (E.plugFallback h)
      (plugInterior_mem_of_local _ (E.plugSeam_local j b (q := (t, 0)) (by simp)))
      (plugInterior_mem_of_local _ (E.plugHost_local h hq)) heq
    rw [E.plugSeam_zero] at he
    exact E.toTorus.cutMap_ne_pieceChart _ _ _ _
      (E.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampPants hq) he
  seam_neg t r hr hr0 := congrArg (plugInteriorClamp (E.plugFallback h))
    (E.plugSeam_neg h t hr hr0)
  seam_pos t r hr0 hr := congrArg (plugInteriorClamp (E.plugFallback h))
    (E.plugSeam_pos h hlin t hr0 hr)


theorem boundedSplitCharts_solid_val (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
    (q : ℂ × Circle) (hq : ‖q.1‖ < 3) :
    boundedSplitInteriorVal W ((E.boundedSplitCharts h hlin).solid q) =
      E.toTorus.pieceChart (E.seamPiece j b) (discPlanarBase 1) (E.splitData h).ΘV
        clampDisc q :=
  plugInteriorClamp_val (E.plugFallback h)
    (plugInterior_mem_of_local _ (E.plugSolid_local h hq))

theorem boundedSplitCharts_host_val (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
    (q : ℂ × Circle) (hq : q.1 ∈ SplitTube.pantsInterior) :
    boundedSplitInteriorVal W ((E.boundedSplitCharts h hlin).hostMap q) =
      E.toTorus.pieceChart (E.hostPiece j b) pantsPlanarBase (E.splitData h).ΘH clampPants q :=
  plugInteriorClamp_val (E.plugFallback h)
    (plugInterior_mem_of_local _ (E.plugHost_local h hq))

theorem boundedSplitCharts_seam_val (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
    (q : Torus × ℝ) (hq : |q.2| < 1) :
    boundedSplitInteriorVal W ((E.boundedSplitCharts h hlin).seam q) =
      E.toTorus.seam j (E.seamCoord j b q) :=
  plugInteriorClamp_val (E.plugFallback h)
    (plugInterior_mem_of_local _ (E.plugSeam_local j b hq))

def boundedSplitTubeMap (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    SphereTwo × ℝ → W.Carrier :=
  boundedSplitInteriorVal W ∘ (E.boundedSplitCharts h hlin).tubeMap

theorem boundedSplitTubeMap_mem_interior (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) (q : SphereTwo × ℝ) :
    E.boundedSplitTubeMap h hlin q ∈ W.interior :=
  ((E.boundedSplitCharts h hlin).tubeMap q).property

theorem boundedSplitTubeMap_local (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) {q : SphereTwo × ℝ} (hq : |q.2| < 3) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ)) W.model ∞
      (E.boundedSplitTubeMap h hlin) q :=
  ((E.boundedSplitCharts h hlin).isLocalDiffeomorphAt_tubeMap hq).comp _ _
    (boundedSplitInteriorVal_local W _)

theorem boundedSplitTubeMap_injOn (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) {q q' : SphereTwo × ℝ} (hq : |q.2| < 3)
    (hq' : |q'.2| < 3)
    (heq : E.boundedSplitTubeMap h hlin q = E.boundedSplitTubeMap h hlin q') : q = q' :=
  (E.boundedSplitCharts h hlin).tubeMap_injOn hq hq' (Subtype.ext heq)

private def plugLiftedTubeMap (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    ClosureSphere.{u} × ℝ → W.Carrier :=
  fun q => E.boundedSplitTubeMap h hlin (q.1.down, q.2)

private theorem plugLiftedTubeMap_local (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) {q : ClosureSphere.{u} × ℝ} (hq : |q.2| < 3) :
    IsLocalDiffeomorphAt sphereSignedCollarModel W.model ∞
      (E.plugLiftedTubeMap h hlin) q := by
  let d := (uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).symm.prodCongr
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  exact (d.isLocalDiffeomorph q).comp _ _ (E.boundedSplitTubeMap_local h hlin hq)

private theorem plugTubePartial (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞,
      d.source = sphereSignedCollarSource ∧
      d.target = E.plugLiftedTubeMap h hlin '' sphereSignedCollarSource ∧
      d.toFun = E.plugLiftedTubeMap h hlin := by
  apply IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
  · intro q
    have hq : -1 < q.val.2 ∧ q.val.2 < 1 := q.property.2
    apply E.plugLiftedTubeMap_local h hlin
    apply abs_lt.mpr
    constructor <;> linarith [hq.1, hq.2]
  · exact isOpen_univ.prod isOpen_Ioo
  · exact ⟨(Classical.choice inferInstance, 0), mem_univ _, by norm_num⟩
  · intro q hq q' hq' heq
    have ha : |q.2| < 3 := by
      have hh := hq.2
      apply abs_lt.mpr
      constructor <;> linarith [hh.1, hh.2]
    have hb : |q'.2| < 3 := by
      have hh := hq'.2
      apply abs_lt.mpr
      constructor <;> linarith [hh.1, hh.2]
    have hh := E.boundedSplitTubeMap_injOn h hlin ha hb heq
    exact Prod.ext (ULift.ext (congrArg Prod.fst hh)) (congrArg (fun p : SphereTwo × ℝ => p.2) hh)


private theorem plugContinuousHalfLift : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

private def plugClampedHalfPoint (s : {r : ℝ // 0 ≤ r}) : EuclideanHalfSpace 1 :=
  halfSpaceOneLift (min (s : ℝ) (1 / 2))

private theorem plugClampedHalfPoint_coord (s : {r : ℝ // 0 ≤ r}) :
    (plugClampedHalfPoint s).1 0 = min (s : ℝ) (1 / 2) := by
  change max (min (s : ℝ) (1 / 2)) 0 = min (s : ℝ) (1 / 2)
  exact max_eq_left (le_min s.property (by norm_num))

private theorem plugClampedHalfPoint_continuous : Continuous plugClampedHalfPoint :=
  plugContinuousHalfLift.comp (continuous_subtype_val.min continuous_const)

private theorem plugClampedHalfPoint_zero : plugClampedHalfPoint 0 = halfZero := by
  change halfSpaceOneLift (min (0 : ℝ) (1 / 2)) = halfZero
  norm_num
  exact (halfSpaceOneLift_coord halfZero).trans rfl

private theorem plugCollars_avoid_compact {n : ℕ} (A : BoundaryTori W n)
    {K : Set W.Carrier} (hK : IsCompact K) (hKI : K ⊆ W.interior) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 ∧ ∀ r,
      Disjoint K (shrinkHalfCollar hρ (A.collar r)).target := by
  let g : Fin n × (Torus × {r : ℝ // 0 ≤ r}) → W.Carrier :=
    fun p => A.collar p.1 (p.2.1, plugClampedHalfPoint p.2.2)
  have hg : Continuous g := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    apply (A.collar i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (continuous_fst.prodMk (plugClampedHalfPoint_continuous.comp continuous_snd))
    intro p
    change (p.1, plugClampedHalfPoint p.2) ∈ (A.collar i).source
    rw [A.source_eq]
    change (plugClampedHalfPoint p.2).1 0 < 1
    rw [plugClampedHalfPoint_coord]
    exact (min_le_right p.2.val (1 / 2)).trans_lt (by norm_num)
  let f : (Fin n × Torus) × {r : ℝ // 0 ≤ r} → W.Carrier :=
    fun p => g (p.1.1, p.1.2, p.2)
  have hf : Continuous f := hg.comp
    ((continuous_fst.fst).prodMk ((continuous_fst.snd).prodMk continuous_snd))
  have hzero (p : Fin n × Torus) : f (p, 0) ∈ Kᶜ := by
    change A.collar p.1 (p.2, plugClampedHalfPoint 0) ∉ K
    rw [plugClampedHalfPoint_zero]
    intro hp
    exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp
      (A.boundary_zero p.1 p.2) (hKI hp)
  have hprod : f ⁻¹' Kᶜ ∈ nhdsSet (univ : Set (Fin n × Torus)) ×ˢ
      nhds (0 : {r : ℝ // 0 ≤ r}) :=
    isCompact_univ.mem_nhdsSet_prod_of_forall (fun p hp => by
      simpa only [nhds_prod_eq] using
        ((hK.isClosed.isOpen_compl).preimage hf).mem_nhds (hzero p))
  obtain ⟨V, hV, R, hR, hVR⟩ := Filter.mem_prod_iff.mp hprod
  have hVall (p : Fin n × Torus) : p ∈ V := by
    have hVu : V = univ := by simpa using hV
    simp only [hVu, mem_univ]
  obtain ⟨a, ha, haR⟩ := Metric.mem_nhds_iff.mp hR
  let ρ : ℝ := min a (1 / 2)
  have hρ : 0 < ρ := lt_min ha (by norm_num)
  have hρ1 : ρ ≤ 1 := (min_le_right a (1 / 2)).trans (by norm_num)
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro y hyK hy
  let p := (shrinkHalfCollar hρ (A.collar i)).symm y
  have hp := (shrinkHalfCollar hρ (A.collar i)).map_target' hy
  have hp1 : p.2.1 0 < 1 := by
    rwa [shrinkHalfCollar_source hρ hρ1 (A.source_eq i)] at hp
  let s := halfSpaceScale hρ p.2
  have hsa : s.1 0 < a := (halfSpaceScale_lt hρ hp1).trans_le (min_le_left a (1 / 2))
  have hslo : s.1 0 < 1 / 2 :=
    (halfSpaceScale_lt hρ hp1).trans_le (min_le_right a (1 / 2))
  have he : plugClampedHalfPoint ⟨s.1 0, s.2⟩ = s := by
    unfold plugClampedHalfPoint
    rw [min_eq_left hslo.le]
    exact halfSpaceOneLift_coord s
  have hsR : (⟨s.1 0, s.2⟩ : {r : ℝ // 0 ≤ r}) ∈ R := by
    apply haR
    change dist (s.1 0) (0 : ℝ) < a
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg s.2]
  have hfK : f ((i, p.1), ⟨s.1 0, s.2⟩) ∈ Kᶜ :=
    hVR (show ((i, p.1), ⟨s.1 0, s.2⟩) ∈ V ×ˢ R from ⟨hVall (i, p.1), hsR⟩)
  apply hfK
  change A.collar i (p.1, plugClampedHalfPoint ⟨s.1 0, s.2⟩) ∈ K
  rw [he]
  have hy' := (shrinkHalfCollar hρ (A.collar i)).right_inv' hy
  exact hy' ▸ hyK

private theorem plugTube_compact (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    IsCompact (E.plugLiftedTubeMap h hlin '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  have hsm : ContMDiffOn sphereSignedCollarModel W.model ∞
      (E.plugLiftedTubeMap h hlin) (univ ×ˢ Icc (-1 : ℝ) 1) := by
    intro q hq
    apply (E.plugLiftedTubeMap_local h hlin ?_).contMDiffAt.contMDiffWithinAt
    apply abs_lt.mpr
    constructor <;> linarith [hq.2.1, hq.2.2]
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn hsm.continuousOn

theorem exists_boundedSplitSignedTube (j : Fin E.toTorus.pairing.count) (b : Bool)
    (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞,
      d.source = sphereSignedCollarSource ∧ d.target ⊆ W.interior ∧
      (∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s)) ∧
      ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 ∧ ∀ r,
        Disjoint d.target (shrinkHalfCollar hρ (E.toTorus.external.collar r)).target := by
  obtain ⟨d, hd, ht, heq⟩ := E.plugTubePartial h hlin
  let K := E.plugLiftedTubeMap h hlin '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hKI : K ⊆ W.interior := by
    rintro y ⟨q, hq, rfl⟩
    exact E.boundedSplitTubeMap_mem_interior h hlin _
  obtain ⟨ρ, hρ, hρ1, hav⟩ := plugCollars_avoid_compact E.toTorus.external
    (E.plugTube_compact h hlin) hKI
  have hsub : d.target ⊆ K := by
    rw [ht]
    apply image_mono
    intro q hq
    exact ⟨hq.1, hq.2.1.le, hq.2.2.le⟩
  refine ⟨d, hd, hsub.trans hKI, ?_, ρ, hρ, hρ1, ?_⟩
  · intro z s
    exact congrFun heq (z, s)
  · intro r
    exact (hav r).mono_left hsub

end GC.Seifert.ElementaryPresentation

namespace GC.GraphManifold

theorem exists_fibrePlugSignedTube :
    ∃ (W : CompactCarrier.{u}) (E : GC.Seifert.ElementaryPresentation W)
      (j : Fin E.toTorus.pairing.count),
      W.kind = .withBoundary ∧ E.toTorus.components.count = 2 ∧
      E.toTorus.pairing.count = 1 ∧ E.toTorus.externalCount = 2 ∧
      E.IsSplitSeam j true ∧ E.IsLinearSeam j ∧
      ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model
        (ClosureSphere.{u} × ℝ) W.Carrier ∞,
        d.source = sphereSignedCollarSource ∧ d.target ⊆ W.interior ∧
        ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 ∧ ∀ r,
          Disjoint d.target (shrinkHalfCollar hρ (E.toTorus.external.collar r)).target := by
  obtain ⟨W, E, j, hW, hC, hP, hE, hs, hl⟩ := exists_fibrePlug.{u}
  obtain ⟨d, hd, hdi, heq, ρ, hρ, hρ1, hav⟩ := E.exists_boundedSplitSignedTube j true hs hl
  exact ⟨W, E, j, hW, hC, hP, hE, hs, hl, d, hd, hdi, ρ, hρ, hρ1, hav⟩

end GC.GraphManifold
