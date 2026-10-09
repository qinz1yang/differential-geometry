import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitSideDataStatement
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelInj

/-!
# Points of the lift in the cut carrier of a mixed stage

Lane N2f, tier 2 (mixed form of route A′). The texts of the elementary files
`MoveSplitCappedSideModelPoints` and `MoveSplitCappedSideModelInj` (lane N2d) with the elementary
presentation and its chosen split datum replaced by a mixed stage `σ`, a split seam `h` and an
explicit split datum `SD` (`MixedSplitCharts`): the solid and host points `solidPt`, `hostPt` of
the cut carrier, the lift `liftPt` of the model solid torus of side `t`, its boundary points
(seam torus of `V`, port tori), and its injectivity on the side domain (`liftMap_injOn`). Only the
torus presentation, the two non-frozen pieces of the site and `SD` are read; the generic planar and
cut-carrier lemmas of the elementary files are used as they are.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (clampDisc clampPants clampDisc_val clampPants_val
  discCollar_eq pantsCollar_eq isLocalDiffeomorphAt_clampDisc isLocalDiffeomorphAt_clampPants
  sideHeight sideHeight_not sideHeight_neg seamRadius_one OnSolidBoundary)

section

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)

def solidPt (z : ℂ) (w : Circle) : σ.toTorus.cutCarrier.Carrier :=
  ((SD).ΘV (clampDisc z, w) : σ.toTorus.cutCarrier.Carrier)

def hostPt (z : ℂ) (ν : Circle) : σ.toTorus.cutCarrier.Carrier :=
  ((SD).ΘH (clampPants z, ν) : σ.toTorus.cutCarrier.Carrier)

theorem solidMap_eq_cutMap (q : ℂ × Circle) :
    σ.solidMap SD q = σ.toTorus.cutMap (σ.solidPt h SD q.1 q.2) := rfl

theorem hostMap_eq_cutMap (q : ℂ × Circle) :
    σ.hostMap SD q = σ.toTorus.cutMap (σ.hostPt h SD q.1 q.2) := rfl

theorem solidPt_mem (z : ℂ) (w : Circle) :
    σ.solidPt h SD z w ∈ σ.toTorus.components.piece (σ.seamPiece j b) :=
  ((SD).ΘV (clampDisc z, w)).property

theorem hostPt_mem (z : ℂ) (ν : Circle) :
    σ.hostPt h SD z ν ∈ σ.toTorus.components.piece (σ.hostPiece j b) :=
  ((SD).ΘH (clampPants z, ν)).property

theorem solidPt_isInteriorPoint {z : ℂ} (hz : ‖z‖ < 3) (w : Circle) :
    σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.solidPt h SD z w) :=
  (σ.toTorus.pieceChart_isInteriorPoint _ _ (SD).ΘV clampDisc (q := (z, w))
    (isLocalDiffeomorphAt_clampDisc hz)).1

theorem hostPt_isInteriorPoint {z : ℂ} (hz : z ∈ SplitTube.pantsInterior) (ν : Circle) :
    σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.hostPt h SD z ν) :=
  (σ.toTorus.pieceChart_isInteriorPoint _ _ (SD).ΘH clampPants (q := (z, ν))
    (isLocalDiffeomorphAt_clampPants hz)).1

theorem solidPt_three_smul (θ w : Circle) :
    σ.solidPt h SD ((3 : ℝ) • (θ : ℂ)) w =
      σ.toTorus.sideCollar (σ.seamSide j b) ((θ, w), halfZero) := by
  have hp : ((θ, w), halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource _
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.seamPiece j b)
    ⟨σ.seamSide j b, σ.sidePiece_seamSide j b⟩ hp
  have e2 := (SD).hV 0 ((θ, w), halfZero) hp (by
    change (0 : ℝ) < (SD).δ
    exact (SD).hδ)
  rw [σ.standardPort_seamPiece h] at e2
  rw [← e1, e2]
  change ((SD).ΘV (clampDisc ((3 : ℝ) • (θ : ℂ)), w) : σ.toTorus.cutCarrier.Carrier) =
    ((SD).ΘV ((discPlanarBase.{u} 1).collar 0 (θ, halfPoint 0 le_rfl), w) :
      σ.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq le_rfl zero_lt_one]
  norm_num

theorem hostPt_collar (l : Fin 3) (θ ν : Circle) :
    σ.hostPt h SD (planarCollarFormula 3 l ((θ : ℂ), 0)) ν =
      σ.toTorus.sideCollar
        (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l).val
        ((θ, ν), halfZero) := by
  have hp : ((θ, ν), halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource _
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.hostPiece j b)
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l) hp
  have e2 := (SD).hH l ((θ, ν), halfZero) hp (by
    change (0 : ℝ) < (SD).δ
    exact (SD).hδ)
  rw [← e1, e2]
  change ((SD).ΘH (clampPants (planarCollarFormula 3 l ((θ : ℂ), 0)), ν) :
      σ.toTorus.cutCarrier.Carrier) =
    ((SD).ΘH (pantsPlanarBase.{u}.collar l (θ, halfPoint 0 le_rfl), ν) :
      σ.toTorus.cutCarrier.Carrier)
  rw [pantsCollar_eq l le_rfl zero_lt_one]

theorem splitCharts_seam_zero (hlin : σ.IsLinearSeam j) (τ : Torus) :
    (σ.splitCharts SD hlin).seam (τ, 0) =
      (σ.splitCharts SD hlin).solid ((3 : ℝ) • (τ.1 : ℂ), τ.2) := by
  change σ.seamMap j b (τ, 0) = σ.solidMap SD ((3 : ℝ) • (τ.1 : ℂ), τ.2)
  rw [σ.seamMap_zero, σ.solidMap_eq_cutMap, σ.solidPt_three_smul]

section Lift

open SplitTube

variable (hlin : σ.IsLinearSeam j)

def sideDom (t : Bool) (q : ℂ × Circle) : Prop :=
  ‖q.1‖ ≤ 3 ∧ -3 < sgnR t * stripLevel (σ.hostSide h)
    ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖))

def liftFib (q : ℂ × Circle) : Circle :=
  q.2 ^ ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d) *
    unitOf q.1 ^ (σ.splitCharts SD hlin).e₁

def liftPt (t : Bool) (q : ℂ × Circle) : σ.toTorus.cutCarrier.Carrier :=
  if ‖q.1‖ ≤ 3 / 2 then σ.solidPt h SD ((2 : ℝ) • q.1) (q.2 ^ (σ.splitCharts SD hlin).e₀)
  else σ.hostPt h SD (hostChart (σ.hostSide h) ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖)))
    (σ.liftFib h SD hlin q)

theorem liftMap_eq_cutMap (t : Bool) (q : ℂ × Circle) :
    (σ.splitCharts SD hlin).liftMap t q = σ.toTorus.cutMap (σ.liftPt h SD hlin t q) := by
  unfold SplitCharts.liftMap liftPt
  split_ifs
  · rfl
  · rfl

theorem point_ne_zero {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q) :
    (σ.hostSide h).val ≠ 0 → (sideData (σ.hostSide h) t).point (q.2, ‖q.1‖) ≠ 0 := fun hl =>
  ne_zero_of_level _ t hl hq.2 (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1

theorem hostChart_point_mem_planarModel {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (h32 : 3 / 2 ≤ ‖q.1‖) :
    hostChart (σ.hostSide h) ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖)) ∈
      planarModel 3 :=
  hostChart_mem_planarModel _ t (σ.point_ne_zero h hq)
    (norm_point_le _ t (q := (q.2, ‖q.1‖)) h32 hq.1).1
    (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1 hq.2

theorem hostChart_point_mem_pantsInterior {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    hostChart (σ.hostSide h) ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖)) ∈
      pantsInterior :=
  hostChart_mem_pantsInterior _ t (σ.point_ne_zero h hq)
    ((norm_point_le _ t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32)
    ((le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).2 h3) hq.2

theorem isOpen_sideDom_interior (t : Bool) :
    IsOpen {q : ℂ × Circle | ‖q.1‖ < 3 ∧ -3 < sgnR t * stripLevel (σ.hostSide h)
      ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖))} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * stripLevel (σ.hostSide h)
      ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖))) {q | ‖q.1‖ < 3} := by
    refine continuousOn_const.mul ((contDiff_stripLevel _).continuous.comp_continuousOn ?_)
    refine (sideData (σ.hostSide h) t).continuousOn_point.comp
      (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, le_of_lt hq⟩
  have := hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt (continuous_const (y := (-3 : ℝ))) continuous_id)
  exact this

def portSide' (t : Bool) : σ.toTorus.Side :=
  (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
    (sidePort (σ.hostSide h) t)).val

theorem sidePiece_portSide (t : Bool) :
    σ.toTorus.sidePiece (σ.portSide' h t) = σ.hostPiece j b :=
  (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
    (sidePort (σ.hostSide h) t)).property

theorem portSide_ne_seamSide_not (t : Bool) : σ.portSide' h t ≠ σ.seamSide j (!b) := by
  intro he
  have h1 : σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
      (sidePort (σ.hostSide h) t) =
      σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (σ.hostSide h) := by
    rw [σ.standardPort_hostSide h]
    exact Subtype.ext he
  exact sidePort_ne (σ.hostSide h) t
    ((σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).injective h1)

theorem portSide_injective : Injective (σ.portSide' h) := by
  intro t t' he
  have h1 := (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).injective
    (Subtype.ext he)
  by_contra hne
  rcases Bool.eq_false_or_eq_true t with rfl | rfl <;>
    rcases Bool.eq_false_or_eq_true t' with rfl | rfl
  · exact hne rfl
  · exact sidePort_false_ne_true _ h1.symm
  · exact sidePort_false_ne_true _ h1
  · exact hne rfl

theorem cutMap_seamSide_ne_portSide (t : Bool) (τ τ' : Torus) :
    σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide j b) (τ, halfZero)) ≠
      σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.portSide' h t) (τ', halfZero)) := by
  intro he
  have hne : σ.toTorus.sideCollar (σ.seamSide j b) (τ, halfZero) ≠
      σ.toTorus.sideCollar (σ.portSide' h t) (τ', halfZero) := by
    intro he'
    have h1 := (σ.toTorus.sideCollar_zero_mem (σ.seamSide j b) τ).2
    have h2 := (σ.toTorus.sideCollar_zero_mem (σ.portSide' h t) τ').2
    rw [he'] at h1
    rw [σ.sidePiece_portSide h] at h2
    rw [σ.sidePiece_seamSide] at h1
    exact σ.seamPiece_ne_hostPiece h (σ.toTorus.eq_of_mem_piece' h1 h2)
  obtain ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := σ.toTorus.exists_seam_of_cutMap_sideCollar he hne
  · cases b
    · exact absurd h1 (by simp [seamSide])
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact σ.portSide_ne_seamSide_not h t (by rw [h2]; rfl)
  · cases b
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact σ.portSide_ne_seamSide_not h t (by rw [h2]; rfl)
    · exact absurd h1 (by simp [seamSide])

theorem liftPt_of_three_halves (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ = 3 / 2) :
    σ.liftPt h SD hlin t q = σ.toTorus.sideCollar (σ.seamSide j b)
      ((unitOf q.1, q.2 ^ (σ.splitCharts SD hlin).e₀), halfZero) := by
  unfold liftPt
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le), ← σ.solidPt_three_smul h SD]
  congr 1
  rw [← norm_smul_unitOf q.1, h32, smul_smul, unitOf_smul (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num

theorem liftPt_of_three (t : Bool) {q : ℂ × Circle} (h3 : ‖q.1‖ = 3) :
    σ.liftPt h SD hlin t q = σ.toTorus.sideCollar (σ.portSide' h t)
      ((q.2⁻¹, σ.liftFib h SD hlin q), halfZero) := by
  unfold liftPt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h3]; norm_num)), h3,
    sideData_point_collar _ t (by norm_num) (by norm_num), hostChart_hostInv]
  rw [show collarDepth 3 = 0 by simp [collarDepth]]
  exact σ.hostPt_collar h SD _ _ _

theorem liftPt_isInteriorPoint_of_lt (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ < 3 / 2) :
    σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q) := by
  unfold liftPt
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le)]
  refine σ.solidPt_isInteriorPoint h SD ?_ _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem liftPt_isInteriorPoint_of_mid (t : Bool) {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q) := by
  unfold liftPt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h32))]
  exact σ.hostPt_isInteriorPoint h SD (σ.hostChart_point_mem_pantsInterior h hq h32 h3) _

end Lift

end

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)

theorem solidPt_inj {z z' : ℂ} {w w' : Circle} (hz : ‖z‖ ≤ 3) (hz' : ‖z'‖ ≤ 3)
    (he : σ.solidPt h SD z w = σ.solidPt h SD z' w') : z = z' ∧ w = w' := by
  have h1 := Prod.ext_iff.mp ((SD).ΘV.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : (discPlanarBase.{u} 1).surface.Carrier =>
    ((show discSet.{u} from x).val).down) h1.1
  dsimp only at h2
  rw [clampDisc_val hz, clampDisc_val hz'] at h2
  exact h2

theorem hostPt_inj {z z' : ℂ} {ν ν' : Circle} (hz : z ∈ planarModel 3) (hz' : z' ∈ planarModel 3)
    (he : σ.hostPt h SD z ν = σ.hostPt h SD z' ν') : z = z' ∧ ν = ν' := by
  have h1 := Prod.ext_iff.mp ((SD).ΘH.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : pantsPlanarBase.{u}.surface.Carrier =>
    ((show planarSet.{u} 3 from x).val).down) h1.1
  dsimp only at h2
  rw [clampPants_val hz, clampPants_val hz'] at h2
  exact h2

theorem solidPt_ne_hostPt (z z' : ℂ) (w ν : Circle) : σ.solidPt h SD z w ≠ σ.hostPt h SD z' ν := by
  intro he
  have h1 := σ.solidPt_mem h SD z w
  rw [he] at h1
  exact σ.seamPiece_ne_hostPiece h (σ.toTorus.eq_of_mem_piece' h1 (σ.hostPt_mem h SD z' ν))

section Lift

variable (hlin : σ.IsLinearSeam j)

theorem liftPt_inj {t : Bool} {q q' : ℂ × Circle} (hq : σ.sideDom h t q) (hq' : σ.sideDom h t q')
    (he : σ.liftPt h SD hlin t q = σ.liftPt h SD hlin t q') : q = q' := by
  have he₀ := (σ.splitCharts SD hlin).he₀
  have he₁ := (σ.splitCharts SD hlin).he₁
  unfold liftPt at he
  by_cases h1 : ‖q.1‖ ≤ 3 / 2 <;> by_cases h1' : ‖q'.1‖ ≤ 3 / 2
  · simp only [h1, h1', ↓reduceIte] at he
    have hn : ∀ z : ℂ, ‖z‖ ≤ 3 / 2 → ‖(2 : ℝ) • z‖ ≤ 3 := fun z hz => by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    obtain ⟨e1, e2⟩ := σ.solidPt_inj h SD (hn _ h1) (hn _ h1') he
    refine Prod.ext (smul_right_injective ℂ (by norm_num : (2 : ℝ) ≠ 0) e1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he (σ.solidPt_ne_hostPt h SD _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he.symm (σ.solidPt_ne_hostPt h SD _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    push Not at h1 h1'
    obtain ⟨e1, e2⟩ := σ.hostPt_inj h SD (σ.hostChart_point_mem_planarModel h hq h1.le)
      (σ.hostChart_point_mem_planarModel h hq' h1'.le) he
    have e3 := congrArg (hostInv (σ.hostSide h)) e1
    rw [hostInv_hostChart, hostInv_hostChart] at e3
    have e4 := (sideData (σ.hostSide h) t).point_injOn ⟨mem_univ _, norm_nonneg _, hq.1⟩
      ⟨mem_univ _, norm_nonneg _, hq'.1⟩ e3
    have e5 : q.2 = q'.2 := congrArg Prod.fst e4
    have e6 : ‖q.1‖ = ‖q'.1‖ := congrArg Prod.snd e4
    unfold liftFib at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq e6 e7) e5

theorem liftPt_radius {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hi : ¬ σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q)) :
    ‖q.1‖ = 3 / 2 ∨ ‖q.1‖ = 3 := by
  by_contra hc
  push Not at hc
  rcases lt_or_gt_of_ne hc.1 with h32 | h32
  · exact hi (σ.liftPt_isInteriorPoint_of_lt h SD hlin t h32)
  · exact hi (σ.liftPt_isInteriorPoint_of_mid h SD hlin t hq h32 (lt_of_le_of_ne hq.1 hc.2))

theorem liftMap_injOn (t : Bool) :
    InjOn ((σ.splitCharts SD hlin).liftMap t) {q | σ.sideDom h t q} := by
  have he₀ := (σ.splitCharts SD hlin).he₀
  have he₁ := (σ.splitCharts SD hlin).he₁
  intro q hq q' hq' he
  rw [σ.liftMap_eq_cutMap, σ.liftMap_eq_cutMap] at he
  by_cases hi : σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q)
  · exact σ.liftPt_inj h SD hlin hq hq' (σ.toTorus.cutMap_eq_of_isInteriorPoint hi he)
  by_cases hi' : σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q')
  · exact (σ.liftPt_inj h SD hlin hq' hq (σ.toTorus.cutMap_eq_of_isInteriorPoint hi' he.symm)).symm
  rcases σ.liftPt_radius h SD hlin hq hi with h1 | h1 <;>
    rcases σ.liftPt_radius h SD hlin hq' hi' with h1' | h1'
  · rw [σ.liftPt_of_three_halves h SD hlin t h1, σ.liftPt_of_three_halves h SD hlin t h1'] at he
    have e := Prod.ext_iff.mp (σ.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e2 : q.2 ^ (σ.splitCharts SD hlin).e₀ = q'.2 ^ (σ.splitCharts SD hlin).e₀ := e.2
    refine Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e.1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · rw [σ.liftPt_of_three_halves h SD hlin t h1, σ.liftPt_of_three h SD hlin t h1'] at he
    exact absurd he (σ.cutMap_seamSide_ne_portSide h t _ _)
  · rw [σ.liftPt_of_three h SD hlin t h1, σ.liftPt_of_three_halves h SD hlin t h1'] at he
    exact absurd he.symm (σ.cutMap_seamSide_ne_portSide h t _ _)
  · rw [σ.liftPt_of_three h SD hlin t h1, σ.liftPt_of_three h SD hlin t h1'] at he
    have e := Prod.ext_iff.mp (σ.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e5 : q.2 = q'.2 := inv_injective e.1
    have e2 : σ.liftFib h SD hlin q = σ.liftFib h SD hlin q' := e.2
    unfold liftFib at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e7) e5

end Lift

end

end GC.Seifert.RelativeNormalization.MixedStage
