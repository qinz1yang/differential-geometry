import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelRegion

/-!
# Points of the lift in the cut carrier

Lane N2d, side model, step 4 (cut carrier). Boundary points of the cut carrier on one side are
determined by their image (`eq_of_cutMap_sideCollar_eq`), and boundary points of two different
sides with the same image lie on the two sides of one seam (`exists_seam_of_cutMap_sideCollar`).
For a split seam, the boundary torus of the solid torus `V` and the circle `l` of the host `H`
read the side collars (`solidVal_three_smul`, `hostVal_collar`), and the seam chart of the split
charts at height `0` is the boundary of `V` (`splitCharts_seam_zero`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem mem_target_of_mem_left {k : Fin T.pairing.count} {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.pairing.gluing.left k) : y ∈ (T.sideCollar (.inl k)).target := by
  rw [T.eq_leftCollar_of_mem hy]
  exact (T.sideCollar (.inl k)).map_source (T.zero_mem_sideCollar_source _ _)

theorem mem_target_of_mem_right {k : Fin T.pairing.count} {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.pairing.gluing.right k) : y ∈ (T.sideCollar (.inr (.inl k))).target := by
  rw [T.eq_rightCollar_of_mem hy]
  exact (T.sideCollar (.inr (.inl k))).map_source (T.zero_mem_sideCollar_source _ _)

theorem side_eq_of_mem_target {s s' : T.Side} {y : T.cutCarrier.Carrier}
    (h : y ∈ (T.sideCollar s).target) (h' : y ∈ (T.sideCollar s').target) : s = s' := by
  by_contra hne
  exact (T.sideCollar_disjoint hne).le_bot ⟨h, h'⟩

theorem sideCollar_zero_mem_target (s : T.Side) (τ : Torus) :
    T.sideCollar s (τ, halfZero) ∈ (T.sideCollar s).target :=
  (T.sideCollar s).map_source (T.zero_mem_sideCollar_source s τ)

theorem exists_seam_of_cutMap_sideCollar {s s' : T.Side} {τ τ' : Torus}
    (h : T.cutMap (T.sideCollar s (τ, halfZero)) = T.cutMap (T.sideCollar s' (τ', halfZero)))
    (hne : T.sideCollar s (τ, halfZero) ≠ T.sideCollar s' (τ', halfZero)) :
    ∃ k, (s = .inl k ∧ s' = .inr (.inl k)) ∨ (s = .inr (.inl k) ∧ s' = .inl k) := by
  rcases T.cutMap_eq_cases h with he | ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact absurd he hne
  · exact ⟨k, Or.inl ⟨T.side_eq_of_mem_target (T.sideCollar_zero_mem_target s τ)
      (T.mem_target_of_mem_left h1), T.side_eq_of_mem_target (T.sideCollar_zero_mem_target s' τ')
      (T.mem_target_of_mem_right h2)⟩⟩
  · exact ⟨k, Or.inr ⟨T.side_eq_of_mem_target (T.sideCollar_zero_mem_target s τ)
      (T.mem_target_of_mem_right h1), T.side_eq_of_mem_target (T.sideCollar_zero_mem_target s' τ')
      (T.mem_target_of_mem_left h2)⟩⟩

theorem eq_of_cutMap_sideCollar_eq {s : T.Side} {τ τ' : Torus}
    (h : T.cutMap (T.sideCollar s (τ, halfZero)) = T.cutMap (T.sideCollar s (τ', halfZero))) :
    τ = τ' := by
  by_cases he : T.sideCollar s (τ, halfZero) = T.sideCollar s (τ', halfZero)
  · have := (T.sideCollar s).injOn (T.zero_mem_sideCollar_source s τ)
      (T.zero_mem_sideCollar_source s τ') he
    exact congrArg Prod.fst this
  · obtain ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := T.exists_seam_of_cutMap_sideCollar h he
    · rw [h1] at h2; exact absurd h2 (by simp)
    · rw [h1] at h2; exact absurd h2 (by simp)

theorem not_isInteriorPoint_sideCollar (s : T.Side) (τ : Torus) :
    ¬ T.cutCarrier.model.IsInteriorPoint (T.sideCollar s (τ, halfZero)) :=
  (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp (T.sideCollar_zero_mem s τ).1

end TorusPresentation

namespace SplitTube

theorem continuousOn_blaschke_comp {X : Type*} [TopologicalSpace X] {α : X → ℝ} {β : X → Circle}
    {s : Set X} (hα : ContinuousOn α s) (hβ : ContinuousOn β s) (h : ∀ x ∈ s, |α x| < 1) :
    ContinuousOn (fun x => blaschke (α x) (β x)) s := by
  have hval : ContinuousOn (fun x => blaschkeVal (α x) ((β x : Circle) : ℂ)) s := by
    have hb : ContinuousOn (fun x => ((β x : Circle) : ℂ)) s :=
      continuous_subtype_val.comp_continuousOn hβ
    have ha : ContinuousOn (fun x => ((α x : ℝ) : ℂ)) s :=
      Complex.continuous_ofReal.comp_continuousOn hα
    exact (hb.add ha).div (continuousOn_const.add (ha.mul hb))
      (fun x hx => one_add_mul_ne_zero (h x hx) (β x))
  have hne : MapsTo (fun x => blaschkeVal (α x) ((β x : Circle) : ℂ)) s {z : ℂ | z ≠ 0} := by
    intro x hx h0
    have hn := norm_blaschkeVal (h x hx) (β x)
    rw [show blaschkeVal (α x) ((β x : Circle) : ℂ) = 0 from h0, norm_zero] at hn
    exact zero_ne_one hn
  exact contMDiffOn_unitOf.continuousOn.comp hval hne

namespace CollarData

variable {l : Fin 3} (D : CollarData l)

theorem continuousOn_famA : ContinuousOn D.famA (Icc 0 3) := by
  intro x hx
  by_cases h2 : x < 2
  · have heq : D.famA =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h2] with y hy
      simp [famA, sideBlend_of_le (le_of_lt hy)]
    exact (continuousAt_const.congr heq.symm).continuousWithinAt
  · push Not at h2
    exact (D.contDiffOn_famA.continuousOn.continuousAt
      (Ioo_mem_nhds (by linarith) (by linarith [hx.2]))).continuousWithinAt

theorem continuousOn_point : ContinuousOn D.point (univ ×ˢ Icc 0 3) := by
  have hs : ContinuousOn (fun q : Circle × ℝ => q.2) (univ ×ˢ Icc 0 3) :=
    continuous_snd.continuousOn
  have hmaps : MapsTo (fun q : Circle × ℝ => q.2) (univ ×ˢ Icc 0 3) (Icc 0 3) := fun q hq => hq.2
  have hc := D.continuousOn_famC.comp hs hmaps
  have hr := D.continuousOn_famR.comp hs hmaps
  have ha := D.continuousOn_famA.comp hs hmaps
  have hm : ContinuousOn (fun q : Circle × ℝ => D.famMu q.2) (univ ×ˢ Icc 0 3) :=
    (D.contMDiff_famMu.continuous.comp continuous_snd).continuousOn
  have hb := continuousOn_blaschke_comp ha continuous_fst.continuousOn
    (fun q hq => D.famA_lt' hq.2)
  have hmb : ContinuousOn (fun q : Circle × ℝ => ((D.famMu q.2 * blaschke (D.famA q.2) q.1 :
      Circle) : ℂ)) (univ ×ˢ Icc 0 3) :=
    continuous_subtype_val.comp_continuousOn (hm.mul hb)
  exact hc.add ((Complex.continuous_ofReal.comp_continuousOn hr).mul hmb)

end CollarData

end SplitTube

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

def solidPt (z : ℂ) (w : Circle) : E.toTorus.cutCarrier.Carrier :=
  ((E.splitData h).ΘV (clampDisc z, w) : E.toTorus.cutCarrier.Carrier)

def hostPt (z : ℂ) (ν : Circle) : E.toTorus.cutCarrier.Carrier :=
  ((E.splitData h).ΘH (clampPants z, ν) : E.toTorus.cutCarrier.Carrier)

theorem solidMap_eq_cutMap (q : ℂ × Circle) :
    E.solidMap h q = E.toTorus.cutMap (E.solidPt h q.1 q.2) := rfl

theorem hostMap_eq_cutMap (q : ℂ × Circle) :
    E.hostMap h q = E.toTorus.cutMap (E.hostPt h q.1 q.2) := rfl

theorem solidPt_mem (z : ℂ) (w : Circle) :
    E.solidPt h z w ∈ E.toTorus.components.piece (E.seamPiece j b) :=
  ((E.splitData h).ΘV (clampDisc z, w)).property

theorem hostPt_mem (z : ℂ) (ν : Circle) :
    E.hostPt h z ν ∈ E.toTorus.components.piece (E.hostPiece j b) :=
  ((E.splitData h).ΘH (clampPants z, ν)).property

theorem solidPt_isInteriorPoint {z : ℂ} (hz : ‖z‖ < 3) (w : Circle) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.solidPt h z w) :=
  (E.toTorus.pieceChart_isInteriorPoint _ _ (E.splitData h).ΘV clampDisc (q := (z, w))
    (isLocalDiffeomorphAt_clampDisc hz)).1

theorem hostPt_isInteriorPoint {z : ℂ} (hz : z ∈ SplitTube.pantsInterior) (ν : Circle) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.hostPt h z ν) :=
  (E.toTorus.pieceChart_isInteriorPoint _ _ (E.splitData h).ΘH clampPants (q := (z, ν))
    (isLocalDiffeomorphAt_clampPants hz)).1

theorem solidPt_three_smul (θ w : Circle) :
    E.solidPt h ((3 : ℝ) • (θ : ℂ)) w =
      E.toTorus.sideCollar (E.seamSide j b) ((θ, w), halfZero) := by
  have hp : ((θ, w), halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource _
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.seamPiece j b)
    ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ hp
  have e2 := (E.splitData h).hV 0 ((θ, w), halfZero) hp (by
    change (0 : ℝ) < (E.splitData h).δ
    exact (E.splitData h).hδ)
  rw [E.standardPort_seamPiece h] at e2
  rw [← e1, e2]
  change ((E.splitData h).ΘV (clampDisc ((3 : ℝ) • (θ : ℂ)), w) : E.toTorus.cutCarrier.Carrier) =
    ((E.splitData h).ΘV ((discPlanarBase.{u} 1).collar 0 (θ, halfPoint 0 le_rfl), w) :
      E.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq le_rfl zero_lt_one]
  norm_num

theorem hostPt_collar (l : Fin 3) (θ ν : Circle) :
    E.hostPt h (planarCollarFormula 3 l ((θ : ℂ), 0)) ν =
      E.toTorus.sideCollar (E.standardPort (E.hostPiece j b) h.2.1 l).val ((θ, ν), halfZero) := by
  have hp : ((θ, ν), halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource _
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    (E.standardPort (E.hostPiece j b) h.2.1 l) hp
  have e2 := (E.splitData h).hH l ((θ, ν), halfZero) hp (by
    change (0 : ℝ) < (E.splitData h).δ
    exact (E.splitData h).hδ)
  rw [← e1, e2]
  change ((E.splitData h).ΘH (clampPants (planarCollarFormula 3 l ((θ : ℂ), 0)), ν) :
      E.toTorus.cutCarrier.Carrier) =
    ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar l (θ, halfPoint 0 le_rfl), ν) :
      E.toTorus.cutCarrier.Carrier)
  rw [pantsCollar_eq l le_rfl zero_lt_one]

theorem splitCharts_seam_zero (hlin : E.IsLinearSeam j) (τ : Torus) :
    (E.splitCharts h hlin).seam (τ, 0) =
      (E.splitCharts h hlin).solid ((3 : ℝ) • (τ.1 : ℂ), τ.2) := by
  change E.seamMap j b (τ, 0) = E.solidMap h ((3 : ℝ) • (τ.1 : ℂ), τ.2)
  rw [E.seamMap_zero, E.solidMap_eq_cutMap, E.solidPt_three_smul]

section Lift

open SplitTube

variable (hlin : E.IsLinearSeam j)

def sideDom (t : Bool) (q : ℂ × Circle) : Prop :=
  ‖q.1‖ ≤ 3 ∧ -3 < sgnR t * stripLevel (E.hostSide h)
    ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖))

def liftFib (q : ℂ × Circle) : Circle :=
  q.2 ^ ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d) *
    unitOf q.1 ^ (E.splitCharts h hlin).e₁

def liftPt (t : Bool) (q : ℂ × Circle) : E.toTorus.cutCarrier.Carrier :=
  if ‖q.1‖ ≤ 3 / 2 then E.solidPt h ((2 : ℝ) • q.1) (q.2 ^ (E.splitCharts h hlin).e₀)
  else E.hostPt h (hostChart (E.hostSide h) ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖)))
    (E.liftFib h hlin q)

theorem liftMap_eq_cutMap (t : Bool) (q : ℂ × Circle) :
    (E.splitCharts h hlin).liftMap t q = E.toTorus.cutMap (E.liftPt h hlin t q) := by
  unfold SplitCharts.liftMap liftPt
  split_ifs
  · rfl
  · rfl

theorem point_ne_zero {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q) :
    (E.hostSide h).val ≠ 0 → (sideData (E.hostSide h) t).point (q.2, ‖q.1‖) ≠ 0 := fun hl =>
  ne_zero_of_level _ t hl hq.2 (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1

theorem hostChart_point_mem_planarModel {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (h32 : 3 / 2 ≤ ‖q.1‖) :
    hostChart (E.hostSide h) ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖)) ∈
      planarModel 3 :=
  hostChart_mem_planarModel _ t (E.point_ne_zero h hq)
    (norm_point_le _ t (q := (q.2, ‖q.1‖)) h32 hq.1).1
    (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1 hq.2

theorem hostChart_point_mem_pantsInterior {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    hostChart (E.hostSide h) ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖)) ∈
      pantsInterior :=
  hostChart_mem_pantsInterior _ t (E.point_ne_zero h hq)
    ((norm_point_le _ t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32)
    ((le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).2 h3) hq.2

theorem isOpen_sideDom_interior (t : Bool) :
    IsOpen {q : ℂ × Circle | ‖q.1‖ < 3 ∧ -3 < sgnR t * stripLevel (E.hostSide h)
      ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖))} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * stripLevel (E.hostSide h)
      ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖))) {q | ‖q.1‖ < 3} := by
    refine continuousOn_const.mul ((contDiff_stripLevel _).continuous.comp_continuousOn ?_)
    refine (sideData (E.hostSide h) t).continuousOn_point.comp
      (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, le_of_lt hq⟩
  have := hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt (continuous_const (y := (-3 : ℝ))) continuous_id)
  exact this

def portSide' (t : Bool) : E.toTorus.Side :=
  (E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.hostSide h) t)).val

theorem sidePiece_portSide (t : Bool) :
    E.toTorus.sidePiece (E.portSide' h t) = E.hostPiece j b :=
  (E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.hostSide h) t)).property

theorem portSide_ne_seamSide_not (t : Bool) : E.portSide' h t ≠ E.seamSide j (!b) := by
  intro he
  have h1 : E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.hostSide h) t) =
      E.standardPort (E.hostPiece j b) h.2.1 (E.hostSide h) := by
    rw [E.standardPort_hostSide h]
    exact Subtype.ext he
  exact sidePort_ne (E.hostSide h) t ((E.standardPort (E.hostPiece j b) h.2.1).injective h1)

theorem portSide_injective : Injective (E.portSide' h) := by
  intro t t' he
  have h1 := (E.standardPort (E.hostPiece j b) h.2.1).injective (Subtype.ext he)
  by_contra hne
  rcases Bool.eq_false_or_eq_true t with rfl | rfl <;>
    rcases Bool.eq_false_or_eq_true t' with rfl | rfl
  · exact hne rfl
  · exact sidePort_false_ne_true _ h1.symm
  · exact sidePort_false_ne_true _ h1
  · exact hne rfl

theorem cutMap_seamSide_ne_portSide (t : Bool) (τ τ' : Torus) :
    E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (τ, halfZero)) ≠
      E.toTorus.cutMap (E.toTorus.sideCollar (E.portSide' h t) (τ', halfZero)) := by
  intro he
  have hne : E.toTorus.sideCollar (E.seamSide j b) (τ, halfZero) ≠
      E.toTorus.sideCollar (E.portSide' h t) (τ', halfZero) := by
    intro he'
    have h1 := (E.toTorus.sideCollar_zero_mem (E.seamSide j b) τ).2
    have h2 := (E.toTorus.sideCollar_zero_mem (E.portSide' h t) τ').2
    rw [he'] at h1
    rw [E.sidePiece_portSide h] at h2
    rw [E.sidePiece_seamSide] at h1
    exact E.seamPiece_ne_hostPiece h (E.toTorus.eq_of_mem_piece' h1 h2)
  obtain ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := E.toTorus.exists_seam_of_cutMap_sideCollar he hne
  · cases b
    · exact absurd h1 (by simp [seamSide])
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact E.portSide_ne_seamSide_not h t (by rw [h2]; rfl)
  · cases b
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact E.portSide_ne_seamSide_not h t (by rw [h2]; rfl)
    · exact absurd h1 (by simp [seamSide])

theorem liftPt_of_three_halves (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ = 3 / 2) :
    E.liftPt h hlin t q = E.toTorus.sideCollar (E.seamSide j b)
      ((unitOf q.1, q.2 ^ (E.splitCharts h hlin).e₀), halfZero) := by
  unfold liftPt
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le), ← E.solidPt_three_smul h]
  congr 1
  rw [← norm_smul_unitOf q.1, h32, smul_smul, unitOf_smul (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num

theorem liftPt_of_three (t : Bool) {q : ℂ × Circle} (h3 : ‖q.1‖ = 3) :
    E.liftPt h hlin t q = E.toTorus.sideCollar (E.portSide' h t)
      ((q.2⁻¹, E.liftFib h hlin q), halfZero) := by
  unfold liftPt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h3]; norm_num)), h3,
    sideData_point_collar _ t (by norm_num) (by norm_num), hostChart_hostInv]
  rw [show collarDepth 3 = 0 by simp [collarDepth]]
  exact E.hostPt_collar h _ _ _

theorem liftPt_isInteriorPoint_of_lt (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ < 3 / 2) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q) := by
  unfold liftPt
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le)]
  refine E.solidPt_isInteriorPoint h ?_ _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem liftPt_isInteriorPoint_of_mid (t : Bool) {q : ℂ × Circle} (hq : E.sideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q) := by
  unfold liftPt
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h32))]
  exact E.hostPt_isInteriorPoint h (E.hostChart_point_mem_pantsInterior h hq h32 h3) _

end Lift

end ElementaryPresentation

end GC.Seifert
