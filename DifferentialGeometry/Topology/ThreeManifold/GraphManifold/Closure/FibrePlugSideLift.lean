import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideBall

/-!
The complete native bounded side lift, retaining the true solid boundary seam and external collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool}

def boundedPlugSideHost (h : E.IsSplitSeam j b) : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm
    ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem boundedPlugSidePortSolid (l : Fin 1) :
    E.standardPort (E.seamPiece j b) h.1 l = ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
  have hs : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
  exact Subsingleton.elim _ _

theorem boundedPlugSidePortHost :
    E.standardPort (E.hostPiece j b) h.2.1 (E.boundedPlugSideHost h) =
      ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩ :=
  Equiv.apply_symm_apply _ _

def boundedPlugSideSolidPoint (z : ℂ) (w : Circle) : E.toTorus.cutCarrier.Carrier :=
  ((E.splitData h).ΘV (clampDisc z, w) : E.toTorus.cutCarrier.Carrier)

abbrev boundedPlugSideHostPoint (z : ℂ) (ν : Circle) : E.toTorus.cutCarrier.Carrier :=
  E.boundedModelHostPoint h z ν

def boundedPlugSideSolidMap (q : ℂ × Circle) : W.Carrier :=
  E.toTorus.cutMap (E.boundedPlugSideSolidPoint h q.1 q.2)

def boundedPlugSideHostMap (q : ℂ × Circle) : W.Carrier :=
  E.toTorus.cutMap (E.boundedPlugSideHostPoint h q.1 q.2)

theorem boundedPlugSideSolidMap_eq_cutMap (q : ℂ × Circle) :
    E.boundedPlugSideSolidMap h q = E.toTorus.cutMap (E.boundedPlugSideSolidPoint h q.1 q.2) := rfl

theorem boundedPlugSideHostMap_eq_cutMap (q : ℂ × Circle) :
    E.boundedPlugSideHostMap h q = E.toTorus.cutMap (E.boundedPlugSideHostPoint h q.1 q.2) := rfl

theorem boundedPlugSideSolidPoint_mem (z : ℂ) (w : Circle) :
    E.boundedPlugSideSolidPoint h z w ∈ E.toTorus.components.piece (E.seamPiece j b) :=
  ((E.splitData h).ΘV (clampDisc z, w)).property

theorem boundedPlugSideHostPoint_mem (z : ℂ) (ν : Circle) :
    E.boundedPlugSideHostPoint h z ν ∈ E.toTorus.components.piece (E.hostPiece j b) :=
  ((E.splitData h).ΘH (clampPants z, ν)).property

theorem boundedPlugSideSolidPoint_interior {z : ℂ} (hz : ‖z‖ < 3) (w : Circle) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideSolidPoint h z w) :=
  (E.toTorus.pieceChart_isInteriorPoint _ _ (E.splitData h).ΘV clampDisc (q := (z, w))
    (isLocalDiffeomorphAt_clampDisc hz)).1

theorem boundedPlugSideHostPoint_interior {z : ℂ} (hz : z ∈ SplitTube.pantsInterior) (ν : Circle) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideHostPoint h z ν) :=
  (E.toTorus.pieceChart_isInteriorPoint _ _ (E.splitData h).ΘH clampPants (q := (z, ν))
    (isLocalDiffeomorphAt_clampPants hz)).1

theorem boundedPlugSideSolidPoint_boundary (θ w : Circle) :
    E.boundedPlugSideSolidPoint h ((3 : ℝ) • (θ : ℂ)) w =
      E.toTorus.sideCollar (E.seamSide j b) ((θ, w), halfZero) := by
  have hp : ((θ, w), halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource _
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.seamPiece j b)
    ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ hp
  have e2 := (E.splitData h).hV 0 ((θ, w), halfZero) hp (by
    change (0 : ℝ) < (E.splitData h).δ
    exact (E.splitData h).hδ)
  rw [E.boundedPlugSidePortSolid h] at e2
  rw [← e1, e2]
  change ((E.splitData h).ΘV (clampDisc ((3 : ℝ) • (θ : ℂ)), w) : E.toTorus.cutCarrier.Carrier) =
    ((E.splitData h).ΘV ((discPlanarBase.{u} 1).collar 0 (θ, halfPoint 0 le_rfl), w) :
      E.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq le_rfl zero_lt_one]
  norm_num

theorem boundedPlugSideHostPoint_collar (l : Fin 3) (θ ν : Circle) :
    E.boundedPlugSideHostPoint h (planarCollarFormula 3 l ((θ : ℂ), 0)) ν =
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

section Lift

open SplitTube

variable (hlin : E.IsLinearSeam j)

def boundedPlugSideLevel (t : Bool) (q : ℂ × Circle) : ℝ :=
  stripLevel (E.boundedPlugSideHost h)
    ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖))

def boundedPlugSideDom (t : Bool) (q : ℂ × Circle) : Prop :=
  ‖q.1‖ ≤ 3 ∧ -3 < sgnR t * E.boundedPlugSideLevel h t q

def boundedPlugSideFibre (q : ℂ × Circle) : Circle :=
  q.2 ^ ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d) *
    unitOf q.1 ^ (E.boundedSplitCharts h hlin).e₁

def boundedPlugSideLiftPoint (t : Bool) (q : ℂ × Circle) : E.toTorus.cutCarrier.Carrier :=
  if ‖q.1‖ ≤ 3 / 2 then E.boundedPlugSideSolidPoint h ((2 : ℝ) • q.1) (q.2 ^
    (E.boundedSplitCharts h hlin).e₀)
  else E.boundedPlugSideHostPoint h (hostChart (E.boundedPlugSideHost h) ((sideData
    (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖)))
    (E.boundedPlugSideFibre h hlin q)

def boundedPlugSideLiftMap (t : Bool) (q : ℂ × Circle) : W.Carrier :=
  E.toTorus.cutMap (E.boundedPlugSideLiftPoint h hlin t q)

theorem boundedPlugSideLiftMap_eq_cutMap (t : Bool) (q : ℂ × Circle) :
    E.boundedPlugSideLiftMap h hlin t q =
      E.toTorus.cutMap (E.boundedPlugSideLiftPoint h hlin t q) := rfl

theorem boundedPlugSide_point_ne_zero {t : Bool} {q : ℂ × Circle} (hq : E.boundedPlugSideDom h
    t q) :
    (E.boundedPlugSideHost h).val ≠ 0 → (sideData (E.boundedPlugSideHost h) t).point (q.2,
      ‖q.1‖) ≠ 0 := fun hl =>
  ne_zero_of_level _ t hl hq.2 (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1

theorem boundedPlugSide_hostPoint_planar {t : Bool} {q : ℂ × Circle} (hq : E.boundedPlugSideDom
    h t q)
    (h32 : 3 / 2 ≤ ‖q.1‖) :
    hostChart (E.boundedPlugSideHost h) ((sideData (E.boundedPlugSideHost h) t).point (q.2,
      ‖q.1‖)) ∈
      planarModel 3 :=
  hostChart_mem_planarModel _ t (E.boundedPlugSide_point_ne_zero h hq)
    (norm_point_le _ t (q := (q.2, ‖q.1‖)) h32 hq.1).1
    (le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).1 hq.2

theorem boundedPlugSide_hostPoint_interior {t : Bool} {q : ℂ × Circle} (hq :
    E.boundedPlugSideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    hostChart (E.boundedPlugSideHost h) ((sideData (E.boundedPlugSideHost h) t).point (q.2,
      ‖q.1‖)) ∈
      pantsInterior :=
  hostChart_mem_pantsInterior _ t (E.boundedPlugSide_point_ne_zero h hq)
    ((norm_point_le _ t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32)
    ((le_norm_point_sub _ t (q := (q.2, ‖q.1‖)) (norm_nonneg _) hq.1).2 h3) hq.2

theorem boundedPlugSide_isOpen_domain (t : Bool) :
    IsOpen {q : ℂ × Circle | ‖q.1‖ < 3 ∧ -3 < sgnR t * stripLevel (E.boundedPlugSideHost h)
      ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖))} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * stripLevel (E.boundedPlugSideHost h)
      ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖))) {q | ‖q.1‖ < 3} := by
    refine continuousOn_const.mul ((contDiff_stripLevel _).continuous.comp_continuousOn ?_)
    refine (sideData (E.boundedPlugSideHost h) t).continuousOn_point.comp
      (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, le_of_lt hq⟩
  have := hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt (continuous_const (y := (-3 : ℝ))) continuous_id)
  exact this

def boundedPlugSidePort (t : Bool) : E.toTorus.Side :=
  (E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.boundedPlugSideHost h) t)).val

theorem boundedPlugSidePort_owner (t : Bool) :
    E.toTorus.sidePiece (E.boundedPlugSidePort h t) = E.hostPiece j b :=
  (E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.boundedPlugSideHost h) t)).property

theorem boundedPlugSidePort_ne_host (t : Bool) : E.boundedPlugSidePort h t ≠ E.seamSide j (!b) := by
  intro he
  have h1 : E.standardPort (E.hostPiece j b) h.2.1 (sidePort (E.boundedPlugSideHost h) t) =
      E.standardPort (E.hostPiece j b) h.2.1 (E.boundedPlugSideHost h) := by
    rw [E.boundedPlugSidePortHost h]
    exact Subtype.ext he
  exact sidePort_ne (E.boundedPlugSideHost h) t ((E.standardPort (E.hostPiece j b)
    h.2.1).injective h1)

theorem boundedPlugSidePort_injective : Injective (E.boundedPlugSidePort h) := by
  intro t t' he
  have h1 := (E.standardPort (E.hostPiece j b) h.2.1).injective (Subtype.ext he)
  by_contra hne
  rcases Bool.eq_false_or_eq_true t with rfl | rfl <;>
    rcases Bool.eq_false_or_eq_true t' with rfl | rfl
  · exact hne rfl
  · exact sidePort_false_ne_true _ h1.symm
  · exact sidePort_false_ne_true _ h1
  · exact hne rfl

theorem boundedPlugSide_seam_ne_port (t : Bool) (τ τ' : Torus) :
    E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (τ, halfZero)) ≠
      E.toTorus.cutMap (E.toTorus.sideCollar (E.boundedPlugSidePort h t) (τ', halfZero)) := by
  intro he
  have hne : E.toTorus.sideCollar (E.seamSide j b) (τ, halfZero) ≠
      E.toTorus.sideCollar (E.boundedPlugSidePort h t) (τ', halfZero) := by
    intro he'
    have h1 := (E.toTorus.sideCollar_zero_mem (E.seamSide j b) τ).2
    have h2 := (E.toTorus.sideCollar_zero_mem (E.boundedPlugSidePort h t) τ').2
    rw [he'] at h1
    rw [E.boundedPlugSidePort_owner h] at h2
    rw [E.sidePiece_seamSide] at h1
    exact E.seamPiece_ne_hostPiece h (E.toTorus.eq_of_mem_piece' h1 h2)
  obtain ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := E.toTorus.exists_seam_of_cutMap_sideCollar he hne
  · cases b
    · exact absurd h1 (by simp [seamSide])
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact E.boundedPlugSidePort_ne_host h t (by rw [h2]; rfl)
  · cases b
    · have hk : j = k := by simpa [seamSide] using h1
      subst hk
      exact E.boundedPlugSidePort_ne_host h t (by rw [h2]; rfl)
    · exact absurd h1 (by simp [seamSide])

theorem boundedPlugSideLiftPoint_half (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ = 3 / 2) :
    E.boundedPlugSideLiftPoint h hlin t q = E.toTorus.sideCollar (E.seamSide j b)
      ((unitOf q.1, q.2 ^ (E.boundedSplitCharts h hlin).e₀), halfZero) := by
  unfold boundedPlugSideLiftPoint
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le), ← E.boundedPlugSideSolidPoint_boundary h]
  congr 1
  rw [← norm_smul_unitOf q.1, h32, smul_smul, unitOf_smul (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num

theorem boundedPlugSideLiftPoint_three (t : Bool) {q : ℂ × Circle} (h3 : ‖q.1‖ = 3) :
    E.boundedPlugSideLiftPoint h hlin t q = E.toTorus.sideCollar (E.boundedPlugSidePort h t)
      ((q.2⁻¹, E.boundedPlugSideFibre h hlin q), halfZero) := by
  unfold boundedPlugSideLiftPoint
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h3]; norm_num)), h3,
    sideData_point_collar _ t (by norm_num) (by norm_num), hostChart_hostInv]
  rw [show collarDepth 3 = 0 by simp [collarDepth]]
  exact E.boundedPlugSideHostPoint_collar h _ _ _

theorem boundedPlugSideLiftPoint_interior_solid (t : Bool) {q : ℂ × Circle} (h32 : ‖q.1‖ < 3 / 2) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideLiftPoint h hlin t q) := by
  unfold boundedPlugSideLiftPoint
  rw [ite_eq_left_of_eq_true _ _ (eq_true h32.le)]
  refine E.boundedPlugSideSolidPoint_interior h ?_ _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem boundedPlugSideLiftPoint_interior_host (t : Bool) {q : ℂ × Circle} (hq :
    E.boundedPlugSideDom h t q)
    (h32 : 3 / 2 < ‖q.1‖) (h3 : ‖q.1‖ < 3) :
    E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideLiftPoint h hlin t q) := by
  unfold boundedPlugSideLiftPoint
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h32))]
  exact E.boundedPlugSideHostPoint_interior h (E.boundedPlugSide_hostPoint_interior h hq h32 h3) _

end Lift

theorem boundedPlugSideSolidPoint_injective {z z' : ℂ} {w w' : Circle} (hz : ‖z‖ ≤ 3) (hz' :
    ‖z'‖ ≤ 3)
    (he : E.boundedPlugSideSolidPoint h z w = E.boundedPlugSideSolidPoint h z' w') : z = z' ∧ w
      = w' := by
  have h1 := Prod.ext_iff.mp ((E.splitData h).ΘV.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : (discPlanarBase.{u} 1).surface.Carrier =>
    ((show discSet.{u} from x).val).down) h1.1
  dsimp only at h2
  rw [clampDisc_val hz, clampDisc_val hz'] at h2
  exact h2

theorem boundedPlugSideHostPoint_injective {z z' : ℂ} {ν ν' : Circle} (hz : z ∈ planarModel 3)
    (hz' : z' ∈ planarModel 3)
    (he : E.boundedPlugSideHostPoint h z ν = E.boundedPlugSideHostPoint h z' ν') : z = z' ∧ ν =
      ν' := by
  have h1 := Prod.ext_iff.mp ((E.splitData h).ΘH.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : pantsPlanarBase.{u}.surface.Carrier =>
    ((show planarSet.{u} 3 from x).val).down) h1.1
  dsimp only at h2
  rw [clampPants_val hz, clampPants_val hz'] at h2
  exact h2

theorem boundedPlugSideSolidPoint_ne_host (z z' : ℂ) (w ν : Circle) :
    E.boundedPlugSideSolidPoint h z w ≠ E.boundedPlugSideHostPoint h z' ν := by
  intro he
  have h1 := E.boundedPlugSideSolidPoint_mem h z w
  rw [he] at h1
  exact E.seamPiece_ne_hostPiece h (E.toTorus.eq_of_mem_piece' h1
    (E.boundedPlugSideHostPoint_mem h z' ν))

section Injectivity

variable (hlin : E.IsLinearSeam j)

theorem boundedPlugSideLiftPoint_injective {t : Bool} {q q' : ℂ × Circle} (hq :
    E.boundedPlugSideDom h t q) (hq' : E.boundedPlugSideDom h t q')
    (he : E.boundedPlugSideLiftPoint h hlin t q = E.boundedPlugSideLiftPoint h hlin t q') : q =
      q' := by
  have he₀ := (E.boundedSplitCharts h hlin).he₀
  have he₁ := (E.boundedSplitCharts h hlin).he₁
  unfold boundedPlugSideLiftPoint at he
  by_cases h1 : ‖q.1‖ ≤ 3 / 2 <;> by_cases h1' : ‖q'.1‖ ≤ 3 / 2
  · simp only [h1, h1', ↓reduceIte] at he
    have hn : ∀ z : ℂ, ‖z‖ ≤ 3 / 2 → ‖(2 : ℝ) • z‖ ≤ 3 := fun z hz => by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    obtain ⟨e1, e2⟩ := E.boundedPlugSideSolidPoint_injective h (hn _ h1) (hn _ h1') he
    refine Prod.ext (smul_right_injective ℂ (by norm_num : (2 : ℝ) ≠ 0) e1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he (E.boundedPlugSideSolidPoint_ne_host h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he.symm (E.boundedPlugSideSolidPoint_ne_host h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    push Not at h1 h1'
    obtain ⟨e1, e2⟩ := E.boundedPlugSideHostPoint_injective h
      (E.boundedPlugSide_hostPoint_planar h hq h1.le)
      (E.boundedPlugSide_hostPoint_planar h hq' h1'.le) he
    have e3 := congrArg (hostInv (E.boundedPlugSideHost h)) e1
    rw [hostInv_hostChart, hostInv_hostChart] at e3
    have e4 := (sideData (E.boundedPlugSideHost h) t).point_injOn ⟨mem_univ _, norm_nonneg _, hq.1⟩
      ⟨mem_univ _, norm_nonneg _, hq'.1⟩ e3
    have e5 : q.2 = q'.2 := congrArg Prod.fst e4
    have e6 : ‖q.1‖ = ‖q'.1‖ := congrArg Prod.snd e4
    unfold boundedPlugSideFibre at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq e6 e7) e5

theorem boundedPlugSideLiftPoint_radius {t : Bool} {q : ℂ × Circle} (hq : E.boundedPlugSideDom
    h t q)
    (hi : ¬ E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideLiftPoint h hlin t q)) :
    ‖q.1‖ = 3 / 2 ∨ ‖q.1‖ = 3 := by
  by_contra hc
  push Not at hc
  rcases lt_or_gt_of_ne hc.1 with h32 | h32
  · exact hi (E.boundedPlugSideLiftPoint_interior_solid h hlin t h32)
  · exact hi (E.boundedPlugSideLiftPoint_interior_host h hlin t hq h32 (lt_of_le_of_ne hq.1 hc.2))

theorem boundedPlugSideLiftMap_injOn (t : Bool) :
    InjOn (E.boundedPlugSideLiftMap h hlin t) {q | E.boundedPlugSideDom h t q} := by
  have he₀ := (E.boundedSplitCharts h hlin).he₀
  have he₁ := (E.boundedSplitCharts h hlin).he₁
  intro q hq q' hq' he
  rw [E.boundedPlugSideLiftMap_eq_cutMap, E.boundedPlugSideLiftMap_eq_cutMap] at he
  by_cases hi : E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideLiftPoint h hlin t q)
  · exact E.boundedPlugSideLiftPoint_injective h hlin hq hq'
      (E.toTorus.cutMap_eq_of_isInteriorPoint hi he)
  by_cases hi' : E.toTorus.cutCarrier.model.IsInteriorPoint (E.boundedPlugSideLiftPoint h hlin t q')
  · exact (E.boundedPlugSideLiftPoint_injective h hlin hq' hq
      (E.toTorus.cutMap_eq_of_isInteriorPoint hi' he.symm)).symm
  rcases E.boundedPlugSideLiftPoint_radius h hlin hq hi with h1 | h1 <;>
    rcases E.boundedPlugSideLiftPoint_radius h hlin hq' hi' with h1' | h1'
  · rw [E.boundedPlugSideLiftPoint_half h hlin t h1, E.boundedPlugSideLiftPoint_half h hlin t
    h1'] at he
    have e := Prod.ext_iff.mp (E.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e2 : q.2 ^ (E.boundedSplitCharts h hlin).e₀ = q'.2 ^ (E.boundedSplitCharts h hlin).e₀
      := e.2
    refine Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e.1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · rw [E.boundedPlugSideLiftPoint_half h hlin t h1, E.boundedPlugSideLiftPoint_three h hlin t
    h1'] at he
    exact absurd he (E.boundedPlugSide_seam_ne_port h t _ _)
  · rw [E.boundedPlugSideLiftPoint_three h hlin t h1, E.boundedPlugSideLiftPoint_half h hlin t
    h1'] at he
    exact absurd he.symm (E.boundedPlugSide_seam_ne_port h t _ _)
  · rw [E.boundedPlugSideLiftPoint_three h hlin t h1, E.boundedPlugSideLiftPoint_three h hlin t
    h1'] at he
    have e := Prod.ext_iff.mp (E.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e5 : q.2 = q'.2 := inv_injective e.1
    have e2 : E.boundedPlugSideFibre h hlin q = E.boundedPlugSideFibre h hlin q' := e.2
    unfold boundedPlugSideFibre at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e7) e5

end Injectivity

section Smooth

variable (hlin : E.IsLinearSeam j)

def boundedPlugSideCharts : SplitCharts (boundedSplitInterior W) := by
  let C := E.boundedSplitCharts h hlin
  let f : ℂ × Circle → boundedSplitInterior W := fun q =>
    if ‖q.1‖ = 3 then C.seam ((unitOf q.1, q.2), 0) else C.solid q
  have hf : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → f q = C.solid q := by
    intro q hq
    exact ite_eq_right (ne_of_lt hq)
  refine { C with
    solid := f
    solid_local := ?_
    solid_inj := ?_
    solid_ne_host := ?_
    seam_ne_solid := ?_
    seam_neg := ?_ }
  · intro q hq
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := C.solid_local q hq)
    filter_upwards [(isOpen_lt (continuous_norm.comp continuous_fst)
      continuous_const).mem_nhds hq] with p hp
    exact hf p hp
  · intro q q' hq hq' he
    exact C.solid_inj q q' hq hq' ((hf q hq).symm.trans (he.trans (hf q' hq')))
  · intro q q' hq hq' he
    exact C.solid_ne_host q q' hq hq' ((hf q hq).symm.trans he)
  · intro t q hq he
    exact C.seam_ne_solid t q hq (he.trans (hf q hq))
  · intro t r hr hr0
    have hn : ‖(3 + 3 * r / 2 : ℝ) • (t.1 : ℂ)‖ < 3 := by
      rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one,
        abs_of_pos (by linarith [C.hδ1])]
      linarith
    exact (C.seam_neg t r hr hr0).trans (hf _ hn).symm

theorem boundedPlugSideCharts_seam_zero (t : Torus) :
    (E.boundedPlugSideCharts h hlin).seam (t, 0) =
      (E.boundedPlugSideCharts h hlin).solid ((3 : ℝ) • (t.1 : ℂ), t.2) := by
  change (E.boundedSplitCharts h hlin).seam (t, 0) =
    if ‖(3 : ℝ) • (t.1 : ℂ)‖ = 3 then
      (E.boundedSplitCharts h hlin).seam ((unitOf ((3 : ℝ) • (t.1 : ℂ)), t.2), 0)
    else _
  rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one, abs_of_pos (by norm_num),
    ite_eq_left rfl, unitOf_smul (by norm_num : (0 : ℝ) < 3)]

theorem boundedPlugSideCharts_tubeMap (q : SphereTwo × ℝ) :
    (E.boundedPlugSideCharts h hlin).tubeMap q = (E.boundedSplitCharts h hlin).tubeMap q := by
  unfold SplitCharts.tubeMap
  split_ifs with hn hp
  · have hnorm : ‖(capModel (E.boundedSplitCharts h hlin).e₀ (SplitCharts.side q) q).1‖ < 3 := by
      simp only [capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have hh := (seamHeight_neg_iff q.1).mp hn
      linarith
    change (if ‖(capModel (E.boundedSplitCharts h hlin).e₀ (SplitCharts.side q) q).1‖ = 3
      then _ else _) = _
    rw [ite_eq_right (ne_of_lt hnorm)]
    rfl
  · rfl
  · rfl

theorem boundedPlugSideCharts_tubeMap_val (q : SphereTwo × ℝ) :
    boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).tubeMap q) =
      E.boundedSplitTubeMap h hlin q := by
  rw [E.boundedPlugSideCharts_tubeMap h hlin q]
  rfl

theorem boundedPlugSideCharts_seam_val (q : Torus × ℝ) (hq : |q.2| < 1) :
    boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).seam q) =
      E.toTorus.seam j (E.seamCoord j b q) :=
  E.boundedSplitCharts_seam_val h hlin q hq

theorem boundedPlugSideCharts_solid_val (q : ℂ × Circle) (hq : ‖q.1‖ ≤ 3) :
    boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).solid q) =
      E.boundedPlugSideSolidMap h q := by
  change boundedSplitInteriorVal W
    (if ‖q.1‖ = 3 then (E.boundedSplitCharts h hlin).seam ((unitOf q.1, q.2), 0)
    else (E.boundedSplitCharts h hlin).solid q) = _
  by_cases he : ‖q.1‖ = 3
  · rw [ite_eq_left he, E.boundedSplitCharts_seam_val h hlin _ (by simp)]
    have hs : E.toTorus.seam j (E.seamCoord j b ((unitOf q.1, q.2), 0)) =
        E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b)
          ((unitOf q.1, q.2), halfZero)) := by
      rw [E.seamCoord_apply, neg_zero]
      exact (E.cutMap_sideCollar_eq_seam j b (unitOf q.1, q.2) 0 le_rfl zero_lt_one).symm
    have hp : E.boundedPlugSideSolidPoint h q.1 q.2 =
        E.toTorus.sideCollar (E.seamSide j b) ((unitOf q.1, q.2), halfZero) := by
      have hz : q.1 = (3 : ℝ) • (unitOf q.1 : ℂ) := by
        rw [← he]
        exact (norm_smul_unitOf q.1).symm
      exact (congrArg (fun z => E.boundedPlugSideSolidPoint h z q.2) hz).trans
        (E.boundedPlugSideSolidPoint_boundary h _ _)
    exact hs.trans (congrArg E.toTorus.cutMap hp).symm
  · rw [ite_eq_right he, E.boundedSplitCharts_solid_val h hlin q
      (lt_of_le_of_ne hq he)]
    rfl

theorem boundedPlugSideCharts_host_val (q : ℂ × Circle) (hq : q.1 ∈ pantsInterior) :
    boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).hostMap q) =
      E.boundedPlugSideHostMap h q :=
  E.boundedSplitCharts_host_val h hlin q hq

theorem boundedPlugSideCharts_liftMap_val (t : Bool) {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (h3 : ‖q.1‖ < 3) :
    boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).liftMap t q) =
      E.boundedPlugSideLiftMap h hlin t q := by
  by_cases h2 : ‖q.1‖ ≤ 3 / 2
  · change boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).liftMap t q) =
      E.toTorus.cutMap (E.boundedPlugSideLiftPoint h hlin t q)
    rw [SplitCharts.liftMap_of_le _ t h2]
    change boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).solid
      ((2 : ℝ) • q.1, q.2 ^ (E.boundedSplitCharts h hlin).e₀)) = _
    rw [E.boundedPlugSideCharts_solid_val h hlin _ (by
      change ‖(2 : ℝ) • q.1‖ ≤ 3
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith)]
    exact congrArg E.toTorus.cutMap (by
      unfold boundedPlugSideLiftPoint
      rw [ite_eq_left h2])
  · rw [SplitCharts.liftMap_of_gt _ t (lt_of_not_ge h2)]
    have hh := E.boundedPlugSide_hostPoint_interior h hq (lt_of_not_ge h2) h3
    change boundedSplitInteriorVal W ((E.boundedPlugSideCharts h hlin).hostMap
      (hostChart (E.boundedPlugSideHost h)
        ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖)),
        E.boundedPlugSideFibre h hlin q)) = _
    rw [E.boundedPlugSideCharts_host_val h hlin _ hh]
    change E.toTorus.cutMap _ = E.toTorus.cutMap (E.boundedPlugSideLiftPoint h hlin t q)
    apply congrArg E.toTorus.cutMap
    unfold boundedPlugSideLiftPoint
    rw [ite_eq_right h2]

private instance boundedPlugSideInteriorBoundaryless : BoundarylessManifold W.model W.interior where
  isInteriorPoint' x := W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property

private def boundedPlugSideInteriorIdentity :
    W.interior ≃ₘ⟮W.model, 𝓡 3⟯ boundedSplitInterior W :=
  DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.interior)

private theorem boundedPlugSideInteriorVal_local :
    IsLocalDiffeomorph (𝓡 3) W.model ∞ (boundedSplitInteriorVal W) := by
  intro x
  exact (boundedPlugSideInteriorIdentity.symm.isLocalDiffeomorph x).comp _ _
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val W.interior x)

theorem boundedPlugSideLiftMap_local (t : Bool) (q : ℂ × Circle)
    (hq : E.boundedPlugSideDom h t q) (h3 : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞
      (E.boundedPlugSideLiftMap h hlin t) q := by
  have hc := (E.boundedPlugSideCharts h hlin).isLocalDiffeomorphAt_liftMap
    (E.boundedPlugSideCharts_seam_zero h hlin) t h3 (fun h2 =>
      ⟨E.boundedPlugSide_hostPoint_interior h hq h2 h3,
        E.boundedPlugSide_point_ne_zero h hq⟩)
  have hg := hc.comp W.model W.Carrier (boundedPlugSideInteriorVal_local (W := W) _)
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hg)
  have hopen := E.boundedPlugSide_isOpen_domain h t
  have hmem : q ∈ {p : ℂ × Circle | ‖p.1‖ < 3 ∧
      -3 < sgnR t * stripLevel (E.boundedPlugSideHost h)
        ((sideData (E.boundedPlugSideHost h) t).point (p.2, ‖p.1‖))} := ⟨h3, hq.2⟩
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact (E.boundedPlugSideCharts_liftMap_val h hlin t ⟨hp.1.le, hp.2⟩ hp.1).symm

theorem boundedPlugSideLiftPoint_collar (t : Bool) (p : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs3 : s < 1 / 3) (hδ : s < (E.splitData h).δ) :
    E.boundedPlugSideLiftPoint h hlin t ((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ), p.2) =
      E.toTorus.sideCollar (E.boundedPlugSidePort h t)
        (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
          (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
          halfPoint s hs) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) p.1
  have hgt : ¬‖((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ))‖ ≤ 3 / 2 := by
    rw [hn]
    linarith
  unfold boundedPlugSideLiftPoint boundedPlugSideFibre
  rw [ite_eq_right hgt, hn, sideData_point_collar _ t (by linarith) (by linarith),
    hostChart_hostInv, collarDepth_three_sub, unitOf_smul (by linarith) p.1]
  exact E.boundedModelHostPoint_collar h _ _ _ hs (by linarith) hδ

theorem boundedPlugSideLiftMap_collar (t : Bool) (p : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs3 : s < 1 / 3) (hδ : s < (E.splitData h).δ) :
    E.boundedPlugSideLiftMap h hlin t ((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ), p.2) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.boundedPlugSidePort h t)
        (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
          (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
          halfPoint s hs)) :=
  congrArg E.toTorus.cutMap (E.boundedPlugSideLiftPoint_collar h hlin t p hs hs3 hδ)

end Smooth

end GC.Seifert.ElementaryPresentation
