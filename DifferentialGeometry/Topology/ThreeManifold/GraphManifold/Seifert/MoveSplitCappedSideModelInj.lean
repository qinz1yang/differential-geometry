import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelPoints

/-!
# Injectivity of the lift

Lane N2d, side model, step 4 (injectivity). The points `liftPt` of the solid torus model are
pairwise distinct on the side domain (`liftPt_inj`), and so are their images in `Q`
(`liftMap_injOn`): interior points of the cut carrier are alone in their fibre, the boundary
torus of `V` is met only at radius `3/2`, the circle `sidePort` of `H` only at radius `3`, and
these two tori are never glued to each other.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem eq_of_norm_eq_of_unitOf_eq {z z' : ℂ} (hn : ‖z‖ = ‖z'‖) (hu : unitOf z = unitOf z') :
    z = z' := by
  rw [← norm_smul_unitOf z, ← norm_smul_unitOf z', hn, hu]

namespace ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem solidPt_inj {z z' : ℂ} {w w' : Circle} (hz : ‖z‖ ≤ 3) (hz' : ‖z'‖ ≤ 3)
    (he : E.solidPt h z w = E.solidPt h z' w') : z = z' ∧ w = w' := by
  have h1 := Prod.ext_iff.mp ((E.splitData h).ΘV.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : (discPlanarBase.{u} 1).surface.Carrier =>
    ((show discSet.{u} from x).val).down) h1.1
  dsimp only at h2
  rw [clampDisc_val hz, clampDisc_val hz'] at h2
  exact h2

theorem hostPt_inj {z z' : ℂ} {ν ν' : Circle} (hz : z ∈ planarModel 3) (hz' : z' ∈ planarModel 3)
    (he : E.hostPt h z ν = E.hostPt h z' ν') : z = z' ∧ ν = ν' := by
  have h1 := Prod.ext_iff.mp ((E.splitData h).ΘH.injective (Subtype.ext he))
  refine ⟨?_, h1.2⟩
  have h2 := congrArg (fun x : pantsPlanarBase.{u}.surface.Carrier =>
    ((show planarSet.{u} 3 from x).val).down) h1.1
  dsimp only at h2
  rw [clampPants_val hz, clampPants_val hz'] at h2
  exact h2

theorem solidPt_ne_hostPt (z z' : ℂ) (w ν : Circle) : E.solidPt h z w ≠ E.hostPt h z' ν := by
  intro he
  have h1 := E.solidPt_mem h z w
  rw [he] at h1
  exact E.seamPiece_ne_hostPiece h (E.toTorus.eq_of_mem_piece' h1 (E.hostPt_mem h z' ν))

section Lift

variable (hlin : E.IsLinearSeam j)

theorem liftPt_inj {t : Bool} {q q' : ℂ × Circle} (hq : E.sideDom h t q) (hq' : E.sideDom h t q')
    (he : E.liftPt h hlin t q = E.liftPt h hlin t q') : q = q' := by
  have he₀ := (E.splitCharts h hlin).he₀
  have he₁ := (E.splitCharts h hlin).he₁
  unfold liftPt at he
  by_cases h1 : ‖q.1‖ ≤ 3 / 2 <;> by_cases h1' : ‖q'.1‖ ≤ 3 / 2
  · simp only [h1, h1', ↓reduceIte] at he
    have hn : ∀ z : ℂ, ‖z‖ ≤ 3 / 2 → ‖(2 : ℝ) • z‖ ≤ 3 := fun z hz => by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    obtain ⟨e1, e2⟩ := E.solidPt_inj h (hn _ h1) (hn _ h1') he
    refine Prod.ext (smul_right_injective ℂ (by norm_num : (2 : ℝ) ≠ 0) e1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he (E.solidPt_ne_hostPt h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he.symm (E.solidPt_ne_hostPt h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    push Not at h1 h1'
    obtain ⟨e1, e2⟩ := E.hostPt_inj h (E.hostChart_point_mem_planarModel h hq h1.le)
      (E.hostChart_point_mem_planarModel h hq' h1'.le) he
    have e3 := congrArg (hostInv (E.hostSide h)) e1
    rw [hostInv_hostChart, hostInv_hostChart] at e3
    have e4 := (sideData (E.hostSide h) t).point_injOn ⟨mem_univ _, norm_nonneg _, hq.1⟩
      ⟨mem_univ _, norm_nonneg _, hq'.1⟩ e3
    have e5 : q.2 = q'.2 := congrArg Prod.fst e4
    have e6 : ‖q.1‖ = ‖q'.1‖ := congrArg Prod.snd e4
    unfold liftFib at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq e6 e7) e5

theorem liftPt_radius {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hi : ¬ E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q)) :
    ‖q.1‖ = 3 / 2 ∨ ‖q.1‖ = 3 := by
  by_contra hc
  push Not at hc
  rcases lt_or_gt_of_ne hc.1 with h32 | h32
  · exact hi (E.liftPt_isInteriorPoint_of_lt h hlin t h32)
  · exact hi (E.liftPt_isInteriorPoint_of_mid h hlin t hq h32 (lt_of_le_of_ne hq.1 hc.2))

theorem liftMap_injOn (t : Bool) :
    InjOn ((E.splitCharts h hlin).liftMap t) {q | E.sideDom h t q} := by
  have he₀ := (E.splitCharts h hlin).he₀
  have he₁ := (E.splitCharts h hlin).he₁
  intro q hq q' hq' he
  rw [E.liftMap_eq_cutMap, E.liftMap_eq_cutMap] at he
  by_cases hi : E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q)
  · exact E.liftPt_inj h hlin hq hq' (E.toTorus.cutMap_eq_of_isInteriorPoint hi he)
  by_cases hi' : E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q')
  · exact (E.liftPt_inj h hlin hq' hq (E.toTorus.cutMap_eq_of_isInteriorPoint hi' he.symm)).symm
  rcases E.liftPt_radius h hlin hq hi with h1 | h1 <;>
    rcases E.liftPt_radius h hlin hq' hi' with h1' | h1'
  · rw [E.liftPt_of_three_halves h hlin t h1, E.liftPt_of_three_halves h hlin t h1'] at he
    have e := Prod.ext_iff.mp (E.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e2 : q.2 ^ (E.splitCharts h hlin).e₀ = q'.2 ^ (E.splitCharts h hlin).e₀ := e.2
    refine Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e.1) ?_
    rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
  · rw [E.liftPt_of_three_halves h hlin t h1, E.liftPt_of_three h hlin t h1'] at he
    exact absurd he (E.cutMap_seamSide_ne_portSide h t _ _)
  · rw [E.liftPt_of_three h hlin t h1, E.liftPt_of_three_halves h hlin t h1'] at he
    exact absurd he.symm (E.cutMap_seamSide_ne_portSide h t _ _)
  · rw [E.liftPt_of_three h hlin t h1, E.liftPt_of_three h hlin t h1'] at he
    have e := Prod.ext_iff.mp (E.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e5 : q.2 = q'.2 := inv_injective e.1
    have e2 : E.liftFib h hlin q = E.liftFib h hlin q' := e.2
    unfold liftFib at e2
    rw [e5, mul_right_inj] at e2
    have e7 : unitOf q.1 = unitOf q'.1 := by
      rw [← zpow_zpow_unit he₁ (unitOf q.1), e2, zpow_zpow_unit he₁]
    exact Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e7) e5

end Lift

end ElementaryPresentation

end GC.Seifert
