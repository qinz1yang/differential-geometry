import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelSolidLocal

/-!
# The capped solid torus of one side: injectivity and the two sides

Lane N2f, side model, step 5 (injectivity). Two lifted points of the two sides with the same image
have the same level unless both lie on the boundary circle `‖ζ‖ = 3` (`liftMap_cross`): equal
interior points of the cut carrier have equal host or solid coordinates, and boundary points are
the seam torus of `V` or the port tori. A fake point of side `t` reads the cap of side `t` or the
tube at a level `sgnR(t) · r` with `1 < r ≤ 2` (`fakeMap_cases`), while a real point is a core
point off the boundary spheres at a level with `sgnR(t) · level > 2`. Hence `solMap` is injective
on the closed model solid torus (`solMap_injOn`), and the two sides meet only at boundary points of
both model solid tori (`solMap_cross`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.ElementaryPresentation

open SplitTube

section Cross

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

theorem sideLevel_eq_of_le (t t' : Bool) {q : ℂ × Circle} (h2 : ‖q.1‖ ≤ 2) :
    E.sideLevel h t q = E.sideLevel h t' q := by
  rw [E.sideLevel_of_le h t h2, E.sideLevel_of_le h t' h2]

theorem sideLevel_eq_of_liftPt_eq {t t' : Bool} {q q' : ℂ × Circle} (hq : E.sideDom h t q)
    (hq' : E.sideDom h t' q') (he : E.liftPt h hlin t q = E.liftPt h hlin t' q') :
    E.sideLevel h t q = E.sideLevel h t' q' := by
  have he₀ := (E.splitCharts h hlin).he₀
  unfold liftPt at he
  by_cases h1 : ‖q.1‖ ≤ 3 / 2 <;> by_cases h1' : ‖q'.1‖ ≤ 3 / 2
  · simp only [h1, h1', ↓reduceIte] at he
    have hn : ∀ z : ℂ, ‖z‖ ≤ 3 / 2 → ‖(2 : ℝ) • z‖ ≤ 3 := fun z hz => by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    obtain ⟨e1, e2⟩ := E.solidPt_inj h (hn _ h1) (hn _ h1') he
    have hqq : q = q' := by
      refine Prod.ext (smul_right_injective ℂ (by norm_num : (2 : ℝ) ≠ 0) e1) ?_
      rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
    subst hqq
    exact E.sideLevel_eq_of_le h t t' (by linarith)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he (E.solidPt_ne_hostPt h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he.symm (E.solidPt_ne_hostPt h _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    push Not at h1 h1'
    obtain ⟨e1, -⟩ := E.hostPt_inj h (E.hostChart_point_mem_planarModel h hq h1.le)
      (E.hostChart_point_mem_planarModel h hq' h1'.le) he
    have e3 := congrArg (hostInv (E.hostSide h)) e1
    rw [hostInv_hostChart, hostInv_hostChart] at e3
    unfold sideLevel
    rw [e3]

theorem liftMap_cross {t t' : Bool} {q q' : ℂ × Circle} (hq : E.sideDom h t q)
    (hq' : E.sideDom h t' q')
    (he : (E.splitCharts h hlin).liftMap t q = (E.splitCharts h hlin).liftMap t' q') :
    E.sideLevel h t q = E.sideLevel h t' q' ∨ (‖q.1‖ = 3 ∧ ‖q'.1‖ = 3) := by
  have he₀ := (E.splitCharts h hlin).he₀
  rw [E.liftMap_eq_cutMap, E.liftMap_eq_cutMap] at he
  by_cases hi : E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t q)
  · exact Or.inl (E.sideLevel_eq_of_liftPt_eq h hlin hq hq'
      (E.toTorus.cutMap_eq_of_isInteriorPoint hi he))
  by_cases hi' : E.toTorus.cutCarrier.model.IsInteriorPoint (E.liftPt h hlin t' q')
  · exact Or.inl (E.sideLevel_eq_of_liftPt_eq h hlin hq' hq
      (E.toTorus.cutMap_eq_of_isInteriorPoint hi' he.symm)).symm
  rcases E.liftPt_radius h hlin hq hi with h1 | h1 <;>
    rcases E.liftPt_radius h hlin hq' hi' with h1' | h1'
  · left
    rw [E.liftPt_of_three_halves h hlin t h1, E.liftPt_of_three_halves h hlin t' h1'] at he
    have e := Prod.ext_iff.mp (E.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e2 : q.2 ^ (E.splitCharts h hlin).e₀ = q'.2 ^ (E.splitCharts h hlin).e₀ := e.2
    have hqq : q = q' := by
      refine Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e.1) ?_
      rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
    subst hqq
    exact E.sideLevel_eq_of_le h t t' (by linarith)
  · rw [E.liftPt_of_three_halves h hlin t h1, E.liftPt_of_three h hlin t' h1'] at he
    exact absurd he (E.cutMap_seamSide_ne_portSide h t' _ _)
  · rw [E.liftPt_of_three h hlin t h1, E.liftPt_of_three_halves h hlin t' h1'] at he
    exact absurd he.symm (E.cutMap_seamSide_ne_portSide h t _ _)
  · exact Or.inr ⟨h1, h1'⟩

end Cross

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

theorem one_lt_abs_sideLevel {t : Bool} {q : ℂ × Circle} (h2 : 2 < sgnR t * E.sideLevel h t q) :
    1 < |E.sideLevel h t q| := by
  rw [← SplitCharts.abs_sgnR_mul t]
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem coreMap_liftMap_ne_cap {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hlev : 1 < |E.sideLevel h t q|) (c : (E.splitSeamTube j b h hlin).Boundary)
    (w : ClosedCell 3) : coreMap K ((E.splitCharts h hlin).liftMap t q) ≠ K.cap c w := by
  rw [coreMap_of_mem K (liftMap_mem_core hq hlev)]
  exact coreInclusion_ne_cap_of_forall_ne K _ (fun c' z => liftMap_ne_boundarySphere hq hlev c' z)
    c w

theorem coreMap_liftMap_ne_tubeMap {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hlev : 1 < |E.sideLevel h t q|) {z : S2} {lv : ℝ} (h1 : 1 ≤ |lv|) (h3 : |lv| < 3)
    (hne : E.sideLevel h t q ≠ lv) :
    coreMap K ((E.splitCharts h hlin).liftMap t q) ≠
      coreMap K ((E.splitCharts h hlin).tubeMap (z, lv)) := by
  intro he
  exact liftMap_ne_tubeMap hq h3 hne (coreMap_injOn K (liftMap_mem_core hq hlev)
    ((E.splitCharts h hlin).tubeMap_mem_core (q := (z, lv)) h1 h3) he)

theorem abs_sgnR_mul_of_pos (t : Bool) {r : ℝ} (hr : 0 < r) : |sgnR t * r| = r := by
  rw [SplitCharts.abs_sgnR_mul, abs_of_pos hr]

namespace SideCap

variable {t : Bool} (S : E.SideCap h hlin K t)

theorem ball_cases {x : E3} (hx : ‖x‖ ≤ 2) :
    (∃ w, S.Φ x = K.cap ((), t) w) ∨ ∃ z : S2, 1 < ‖x‖ ∧
      S.Φ x = coreMap K ((E.splitCharts h hlin).tubeMap (z, sgnR t * ‖x‖)) := by
  by_cases h1 : ‖x‖ ≤ 1
  · exact Or.inl (S.cap_in x h1)
  · push Not at h1
    obtain ⟨z, hz⟩ := S.shell x h1.le (by linarith)
    exact Or.inr ⟨z, h1, hz⟩

theorem fakeMap_cases {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * E.sideLevel h t q ≤ 2) :
    (∃ w, S.fakeMap q = K.cap ((), t) w) ∨ ∃ z : S2, ∃ r : ℝ, 1 < r ∧ r ≤ 2 ∧
      S.fakeMap q = coreMap K ((E.splitCharts h hlin).tubeMap (z, sgnR t * r)) := by
  rcases S.ball_cases (S.norm_two_smul_le h3 h2) with hc | ⟨z, h1, hz⟩
  · exact Or.inl hc
  · exact Or.inr ⟨z, _, h1, S.norm_two_smul_le h3 h2, hz⟩

theorem fakeMap_ne_coreMap_liftMap {t' : Bool} {q q' : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.sideLevel h t q ≤ 2) (hq' : E.sideDom h t' q')
    (hlev : 1 < |E.sideLevel h t' q'|)
    (hne : ∀ r : ℝ, 1 < r → r ≤ 2 → E.sideLevel h t' q' ≠ sgnR t * r) :
    S.fakeMap q ≠ coreMap K ((E.splitCharts h hlin).liftMap t' q') := by
  rcases S.fakeMap_cases h3 h2 with ⟨w, hw⟩ | ⟨z, r, h1, hr2, hz⟩
  · rw [hw]
    exact (coreMap_liftMap_ne_cap hq' hlev _ w).symm
  · rw [hz]
    have habs := abs_sgnR_mul_of_pos t (show 0 < r by linarith)
    exact (coreMap_liftMap_ne_tubeMap hq' hlev (by rw [habs]; linarith) (by rw [habs]; linarith)
      (hne r h1 hr2)).symm

theorem fakeMap_inj {q q' : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * E.sideLevel h t q ≤ 2)
    (h3' : ‖q'.1‖ < 3) (h2' : sgnR t * E.sideLevel h t q' ≤ 2)
    (he : S.fakeMap q = S.fakeMap q') : q = q' := by
  have hb := S.norm_two_smul_le h3 h2
  have hb' := S.norm_two_smul_le h3' h2'
  have e1 := S.inj (mem_ball_zero_iff.mpr (by linarith)) (mem_ball_zero_iff.mpr (by linarith)) he
  have e2 := smul_right_injective E3 (by norm_num : (2 : ℝ) ≠ 0) e1
  have e3 := S.G.symm.injective e2
  exact torusPD_injOn (show ‖q.1‖ < 4 by linarith) (show ‖q'.1‖ < 4 by linarith) e3

theorem solMap_cases {q : ℂ × Circle} (h3 : ‖q.1‖ ≤ 3) :
    (‖q.1‖ < 3 ∧ sgnR t * E.sideLevel h t q ≤ 2 ∧ S.solMap q = S.fakeMap q) ∨
      (E.sideDom h t q ∧ 2 < sgnR t * E.sideLevel h t q ∧
        S.solMap q = coreMap K ((E.splitCharts h hlin).liftMap t q)) := by
  by_cases hc : ‖q.1‖ < 3 ∧ sgnR t * E.sideLevel h t q ≤ 2
  · exact Or.inl ⟨hc.1, hc.2, S.solMap_of_fake hc.1 hc.2⟩
  · have h2 : 2 < sgnR t * E.sideLevel h t q := by
      by_cases h3' : ‖q.1‖ < 3
      · exact not_le.mp fun h2 => hc ⟨h3', h2⟩
      · have he : ‖q.1‖ = 3 := le_antisymm h3 (not_lt.mp h3')
        linarith [E.three_lt_sideLevel_of_ge h t (q := q) (by linarith) h3]
    exact Or.inr ⟨(E.sideDom_iff h).mpr ⟨h3, by linarith⟩, h2, S.solMap_of_real h2⟩

theorem solMap_injOn : InjOn S.solMap {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  intro q hq q' hq' he
  have hss := sgnR_mul_self t
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩ <;>
    rcases S.solMap_cases hq' with ⟨h3', h2', e'⟩ | ⟨hd', h2', e'⟩ <;> rw [e, e'] at he
  · exact S.fakeMap_inj h3 h2 h3' h2' he
  · refine absurd he (S.fakeMap_ne_coreMap_liftMap h3 h2 hd' (one_lt_abs_sideLevel h2')
      fun r _ hr hc => ?_)
    rw [hc, ← mul_assoc, hss, one_mul] at h2'
    linarith
  · refine absurd he.symm (S.fakeMap_ne_coreMap_liftMap h3' h2' hd (one_lt_abs_sideLevel h2)
      fun r _ hr hc => ?_)
    rw [hc, ← mul_assoc, hss, one_mul] at h2
    linarith
  · exact E.liftMap_injOn h hlin t hd hd' (coreMap_injOn K
      (liftMap_mem_core hd (one_lt_abs_sideLevel h2))
      (liftMap_mem_core hd' (one_lt_abs_sideLevel h2')) he)

end SideCap

theorem sgnR_false : sgnR false = -1 := rfl

theorem sgnR_true : sgnR true = 1 := rfl

theorem solMap_cross (S : E.SideCap h hlin K false) (S' : E.SideCap h hlin K true)
    {q q' : ℂ × Circle} (hq : ‖q.1‖ ≤ 3) (hq' : ‖q'.1‖ ≤ 3) (he : S.solMap q = S'.solMap q') :
    ‖q.1‖ = 3 ∧ ‖q'.1‖ = 3 := by
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩ <;>
    rcases S'.solMap_cases hq' with ⟨h3', h2', e'⟩ | ⟨hd', h2', e'⟩ <;> rw [e, e'] at he
  · exfalso
    rcases S.fakeMap_cases h3 h2 with ⟨w, hw⟩ | ⟨z, r, h1, hr2, hz⟩ <;>
      rcases S'.fakeMap_cases h3' h2' with ⟨w', hw'⟩ | ⟨z', r', h1', hr2', hz'⟩
    · rw [hw, hw'] at he
      exact Set.disjoint_left.mp (K.cap_disjoint (show ((), false) ≠ ((), true) by simp))
        ⟨w, rfl⟩ ⟨w', he.symm⟩
    · rw [hw, hz'] at he
      exact (E.splitCharts h hlin).coreMap_tubeMap_ne_cap K (q := (z', sgnR true * r'))
        (by change 1 < |sgnR true * r'|; rw [abs_sgnR_mul_of_pos true (by linarith)]; exact h1')
        (by change |sgnR true * r'| < 3; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith)
        _ w he.symm
    · rw [hz, hw'] at he
      exact (E.splitCharts h hlin).coreMap_tubeMap_ne_cap K (q := (z, sgnR false * r))
        (by change 1 < |sgnR false * r|; rw [abs_sgnR_mul_of_pos false (by linarith)]; exact h1)
        (by change |sgnR false * r| < 3; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        _ w' he
    · rw [hz, hz'] at he
      have hqq := (E.splitCharts h hlin).coreMap_tubeMap_inj K (q := (z, sgnR false * r))
        (q' := (z', sgnR true * r'))
        (by change 1 ≤ |sgnR false * r|; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        (by change |sgnR false * r| < 3; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        (by change 1 ≤ |sgnR true * r'|; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith)
        (by change |sgnR true * r'| < 3; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith) he
      have e2 := congrArg Prod.snd hqq
      simp only [sgnR_false, sgnR_true] at e2
      linarith
  · refine absurd he (S.fakeMap_ne_coreMap_liftMap h3 h2 hd' (one_lt_abs_sideLevel h2')
      fun r hr _ hc => ?_)
    rw [hc, sgnR_true, sgnR_false] at h2'
    linarith
  · refine absurd he.symm (S'.fakeMap_ne_coreMap_liftMap h3' h2' hd (one_lt_abs_sideLevel h2)
      fun r hr _ hc => ?_)
    rw [hc, sgnR_true, sgnR_false] at h2
    linarith
  · have hl := coreMap_injOn K (liftMap_mem_core hd (one_lt_abs_sideLevel h2))
      (liftMap_mem_core hd' (one_lt_abs_sideLevel h2')) he
    rcases E.liftMap_cross h hlin hd hd' hl with hlev | hb
    · rw [hlev, sgnR_false] at h2
      rw [sgnR_true] at h2'
      linarith
    · exact hb

end GC.Seifert.ElementaryPresentation
