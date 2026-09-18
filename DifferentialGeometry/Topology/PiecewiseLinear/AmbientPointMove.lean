import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import Mathlib.Topology.Connected.Basic

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_small_point_move {U : Set E} (hU : IsOpen U)
    {p : E} (hp : p ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : E, dist q p < δ →
      ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h p = q := by
  classical
  let T : Finset E := {p}
  have hT : AffineIndependent ℝ ((↑) : T → E) := affineIndependent_of_subsingleton ℝ _
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hK : K.space = {p} := by
    rw [simplexComplex_space T hT (Finset.singleton_nonempty p)]
    simp [T]
  have hpK : {p} ∈ K.faces := ⟨Finset.singleton_nonempty p, subset_rfl⟩
  obtain ⟨N, hN, hpN, hNU⟩ := exists_isPolyhedron_neighborhood isCompact_singleton hU
    (singleton_subset_iff.mpr hp)
  have hstar : openStar K p ⊆ interior N := by
    rw [← hK] at hpN
    exact (openStar_subset_space K p).trans hpN
  obtain ⟨δ, hδ, hmove⟩ := exists_isPLHomeomorphOn_of_small_vertex_move K p hN hstar
  refine ⟨δ, hδ, fun q hq => ?_⟩
  obtain ⟨h, hh, hfix, hmap⟩ := hmove q hq
  refine ⟨h, hh, hfix.mono (compl_subset_compl.mpr hNU), ?_⟩
  rw [hmap (hK.symm ▸ mem_singleton p), simplicialMap_vertex K _ hpK, Function.update_self]

theorem exists_isPLHomeomorphOn_map_point_eqOn_compl {U : Set E}
    (hU : IsOpen U) (hc : IsPreconnected U) {p q : E} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h p = q := by
  classical
  let A : Set E := {x | x ∈ U ∧ ∃ h : E ≃ₜ E,
    IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h p = x}
  have hsymm {h : E ≃ₜ E} (hh : IsPLHomeomorphOn h univ univ) :
      IsPLHomeomorphOn h.symm univ univ := by
    apply hh.symm.congr
    intro x hx
    exact h.injective ((h.apply_symm_apply x).trans (hh.bijOn.invOn_invFunOn.2 hx).symm)
  have hfixsymm {h : E ≃ₜ E} (hh : EqOn h id Uᶜ) : EqOn h.symm id Uᶜ := by
    intro x hx
    exact h.symm_apply_eq.mpr (hh hx).symm
  have hlocal (x : E) (hx : x ∈ U) :
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, ∃ h : E ≃ₜ E,
          IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h x = y := by
    obtain ⟨δ, hδ, hmove⟩ := exists_isPLHomeomorphOn_small_point_move hU hx
    exact ⟨Metric.ball x δ ∩ U, Metric.isOpen_ball.inter hU,
      ⟨Metric.mem_ball_self hδ, hx⟩, inter_subset_right, fun y hy => hmove y hy.1⟩
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxU, h, hh, hfix, hpx⟩
    obtain ⟨V, hV, hxV, hVU, hmove⟩ := hlocal x hxU
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    obtain ⟨g, hg, hgfix, hxy⟩ := hmove y hy
    refine ⟨hVU hy, h.trans g, hh.trans hg, ?_, ?_⟩
    · intro z hz
      change g (h z) = z
      exact (congrArg g (hfix hz)).trans (hgfix hz)
    · change g (h p) = y
      rw [hpx, hxy]
  have hB : IsOpen (U \ A) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxU, hxA⟩
    obtain ⟨V, hV, hxV, hVU, hmove⟩ := hlocal x hxU
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    refine ⟨hVU hy, ?_⟩
    rintro ⟨_, h, hh, hfix, hpy⟩
    obtain ⟨g, hg, hgfix, hxy⟩ := hmove y hy
    apply hxA
    refine ⟨hxU, h.trans g.symm, hh.trans (hsymm hg), ?_, ?_⟩
    · intro z hz
      change g.symm (h z) = z
      exact (congrArg g.symm (hfix hz)).trans (hfixsymm hgfix hz)
    · change g.symm (h p) = x
      rw [hpy, ← hxy, g.symm_apply_apply]
  have hpA : p ∈ A := by
    refine ⟨hp, Homeomorph.refl E, ?_, fun _ _ => rfl, rfl⟩
    exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
      (isPiecewiseAffineOn_id isOpen_univ).congr
        (fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx)⟩
  have hUA : U ⊆ A := hc.subset_left_of_subset_union hA hB disjoint_sdiff_right
    (fun x hx => by
      by_cases h : x ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩)
    ⟨p, hp, hpA⟩
  exact (hUA hq).2

end DifferentialGeometry.Topology.PiecewiseLinear
