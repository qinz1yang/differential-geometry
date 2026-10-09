import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleChart
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleCount
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleMultiplicity
import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartCutoffProfiles

/-!
# The circle family of the flat torus (S-FIXTURE-C1b, F1, G3 file 3)

`torCircleFamily_FXC1 : CircleFamily 𝓘(ℝ, E3) (Tor Λ) (fun _ => R) _ β`: the finite `R`-spaced
centre net (`torCentres_FXC1`), at every centre the LC83 chart `torChart_FXC1`, and the formula
cutoff `Φ_{8,9} ∘ η_j` (`CircleChart.formulaCutoff`). The support multiplicity is below
`401² ≤ V(6·10⁶ + 2/3)/V(1/3)` (`torCentres_ncard_le_FXC1`, `circle_multiplicity_const_ge_FXC1`).
All hypotheses are the numerical ones of the K1 kernel: `L₀ = L₁ = N R`, `L₂ ≤ R β₂`,
`8R/β₂ ≤ L_p`, `0 < β₂ ≤ 10⁻⁷`, `β₃ ≤ 3/20`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

section Family

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)

include hR hβ2 hβ2s hL2 hLp in
/-- The formula cutoff `Φ_{8,9}(η_j)` of the chart at `j`. -/
def torCutoff_FXC1 (j : Tor_FXC1 Λ) : Tor_FXC1 Λ → ℝ :=
  letI := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j).formulaCutoff

include hR hβ2 hβ2s hL2 hLp in
/-- The cutoff is supported in the physical ball `B(j, 200 R)`. -/
theorem torCutoff_tsupport_FXC1 (j : Tor_FXC1 Λ) :
    tsupport (torCutoff_FXC1 Λ hR hβ2 hβ2s hL2 hLp j) ⊆ ball j (200 * R) := by
  intro x hx
  have key : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j ≤ 102 := by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    have h := (CircleChart.formulaCutoff_spec
      (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.2.2.2.1 hx
    exact h.1
  have h1 : R⁻¹ * dist x j ≤ 102 := key
  have h2 := (inv_mul_le_iff₀ hR).mp h1
  rw [mem_ball]
  linarith

include hR hβ2 hβ2s hL2 hLp in
/-- The cutoff is one on the physical ball `B(j, 2 R)`. -/
theorem torCutoff_plateau_FXC1 (j : Tor_FXC1 Λ) {x : Tor_FXC1 Λ} (hx : x ∈ ball j (2 * R)) :
    torCutoff_FXC1 Λ hR hβ2 hβ2s hL2 hLp j x = 1 := by
  have hx' : dist x j < 2 * R := mem_ball.mp hx
  have hRi := inv_pos.mpr hR
  have hr : R⁻¹ * dist x j < 2 := by
    rw [inv_mul_lt_iff₀ hR]
    linarith
  have hb := (torEta_dist_bounds_FXC1 Λ hR hβ2 hβ2s hLp j x j (by linarith) (by
    rw [dist_self]
    positivity)).1
  rw [torEta_center_FXC1, sub_zero] at hb
  have hb8 : ‖torEta_FXC1 Λ R j x‖ ≤ 8 := by linarith
  let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  refine (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.2.1 x
    ?_ hb8
  change R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist x j < 200
  linarith

variable (N : ℕ) (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R)

include hL0 in
theorem torCentres_pos_FXC1 : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exfalso
    have := Λ.pos 0
    rw [hL0, h] at this
    simp at this
  · exact h

include hR hβ2s hL2 in
theorem torL2_le_half_FXC1 : Λ.L 2 ≤ R / 2 := by
  have h : R * β 2 ≤ R * (1 / 10 ^ 7) := mul_le_mul_of_nonneg_left hβ2s hR.le
  linarith

include hL0 hL1 in
/-- Distinct centres are at least `R` apart. -/
theorem torCentres_dist_ge_FXC1 (hR : 0 < R) {j j' : Tor_FXC1 Λ} (hj : j ∈ torCentres_FXC1 Λ R N)
    (hj' : j' ∈ torCentres_FXC1 Λ R N) (hne : j ≠ j') : R ≤ dist j j' := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hj
  obtain ⟨⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩ := hj'
  refine torCentres_sep_FXC1 Λ N hL0 hL1 hR ha hb ha' hb' ?_
  rintro ⟨rfl, rfl⟩
  exact hne rfl

include hR hβ2 hβ2s hL2 hLp hL0 hL1 in
/-- **The circle family of the flat torus** at the constant scale `ρ ≡ R`. -/
def torCircleFamily_FXC1 (hβ3 : β 3 ≤ 3 / 20) :
    CircleFamily 𝓘(ℝ, E3) (Tor_FXC1 Λ) (fun _ => R) (fun _ => hR) β where
  centres := torCentres_FXC1 Λ R N
  finite_centres := torCentres_finite_FXC1 Λ N R
  centres_subset := by
    rw [torStratum_two_eq_univ_FXC1 Λ hR hβ2 (hβ2s.trans (by norm_num)) hβ3 hL2 hLp]
    exact subset_univ _
  disjoint_centres := fun j hj j' hj' hne => by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h := torCentres_dist_ge_FXC1 Λ N hL0 hL1 hR hj hj' hne
    have h1 : dist x j < R / 3 := mem_ball.mp hx
    have h2 : dist x j' < R / 3 := mem_ball.mp hx'
    have h3 := dist_triangle_left j j' x
    linarith
  covers := fun p _ => by
    obtain ⟨j, hj, hd⟩ := torCentres_cover_FXC1 Λ N hL0 hL1 hR
      (torCentres_pos_FXC1 Λ N hL0) (torL2_le_half_FXC1 Λ hR hβ2s hL2) p
    exact ⟨j, hj, ball_subset_ball' (by linarith)⟩
  chart := fun j _ => torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j
  chart_center := fun _ _ => rfl
  cutoff := fun j => torCutoff_FXC1 Λ hR hβ2 hβ2s hL2 hLp j
  contMDiff_cutoff := fun j _ => by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    exact (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).1
  cutoff_mem_Icc := fun j _ => by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    exact (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.1
  cutoff_eq_one := fun j _ => by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    exact (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.2.1
  coord_lt_of_cutoff_ne_zero := fun j _ => by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    exact (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.2.2.1
  tsupport_subset_domain := fun j _ => by
    let := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    exact (CircleChart.formulaCutoff_spec (torChart_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)).2.2.2.2.2
  plateau := fun j _ x hx => torCutoff_plateau_FXC1 Λ hR hβ2 hβ2s hL2 hLp j hx
  tsupport_subset_ball := fun j _ => torCutoff_tsupport_FXC1 Λ hR hβ2 hβ2s hL2 hLp j
  multiplicity := fun x => by
    refine le_trans ?_ circle_multiplicity_const_ge_FXC1
    have hsub : torCentres_FXC1 Λ R N ∩
        {j | x ∈ tsupport (torCutoff_FXC1 Λ hR hβ2 hβ2s hL2 hLp j)} ⊆
        torCentres_FXC1 Λ R N ∩ {j | dist x j < 200 * R} := by
      rintro j ⟨hj, hx⟩
      refine ⟨hj, ?_⟩
      have h := torCutoff_tsupport_FXC1 Λ hR hβ2 hβ2s hL2 hLp j hx
      rw [mem_ball] at h
      exact h
    have h1 := Set.ncard_le_ncard hsub
      ((torCentres_finite_FXC1 Λ N R).subset Set.inter_subset_left)
    have h2 := h1.trans (torCentres_ncard_le_FXC1 Λ N hL0 hL1 hR x)
    exact_mod_cast h2

end Family

end DifferentialGeometry.Geometry.Collapse
