import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusEll
import DifferentialGeometry.Geometry.Collapse.FixtureC1.ThinPlaneKL
import DifferentialGeometry.Geometry.Collapse.FixtureC1.NoEdgeOfSplitting

/-!
# The flat torus has splitting rank exactly two everywhere (S-FIXTURE-C1, K1, file 6)

At the constant scale `ρ ≡ R`, the thin torus `T²_{L₀,L₁} × S¹(L₂)` with `L₂ ≤ R β₂`,
`Lp ≥ 8R/β₂` (`Lp` the smaller planar period) satisfies, at every point `p`:

* `torPlaneKL_FXC1`: the plane chart `R⁻¹ ell` is a Kleiner-Lott approximation into `ℝ² ×₂ PUnit`
  (any tolerance `δ` with `L₂ ≤ 2Rδ` and `Lp ≥ 4Rδ⁻¹`);
* `torRank_eq_two_FXC1`: `scaledSplittingRank = 2` (the thin-plane exactness lemma of the
  metric-rank chain: the two-splitting at `β₂` and the exclusion of a three-splitting at
  `β₃ ≤ 3/20`);
* `torStratum_two_eq_univ_FXC1`: the two-stratum is the whole torus, the others are empty.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric GC.MetricGeometry
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- **The plane chart of the torus is a Kleiner-Lott `δ`-approximation** of the rescaled metric
`R⁻¹ d` into `ℝ² ×₂ PUnit` at `π pt ↦ (0, ★)`. -/
def torPlaneKL_FXC1 (Λ : TorusPeriods_FXC1) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL2 : Λ.L 2 ≤ 2 * (R * δ)) (hLp : 4 * (R * δ⁻¹) ≤ planePeriod_FXC1 Λ) (pt : E3) :
    @KleinerLottApprox (Tor_FXC1 Λ) (WithLp 2 (ℝ² × PUnit.{1}))
      ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) _ (torPi_FXC1 Λ pt)
      (WithLp.toLp 2 ((0 : ℝ²), PUnit.unit)) δ := by
  refine kleinerLott_of_thin_chart_FXC1 (D := Λ.L 2 / 2) hR hδ hδ1 (ell_FXC1 Λ pt)
    (ell_base_FXC1 Λ pt) (fun q hq q' hq' => ?_) (by linarith) (fun u hu => ?_)
  · exact ell_dist_bounds_FXC1 Λ pt q q' (r := R * δ⁻¹) (by linarith)
      (by rw [dist_comm]; exact hq) (by rw [dist_comm]; exact hq')
  · have hLp0 := planePeriod_pos_FXC1 Λ
    obtain ⟨q, hq, hd⟩ := exists_ell_eq_FXC1 Λ pt u (by linarith)
    exact ⟨q, by rw [mem_ball, dist_comm]; exact lt_of_le_of_lt hd hu, hq⟩

/-- **Rank exactly two at every point** of the thin torus at the constant scale `R`. -/
theorem torRank_eq_two_FXC1 (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ}
    (hβ2 : 0 < β 2) (hβ2' : β 2 ≤ 1 / 50) (hβ3 : β 3 ≤ 3 / 20) (hL2 : Λ.L 2 ≤ R * β 2)
    (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ) (p : Tor_FXC1 Λ) :
    scaledSplittingRank.{0, 0} (fun _ : Tor_FXC1 Λ => R) (fun _ => hR) β p = 2 := by
  obtain ⟨pt, rfl⟩ := torPi_surjective_FXC1 Λ p
  have hδ : 0 < β 2 / 2 := half_pos hβ2
  have hδ1 : β 2 / 2 < 1 := by linarith
  have hinv : (β 2 / 2)⁻¹ = 2 / β 2 := by field_simp
  have hf := torPlaneKL_FXC1 Λ hR hδ hδ1 (by nlinarith) (by
    rw [hinv]
    calc 4 * (R * (2 / β 2)) = 8 * R / β 2 := by field_simp; ring
      _ ≤ _ := hLp) pt
  exact scaledSplittingRank_eq_two_of_thin_plane_only_SMR (D := 0) hf (fun _ _ => by simp)
    (by linarith) (by linarith) (by linarith) hβ3

theorem torStratum_two_eq_univ_FXC1 (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ}
    (hβ2 : 0 < β 2) (hβ2' : β 2 ≤ 1 / 50) (hβ3 : β 3 ≤ 3 / 20) (hL2 : Λ.L 2 ≤ R * β 2)
    (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ) :
    scaledSplittingStratum.{0, 0} (fun _ : Tor_FXC1 Λ => R) (fun _ => hR) β 2 = univ :=
  eq_univ_of_forall fun p => torRank_eq_two_FXC1 Λ hR hβ2 hβ2' hβ3 hL2 hLp p

theorem torStratum_ne_two_empty_FXC1 (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ}
    (hβ2 : 0 < β 2) (hβ2' : β 2 ≤ 1 / 50) (hβ3 : β 3 ≤ 3 / 20) (hL2 : Λ.L 2 ≤ R * β 2)
    (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ) {k : Fin 4} (hk : k ≠ 2) :
    scaledSplittingStratum.{0, 0} (fun _ : Tor_FXC1 Λ => R) (fun _ => hR) β k = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => hk (Fin.ext ?_)
  change scaledSplittingRank.{0, 0} (fun _ : Tor_FXC1 Λ => R) (fun _ => hR) β p = k.val at hp
  rw [torRank_eq_two_FXC1 Λ hR hβ2 hβ2' hβ3 hL2 hLp p] at hp
  exact hp.symm


/-- **A two-splitting at the scale `R`** (the rescaled `HasEuclideanSplitting` at every point). -/
theorem torHasSplitting_two_FXC1 (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ}
    (hβ2 : 0 < β 2) (hβ2' : β 2 ≤ 1 / 50) (hβ3 : β 3 ≤ 3 / 20) (hL2 : Λ.L 2 ≤ R * β 2)
    (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ) (p : Tor_FXC1 Λ) :
    @HasEuclideanSplitting.{0, 0} (Tor_FXC1 Λ) ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) p 2
      (β 2) :=
  (((scaledSplittingRank_eq_iff (ρ := fun _ : Tor_FXC1 Λ => R) (hρ := fun _ => hR)).mp
    (torRank_eq_two_FXC1 Λ hR hβ2 hβ2' hβ3 hL2 hLp p)).2.1 (by norm_num))

/-- **The torus has no strong edge point** (`b ≤ 1/6`, `s ≤ 1/7`, `b + s ≤ 1/100`). -/
theorem torNotEdge_FXC1 (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ}
    (hβ2 : 0 < β 2) (hβ2' : β 2 ≤ 1 / 50) (hβ3 : β 3 ≤ 3 / 20) (hL2 : Λ.L 2 ≤ R * β 2)
    (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ) {Δ b s : ℝ} (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7)
    (hbs : b + s ≤ 1 / 100) (p : Tor_FXC1 Λ) :
    ¬ @isEdgePoint.{0, 0} (Tor_FXC1 Λ) ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) p Δ b s :=
  @not_isEdgePoint_of_hasEuclideanSplitting_two_FXC1.{0, 0} (Tor_FXC1 Λ)
    ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) p (β 2) Δ b s (by linarith)
    (torHasSplitting_two_FXC1 Λ hR hβ2 hβ2' hβ3 hL2 hLp p) hb hs hbs

end DifferentialGeometry.Geometry.Collapse
