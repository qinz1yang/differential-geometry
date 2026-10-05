import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Metric.SupportComparisonLists

/-!
# EGP04 (EC), value clause, for pairs of revised edge charts `edgeB` (lane B-EGP04-EC)

Blueprint `master207B.tex`, EGP04 (`lem:fibration-edge-actual-comparison`): for a listed edge chart
`j ∈ J_e(i)` one sign `a` and the affine map `λ_j(t) = a t + c_j` with
`|U_j − λ_j(η_i)| < θ` on ALL of `D_i = B(p_i, 20Δρ(p_i))`, `U_j = s_j η_j`, `s_j = ρ(j)/ρ(i)`.
The closed row is `egp04_edge` (`LocalChartFamilyE`, `CompactSpace`); this is its value clause on
the boundary family's revised edge charts `edgeB` (BCF2-K "Supplier gap", optional G3b), on a
complete σ-compact carrier. The derivative clause is not stated (BCF02 does not use it).

* `egp04_edgeB_value_of_meet_BEC` (kernel tier, on the projection `LocalPacketsOnB`): for every
  revised edge centre `i` and every revised edge centre `j` whose closed `15Δρ(j)`-ball meets `D_i`,
  one sign `a` with `|s_j η_j(x) − (a η_i(x) + s_j η_j(i))| < θ` on `D_i`; EGP03's complete
  real-factor kernel `exists_sign_raw_alignment_real_complete_BCG1` at `H = 20Δ` (sign) plus the
  four value errors `μΔ` of `EdgeFamilyOn.exists_split_BCG1`; `c_j = s_j η_j(i)` is canonical.
* `egp04_edgeB_value_BEC` (row tier): the same for `j ∈ J_e(i)` = the revised edge centres whose
  cutoff support (`cutoff_BAUGA`) meets `D_i`, through `tsupport_edgeB_cutoff_subset_BAUGA`.
* `egp04_edgeB_value_BFRZ` (on the final boundary family `LocalPacketsOnBFRZ`, by projection).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **EGP04 (EC), value clause, for meeting pairs of revised edge charts** (kernel tier). For
`0 < θ`, an exclusion quality `ν < 10⁻⁶` and `Δ ≥ 1`: an early `σ` and a raw quality `η`; on every
enriched boundary base family with `σ⁻¹ ≤ Lmax`, `b ≤ η`, `3b ≤ σ`, `b(2(20Δ+1)) ≤ 1`,
`b, s < 10⁻⁶`, `10⁶ΔΛ < 10⁻⁵`, `μΔ < θ/100`, for every revised edge centre `i` and every revised
edge centre `j` with `B̄(j, 15Δρ(j)) ∩ D_i ≠ ∅` there is one sign `a` with
`|s_j η_j(x) − (a η_i(x) + s_j η_j(i))| < θ` for all `x ∈ D_i = B(i, 20Δρ(i))`. -/
theorem egp04_edgeB_value_of_meet_BEC {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs U₁ U₂ Ue₁ Ue₂),
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 → μ * Δ < θ / 100 →
      ∀ (i : X) (hi : i ∈ F.edgeB.centres) (j : X) (hj : j ∈ F.edgeB.centres),
      (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * F.edgeB.coord_BCG1 j hj x -
          (a * F.edgeB.coord_BCG1 i hi x + ρ j / ρ i * F.edgeB.coord_BCG1 j hj i)| < θ := by
  set H : ℝ := 20 * Δ with hH
  have hH0 : 0 < H := by rw [hH]; linarith
  set τ' : ℝ := min (θ / 200) (1 / (2 * (H + 1))) with hτdef
  have hτ : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτθ : τ' ≤ θ / 200 := min_le_left _ _
  have hτH : τ' ≤ 1 / (2 * (H + 1)) := min_le_right _ _
  have hτ1 : τ' < 1 := by
    have : 1 / (2 * (H + 1)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have ha : 20 * τ' ≤ H + 1 := by linarith
  have ha2 : 2 * (H + 1) ≤ τ'⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hτ]
    rwa [one_div] at hτH
  obtain ⟨σ, hσ, hσ1, hk⟩ := exists_sign_raw_alignment_real_complete_BCG1 hτ hτ1 hν
    (by linarith) ha ha2
  obtain ⟨η, hη, hk⟩ := hk (36 * Δ) (by positivity)
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    U₁ U₂ Ue₁ Ue₂ F hσL hbη h3b hbH hb6 hs6 hΛ hLΛ hμ i hi j hj hm
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  obtain ⟨hs1, hs2, hdij, hsub⟩ :=
    edge_comparison_list_edge_bounds F.lipschitz_scale hri hrj hΔ hLΛ' hm
  have hiU : i ∈ U₁ := F.edgeB_domain i hi (mem_ball_self (by positivity))
  have hsec := F.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hσL i hiU
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i 2 ν :=
    @not_hasEuclideanSplitting_two_of_isEdgePoint.{0, 0, 0} X
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) i Δ b s ν (F.edgeB.strong i hi) hb6 hs6 hν1
  obtain ⟨Yj, mYj, qj, fj, hcj0, hvalj⟩ := F.edgeB.exists_split_BCG1 hj
  obtain ⟨Yi, mYi, qi, fi, hci0, hvali⟩ := F.edgeB.exists_split_BCG1 hi
  obtain ⟨a, ha, hlin⟩ := hk X g hmetric ρ hρ i j hsec hno (by linarith) (by linarith)
    hdij.le Yj Yi qj qi hbη h3b hbH fj fi
  refine ⟨a, ha, fun x hx => ?_⟩
  have habs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hsj : 0 < ρ j / ρ i := div_pos hrj hri
  have hμΔ0 : 0 ≤ μ * Δ := by
    have := hvali i (by rw [dist_self]; positivity)
    linarith [abs_nonneg (F.edgeB.coord_BCG1 i hi i - (@KleinerLottApprox.toFun X _
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _ fi i).fst)]
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hxj : dist x j < 100 * Δ * ρ j := by
    have h := mem_ball.mp (hsub hx)
    nlinarith
  have hij : dist i j < 100 * Δ * ρ j := by
    have h := mem_ball.mp (hsub (mem_ball_self (by positivity : 0 < 20 * Δ * ρ i)))
    nlinarith
  have hxi100 : dist x i < 100 * Δ * ρ i := by nlinarith
  have hmain := hlin x (by rw [mem_ball]; nlinarith)
  set c := ρ j / ρ i with hcdef
  set φx := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _
    fj x).fst
  set φi := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _
    fj i).fst
  set ψx := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
    fi x).fst
  set ux := F.edgeB.coord_BCG1 j hj x
  set ui := F.edgeB.coord_BCG1 j hj i
  set vx := F.edgeB.coord_BCG1 i hi x
  have e1 : |ux - φx| < μ * Δ := hvalj x hxj
  have e2 : |ui - φi| < μ * Δ := hvalj i hij
  have e3 : |vx - ψx| < μ * Δ := hvali x hxi100
  have hc2 : c < 101 / 100 := hs2
  have hsplit : c * ux - (a * vx + c * ui) =
      (c * φx - a * ψx - c * φi) + c * (ux - φx) - a * (vx - ψx) - c * (ui - φi) := by ring
  have b1 : |c * (ux - φx)| ≤ 101 / 100 * (μ * Δ) := by
    rw [abs_mul, abs_of_pos hsj]
    exact mul_le_mul hc2.le e1.le (abs_nonneg _) (by norm_num)
  have b2 : |c * (ui - φi)| ≤ 101 / 100 * (μ * Δ) := by
    rw [abs_mul, abs_of_pos hsj]
    exact mul_le_mul hc2.le e2.le (abs_nonneg _) (by norm_num)
  have b3 : |a * (vx - ψx)| < μ * Δ := by rw [abs_mul, habs, one_mul]; exact e3
  rw [hsplit]
  calc |(c * φx - a * ψx - c * φi) + c * (ux - φx) - a * (vx - ψx) - c * (ui - φi)|
      ≤ |c * φx - a * ψx - c * φi| + |c * (ux - φx)| + |a * (vx - ψx)| +
          |c * (ui - φi)| := by
        have t1 := abs_sub (c * φx - a * ψx - c * φi + c * (ux - φx) - a * (vx - ψx))
          (c * (ui - φi))
        have t2 := abs_sub (c * φx - a * ψx - c * φi + c * (ux - φx)) (a * (vx - ψx))
        have t3 := abs_add_le (c * φx - a * ψx - c * φi) (c * (ux - φx))
        linarith
    _ < 50 * τ' + 101 / 100 * (μ * Δ) + μ * Δ + 101 / 100 * (μ * Δ) := by linarith
    _ ≤ θ := by linarith

/-- **EGP04 (EC), value clause, on the revised edge charts** (row tier). With in addition
`μ, τ ≤ 1/100`: for every revised edge centre `i` and every `j ∈ J_e(i)` (a revised edge centre
whose cutoff support meets `D_i`) one sign `a` with `|s_j η_j − (a η_i + s_j η_j(i))| < θ` on all
of `D_i`. -/
theorem egp04_edgeB_value_BEC {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs U₁ U₂ Ue₁ Ue₂),
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
      μ * Δ < θ / 100 →
      ∀ (i : X) (hi : i ∈ F.edgeB.centres) (j : X) (hj : j ∈ F.edgeB.centres),
      (tsupport (F.edgeB.cutoff_BAUGA j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * F.edgeB.coord_BCG1 j hj x -
          (a * F.edgeB.coord_BCG1 i hi x + ρ j / ρ i * F.edgeB.coord_BCG1 j hj i)| < θ := by
  obtain ⟨σ, hσ, hσ1, η, hη, h⟩ := egp04_edgeB_value_of_meet_BEC hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    U₁ U₂ Ue₁ Ue₂ F hσL hbη h3b hbH hb6 hs6 hΛ hLΛ hμ1 hτ hμ i hi j hj hm
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  obtain ⟨hsupp, -, -⟩ := F.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ1 hτ hΔΛ hj
  obtain ⟨y, hy1, hy2⟩ := hm
  have hm' : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
    refine ⟨y, closedBall_subset_closedBall ?_ (hsupp hy1), hy2⟩
    nlinarith [hρ j]
  exact h F hσL hbη h3b hbH hb6 hs6 hΛ hLΛ hμ i hi j hj hm'

/-- **EGP04 (EC), value clause, on the final boundary family `LocalPacketsOnBFRZ`** (projection of
`egp04_edgeB_value_BEC` to the enriched base family; same constants). -/
theorem egp04_edgeB_value_BFRZ {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
      (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM),
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
      μ * Δ < θ / 100 →
      ∀ (i : X) (hi : i ∈ F.edgeB.centres) (j : X) (hj : j ∈ F.edgeB.centres),
      (tsupport (F.edgeB.cutoff_BAUGA j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * F.edgeB.coord_BCG1 j hj x -
          (a * F.edgeB.coord_BCG1 i hi x + ρ j / ρ i * F.edgeB.coord_BCG1 j hj i)| < θ := by
  obtain ⟨σ, hσ, hσ1, η, hη, h⟩ := egp04_edgeB_value_BEC hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    U₁ U₂ Ue₁ Ue₂ oM F
  exact h F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB

end DifferentialGeometry.Geometry.Collapse
