import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeChartTests
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparisonApplications

/-!
# EGP04 on the boundary family: the listed `edgeB` charts (lane B-PORT-EDGE, G1)

GENERATED from `Geometry/Fibration/ActualEdgeAffineComparison.lean` (sections `Pair`, `Row`) and
`…/ActualEdgeAffineComparisonApplications.lean` by `build-logs/scratch/B-PORT-EDGE/gen_egp04e.py`
(tables of `portedge.py`); do not edit by hand, re-run the script.

EGP04's (EC) value AND derivative clauses for every listed `edgeB` chart `j ∈ J_e(i)` on
`D_i = B(i, 20Δρ(i))` (`egp04_edge_pair_KC2_BAUGP`, row `egp04_edge_BAUGP`, consumer
`egp04_edge_at_centre_BAUGP`) on the enriched boundary base family. Substitution table as in
`BoundaryPortEdgeComparisonList.lean`; the edge coordinate's Lipschitz bound is lane B-PORT-A's
`EdgeFamilyOn.coord_lipschitz_KA2_BAUGP`; FC18 (ii) is BAUG-A's
`LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA`. Reused unchanged (generic):
`sqrt_inv_sq_mul_KC2`, `abs_sub_le_of_common_unit_KC2`, `exists_raw_offset_lift_KC2`,
`egp04_riesz_budget_KC2`. This supersedes no boundary statement: the value clause alone was
`egp04_edgeB_value_BFRZ` (lane B-EGP04-EC).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open scoped InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian.Exponential

section Pair

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The derivative of an edge coordinate in reference units: `|s_j dη_j(w)| ≤ (1 + σ)√(R_i⁻² g)`
on the chart ball. -/
theorem EdgeFamilyOn.abs_deriv_le_KC2_BAUGP
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hσ : 0 ≤ 1 + σc) {i j : X}
    (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x w| ≤
      (1 + σc) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hrj := hρ j
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.coord_BAUGA j) x :=
    ((F.contMDiffOn_coord_BAUGA hj).contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
    (fun y _ z _ => F.coord_lipschitz_KA2_BAUGP hσ hj y z) w
  rw [sqrt_inv_sq_mul_KC2 hri, abs_mul, abs_of_pos (div_pos hrj hri)]
  have hq := Real.sqrt_nonneg (g.inner x w w)
  calc ρ j / ρ i * |mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x w|
      ≤ ρ j / ρ i * ((1 + σc) / ρ j * Real.sqrt (g.inner x w w)) :=
        mul_le_mul_of_nonneg_left h (div_pos hrj hri).le
    _ = (1 + σc) * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by
        field_simp

/-- **EGP04 for one listed edge chart** (`j ∈ J_e`), given EGP03's (ER) with the sign `a` on
`B(i, 600Δρ(i))`: on `D_i = B(i, 20Δρ(i))` the value and the derivative clauses of (EC). -/
theorem egp04_edge_pair_KC2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {θ E a : ℝ} (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμ1 : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hbθ : b ≤ θ ^ 2 / 10 ^ 8) (hbL : b ≤ 1 / (1000 * (1000000 * Δ)))
    (hE : E ≤ θ ^ 2 / 10 ^ 8) (hσc : σc ≤ θ ^ 2 / 10 ^ 8) (hμ : μ * Δ < θ / 100)
    {i j : X} (hi : i ∈ L.edgeB.centres) (hj : j ∈ egpEdgeList_BAUGP L i)
    (ha : a = 1 ∨ a = -1)
    (hER : ∀ x ∈ ball i (600 * Δ * ρ i), |ρ j / ρ i * egpRaw_BAUGP L.edgeB j x - a * egpRaw_BAUGP L.edgeB i x -
      ρ j / ρ i * egpRaw_BAUGP L.edgeB j i| < E) :
    ∀ x ∈ ball i (20 * Δ * ρ i),
      |ρ j / ρ i * L.edgeB.coord_BAUGA j x - (a * L.edgeB.coord_BAUGA i x + ρ j / ρ i * egpRaw_BAUGP L.edgeB j i)| <
          θ ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
          |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
            a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x w| < θ := by
  intro x hx
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  obtain ⟨hjc, y₀, hy1, hy2⟩ := hj
  have h14 := (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ1 hτ hΔΛ hjc).1 hy1
  have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
    refine ⟨y₀, closedBall_subset_closedBall ?_ h14, hy2⟩
    nlinarith [hρ j]
  obtain ⟨hs1, hs2, hdij, hsub⟩ := edge_comparison_list_edge_bounds hρL hri hrj hΔ hLΛ' hm
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hxj57 : dist x j < 57 * Δ * ρ j := hsub hx
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hΔρj : 0 < Δ * ρ j := mul_pos hΔ0 hrj
  have hx100i : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hx100j : x ∈ ball j (100 * Δ * ρ j) := mem_ball.mpr (by linarith)
  have hx600 : x ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hE0 : 0 < E := lt_of_le_of_lt (abs_nonneg _) (hER i (mem_ball_self (by positivity)))
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have habs : |a| = 1 := by rcases ha with rfl | rfl <;> simp
  have hsj : 0 < ρ j / ρ i := div_pos hrj hri
  refine ⟨?_, ?_⟩
  · -- the value clause
    have hvj := L.edgeB.value_KC2_BAUGP hjc hx100j
    have hvi := L.edgeB.value_KC2_BAUGP hi hx100i
    have hμΔ0 : 0 < μ * Δ := lt_of_le_of_lt (abs_nonneg _) hvi
    have hval := abs_affine_value_error_le hsj.le habs hvj.le hvi.le
      (hER x hx600).le
    have h1 : ρ j / ρ i * (μ * Δ) ≤ 101 / 100 * (μ * Δ) :=
      mul_le_mul_of_nonneg_right hs2.le hμΔ0.le
    linarith
  · -- the derivative clause
    obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2_BAUGP L.edgeB hi
    have hb0 : 0 < b := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Bi))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b ψ
    have hbinv : 1000 * (1000000 * Δ) ≤ b⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hb0]
      simpa only [one_div] using hbL
    have hbΔ : b * (1000 * (1000000 * Δ)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hbL
      linarith
    have hbb : b ≤ b * Δ := le_mul_of_one_le_right hb0.le hΔ
    have hb1 : 5 * b ≤ Δ := by linarith
    have hxiR : (ρ i)⁻¹ * dist x i < 20 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hri hx
    have h400 : |400 * Δ * a| = 400 * Δ := by
      rw [abs_mul, habs, mul_one, abs_of_pos (by positivity)]
    obtain ⟨y, hyR, hyu, hyd⟩ := @exists_raw_offset_lift_KC2 X Bi
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) mBi i qi b ψ x (400 * Δ * a) (by
        change |400 * Δ * a| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b < b⁻¹
        rw [h400]
        linarith)
    change (ρ i)⁻¹ * dist y i < |400 * Δ * a| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b at hyR
    change abs ((ρ i)⁻¹ * dist x y - |400 * Δ * a|) < 3 * b at hyd
    rw [hψx, hψx] at hyu
    rw [h400] at hyR hyd
    -- the endpoint `y`
    have hyiR : (ρ i)⁻¹ * dist y i < 441 * Δ := by linarith
    have hyi : dist y i < 441 * Δ * ρ i := by
      rw [inv_mul_lt_iff₀ hri] at hyiR
      linarith
    set ℓ := (ρ i)⁻¹ * dist x y with hℓ
    have hℓ1 : 400 * Δ - 3 * b < ℓ := by linarith [(abs_lt.mp hyd).1]
    have hℓ2 : ℓ < 400 * Δ + 3 * b := by linarith [(abs_lt.mp hyd).2]
    have hdxy : 399 * Δ * ρ i < dist x y := by
      have h := hℓ1
      rw [hℓ, lt_inv_mul_iff₀ hri] at h
      have h' := mul_le_mul_of_nonneg_right (show 399 * Δ ≤ 400 * Δ - 3 * b by linarith) hri.le
      linarith
    have hxy : x ≠ y := by
      intro h
      rw [h, dist_self] at hdxy
      linarith
    have hy1000i : y ∈ ball i (1000 * Δ * ρ i) := mem_ball.mpr (by linarith)
    have hy600 : y ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
    have hρij : 99 / 100 * ρ i < ρ j := by
      have := (lt_div_iff₀ hri).mp hs1
      linarith
    have hρji : ρ j < 101 / 100 * ρ i := by
      have := (div_lt_iff₀ hri).mp hs2
      linarith
    have hy1000j : y ∈ ball j (1000 * Δ * ρ j) := by
      rw [mem_ball]
      have ht := dist_triangle y i j
      have h' := mul_lt_mul_of_pos_left hρij hΔ0
      linarith
    have hsepi : 100 * Δ * ρ i < dist x y := by linarith
    have hsepj : 100 * Δ * ρ j < dist x y := by
      have h' := mul_lt_mul_of_pos_left hρji hΔ0
      linarith
    -- one minimizing direction of the reference metric and the two original tests
    obtain ⟨v, hv, hgeo⟩ := exists_minimizing_direction_KC2_BAUGP g hmetric hri hxy
    have hti := L.edgeB.test_at_scale_KC2_BAUGP hi hri hx100i hy1000i hsepi v hv hgeo
    have htj := L.edgeB.test_at_scale_KC2_BAUGP hjc hri hx100j hy1000j hsepj v hv hgeo
    rw [div_self hri.ne', one_mul, one_mul] at hti
    have hσc0 : 0 < σc := lt_of_le_of_lt (abs_nonneg _) hti
    -- the gains
    set Gi := a * (egpRaw_BAUGP L.edgeB i y - egpRaw_BAUGP L.edgeB i x) with hGi
    set Gj := ρ j / ρ i * (egpRaw_BAUGP L.edgeB j y - egpRaw_BAUGP L.edgeB j x) with hGj
    have hGi1 : 400 * Δ - 2 * b ≤ Gi := by
      have h := (abs_lt.mp hyu)
      rcases ha with rfl | rfl
      · rw [hGi]; linarith [h.1]
      · rw [hGi]; linarith [h.2]
    have hinc : |Gj - Gi| < 2 * E := by
      have h1 := hER x hx600
      have h2 := hER y hy600
      have hsplit : Gj - Gi = (ρ j / ρ i * egpRaw_BAUGP L.edgeB j y - a * egpRaw_BAUGP L.edgeB i y -
          ρ j / ρ i * egpRaw_BAUGP L.edgeB j i) -
          (ρ j / ρ i * egpRaw_BAUGP L.edgeB j x - a * egpRaw_BAUGP L.edgeB i x -
            ρ j / ρ i * egpRaw_BAUGP L.edgeB j i) := by
        rw [hGi, hGj]; ring
      rw [hsplit]
      calc _ ≤ _ := abs_sub _ _
        _ < E + E := add_lt_add h2 h1
        _ = 2 * E := by ring
    have hGi2 : ℓ - (5 * b + 2 * E) ≤ Gi := by linarith
    have hGj2 : ℓ - (5 * b + 2 * E) ≤ Gj := by linarith [(abs_lt.mp hinc).1]
    have hℓ0 : 0 < 400 * Δ - 3 * b := by linarith
    have htesti : |a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x v - Gi / ℓ| ≤ σc := by
      have he : a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x v - Gi / ℓ =
          a * (mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x v -
            (egpRaw_BAUGP L.edgeB i y - egpRaw_BAUGP L.edgeB i x) / ℓ) := by
        rw [hGi]; ring
      rw [he, abs_mul, habs, one_mul]
      exact hti.le
    have htestj : |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x v - Gj / ℓ| ≤ σc := htj.le
    have he0 : 0 ≤ 5 * b + 2 * E := by positivity
    have hsi := ContinuousLinearMap.saturation_of_test_gain hℓ0 hℓ1.le he0 htesti hGi2
    have hsj' := ContinuousLinearMap.saturation_of_test_gain hℓ0 hℓ1.le he0 htestj hGj2
    set εs := σc + (5 * b + 2 * E) / (400 * Δ - 3 * b) with hεs
    have hεs0 : 0 ≤ εs := by positivity
    have hfrac : (5 * b + 2 * E) / (400 * Δ - 3 * b) ≤ 7 * (θ ^ 2 / 10 ^ 8) := by
      rw [div_le_iff₀ hℓ0]
      have h1 : 1 ≤ 400 * Δ - 3 * b := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 7 * (θ ^ 2 / 10 ^ 8))
      linarith
    have hεθ : εs < θ ^ 2 / 10 ^ 6 := by
      have : 0 < θ ^ 2 := by positivity
      linarith
    -- the norm bounds in reference units
    have hσ1 : 0 ≤ 1 + σc := by linarith
    have hDj : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        |((ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x) w| ≤
          (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
      intro w
      rw [smul_apply, smul_eq_mul]
      refine (L.edgeB.abs_deriv_le_KC2_BAUGP hσ1 hjc hx100j w).trans ?_
      gcongr
      linarith [div_nonneg he0 hℓ0.le]
    have hDi : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        |(a • mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x) w| ≤
          (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
      intro w
      rw [smul_apply, smul_eq_mul, abs_mul, habs, one_mul]
      have h := L.edgeB.abs_deriv_le_KC2_BAUGP (i := i) hσ1 hi hx100i w
      rw [div_self hri.ne', one_mul] at h
      refine h.trans ?_
      gcongr
      linarith [div_nonneg he0 hℓ0.le]
    intro w hw
    have hsat := abs_sub_le_of_common_unit_KC2 g x (c := (ρ i)⁻¹ ^ 2) (by positivity)
      ((ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x)
      (a • mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x) hεs0 hDj hDi v hv
      (by rw [smul_apply, smul_eq_mul]; exact hsj')
      (by rw [smul_apply, smul_eq_mul]; exact hsi) w hw
    rw [smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul] at hsat
    exact hsat.trans_lt (egp04_riesz_budget_KC2 hεs0 hθ hθ1 hεθ)

end Pair

section Row

/-- **EGP04 (EC) for the listed edge charts on the actual family.** For `0 < θ < 1` there are a
curvature radius `Lc` and a raw quality `η₀` (EGP03 at `E = θ²/10⁸`, and `η₀ ≤ θ²/10⁸, 1/(1000L)`)
such that for every actual family `L` with EGP03's hypotheses, the tangential quality
`σc ≤ θ²/10⁸` and the separate value error `μΔ < θ/100`, every edge centre `i` and every
`j ∈ J_e` have one sign `a` with, on `D_i = B(i, 20Δρ(i))`,
`|s_j η_j − (a η_i + s_j u_j(i))| < θ` and `|s_j dη_j(w) − a dη_i(w)| < θ` for every unit vector
`w` of `ρ(i)⁻² g`. -/
theorem egp04_edge_BAUGP {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
        (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → ∀ i ∈ L.edgeB.centres, ∀ j ∈ egpEdgeList_BAUGP L i,
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
            |ρ j / ρ i * L.edgeB.coord_BAUGA j x -
                (a * L.edgeB.coord_BAUGA i x + ρ j / ρ i * egpRaw_BAUGP L.edgeB j i)| < θ ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x w| < θ := by
  have hE : (0 : ℝ) < θ ^ 2 / 10 ^ 8 := by positivity
  obtain ⟨Lc, η₃, hLc, hη₃, h3⟩ := egp03_row_BAUGP hΔ hβ₂ hβ₂1 hE
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₃ (min (θ ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * Δ)))), hLc,
    lt_min hη₃ (lt_min hE (by positivity)), ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLmax hΛ
    hLΛ hμ hτ hσc hμΔ i hi j hj
  obtain ⟨he, -⟩ := h3 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L
    (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ hμ hτ i hi
  obtain ⟨a, ha, hER⟩ := he j hj
  exact ⟨a, ha, egp04_edge_pair_KC2_BAUGP L hΔ hθ hθ1 hΛ hLΛ hμ hτ
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hb.trans ((min_le_right _ _).trans (min_le_right _ _))) le_rfl hσc hμΔ hi hj ha hER⟩

end Row


/-- **Consumer of `egp04_edge_BAUGP`**: (EC) at the reference centre `p_i ∈ D_i`. -/
theorem egp04_edge_at_centre_BAUGP {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
        (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → ∀ i ∈ L.edgeB.centres, ∀ j ∈ egpEdgeList_BAUGP L i,
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            |ρ j / ρ i * L.edgeB.coord_BAUGA j i -
                (a * L.edgeB.coord_BAUGA i i + ρ j / ρ i * egpRaw_BAUGP L.edgeB j i)| < θ ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) i, (ρ i)⁻¹ ^ 2 * g.inner i w w = 1 →
                |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) i w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) i w| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp04_edge_BAUGP hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLmax hΛ
    hLΛ hμ hτ hσc hμΔ i hi j hj
  obtain ⟨a, ha, hEC⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1
    hLmax hΛ hLΛ hμ hτ hσc hμΔ i hi j hj
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  exact ⟨a, ha, hEC i (mem_ball_self (by positivity))⟩

end DifferentialGeometry.Geometry.Collapse
