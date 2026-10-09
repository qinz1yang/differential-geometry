import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightNormalized

/-!
# BCG02 at a circle reference: value AND differential clause with ONE unit row (lane BCG-7, G5)

Blueprint 207B, BCG02 (`B:8822–8958`) at a circle reference of the regionalised packets
`LocalPacketsOn` (complete σ-compact carrier): for `θ < 1` and the no-three quality `ν`, an early
`σ` (circle quality `3β₂ ≤ σ`) and a rank-one quality bound `η`; at every circle centre `j`, every
rank-one Kleiner–Lott approximation `φ` of `(X, ρ(j)⁻¹d, j)` (`ε₁ ≤ η`) whose real coordinate is a
function `U`, with `‖DU‖ ≤ 1 + δ_N` in `R⁻²g` and BCG02.b (`|DU(w) − (U(γ_w ℓ) − U(x))/ℓ| ≤ ρ(j)ℓ` along
the normalized test geodesics, `ℓ ≤ 500`) on `D_a = B(j, 10ρ(j))`, gives ONE unit row `A`
(`AA† = id`) with

* the value clause `‖e₀U(y) − A(η_j(y) − η_j(j))‖ < θ` on `D_a` (`η_j` the circle chart coordinate), and
* the differential clause `‖DU − (A Dη_j)₀‖ < θ` in the `R⁻²g` normalization at every point of `D_a`.

Requests: `γ, β₂, δ_N ≤ θ²/10⁷`, `ρ(j) ≤ θ²/10¹⁰` (BCG02: "choose the reference adapted qualities, raw
errors and cusp norm errors below `θ²/10⁸`, and impose `2r∂(12L + 1000) < θ²/10⁸`"; here the circle
case with its own constants). Route: TCP02's pair kernel (`tcp02_pair_complete_BCG1`) at the error
`θ²/10⁷` gives `A` and the raw alignment on `B(j, 1000ρ(j))`; the value clause as in
`bcg02_circle_value_of_split_BCG1`; the differential clause by `bcg02_differential_normalized_circle_BCG7`
at the normalized metric with the circle `test` and `lipschitz` fields (`norm_mvfderiv_le_of_lipschitz_rescale_BCG7`).
The binding to the boundary height (`U = U_b`, BCUSP-1's B4 certificates through
`bcg02_taylor_test_BCG7`, `abs_mvfderiv_affineHeight_completion_le_BCG7`) is the next group.

* `bcg02_circle_differential_of_split_BCG7`; consumer `bcg02_circle_value_real_BCG7` (the value clause
  in real form `|U(y) − (A(η_j(y) − η_j(j)))₀| < θ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **BCG02 at a circle reference, value and differential clause with one row** (abstract step; see the
module docstring). -/
theorem bcg02_circle_differential_of_split_BCG7 {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}
      (F : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        U₁ U₂),
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → σ⁻¹ ≤ Lmax → γ ≤ θ ^ 2 / 10000000 →
      β 2 ≤ θ ^ 2 / 10000000 →
      ∀ (j : X) (hj : j ∈ F.circle.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∀ U : X → ℝ, (∀ y, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
          _ _ _ _ φ y).fst = U y) →
      ∀ {δN : ℝ}, 0 ≤ δN → δN ≤ θ ^ 2 / 10000000 → ρ j ≤ θ ^ 2 / 10000000000 →
      (∀ x, dist x j < 10 * ρ j → ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) U x u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u)) →
      (let hMc : CompleteSpace X := ‹CompleteSpace X›;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR;
        ∀ x ∈ ball j 10, ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 500 → |mvfderiv 𝓘(ℝ, E3) U x w -
            (U (intrinsicGeodesic gR hnR x w ℓ) - U x) / ℓ| ≤ ρ j * ℓ) →
      ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        (∀ y, dist y j < 10 * ρ j →
          ‖EuclideanSpace.single 0 (U y) -
            A ((let c := F.circle.chart j hj;
                letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord y) -
              (let c := F.circle.chart j hj;
                letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j))‖ < θ) ∧
        ∀ x, dist x j < 10 * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) U x u -
            A (mvfderiv 𝓘(ℝ, E3) (let c := F.circle.chart j hj;
                letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord) x u) 0| ≤
            θ' * Real.sqrt
              ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  obtain ⟨σ, hσ, hσ1, hpair⟩ := tcp02_pair_complete_BCG1 (E₀ := θ ^ 2 / 10000000)
    (by positivity) hν hν1 (j := 1) le_rfl one_le_two
  obtain ⟨η, hη, hpair⟩ := hpair 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX instC instM hXc instS g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂
    F hν3 hβ3 hβ2 hσL hγθ hβθ j hj Tm _ t₀ ε₁ hε₁ φ U hU δN hδN0 hδN hρθ hnorm htay
  have hρj := hρ j
  have hjU : j ∈ U₁ := (F.circle.centres_subset hj).1
  let Ad := F.circleAdapted j hj
  let _ := Ad.instY
  obtain ⟨φ', hφ'⟩ := exists_finOne_split_KA3 φ
  have hsec := F.sectional_BCG1 hσ (by linarith) hσL hjU
  have hno := F.circle.no_three_BCG1 hj hν3 hβ3
  have hr1 : ρ j / ρ j = 1 := div_self hρj.ne'
  obtain ⟨A, hA, hal⟩ := hpair X g hmetric j j (ρ j) (ρ j) hρj hρj (by rw [hr1]; norm_num)
    (by rw [hr1]; norm_num) (by rw [dist_self, zero_mul]) hsec hno Tm Ad.Y t₀ Ad.a hε₁ hβ2 φ'
    Ad.split
  have hAn := ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 A hA
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hs0 : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = 0 := by
    ext i
    simp
  -- the raw comparison `|U − (Aψ₁)₀| < E` on `B(j, 1000ρ(j))`
  have hraw : ∀ y, dist y j < 1000 * ρ j →
      |U y - A (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
        Ad.split y).fst 0| < θ ^ 2 / 10000000 := by
    intro y hy
    have hmain := hal y hy
    rw [hr1, one_smul, one_smul, hφ' y, hφ' j, hφj, hs0, sub_zero, hU y,
      norm_single_sub_BCG7] at hmain
    exact hmain
  have hcj : (let c := F.circle.chart j hj;
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord j) = 0 := by
    let c := F.circle.chart j hj
    have hc := F.circle.chart_center j hj
    let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)
    have h0 := c.coord_center
    rw [hc] at h0
    exact h0
  have hθ2 : θ ^ 2 < θ := by nlinarith
  have hγpos : 0 < γ := by
    have h := Ad.adapted j (by
      change (ρ j)⁻¹ * dist j j < 200
      rw [dist_self, mul_zero]
      norm_num)
    exact lt_of_le_of_lt (norm_nonneg _) h
  refine ⟨A, hA, fun y hy => ?_, fun x hx => ?_⟩
  · -- the value clause with the same row
    have hyR : y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200 := by
      change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist y j < 200
      rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hρj]
      linarith
    have had : ‖(let c := F.circle.chart j hj;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord y) -
        (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
          Ad.split y).fst‖ < γ := Ad.adapted y hyR
    rw [hcj, sub_zero]
    set ψy := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      Ad.split y).fst
    set cy := (let c := F.circle.chart j hj;
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord y)
    have h1 : ‖EuclideanSpace.single 0 (U y) - A ψy‖ < θ ^ 2 / 10000000 := by
      rw [norm_single_sub_BCG7]
      exact hraw y (by linarith)
    have h2 : ‖A (ψy - cy)‖ ≤ ‖ψy - cy‖ := by
      calc ‖A (ψy - cy)‖ ≤ ‖A‖ * ‖ψy - cy‖ := A.le_opNorm _
        _ ≤ 1 * ‖ψy - cy‖ := by gcongr
        _ = ‖ψy - cy‖ := one_mul _
    have h3 : ‖ψy - cy‖ < γ := by rw [norm_sub_rev]; exact had
    have hsplit : EuclideanSpace.single 0 (U y) - A cy =
        (EuclideanSpace.single 0 (U y) - A ψy) + A (ψy - cy) := by
      rw [map_sub]
      abel
    calc ‖EuclideanSpace.single 0 (U y) - A cy‖
        = ‖(EuclideanSpace.single 0 (U y) - A ψy) + A (ψy - cy)‖ := by rw [hsplit]
      _ ≤ ‖EuclideanSpace.single 0 (U y) - A ψy‖ + ‖A (ψy - cy)‖ := norm_add_le _ _
      _ < θ ^ 2 / 10000000 + γ := by linarith
      _ ≤ θ := by linarith
  · -- the differential clause, at the normalized metric
    let c := F.circle.chart j hj
    have hc := F.circle.chart_center j hj
    let cc : X → ℝ² := (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord)
    have hxR : x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 10 := by
      change (ρ j)⁻¹ * dist x j < 10
      rw [inv_mul_lt_iff₀ hρj]
      linarith
    have hraw' : ∀ y, @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist y j < 411 →
        |U y - A (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
          Ad.split y).fst 0| < θ ^ 2 / 10000000 := by
      intro y hy
      change (ρ j)⁻¹ * dist y j < 411 at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hraw y (by linarith)
    have hnU' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 10,
        ∀ u : TangentSpace 𝓘(ℝ, E3) y, |mvfderiv 𝓘(ℝ, E3) U y u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 10 at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hnorm y (by linarith) u
    have hlip : ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
        ‖cc y - cc z‖ ≤ (1 + γ) * ((ρ j)⁻¹ * dist y z) := by
      intro y hy z hz
      have hL := Ad.lipschitz
      have hyR : y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200 := by
        change (ρ j)⁻¹ * dist y j < 200
        rw [inv_mul_lt_iff₀ hρj]
        rw [mem_ball] at hy
        linarith
      have hzR : z ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200 := by
        change (ρ j)⁻¹ * dist z j < 200
        rw [inv_mul_lt_iff₀ hρj]
        rw [mem_ball] at hz
        linarith
      have h := @LipschitzOnWith.dist_le_mul X ℝ² (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace
        _ _ _ _ hL y hyR z hzR
      rw [Real.coe_toNNReal _ (by linarith)] at h
      rw [dist_eq_norm] at h
      exact h
    have hnc' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 10,
        ∀ u : TangentSpace 𝓘(ℝ, E3) y, ‖mvfderiv 𝓘(ℝ, E3) cc y u‖ ≤ (1 + γ) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 10 at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      have hyb : y ∈ ball j (200 * ρ j) := mem_ball.mpr (by linarith)
      have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) cc y := by
        have hcm : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ cc
            (@ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200) := by
          let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)
          have h := c.contMDiffOn_coord
          rw [hc] at h
          exact h
        have hopen : IsOpen (@ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace
            j 200) := @isOpen_ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200
        have hyR : y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200 := by
          change (ρ j)⁻¹ * dist y j < 200
          rw [inv_mul_lt_iff₀ hρj]
          linarith
        exact ((hcm.contMDiffAt (hopen.mem_nhds hyR)).mdifferentiableAt (by simp))
      exact norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball hyb hdiff
        (by linarith) hρj hlip u
    have htest := Ad.test
    let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj)
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    exact @bcg02_differential_normalized_circle_BCG7 E3 _ _ _ _ E3 _ 𝓘(ℝ, E3) _ X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) instC instM instS
      (radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj))
      (radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hρj))
      ((mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hρj)).mpr hXc)
      (radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hρj))
      gR hnR Ad.Y Ad.instY j Ad.a (β 2) Ad.split A hA cc U θ γ (θ ^ 2 / 10000000) δN (ρ j) hθ hθ1
      hγpos.le (by positivity) hδN0 hρj.le hγθ le_rfl hβθ hδN hρθ hraw' htest hnc' hnU'
      (fun y hy w hw ℓ hℓ hℓ' => htay y hy w hw ℓ hℓ (by linarith)) x hxR

/-- **Consumer: the value clause in real form.** In `ℝ¹`, `‖e₀a − v‖ = |a − v₀|`; so the value clause of
`bcg02_circle_differential_of_split_BCG7` reads `|U(y) − (A(η_j(y) − η_j(j)))₀| < θ`. -/
theorem bcg02_circle_value_real_BCG7 {θ : ℝ} (A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1)) (u : ℝ)
    (d : ℝ²) (h : ‖EuclideanSpace.single 0 u - A d‖ < θ) : |u - A d 0| < θ := by
  rwa [norm_single_sub_BCG7] at h

end DifferentialGeometry.Geometry.Collapse
