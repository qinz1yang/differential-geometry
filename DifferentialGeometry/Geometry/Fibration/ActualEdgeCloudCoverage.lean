import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloud

/-!
# EGP07: the edge cloud coverage (Tier 4), FC27's (CS) test on the actual `π₂F`

Blueprint `master207B.tex`, EGP07 (`thm:fibration-actual-second-cloud`, B:5141–5225), proof,
last two paragraphs: "If `z ∈ S̃₂` with `|z − x| ≤ r(x)/Γ`, its positive `i` marker and FC03 give,
at every preimage `q`, `|η_i(q) − a| ≤ (1 + 7Δ)R/(1 − R) < Δ/10` … Conversely, for each
`u ∈ B̄(a, R)` … EGP05 supplies an actual point with `η_i = u` and `t < Δ/100`. It belongs to the
ORIGINAL enlargement and its image is within `e` of `Φ_i(u)`. FC25 now proves both coverage
directions with error `3q`, `q = 2e + C†R²/2` … its radial trimming also proves the open-ball
distance-to-set convention."

* `hausdorffEDist_ball_le_of_closedBall_KC5` (radial trimming): closed tests at every radius
  `0 < r < R` give the open test at `R` with the SAME error (a point at distance `r` from `x` is
  tested at radius `r`, where the witness is again in the open ball);
  `hausdorffEDist_le_ofReal_KC5`.
* `image_tangent_eq_mk'_KC5`: FC25's tangent image `{x + Tv}` is `AffineSubspace.mk' x (range T)`.
* Physical units of a graph `Φ_phys(u) = ρΦ(ρ⁻¹u)`: `contDiff_physGraph_KC5`,
  `fderiv_physGraph_KC5` (`DΦ_phys(ρa) = DΦ(a)`), `norm_iteratedFDeriv_physGraph_KC5`
  (`‖D²Φ_phys(u)‖ = ρ⁻¹‖D²Φ(ρ⁻¹u)‖`).
* `blockAxisCoord_KC5 τ` (`z ↦ ((z_τ).fst)₀`, norm `≤ 1`): FC25's coordinate projection `P`;
  `blockAxisCoord_projMap_KC5` (`P(π₂F(q)) = ρ(j)η_j(q)` where `ζ_j(q) = 1`).
* `egp07_localization_KC5` (FC03 on `π₂F`), `egp07_closed_test_KC5` (FC25 in physical units on
  closed balls), `egp07_coverage_point_KC5`: the open test
  `d_H(S̃₂ ∩ B(x, r/Γ), (x + range DΦ_i(a)) ∩ B(x, r/Γ)) ≤ Γr`, `r = Σρ(p')`, for ANY preimage `p'`
  of `x` (radii from FC27's (AS), `fc27_edge_cloud_scale`; budget `coverage_budget_lt_half`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Topology ENNReal Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Trimming

variable {H : Type*} [PseudoMetricSpace H]

/-- **Radial trimming.** If `x ∈ S ∩ A` and the closed tests
`d_H(S ∩ B̄(x, r), A ∩ B̄(x, r)) ≤ E` hold for every `0 < r < R`, then the open test
`d_H(S ∩ B(x, R), A ∩ B(x, R)) ≤ E` holds: a point at distance `r` from `x` is tested at radius
`r` itself, where the witness of the closed test is again in the open ball. -/
theorem hausdorffEDist_ball_le_of_closedBall_KC5 {S A : Set H} {x : H} (hxS : x ∈ S)
    (hxA : x ∈ A) {R : ℝ} {E : ℝ≥0∞}
    (hE : ∀ r, 0 < r → r < R →
      hausdorffEDist (S ∩ closedBall x r) (A ∩ closedBall x r) ≤ E) :
    hausdorffEDist (S ∩ ball x R) (A ∩ ball x R) ≤ E := by
  have key : ∀ {U W : Set H}, x ∈ W →
      (∀ r, 0 < r → r < R → hausdorffEDist (U ∩ closedBall x r) (W ∩ closedBall x r) ≤ E) →
      ∀ y ∈ U ∩ ball x R, infEDist y (W ∩ ball x R) ≤ E := by
    intro U W hxW hUW y hy
    have hyR : dist y x < R := mem_ball.mp hy.2
    rcases (dist_nonneg (x := y) (y := x)).eq_or_lt with h0 | hpos
    · have hx : x ∈ W ∩ ball x R := ⟨hxW, mem_ball_self (by linarith)⟩
      refine (infEDist_le_edist_of_mem hx).trans ?_
      rw [edist_dist, ← h0, ENNReal.ofReal_zero]
      exact zero_le
    · have hsub : W ∩ closedBall x (dist y x) ⊆ W ∩ ball x R :=
        inter_subset_inter_right _ (closedBall_subset_ball hyR)
      have hyU : y ∈ U ∩ closedBall x (dist y x) := ⟨hy.1, mem_closedBall.mpr le_rfl⟩
      exact (infEDist_anti hsub).trans
        ((infEDist_le_hausdorffEDist_of_mem hyU).trans (hUW _ hpos hyR))
  refine hausdorffEDist_le_of_infEDist (key hxA hE) (key hxS fun r hr hrR => ?_)
  rw [hausdorffEDist_comm]
  exact hE r hr hrR

/-- A real Hausdorff bound between two sets through `x` inside `B̄(x, R)` is an `ℝ≥0∞` bound. -/
theorem hausdorffEDist_le_ofReal_KC5 {S A : Set H} {x : H} (hxS : x ∈ S) (hxA : x ∈ A)
    {R c : ℝ} (hS : S ⊆ closedBall x R) (hA : A ⊆ closedBall x R) (hc : hausdorffDist S A ≤ c) :
    hausdorffEDist S A ≤ ENNReal.ofReal c := by
  have hne : hausdorffEDist S A ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨x, hxS⟩ ⟨x, hxA⟩
      (isBounded_closedBall.subset hS) (isBounded_closedBall.subset hA)
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hc

end Trimming

section Plane

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The tangent image `{x + T v}` of FC25 is the affine plane `x + range T`. -/
theorem image_tangent_eq_mk'_KC5 (T : E →L[ℝ] F) (x : F) :
    (fun v => x + T v) '' (univ : Set E) =
      (AffineSubspace.mk' x (LinearMap.range (T : E →ₗ[ℝ] F)) : Set F) := by
  ext y
  simp only [mem_image, mem_univ, true_and, SetLike.mem_coe, AffineSubspace.mem_mk',
    vsub_eq_sub, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by abel⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [hv]; abel⟩

end Plane

section Physical

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Physical units of a graph `Φ : ℝ → F`: `Φ_phys(u) = ρ Φ(ρ⁻¹u)` is smooth when `Φ` is. -/
theorem contDiff_physGraph_KC5 {Φ : ℝ → F} {n : WithTop ℕ∞} (hΦ : ContDiff ℝ n Φ) (ρ : ℝ) :
    ContDiff ℝ n (fun u : ℝ => ρ • Φ (ρ⁻¹ • u)) :=
  (hΦ.comp (contDiff_const_smul ρ⁻¹)).const_smul ρ

/-- Physical units do not change the derivative at corresponding points:
`DΦ_phys(ρa) = DΦ(a)`. -/
theorem fderiv_physGraph_KC5 {Φ : ℝ → F} {ρ a : ℝ} (hρ : ρ ≠ 0) (hΦ : DifferentiableAt ℝ Φ a) :
    fderiv ℝ (fun u : ℝ => ρ • Φ (ρ⁻¹ • u)) (ρ * a) = fderiv ℝ Φ a := by
  have ha : ρ⁻¹ • (ρ * a) = a := by
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hρ, one_mul]
  have hin : HasFDerivAt (fun u : ℝ => ρ⁻¹ • u) (ρ⁻¹ • ContinuousLinearMap.id ℝ ℝ) (ρ * a) :=
    (hasFDerivAt_id (ρ * a)).const_smul ρ⁻¹
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ a) (ρ⁻¹ • (ρ * a)) := by
    rw [ha]
    exact hΦ.hasFDerivAt
  have hcomp := (hΦ'.comp (ρ * a) hin).const_smul ρ
  refine (HasFDerivAt.fderiv (f := fun u : ℝ => ρ • Φ (ρ⁻¹ • u)) hcomp).trans ?_
  ext
  simp only [smul_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul, smul_smul, mul_inv_cancel₀ hρ, one_smul]

/-- The Hessian in physical units: `‖D²Φ_phys(u)‖ = ρ⁻¹‖D²Φ(ρ⁻¹u)‖` (`ρ > 0`). -/
theorem norm_iteratedFDeriv_physGraph_KC5 {Φ : ℝ → F} {ρ : ℝ} (hρ : 0 < ρ)
    (hΦ : ContDiff ℝ 2 Φ) (u : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun u : ℝ => ρ • Φ (ρ⁻¹ • u)) u‖ =
      ρ⁻¹ * ‖iteratedFDeriv ℝ 2 Φ (ρ⁻¹ • u)‖ := by
  have hin : ContDiff ℝ 2 (fun u : ℝ => Φ (ρ⁻¹ • u)) := hΦ.comp (contDiff_const_smul ρ⁻¹)
  rw [iteratedFDeriv_const_smul_apply' hin.contDiffAt, iteratedFDeriv_comp_const_smul ρ⁻¹ hΦ]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, abs_pow, abs_inv]
  field_simp

end Physical

section OwnCoordinate

variable {κ : Type*}

/-- The coordinate of block `τ` on its axis: `z ↦ ((z_τ).fst)₀`. -/
def blockAxisCoord_KC5 (τ : κ) : BlockSpace (fun _ : κ => ℝ²) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).comp
    ((WithLp.fstL 2 ℝ ℝ² ℝ).comp (PiLp.proj 2 (fun _ : κ => WithLp 2 (ℝ² × ℝ)) τ))

theorem blockAxisCoord_apply_KC5 (τ : κ) (z : BlockSpace (fun _ : κ => ℝ²)) :
    blockAxisCoord_KC5 τ z = (z τ).fst 0 :=
  rfl

theorem norm_blockAxisCoord_le_KC5 [Fintype κ] (τ : κ) (z : BlockSpace (fun _ : κ => ℝ²)) :
    ‖blockAxisCoord_KC5 τ z‖ ≤ ‖z‖ := by
  rw [blockAxisCoord_apply_KC5]
  calc ‖(z τ).fst 0‖ ≤ ‖(z τ).fst‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖z τ‖ := WithLp.norm_fst_le (x := z τ)
    _ ≤ ‖z‖ := PiLp.norm_apply_le _ _

theorem blockAxisCoord_axis_KC5 (τ : κ) (z : BlockSpace (fun _ : κ => ℝ²)) {a m : ℝ}
    (hz : z τ = WithLp.toLp 2 (planeAxis a, m)) : blockAxisCoord_KC5 τ z = a := by
  rw [blockAxisCoord_apply_KC5, hz, planeAxis_apply]
  simp

end OwnCoordinate

section Coverage

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **EGP07, localization (FC03 on `π₂F`).** If `p ∈ B(j, 100Δρ(j))` has `|η_j(p)| ≤ 7Δ`,
`t(p) ≤ 8Δ` and `|π₂F(q) − π₂F(p)| ≤ Rρ(j)` with `0 ≤ R < 1/100`, then `q ∈ B(j, 100Δρ(j))`,
`|η_j(q) − η_j(p)| < Δ/10` and `|η_j(q)| < 8Δ`. -/
theorem egp07_localization_KC5 (hΔ : 1 ≤ Δ) (j : L.edge.finite_centres.toFinset) {p q : X}
    (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hηp : |L.edge.coord j.1 p| ≤ 7 * Δ)
    (htp : cgpHeight L p ≤ 8 * Δ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 100)
    (hpq : dist (cgpProjMap L Z (cgpQ2Tags L Z) q) (cgpProjMap L Z (cgpQ2Tags L Z) p) ≤
      R * ρ j.1) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      |L.edge.coord j.1 q - L.edge.coord j.1 p| < Δ / 10 ∧ |L.edge.coord j.1 q| < 8 * Δ := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hrj := hρ j.1
  have hΔ0 : 0 < Δ := by linarith
  have hcutp : L.edge.cutoff j.1 p = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hj hp (by linarith) htp
  obtain ⟨e', he'def⟩ : ∃ e', e' = (R + 1 / 100) / 2 := ⟨_, rfl⟩
  have he'0 : 0 < e' := by rw [he'def]; linarith
  have he'R : R < e' := by rw [he'def]; linarith
  have he'1 : e' < 1 / 100 := by rw [he'def]; linarith
  have hblk := dist_block_le_projMap_GAF L Z (edge_mem_cgpQ2Tags L Z j) q p
  have hblk' : dist (WithLp.toLp 2 ((ρ j.1 * L.edge.cutoff j.1 q) •
      planeAxis (L.edge.coord j.1 q), ρ j.1 * L.edge.cutoff j.1 q))
      (WithLp.toLp 2 ((ρ j.1 * 1) • planeAxis (L.edge.coord j.1 p), ρ j.1 * 1)) <
        ρ j.1 * e' := by
    rw [← hcutp]
    exact lt_of_le_of_lt (hblk.trans hpq)
      ((mul_lt_mul_of_pos_right he'R hrj).trans_eq (mul_comm _ _))
  rw [dist_block_scale_GAF hrj, one_smul] at hblk'
  have hd : dist (WithLp.toLp 2 (L.edge.cutoff j.1 q • planeAxis (L.edge.coord j.1 q),
      L.edge.cutoff j.1 q)) (WithLp.toLp 2 (planeAxis (L.edge.coord j.1 p), (1 : ℝ))) < e' :=
    lt_of_mul_lt_mul_left hblk' hrj.le
  have hA : ‖planeAxis (L.edge.coord j.1 p)‖ ≤ 7 * Δ := by
    rw [norm_planeAxis]; exact hηp
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist he'0 (by linarith) hA hd
  rw [← map_sub, norm_planeAxis] at hv
  have hloc := marker_localization_lt he'0.le he'1 hΔ le_rfl
  have hv' : |L.edge.coord j.1 q - L.edge.coord j.1 p| < Δ / 10 := hv.trans hloc
  have hcutq_ne : L.edge.cutoff j.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    linarith
  have hdom := cgpMarkerCutoff_ne_zero L hΔ0 (.inr (.inr j)) q hcutq_ne
  have hdom' : q ∈ ball j.1 (100 * Δ * ρ j.1) := hdom
  have hqη : |L.edge.coord j.1 q| < 8 * Δ := by
    have := abs_sub_abs_le_abs_sub (L.edge.coord j.1 q) (L.edge.coord j.1 p)
    linarith
  exact ⟨hdom', hv', hqη⟩

/-- At a point with full edge cutoff, the axis coordinate of the own block of `π₂F` is the
physical coordinate `ρ(j)η_j`. -/
theorem blockAxisCoord_projMap_KC5 (j : L.edge.finite_centres.toFinset) {q : X}
    (hq : L.edge.cutoff j.1 q = 1) :
    blockAxisCoord_KC5 (cgpEdgeBlockTag L Z j) (cgpProjMap L Z (cgpQ2Tags L Z) q) =
      ρ j.1 * L.edge.coord j.1 q := by
  apply blockAxisCoord_axis_KC5 _ _ (m := ρ j.1 * 1)
  rw [cgpProjMap_apply_of_mem L Z (a := cgpEdgeBlockTag L Z j) (edge_mem_cgpQ2Tags L Z j) q]
  change WithLp.toLp 2 ((ρ j.1 * L.edge.cutoff j.1 q) • planeAxis (L.edge.coord j.1 q),
    ρ j.1 * L.edge.cutoff j.1 q) = _
  rw [hq, mul_one, ← map_smul, smul_eq_mul]

/-- **EGP07's closed coverage test (FC25 in physical units).** For a model `Φ` with own block
`(a, 1)` at `j`, `‖D²Φ‖ ≤ C`, EGP06's value clause (EG) with error `e`, EGP05's section, a core
witness `p` (`|η_j(p)| ≤ 7Δ`, `t(p) ≤ 7Δ`) and `0 < r ≤ R̂ρ(j)`, `R̂ < 1/100`:
`d_H(S̃₂ ∩ B̄(x, r), (x + range DΦ(η_j(p))) ∩ B̄(x, r)) ≤ 3(2ρ(j)e + (C/ρ(j))r²/2)`,
`x = π₂F(p)`. -/
theorem egp07_closed_test_KC5 (hΔ : 1 ≤ Δ) (j : L.edge.finite_centres.toFinset)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (hsm : ContDiff ℝ 2 Φ)
    (hown : ∀ a, Φ a (cgpEdgeBlockTag L Z j) = WithLp.toLp 2 (planeAxis a, 1)) {Cd eg : ℝ}
    (hCd : 0 ≤ Cd) (heg : 0 ≤ eg) (hD2 : ∀ a, ‖iteratedFDeriv ℝ 2 Φ a‖ ≤ Cd)
    (hEG : ∀ x ∈ ball j.1 (100 * Δ * ρ j.1), |L.edge.coord j.1 x| ≤ 8 * Δ →
      cgpHeight L x ≤ 8 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap L Z (cgpQ2Tags L Z) x - Φ (L.edge.coord j.1 x)‖ < eg)
    (hsec : ∀ u : ℝ, |u| < 17 / 2 * Δ → ∃ q : X, L.edge.coord j.1 q = u ∧
      cgpHeight L q < Δ / 100 ∧ dist q j.1 < 10 * Δ * ρ j.1)
    {p : X} (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hηp : |L.edge.coord j.1 p| ≤ 7 * Δ)
    (htp : cgpHeight L p ≤ 7 * Δ) {R r : ℝ} (hR : R < 1 / 100) (hr : 0 < r)
    (hrR : r ≤ R * ρ j.1) :
    hausdorffEDist (cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 ∩
        closedBall (cgpProjMap L Z (cgpQ2Tags L Z) p) r)
      ((AffineSubspace.mk' (cgpProjMap L Z (cgpQ2Tags L Z) p)
          (LinearMap.range (fderiv ℝ Φ (L.edge.coord j.1 p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))) :
          Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
        closedBall (cgpProjMap L Z (cgpQ2Tags L Z) p) r) ≤
      ENNReal.ofReal (3 * (2 * (ρ j.1 * eg) + Cd / ρ j.1 * r ^ 2 / 2)) := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hrj := hρ j.1
  have hΔ0 : 0 < Δ := by linarith
  have hR0 : 0 ≤ R := by
    by_contra h
    have : R * ρ j.1 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hrj
    linarith
  have hcutp : L.edge.cutoff j.1 p = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hj hp (by linarith) (show cgpHeight L p ≤ 8 * Δ by linarith)
  have hp8 : p ∈ fc27EdgeSet L 8 := ⟨j, hp, by linarith, by linarith⟩
  have hPx := blockAxisCoord_projMap_KC5 L Z j hcutp
  have hPΦ : ∀ u : ℝ, blockAxisCoord_KC5 (cgpEdgeBlockTag L Z j)
      ((fun u : ℝ => ρ j.1 • Φ ((ρ j.1)⁻¹ • u)) u) = u := fun u => by
    change blockAxisCoord_KC5 (cgpEdgeBlockTag L Z j) (ρ j.1 • Φ ((ρ j.1)⁻¹ • u)) = u
    rw [map_smul, blockAxisCoord_axis_KC5 _ _ (hown _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hrj.ne', one_mul]
  have hHD := hausdorffDist_coordinate_graph_coverage_le (cgpProjMap L Z (cgpQ2Tags L Z))
    (fun q => ρ j.1 * L.edge.coord j.1 q)
    {q : X | q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |L.edge.coord j.1 q| ≤ 8 * Δ ∧
      cgpHeight L q ≤ 8 * Δ}
    (fun u : ℝ => ρ j.1 • Φ ((ρ j.1)⁻¹ • u)) (blockAxisCoord_KC5 (cgpEdgeBlockTag L Z j))
    (norm_blockAxisCoord_le_KC5 _) hPΦ (cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8)
    (cgpProjMap L Z (cgpQ2Tags L Z) p) ⟨p, hp8, rfl⟩ hr (div_nonneg hCd hrj.le)
    (mul_nonneg hrj.le heg)
    (fun u _ => (contDiff_physGraph_KC5 hsm (ρ j.1)).contDiffAt)
    (fun u _ => by
      rw [norm_iteratedFDeriv_physGraph_KC5 hrj hsm u, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hD2 _) (inv_nonneg.mpr hrj.le))
    (fun y hy => by
      obtain ⟨⟨q, hq8, rfl⟩, hyr⟩ := hy
      obtain ⟨-, -, -, htq⟩ := hq8
      have hloc := egp07_localization_KC5 L Z hΔ j hp hηp (by linarith) hR0 hR
        ((mem_closedBall.mp hyr).trans hrR)
      obtain ⟨hq100, -, hqη⟩ := hloc
      have hcutq : L.edge.cutoff j.1 q = 1 :=
        L.edge.cutoff_eq_one_of_le hΔ0 hj hq100 hqη.le htq
      exact ⟨q, ⟨hq100, hqη.le, htq⟩, rfl, blockAxisCoord_projMap_KC5 L Z j hcutq⟩)
    (fun q hq => by
      obtain ⟨hq100, hqη, htq⟩ := hq
      have h := hEG q hq100 hqη htq
      change dist (cgpProjMap L Z (cgpQ2Tags L Z) q)
        (ρ j.1 • Φ ((ρ j.1)⁻¹ • (ρ j.1 * L.edge.coord j.1 q))) ≤ ρ j.1 * eg
      rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hrj.ne', one_mul, dist_eq_norm]
      have he : cgpProjMap L Z (cgpQ2Tags L Z) q - ρ j.1 • Φ (L.edge.coord j.1 q) =
          ρ j.1 • ((ρ j.1)⁻¹ • cgpProjMap L Z (cgpQ2Tags L Z) q - Φ (L.edge.coord j.1 q)) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hrj.ne', one_smul]
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hrj]
      exact mul_le_mul_of_nonneg_left h.le hrj.le)
    (fun u hu => by
      rw [hPx, mem_closedBall, Real.dist_eq] at hu
      have hu' : |(ρ j.1)⁻¹ * u - L.edge.coord j.1 p| ≤ R := by
        have he : (ρ j.1)⁻¹ * u - L.edge.coord j.1 p =
            (ρ j.1)⁻¹ * (u - ρ j.1 * L.edge.coord j.1 p) := by
          field_simp
        rw [he, abs_mul, abs_inv, abs_of_pos hrj, inv_mul_le_iff₀ hrj]
        linarith
      have hu8 : |(ρ j.1)⁻¹ * u| < 17 / 2 * Δ := by
        have := abs_sub_abs_le_abs_sub ((ρ j.1)⁻¹ * u) (L.edge.coord j.1 p)
        linarith
      obtain ⟨q, hqu, htq, hdq⟩ := hsec _ hu8
      have hq100 : q ∈ ball j.1 (100 * Δ * ρ j.1) := by
        rw [mem_ball]
        have : 0 < Δ * ρ j.1 := mul_pos hΔ0 hrj
        linarith
      have hqη : |L.edge.coord j.1 q| ≤ 8 * Δ := by
        rw [hqu]
        have := abs_sub_abs_le_abs_sub ((ρ j.1)⁻¹ * u) (L.edge.coord j.1 p)
        linarith
      have htq8 : cgpHeight L q ≤ 8 * Δ := by linarith
      refine ⟨q, ⟨hq100, hqη, htq8⟩, ?_, ⟨q, ⟨j, hq100, hqη, htq8⟩, rfl⟩⟩
      rw [hqu, ← mul_assoc, mul_inv_cancel₀ hrj.ne', one_mul])
  rw [hPx, fderiv_physGraph_KC5 hrj.ne' (hsm.differentiable (by norm_num) _),
    image_tangent_eq_mk'_KC5] at hHD
  refine hausdorffEDist_le_ofReal_KC5 ?_ ?_ inter_subset_right inter_subset_right hHD
  · exact ⟨⟨p, hp8, rfl⟩, mem_closedBall_self hr.le⟩
  · exact ⟨AffineSubspace.self_mem_mk' _ _, mem_closedBall_self hr.le⟩

/-- **EGP07's coverage at one core point, open tests (FC27's (CS) form).** Under (EP)'s
`Σ < Γ/200`, `C Σ < Γ³/100`, `e < ΓΣ/100`, for a model `Φ` with own block `(a, 1)`,
`‖D²Φ‖ ≤ C`, (EG)'s value clause and EGP05's section, a core witness `p` of `j` and ANY preimage
`p'` of `x = π₂F(p)`, with `r = Σρ(p')`:
`d_H(S̃₂ ∩ B(x, r/Γ), (x + range DΦ(η_j(p))) ∩ B(x, r/Γ)) ≤ Γr`. -/
theorem egp07_coverage_point_KC5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {Γ Sg eg Cd : ℝ} (hΓ : 0 < Γ) (hS : 0 < Sg)
    (hSΓ : Sg < Γ / 200) (hCd : 0 < Cd) (hSC : Cd * Sg < Γ ^ 3 / 100) (heg : 0 ≤ eg)
    (hegΓ : eg < Γ * Sg / 100) (j : L.edge.finite_centres.toFinset)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (hsm : ContDiff ℝ 2 Φ)
    (hown : ∀ a, Φ a (cgpEdgeBlockTag L Z j) = WithLp.toLp 2 (planeAxis a, 1))
    (hD2 : ∀ a, ‖iteratedFDeriv ℝ 2 Φ a‖ ≤ Cd)
    (hEG : ∀ x ∈ ball j.1 (100 * Δ * ρ j.1), |L.edge.coord j.1 x| ≤ 8 * Δ →
      cgpHeight L x ≤ 8 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap L Z (cgpQ2Tags L Z) x - Φ (L.edge.coord j.1 x)‖ < eg)
    (hsec : ∀ u : ℝ, |u| < 17 / 2 * Δ → ∃ q : X, L.edge.coord j.1 q = u ∧
      cgpHeight L q < Δ / 100 ∧ dist q j.1 < 10 * Δ * ρ j.1)
    {p : X} (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hηp : |L.edge.coord j.1 p| ≤ 7 * Δ)
    (htp : cgpHeight L p ≤ 7 * Δ) {p' : X}
    (hp' : cgpProjMap L Z (cgpQ2Tags L Z) p' = cgpProjMap L Z (cgpQ2Tags L Z) p) :
    hausdorffEDist (cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 ∩
        ball (cgpProjMap L Z (cgpQ2Tags L Z) p) (Sg * ρ p' / Γ))
      ((AffineSubspace.mk' (cgpProjMap L Z (cgpQ2Tags L Z) p)
          (LinearMap.range (fderiv ℝ Φ (L.edge.coord j.1 p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))) :
          Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
        ball (cgpProjMap L Z (cgpQ2Tags L Z) p) (Sg * ρ p' / Γ)) ≤
      ENNReal.ofReal (Γ * (Sg * ρ p')) := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hrj := hρ j.1
  have hΔ0 : 0 < Δ := by linarith
  have hcutp : L.edge.cutoff j.1 p = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hj hp (by linarith) (show cgpHeight L p ≤ 8 * Δ by linarith)
  have hp8 : p ∈ fc27EdgeSet L 8 := ⟨j, hp, by linarith, by linarith⟩
  -- (AS) at the selected preimage `p'`
  have hmk : 0 < cgpMarker L Z (.inr (.inr j)) (cgpProjMap L Z (cgpQ2Tags L Z) p') := by
    rw [hp', cgpMarker_projMap L Z (edge_mem_cgpQ2Tags L Z j)]
    have hblk : cgpMarker L Z (.inr (.inr j)) (cgpGlobalMap L Z p) =
        ρ j.1 * L.edge.cutoff j.1 p := (cgpGlobalMap_edgeBlock L Z j p).2
    rw [hblk, hcutp, mul_one]
    exact hrj
  obtain ⟨hAS, -, -, -⟩ := fc27_edge_cloud_scale L Z hΔ hΛ hsmall
  obtain ⟨hρ1, hρ2⟩ := hAS j p' hmk
  -- radii in reference units
  obtain ⟨rh, hrh⟩ : ∃ rh, rh = Sg * ρ p' / ρ j.1 := ⟨_, rfl⟩
  have hrh1 : 3 * Sg / 4 ≤ rh := by
    rw [hrh, le_div_iff₀ hrj]
    nlinarith
  have hrh2 : rh ≤ 5 * Sg / 4 := by
    rw [hrh, div_le_iff₀ hrj]
    nlinarith
  have hRh := test_radius_lt_of_parameters hΓ hSΓ hrh2
  have hRmax : Sg * ρ p' / Γ = rh / Γ * ρ j.1 := by
    rw [hrh]
    field_simp
  have hrr : ρ j.1 * rh = Sg * ρ p' := by
    rw [hrh]
    field_simp
  have hbud := coverage_budget_lt_half (r := rh) hΓ hS hCd hSC hegΓ (by linarith) (by linarith)
  have hRpos : 0 < rh / Γ * ρ j.1 := by
    have : 0 < rh := by linarith
    positivity
  rw [hRmax]
  refine le_trans (hausdorffEDist_ball_le_of_closedBall_KC5 (x := cgpProjMap L Z (cgpQ2Tags L Z) p)
    (E := ENNReal.ofReal (3 * (2 * (ρ j.1 * eg) + Cd / ρ j.1 * (rh / Γ * ρ j.1) ^ 2 / 2)))
    ?_ (AffineSubspace.self_mem_mk' _ _) fun r hr hrR => ?_) ?_
  · exact ⟨p, hp8, rfl⟩
  · refine (egp07_closed_test_KC5 L Z hΔ j Φ hsm hown hCd.le heg hD2 hEG hsec hp hηp htp hRh hr
      hrR.le).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : r ^ 2 ≤ (rh / Γ * ρ j.1) ^ 2 := pow_le_pow_left₀ hr.le hrR.le 2
    have h3 : Cd / ρ j.1 * r ^ 2 ≤ Cd / ρ j.1 * (rh / Γ * ρ j.1) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg hCd.le hrj.le)
    linarith
  · apply ENNReal.ofReal_le_ofReal
    have he : 3 * (2 * (ρ j.1 * eg) + Cd / ρ j.1 * (rh / Γ * ρ j.1) ^ 2 / 2) =
        ρ j.1 * (3 * (2 * eg + Cd * (rh / Γ) ^ 2 / 2)) := by
      field_simp
    rw [he]
    have h1 := mul_lt_mul_of_pos_left hbud hrj
    have h2 : ρ j.1 * (Γ / 2 * rh) = Γ / 2 * (Sg * ρ p') := by rw [← hrr]; ring
    have h3 : 0 ≤ Sg * ρ p' := by
      have := hρ p'
      positivity
    nlinarith

end Coverage

end DifferentialGeometry.Geometry.Collapse
