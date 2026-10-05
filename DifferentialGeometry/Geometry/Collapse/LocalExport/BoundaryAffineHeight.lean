import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsOn
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment

/-!
# BCG02, value clause at a circle reference: the abstract step on the regionalised packets (BCG-1)

Blueprint 207B, BCG02 (`B:8822–8889`): at a circle reference `p_a` with `R_a = ρ(p_a)`, an
accurate rank-one splitting at `p_a` whose Euclidean coordinate is `U_b` (BCP02) is compared with
the circle's ORIGINAL rank-two splitting by AC76 (ranks two and one, no-three-splitting quality),
FC20–FC21 giving a unit row `A_b`; with the circle value error the value estimate
`|U_b − A_b(η_a − η_a(p_a))| < θ` holds on `D_a = B(p_a, 10R_a)`.

Here the step on the regionalised packets `LocalPacketsOn` (complete, σ-compact carrier), for an
ARBITRARY rank-one Kleiner–Lott approximation `φ` at the circle centre at its own scale (the binding
supplies the BCP02 splitting with coordinate `U_b`, `BoundaryAffineHeightBinding`):

* `tcp02_pair_complete_BCG1`: TCP02's pair kernel (`tcp02_pair_KA3`, X125's
  `exists_scaled_raw_coisometry_parameter_riemannian`) on a complete σ-compact carrier (the closed
  version used compactness only for completeness);
* `CircleFamilyOn.no_three_BCG1`, `ChartFamilyQOn.sectional_BCG1`: no normalized `(3, ν)`-splitting
  at a circle centre (`3ν ≤ β₃ < 1`), the curvature buffer at a centre of `U₁`;
* `ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1`: a coisometry has norm `≤ 1`;
* `bcg02_circle_value_of_split_BCG1`: for `θ > 0` and `ν`, an early `σ` (circle quality `3β₂ ≤ σ`)
  and a rank-one quality bound `η`: at every circle centre `j`, every rank-one `ε₁`-approximation
  `φ` (`ε₁ ≤ η`) of `(X, ρ(j)⁻¹ d, j)` into `ℝ ×₂ T` gives a unit row `A : ℝ² → ℝ¹` with
  `‖u(y) − A(η_j(y) − η_j(j))‖ < θ` on `B(j, 10ρ(j))`, `u` the real coordinate of `φ`, `η_j` the
  circle chart coordinate (`γ ≤ θ/4`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- A coisometry `A A† = id` has operator norm at most one. -/
theorem ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 {m k : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _) : ‖A‖ ≤ 1 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (ContinuousLinearMap.adjoint A)
  rw [ContinuousLinearMap.adjoint_adjoint, hA, LinearIsometryEquiv.norm_map] at h
  have h1 : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg A]

/-- **TCP02's pair kernel on a complete σ-compact carrier** (`tcp02_pair_KA3` with
`[CompleteSpace X] [SigmaCompactSpace X]` in place of `[CompactSpace X]`; same proof). -/
theorem tcp02_pair_complete_BCG1 {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) {j : ℕ}
    (hj : 1 ≤ j) (hj2 : j ≤ 2) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧
    ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (pi pj : X) (ri rj : ℝ) (hri : 0 < ri) (hrj : 0 < rj),
      (1 / 2 : ℝ) ≤ rj / ri → rj / ri ≤ 2 → dist pi pj ≤ C * ri →
      (∀ y, dist y pi < σ⁻¹ * ri → SectionalBoundedBelowAt g y (-(σ * (ri ^ 2)⁻¹))) →
      (¬ ∃ (W : Type) (mW : MetricSpace W), letI _w := mW
        ∃ w : W, Nonempty (@KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin (2 + 1)) × W))
          (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ pi (WithLp.toLp 2 (0, w)) ν)) →
      ∀ (A B : Type) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B) {ε₁ ε₂ : ℝ},
      ε₁ ≤ η → 3 * ε₂ ≤ σ →
      ∀ (φ : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
          (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ pj (WithLp.toLp 2 (0, a₀)) ε₁)
        (ψ : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 2) × B))
          (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ pi (WithLp.toLp 2 (0, b₀)) ε₂),
      ∃ Λ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin j),
        Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x, dist x pi < 1000 * ri →
          ‖(rj / ri) • (@KleinerLottApprox.toFun X _ (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ _ _ _
              φ x).fst -
            Λ (@KleinerLottApprox.toFun X _ (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ _ ψ x).fst -
            (rj / ri) • (@KleinerLottApprox.toFun X _ (mX.rescale rj⁻¹ (inv_pos.mpr hrj)) _ _ _ _
              φ pi).fst‖ < E₀ := by
  have hjpos : (0 : ℝ) < 1 + 24 * j := by positivity
  set τ : ℝ := min (1 / 4004) (E₀ / (4 * (1 + 24 * j))) with hτdef
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 4004 := min_le_left _ _
  have hτE : τ ≤ E₀ / (4 * (1 + 24 * j)) := min_le_right _ _
  have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  have ha : 20 * (j : ℝ) * τ ≤ 1001 := by nlinarith
  have ha2 : 2 * (1001 : ℝ) ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτ]
    linarith
  have hbud : 2 * (1 + 24 * (j : ℝ)) * τ < E₀ := by
    have h := mul_le_mul_of_nonneg_left hτE (by positivity : (0 : ℝ) ≤ 2 * (1 + 24 * j))
    have h' : 2 * (1 + 24 * (j : ℝ)) * (E₀ / (4 * (1 + 24 * j))) = E₀ / 2 := by
      field_simp
      ring
    linarith
  obtain ⟨σ₀, hσ₀, hσ₀1, hprop⟩ :=
    exists_scaled_raw_coisometry_parameter_riemannian.{0} (E := E3) (H := E3)
      (I := 𝓘(ℝ, E3)) hj hj2 (by simp) hτ (by linarith) hν hν1 (by norm_num : (0 : ℝ) < 1001)
      ha ha2
  refine ⟨min σ₀ (1 / 1000), lt_min hσ₀ (by norm_num), min_le_right _ _, fun C hC => ?_⟩
  obtain ⟨η, hη, hη'⟩ := hprop C hC
  refine ⟨η, hη, ?_⟩
  intro X mX _ _ hXc _ g hmetric pi pj ri rj hri hrj hs1 hs2 hd hsec hno A B _ _ a₀ b₀ ε₁ ε₂ hε₁
    hε₂ φ ψ
  have hσ : min σ₀ (1 / 1000) ≤ σ₀ := min_le_left _ _
  have hs : 0 < rj / ri := div_pos hrj hri
  have hmetR : ∀ a b, riemannianEDistOf (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g)
      a b = ENNReal.ofReal (@dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist a b) :=
    riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hri
  have hcR : @CompleteSpace X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toUniformSpace :=
    (mX.rescale_completeSpace_iff ri⁻¹ (inv_pos.mpr hri)).mpr hXc
  have hsecR : ∀ y ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi σ₀⁻¹,
      SectionalBoundedBelowAt (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g) y
        (-σ₀) := by
    intro y hy
    have hy' : dist y pi < (min σ₀ (1 / 1000))⁻¹ * ri := by
      have h1 : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist y pi < σ₀⁻¹ := hy
      rw [MetricSpace.rescale_dist] at h1
      have h2 : dist y pi < σ₀⁻¹ * ri := by
        rw [inv_mul_lt_iff₀ hri] at h1
        linarith
      have h3 : σ₀⁻¹ ≤ (min σ₀ (1 / 1000))⁻¹ := inv_anti₀ (lt_min hσ₀ (by norm_num)) hσ
      nlinarith
    apply (sectionalBoundedBelowAt_scaleMetric_iff (pow_pos (inv_pos.mpr hri) 2)).mpr
    refine (hsec y hy').mono ?_
    rw [inv_pow]
    have hr2 : 0 < (ri ^ 2)⁻¹ := by positivity
    nlinarith
  have hm : (mX.rescale ri⁻¹ (inv_pos.mpr hri)).rescale (rj / ri)⁻¹ (inv_pos.mpr hs) =
      mX.rescale rj⁻¹ (inv_pos.mpr hrj) :=
    MetricSpace.rescale_inv_ratio mX hri hrj
  obtain ⟨φ', hφ'⟩ := exists_kla_transport_KA3 hm.symm φ
  have hdR : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist pi pj ≤ C := by
    rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hri]
    linarith
  obtain ⟨Λ, hΛ, hal⟩ := @hη' X (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ hcR
    (scaleMetric (ri⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g) hmetR pi hsecR hno A B _ _ a₀ b₀
    pj ε₁ ε₂ (rj / ri) hs hs1 hs2 hdR hε₁ (by linarith) φ' ψ
  refine ⟨Λ, hΛ, fun x hx => ?_⟩
  have hε₂pos := @KleinerLottApprox.error_pos X _ (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _ _ _ _ ψ
  have hxR : @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < 1000 := by
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hri]
    linarith
  have hxτ : x ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi τ⁻¹ := by
    change @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < τ⁻¹
    linarith
  have hxψ : x ∈ @ball X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toPseudoMetricSpace pi ε₂⁻¹ := by
    change @dist X (mX.rescale ri⁻¹ (inv_pos.mpr hri)).toDist x pi < ε₂⁻¹
    have h1 : (3000 : ℝ) ≤ ε₂⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hε₂pos]
      have := min_le_right σ₀ (1 / 1000)
      linarith
    linarith
  have hψx := @KleinerLottApprox.norm_euclidean_fst_le X B (mX.rescale ri⁻¹ (inv_pos.mpr hri)) _
    pi b₀ 2 ε₂ ψ x hxψ
  have hmain := hal x hxτ (by
    have : ε₂ ≤ 1 := by have := min_le_right σ₀ (1 / 1000); linarith
    linarith)
  rw [hφ' x, hφ' pi] at hmain
  exact lt_of_le_of_lt hmain hbud

section Region

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}

omit [CompleteSpace X] [SigmaCompactSpace X] in
/-- At a regional circle centre `i` (two-stratum), no normalized `(3, ν)`-splitting exists when
`3ν ≤ β₃ < 1`. -/
theorem CircleFamilyOn.no_three_BCG1 (Cf : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) {i : X}
    (hi : i ∈ Cf.centres) {ν : ℝ} (hν : 3 * ν ≤ β 3) (hβ3 : β 3 < 1) :
    ¬ ∃ (W : Type) (mW : MetricSpace W), letI _w := mW
      ∃ w : W, Nonempty (@KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin (2 + 1)) × W))
        (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 (0, w)) ν) := by
  rintro ⟨W, mW, w, ⟨f⟩⟩
  have hrank : scaledSplittingRank ρ hρ β i = ((2 : Fin 4) : ℕ) := (Cf.centres_subset hi).2
  have h := (scaledSplittingRank_eq_iff.mp hrank).2.2 3 (by decide) le_rfl
  exact h ⟨W, mW, w, ⟨@KleinerLottApprox.weaken X (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i)))
    _ _ _ _ _ _ f hν hβ3⟩⟩

/-- The curvature buffer of `ChartFamilyQOn` at a centre `i ∈ U₁` in the form of TCP02's kernel:
`sec ≥ −σ/ρ(i)²` on `B(i, σ⁻¹ρ(i))` when `σ⁻¹ ≤ Lmax`, `0 < σ ≤ 1`. -/
theorem ChartFamilyQOn.sectional_BCG1
    (Q : ChartFamilyQOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax U₁ U₂)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : σ⁻¹ ≤ Lmax) {i : X} (hi : i ∈ U₁) :
    ∀ y, dist y i < σ⁻¹ * ρ i → SectionalBoundedBelowAt g y (-(σ * (ρ i ^ 2)⁻¹)) := by
  intro y hy
  have h := Q.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hL i hi y (by rw [mem_ball]; exact hy)
  refine h.mono ?_
  have hri := hρ i
  have he : ((σ⁻¹ * ρ i) ^ 2)⁻¹ = σ ^ 2 * (ρ i ^ 2)⁻¹ := by
    field_simp
  rw [he]
  have hr2 : 0 < (ρ i ^ 2)⁻¹ := by positivity
  nlinarith [mul_nonneg (mul_nonneg hσ.le hr2.le) (sub_nonneg.mpr hσ1)]

end Region

/-- **BCG02's value clause at a circle reference, abstract step.** For `θ > 0` and an exclusion
quality `ν`, an early `σ` and a rank-one quality bound `η`: for the regionalised packets with
`3ν ≤ β₃ < 1`, `3β₂ ≤ σ`, `σ⁻¹ ≤ Lmax`, `γ ≤ θ/4`, at every circle centre `j`, every rank-one
Kleiner–Lott `ε₁`-approximation `φ` of `(X, ρ(j)⁻¹ d, j)` into `ℝ ×₂ T` (`ε₁ ≤ η`) gives one unit
row `A : ℝ² → ℝ¹` (`A A† = id`) with `‖u(y) − A(η_j(y) − η_j(j))‖ < θ` on `B(j, 10ρ(j))`, where
`u = (φ ·).fst` (as `t e₀`) and `η_j` is the circle chart coordinate. -/
theorem bcg02_circle_value_of_split_BCG1 {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}
      (F : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        U₁ U₂),
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → σ⁻¹ ≤ Lmax → γ ≤ θ / 4 →
      ∀ (j : X) (hj : j ∈ F.circle.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ y, dist y j < 10 * ρ j →
          ‖EuclideanSpace.single 0
              (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
                φ y).fst -
            A ((let c := F.circle.chart j hj;
                letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord y) -
              (let c := F.circle.chart j hj;
                letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord j))‖ < θ := by
  obtain ⟨σ, hσ, hσ1, hpair⟩ := tcp02_pair_complete_BCG1 (E₀ := θ / 2) (by positivity) hν hν1
    (j := 1) le_rfl one_le_two
  obtain ⟨η, hη, hpair⟩ := hpair 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂ F
    hν3 hβ3 hβ2 hσL hγ j hj Tm _ t₀ ε₁ hε₁ φ
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
  refine ⟨A, hA, fun y hy => ?_⟩
  have hAn := ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 A hA
  have hmain := hal y (by linarith)
  rw [hr1, one_smul, one_smul, hφ' y, hφ' j] at hmain
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hs0 : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = 0 := by
    ext i
    simp
  rw [hφj, hs0, sub_zero] at hmain
  -- the circle value error at `y` and the chart centre
  have hyR : y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j 200 := by
    change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist y j < 200
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hρj]
    linarith
  have had : ‖(let c := F.circle.chart j hj;
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord y) -
      (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
        Ad.split y).fst‖ < γ := Ad.adapted y hyR
  have hcj : (let c := F.circle.chart j hj;
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord j) = 0 := by
    let c := F.circle.chart j hj
    have hc := F.circle.chart_center j hj
    let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)
    have h0 := c.coord_center
    rw [hc] at h0
    exact h0
  rw [hcj, sub_zero]
  set u := EuclideanSpace.single (0 : Fin 1)
    (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst
  set ψy := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
    Ad.split y).fst
  set cy := (let c := F.circle.chart j hj;
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj); c.coord y)
  have hsplit : u - A cy = (u - A ψy) + A (ψy - cy) := by
    rw [map_sub]
    abel
  have h2 : ‖A (ψy - cy)‖ ≤ ‖ψy - cy‖ := by
    calc ‖A (ψy - cy)‖ ≤ ‖A‖ * ‖ψy - cy‖ := A.le_opNorm _
      _ ≤ 1 * ‖ψy - cy‖ := by gcongr
      _ = ‖ψy - cy‖ := one_mul _
  have h3 : ‖ψy - cy‖ < γ := by rw [norm_sub_rev]; exact had
  calc ‖u - A cy‖ = ‖(u - A ψy) + A (ψy - cy)‖ := by rw [hsplit]
    _ ≤ ‖u - A ψy‖ + ‖A (ψy - cy)‖ := norm_add_le _ _
    _ < θ / 2 + γ := by linarith
    _ ≤ θ := by linarith

end DifferentialGeometry.Geometry.Collapse
