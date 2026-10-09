import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphData
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink

/-!
# TCP05 at one circle reference: the model graph from TCP03/TCP04's coisometries

Blueprint `master207B.tex`, TCP05 (B:5537–5598). At a circle centre `i` of `LocalChartPacketsR`,
given TCP03's coisometries for the listed circle / slim / edge / zero charts (their (TC) clauses on
`D_i`) and TCP04's conclusion at `i`, the model graph `Φ_i = tcpModelGraph …` built from them is
smooth, has own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C`, and satisfies (TG) at accuracy `e` on
`{|η_i| ≤ 8} ∩ B(i, 200R_i)` once `θ ≤ e/(100C²)` and `1000CΔΛ < e` (`C = tcpGraphConst`).

* `slim_conv_KA7`, `deriv_conv_KA7`, `zero_conv_KA7`, `edge_conv_KA7`, `edge_deriv_conv_KA7`:
  TCP03's `ℝ¹` (TC) clauses in the scalar form of the model rows.
* `tcp05_budget_lt_KA7`: `√c b < e` for `c ≤ N + 3`, `b = tcpTagBudget θ Δ Λ`.
* `tcp05_centre_KA7`: the conclusion of TCP05 at `i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA7C : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Conversions

/-- TCP03's slim (TC) value clause in scalar form. -/
theorem slim_conv_KA7 {s c r ε : ℝ} (A : ℝ² →L[ℝ] ℝ¹) (v : ℝ²)
    (h : ‖s • EuclideanSpace.single (0 : Fin 1) c - A v -
      s • EuclideanSpace.single (0 : Fin 1) r‖ ≤ ε) :
    |s * c - (EuclideanSpace.proj (0 : Fin 1)).comp A v - s * r| ≤ ε := by
  rw [norm_smul_single_sub_KA7] at h
  exact h

/-- TCP03's (TC) derivative clause in scalar form. -/
theorem deriv_conv_KA7 {s d ε : ℝ} (A : ℝ² →L[ℝ] ℝ¹) (u : ℝ²)
    (h : ‖s • EuclideanSpace.single (0 : Fin 1) d - A u‖ ≤ ε) :
    |s * d - (EuclideanSpace.proj (0 : Fin 1)).comp A u| ≤ ε := by
  rw [norm_smul_single_sub'_KA7] at h
  exact h

/-- TCP03's zero (TC) value clause in scalar form. -/
theorem zero_conv_KA7 {s r ri ε : ℝ} (A : ℝ² →L[ℝ] ℝ¹) (v : ℝ²)
    (h : ‖EuclideanSpace.single (0 : Fin 1) (s * (r - ri)) - A v‖ ≤ ε) :
    |s * r - (EuclideanSpace.proj (0 : Fin 1)).comp A v - s * ri| ≤ ε := by
  rw [norm_single_sub_eq_KA5] at h
  have he : s * r - (EuclideanSpace.proj (0 : Fin 1)).comp A v - s * ri = s * (r - ri) - A v 0 := by
    change s * r - A v 0 - s * ri = _
    ring
  rw [he]
  exact h

/-- TCP03's edge (TC) value clause in the network's input form (`÷ s ≥ 1/2`). -/
theorem edge_conv_KA7 {s c r ε : ℝ} (hs : 1 / 2 ≤ s) (A : ℝ² →L[ℝ] ℝ¹) (v : ℝ²)
    (h : ‖s • EuclideanSpace.single (0 : Fin 1) c - A v -
      s • EuclideanSpace.single (0 : Fin 1) r‖ ≤ ε) :
    |c - ((s⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp A) v + r)| ≤ 2 * ε := by
  rw [norm_smul_single_sub_KA7] at h
  have hs0 : 0 < s := by linarith
  have he : c - ((s⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp A) v + r) =
      s⁻¹ * (s * c - A v 0 - s * r) := by
    change c - (s⁻¹ * A v 0 + r) = _
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hs0)]
  have hε : 0 ≤ ε := (abs_nonneg _).trans h
  have h2 : s⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]
    linarith
  calc s⁻¹ * |s * c - A v 0 - s * r| ≤ 2 * ε :=
        mul_le_mul h2 h (abs_nonneg _) (by norm_num)

/-- TCP03's edge (TC) derivative clause in the network's input form (`÷ s ≥ 1/2`). -/
theorem edge_deriv_conv_KA7 {s d ε : ℝ} (hs : 1 / 2 ≤ s) (A : ℝ² →L[ℝ] ℝ¹) (u : ℝ²)
    (h : ‖s • EuclideanSpace.single (0 : Fin 1) d - A u‖ ≤ ε) :
    |d - (s⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp A) u| ≤ 2 * ε := by
  rw [norm_smul_single_sub'_KA7] at h
  have hs0 : 0 < s := by linarith
  have he : d - (s⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp A) u = s⁻¹ * (s * d - A u 0) := by
    change d - s⁻¹ * A u 0 = _
    field_simp
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hs0)]
  have hε : 0 ≤ ε := (abs_nonneg _).trans h
  have h2 : s⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]
    linarith
  calc s⁻¹ * |s * d - A u 0| ≤ 2 * ε := mul_le_mul h2 h (abs_nonneg _) (by norm_num)

/-- The edge row `s⁻¹ e₀∘A` has norm at most two (`s ≥ 1/2`, `‖A‖ ≤ 1`). -/
theorem norm_edge_row_le_KA7 {s : ℝ} (hs : 1 / 2 ≤ s) (A : ℝ² →L[ℝ] ℝ¹) (hA : ‖A‖ ≤ 1) :
    ‖s⁻¹ • (EuclideanSpace.proj (0 : Fin 1)).comp A‖ ≤ 2 := by
  have hs0 : 0 < s := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
  have h2 : s⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]
    linarith
  have h1 := norm_proj_comp_le_KA7 A hA
  nlinarith [norm_nonneg ((EuclideanSpace.proj (0 : Fin 1)).comp A), inv_pos.mpr hs0]

end Conversions

section Budget

/-- **TCP05's final budget**: for `c ≤ N + 3`, `θ ≤ e/(100C²)` and `1000CΔΛ < e`,
`√c · tcpTagBudget θ Δ Λ < e` (`C = tcpGraphConst = (N + 3) C_B`). -/
theorem tcp05_budget_lt_KA7 {eg θ Δ Λ c : ℝ} (heg : 0 < eg) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ eg / (100 * tcpGraphConst ^ 2)) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΔΛ : 1000 * tcpGraphConst * Δ * Λ < eg) (hc0 : 0 ≤ c) (hc : c ≤ fc07ActiveBound + 3) :
    Real.sqrt c * tcpTagBudget θ Δ Λ < eg := by
  have hB := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  set NB := fc07ActiveBound with hNB
  set TB := tcpBlockBound with hTB
  have hC : tcpGraphConst = (NB + 3) * TB := rfl
  have hC1 := one_le_tcpGraphConst
  set r := Real.sqrt (NB + 3) with hr
  set q := Real.sqrt (NB + 1) with hq
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hcr : Real.sqrt c ≤ r := Real.sqrt_le_sqrt hc
  have hr2 : r ^ 2 = NB + 3 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = NB + 1 := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; linarith
  have hrN : r ≤ NB + 3 := by nlinarith
  have hqr : q * r ≤ NB + 3 := by
    rw [hq, hr, ← Real.sqrt_mul (by linarith)]
    calc Real.sqrt ((NB + 1) * (NB + 3)) ≤ Real.sqrt ((NB + 3) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = NB + 3 := Real.sqrt_sq (by linarith)
  have hb0 := tcpTagBudget_nonneg_KA7 hθ0 hΔ hΛ
  have hstep : Real.sqrt c * tcpTagBudget θ Δ Λ ≤ r * tcpTagBudget θ Δ Λ :=
    mul_le_mul_of_nonneg_right hcr hb0
  have hexp : r * tcpTagBudget θ Δ Λ =
      5 * TB * ((NB + 1) * r) * θ + 200 * TB * (q * r) * (Δ * Λ) := by
    rw [tcpTagBudget]
    ring
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg (by linarith) hΛ
  have h1 : 5 * TB * ((NB + 1) * r) * θ ≤ 5 * (tcpGraphConst ^ 2 * θ) := by
    have ha : (NB + 1) * r ≤ (NB + 3) ^ 2 := by nlinarith
    have hb : TB * (NB + 3) ^ 2 ≤ tcpGraphConst ^ 2 := by
      rw [hC, mul_pow]
      have hsq : 0 ≤ (NB + 3) ^ 2 := sq_nonneg _
      have hTT : TB ≤ TB ^ 2 := by nlinarith
      nlinarith
    have hc' : 5 * TB * ((NB + 1) * r) * θ ≤ 5 * (TB * (NB + 3) ^ 2) * θ := by
      have := mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ 5 * TB)
      nlinarith
    nlinarith
  have h2 : 200 * TB * (q * r) * (Δ * Λ) ≤ 200 * (tcpGraphConst * Δ * Λ) := by
    have := mul_le_mul_of_nonneg_left hqr (by positivity : (0 : ℝ) ≤ 200 * TB)
    have h' : 200 * TB * (q * r) * (Δ * Λ) ≤ 200 * TB * (NB + 3) * (Δ * Λ) :=
      mul_le_mul_of_nonneg_right this hΔΛ0
    rw [hC]
    nlinarith
  have hθC : tcpGraphConst ^ 2 * θ ≤ eg / 100 := by
    have hC2 : 0 < 100 * tcpGraphConst ^ 2 := by positivity
    rw [le_div_iff₀ hC2] at hθ
    nlinarith
  have h3 : 200 * (tcpGraphConst * Δ * Λ) < eg / 5 := by nlinarith
  linarith

end Budget

section Centre

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_TCP05_KA7
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_TCP05_KA7
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_TCP05_KA7
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **TCP05 at one circle reference `i`** (on `LocalChartPacketsR`): from TCP03's (TC) clauses
for the listed circle / slim / edge / zero charts (one coisometry each, accuracy `θ/2`) and
TCP04's conclusion at `i`, with FC07's ranges, `θ ≤ e/(100C²)` and `1000CΔΛ < e`, there is a
smooth `Φ_i : ℝ² → H` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` and (TG) on
`{|η_i| ≤ 8} ∩ B(i, 200R_i)`: `‖R⁻¹F − Φ_iη_i‖ < e`, `‖R⁻¹dF(w) − DΦ_i dη_i(w)‖ ≤ e|w|`. -/
theorem tcp05_centre_KA7
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) {eg θ : ℝ} (heg : 0 < eg) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hθ : θ ≤ eg / (100 * tcpGraphConst ^ 2))
    (hΔΛ : 1000 * tcpGraphConst * Δ * Λ < eg) {i : X} (hi : i ∈ P.circle.centres)
    (hCrow : ∀ j (hj : j ∈ P.circle.centres),
      (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPacketsD.toLocalChartPackets j i‖ ≤ θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hSrow : ∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 ((P.slim.centre j hj).coord x) -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ ≤
            θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • EuclideanSpace.single 0
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w) -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hErow : ∀ j ∈ P.edge.centres,
      (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 (P.edge.coord j x) -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ ≤
            θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w) -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hZrow : ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
        A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
              A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                  mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hH : ((∀ j ∈ P.edge.centres, ¬ (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          ∀ j, ∀ x ∈ ball i (10 * ρ i), P.edge.cutoff j x = 0) ∧
        ((∃ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          (∀ x ∈ ball i (10 * ρ i), P.edge.smoothing x / ρ x < 3 * Δ / 20 ∧
            ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
              P.edge.cutoff j x = edgeCoordinateProfile (P.edge.coord j x / Δ)) ∨
          ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i),
              Δ / 10 ≤ P.edge.smoothing x / ρ x ∧ P.edge.smoothing x / ρ x ≤ 181 * Δ / 20 ∧
              ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edge.smoothing y / ρ y) x ∧
              ‖EuclideanSpace.single 0 (P.edge.smoothing x / ρ x - P.edge.smoothing i / ρ i) -
                  B (cgpCircleCoord P.toLocalChartFamily i hi x -
                    cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w) -
                    B (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                |mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w| ≤
                  2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))) :
    ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiff ℝ ∞ Φ ∧
      (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
      (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
      ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
        ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
            Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
              fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
            eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hθ0' := hθ0.le
  have hΔΛs : 100 * Δ * Λ ≤ 1 / 100 := by linarith [mul_nonneg hΔ0.le hΛ]
  have he8 : e ≤ 1 / 8 := by linarith
  have hT20 : (20 : ℝ) ≤ T := by linarith
  have hΛ20 : Λ ≤ 1 / 20 := by
    have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ
    linarith [mul_nonneg hΔ0.le hΛ]
  obtain ⟨hcnt, hcirc, hslim, hedge, -, hzero⟩ :=
    fc07_input_packet P.toLocalChartPacketsD.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT i
  have hγ : 0 ≤ γ := circle_quality_nonneg_KA4 P.toLocalChartPacketsD.toLocalChartPackets hi
  obtain ⟨-, -, hS1, hE1, -, -, -⟩ :=
    tcp01_row P.toLocalChartPacketsD.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hγ hi
  choose! Acf hAcf using hCrow
  choose! Asf hAsf using hSrow
  choose! Aef hAef using hErow
  choose! Azf hAzf using hZrow
  obtain ⟨τf, Bτ, cτ, hBτ, hcut, hτm, hτx⟩ := tcp05_height_data_KA7
    P.toLocalChartPacketsD.toLocalChartPackets hΔ hi hθ0'
    (fun j hj hm => (hedge j hj hm).2.2.1.trans (hedge j hj hm).2.2.2.1) hH
  obtain ⟨hcount, hcountE⟩ := tcpListed_card_KA7 P.toLocalChartFamily P.zero i hcnt
  set S := tcpListedTags P.toLocalChartFamily P.zero i with hSdef
  set Se := tcpListedEdges P.toLocalChartFamily i with hSedef
  set Ac := tcpAcOf P.toLocalChartFamily P.zero Acf with hAcdef
  set cc := tcpCcOf P.toLocalChartPacketsD.toLocalChartPackets i with hccdef
  set A1 := tcpA1Of P.toLocalChartFamily P.zero i Asf Aef Azf with hA1def
  set c1 := tcpC1Of P.toLocalChartFamily P.zero i with hc1def
  have hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S :=
    fun j h => (mem_tcpListedTags_KA7 (i := i)).mpr (Or.inl h)
  have hSe : ∀ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∉ S :=
    fun j h => (mem_tcpListedTags_KA7 (i := i)).mp h
  have hClist : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      (tsupport (P.circle.cutoff j.1) ∩ ball i (10 * ρ i)).Nonempty := by
    intro j hji hjS
    rcases (mem_tcpListedTags_KA7 (i := i)).mp hjS with h | h
    · exact (hji h).elim
    · exact h
  have hzs : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i := by
    intro k hkS
    have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
    have hk := (Set.Finite.mem_toFinset _).mp k.2
    have hsh := ((hzero k.1 hk hm).1 i (mem_ball_self (by positivity))).2
    have hib : i ∈ ball k.1 (P.zero.zero k.1 hk).radius := by
      rw [mem_ball, dist_comm]
      have := (P.zero.zero k.1 hk).radius_pos
      linarith
    have h := LocalChartPacketsR.zero_ratio_of_meets P hT20 hΛ20 hk
      ⟨i, hib, mem_ball_self (by positivity)⟩
    have : (1 : ℝ) ≤ T / 20 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  refine ⟨tcpModelGraph P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ,
    contDiff_tcpModelGraph _ _ _ _ _ _ _ _ _ _ _,
    fun j hj a => tcpModelGraph_own _ _ _ _ _ _ _ _ _ _ _ j hj a, fun a => ?_, fun x hxi h8 => ?_⟩
  · refine tcp05_model_bounds P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ hΔ hown
      (fun j hji hjS => ?_) (fun j hjS => ?_) (fun k hkS => ⟨?_, hzs k hkS⟩) (fun j hj => ?_)
      (hBτ.trans one_le_two) hcount hcountE a
    · have hm := hClist j hji hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact ⟨DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAcf j.1 hj hm).1,
        (hcirc j.1 hj hm).1⟩
    · have hm := (mem_tcpListedTags_KA7 (i := i)).mp hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact ⟨norm_proj_comp_le_KA7 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAsf j.1 hj hm).1),
        (hS1 j.1 hj hm).1.1.le⟩
    · have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
      have hk := (Set.Finite.mem_toFinset _).mp k.2
      exact norm_proj_comp_le_KA7 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAzf k.1 hk hm).1)
    · have hm := (mem_tcpListedEdges_KA7 (i := i)).mp hj
      have hjc := (Set.Finite.mem_toFinset _).mp j.2
      have hr := (hedge j.1 hjc hm).1
      exact ⟨norm_edge_row_le_KA7 hr.1 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAef j.1 hjc hm).1), hr⟩
  · have hx : x ∈ ball i (10 * ρ i) :=
      mem_ball.mpr (LocalChartPacketsR.dist_lt_of_norm_coord_le P hi (mem_ball.mp hxi) h8)
    have hF : MDifferentiableAt 𝓘(ℝ, E3)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (cgpGlobalMap P.toLocalChartFamily P.zero) x :=
      (cgp01_rowE P.toLocalChartPacketsD.toLocalChartPackets.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ
        hΔΛs he8).mdifferentiableAt (by simp)
    have hpt := tcp05_point_KA7 P.toLocalChartPacketsD.toLocalChartPackets hi S Se Ac cc A1 c1 Bτ cτ
      τf hθ0' hθ1 hΔ hΛ hF hx hxi h8 hown hSe (fun j hji hjS => ?_) (fun j hjS => ?_)
      (fun k hkS => ?_) (fun k => ?_) ?_ hcut
      (fun y hy k hk => image_eq_zero_of_notMem_tsupport
        (fun hyt => hk ((mem_tcpListedEdges_KA7 (i := i)).mpr ⟨y, hyt, hy⟩)))
      hτm hcountE
      (fun j hji hjS hxt => hjS ((mem_tcpListedTags_KA7 (i := i)).mpr (Or.inr ⟨x, hxt, hx⟩)))
      (fun j hjS hxt => hjS ((mem_tcpListedTags_KA7 (i := i)).mpr ⟨x, hxt, hx⟩))
      (fun k hkS hxt => hkS ((mem_tcpListedTags_KA7 (i := i)).mpr ⟨x, hxt, hx⟩))
    · have hcardA := tcpModelActive_card_le_KA6 P.toLocalChartFamily P.zero S Se hcount
      have hlt := tcp05_budget_lt_KA7 heg hθ0' hθ hΔ hΛ hΔΛ (Nat.cast_nonneg _) hcardA
      refine ⟨hpt.1.trans_lt hlt, fun w => (hpt.2 w).trans ?_⟩
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hlt.le (Real.sqrt_nonneg _)
    · -- listed circle blocks
      have hm := hClist j hji hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨hco, hTC⟩ := hAcf j.1 hj hm
      obtain ⟨hratio, -, hsub1, hsub2, -⟩ := hcirc j.1 hj hm
      exact ⟨hsub2 (hsub1 hx), hratio,
        DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco, (hTC x hx).1,
        (hTC x hx).2⟩
    · -- listed slim blocks
      have hm := (mem_tcpListedTags_KA7 (i := i)).mp hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨hco, hTC⟩ := hAsf j.1 hj hm
      obtain ⟨-, -, -, hsub, hsub', -⟩ := hslim j.1 hj hm
      obtain ⟨hratio', hsm⟩ := hS1 j.1 hj hm
      exact ⟨hsub' (hsub hx), hratio'.1.le,
        (hsm.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp),
        norm_proj_comp_le_KA7 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        slim_conv_KA7 _ _ (hTC x hx).1, fun w => deriv_conv_KA7 _ _ ((hTC x hx).2 w)⟩
    · -- the zero block
      have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
      have hk := (Set.Finite.mem_toFinset _).mp k.2
      obtain ⟨hco, hTC⟩ := hAzf k.1 hk hm
      obtain ⟨-, O, hO, hDO, hsmO⟩ := hzero k.1 hk hm
      refine ⟨hzs k hkS, (hsmO.contMDiffAt (hO.mem_nhds (hDO hx))).mdifferentiableAt (by simp),
        norm_proj_comp_le_KA7 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        zero_conv_KA7 _ _ (hTC x hx).1, fun w => ?_⟩
      have h := (hTC x hx).2 w
      rw [norm_single_sub_eq_KA5] at h
      exact h
    · -- the listed edge coordinates
      have hm := (mem_tcpListedEdges_KA7 (i := i)).mp k.2
      have hjc := (Set.Finite.mem_toFinset _).mp k.1.2
      obtain ⟨hco, hTC⟩ := hAef k.1.1 hjc hm
      have hr := (hedge k.1.1 hjc hm).1
      obtain ⟨-, hsm⟩ := hE1 k.1.1 hjc hm
      refine ⟨hr, norm_edge_row_le_KA7 hr.1 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        hsm.contMDiffAt (isOpen_ball.mem_nhds hx),
        (edge_conv_KA7 hr.1 _ _ (hTC x hx).1).trans (by linarith), fun w => ?_⟩
      refine (edge_deriv_conv_KA7 hr.1 _ _ ((hTC x hx).2 w)).trans (le_of_eq ?_)
      ring
    · -- the height input
      obtain ⟨h1, h2, h3⟩ := hτx x hx
      refine ⟨h1, hBτ.trans one_le_two, h2.trans (by linarith), fun w => (h3 w).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end Centre

end DifferentialGeometry.Geometry.Collapse
