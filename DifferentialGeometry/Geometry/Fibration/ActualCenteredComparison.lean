import DifferentialGeometry.Geometry.Fibration.ActualConstantComparison

/-!
# FC22 / FC15: the centered `C¹` comparison from a pointwise derivative comparison, on the actual
# packets at the common basepoint and scale

Blueprint `master207B.tex`, FC22 (`lem:fibration-asymmetric-tests`, B:1451–1503) and FC15
(`lem:fibration-directional-comparison`, B:934–983): the conclusion of FC22 is the CENTERED
comparison `‖F − (AG + b)‖_{C¹(D)} ≤ max(1, L) · c`, `b = F(p) − AG(p)`, where `c` bounds the
derivative difference `‖dF − A dG‖` on `D = B(p, L)` and the value follows by integration along
minimizing segments (FC15's last step). On the actual LC87 family the derivative comparisons of
overlapping charts are produced, at the basepoint `i` and the normalized metric `ρ(i)⁻² g`, by the
FC22 route of TCP03 (B:5370), EGP04 (B:4943) and SGP03 (B:4483); this module supplies the shared
integration step on the actual compact manifold, with the normalized scale written out:

* `centered_c1_of_pointwise_derivative`: if `F, G` are `C¹` on the physical ball `B(p, LR)` and
  `‖dF_x w − A dG_x w‖ ≤ c √(R⁻² g(w, w))` there, then
  `‖F x − (A G x + (F p − A G p))‖ ≤ c · d(p, x)/R ≤ max(1, L) · c` on `B(p, LR)`.
* Consumer `tcp03_circle_centered`: on every comparison ball `D_i = B(i, 10ρ(i))`, every listed
  circle chart `j` of TCP03 (`tcp03_circle_row`, accepted) has FC22's centered `C¹` comparison
  `‖s_j η_j − (A_j η_i + b_j)‖ ≤ 5θ`, `b_j = s_j η_j(i) − A_j η_i(i)`, with the differential bound
  `θ/2`.

(The FC19 common-domain variant is NOT used: PBR01, B:10061–10062, B:10245–10250.)
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

omit [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] in
/-- The physical ball `B(p, LR)` is the ball of radius `L` of the normalized distance `R⁻¹ d`. -/
theorem ball_rescale_eq_FC19 {R : ℝ} (hR : 0 < R) (p : X) (L : ℝ) :
    @ball X (mX.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace p L = ball p (L * R) := by
  ext x
  change R⁻¹ * dist x p < L ↔ dist x p < L * R
  rw [inv_mul_lt_iff₀ hR, mul_comm]

/-- **FC22 / FC15 integration step on the actual manifold** at the normalized scale `R⁻² g`: a
pointwise derivative comparison on the physical ball `B(p, LR)` gives the centered value bound
`c · d(p, x)/R ≤ max(1, L) · c`. -/
theorem centered_c1_of_pointwise_derivative (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {k m : ℕ} (F : X → EuclideanSpace ℝ (Fin k)) (G : X → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) (p : X) {R L c : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hc : 0 ≤ c)
    (hF : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p (L * R)))
    (hG : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p (L * R)))
    (hd : ∀ x ∈ ball p (L * R), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖mvfderiv 𝓘(ℝ, E3) F x w - A (mvfderiv 𝓘(ℝ, E3) G x w)‖ ≤
        c * Real.sqrt (R⁻¹ ^ 2 * g.inner x w w)) :
    ∀ x ∈ ball p (L * R),
      ‖F x - (A (G x) + (F p - A (G p)))‖ ≤ c * (dist p x / R) ∧
        ‖F x - (A (G x) + (F p - A (G p)))‖ ≤ max 1 L * c := by
  have hconn : ConnectedSpace X := connectedSpace_of_aligned_metric g hmetric p
  set S : Set X := ball p (L * R) with hS
  have hball : @ball X (mX.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace p L = S :=
    ball_rescale_eq_FC19 hR p L
  have hdist : ∀ x, R⁻¹ * dist p x = dist p x / R := fun x => by rw [div_eq_inv_mul]
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale R⁻¹ (inv_pos.mpr hR)
  let bR := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hconn' : ConnectedSpace X := hconn
  have hball' : @ball X mR.toPseudoMetricSpace p L = S := hball
  have hF' : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F
      (@ball X mR.toPseudoMetricSpace p L) := by rw [hball']; exact hF
  have hG' : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G
      (@ball X mR.toPseudoMetricSpace p L) := by rw [hball']; exact hG
  have hd' : ∀ x ∈ @ball X mR.toPseudoMetricSpace p L,
      ‖mvfderiv 𝓘(ℝ, E3) F x - A.comp (mvfderiv 𝓘(ℝ, E3) G x)‖ ≤ c := by
    intro x hx
    rw [hball'] at hx
    refine ContinuousLinearMap.opNorm_le_bound _ hc fun w => ?_
    rw [norm_tangent_radialScaled_KA4 g hR x w]
    exact hd x hx w
  have hh := Fibration.centered_affine_c1_of_mfderiv_bound gR hnR F G A p hL hc hF' hG' hd'
  intro x hx
  have hxR : x ∈ @ball X mR.toPseudoMetricSpace p L := by rw [hball']; exact hx
  obtain ⟨h1, h2⟩ := hh x hxR
  refine ⟨h1.trans_eq ?_, (le_max_left _ _).trans h2⟩
  change c * (R⁻¹ * @dist X mX.toDist p x) = _
  rw [hdist x]

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_FC19
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_FC19
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_FC19
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Consumer: FC22's centered form for the listed circle charts of TCP03.** With TCP03's early
thresholds, at every circle centre `i` every listed circle chart `j` has one coisometry `A_j`
such that on `D_i = B(i, 10ρ(i))` the centered comparison of `F = s_j η_j` with `A_j η_i` is at
most `5θ` (`= max(1, 10) · θ/2`) and the differential comparison at most `(θ/2)|w|`. -/
theorem tcp03_circle_centered {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres) j (hj : j ∈ P.circle.centres),
        (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
                (A (cgpCircleCoord P.toLocalChartFamily i hi x) +
                  ((ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj i -
                    A (cgpCircleCoord P.toLocalChartFamily i hi i)))‖ ≤ 5 * θ ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, H⟩ := tcp03_circle_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hγ hσL i hi j hj hmeet
  obtain ⟨A, hA, -, hTC⟩ := H P hΛ hΔ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hγ hσL i hi j hj
    hmeet
  refine ⟨A, hA, fun x hx => ⟨?_, (hTC x hx).2⟩⟩
  obtain ⟨-, hcirc, -, -, -, -⟩ := fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT i
  obtain ⟨-, -, hsub1, hsub2, -⟩ := hcirc j hj hmeet
  have hri := hρ i
  have hFsm : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) 1
      (fun y => (ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj y) (ball i (10 * ρ i)) := by
    have h1 := ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).mono
      (hsub1.trans hsub2)).of_le (m := 1) (by norm_num)
    exact ((ρ j / ρ i) • ContinuousLinearMap.id ℝ ℝ²).contMDiff.comp_contMDiffOn h1
  have hGsm : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) 1 (cgpCircleCoord P.toLocalChartFamily i hi)
      (ball i (10 * ρ i)) :=
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hi).mono
      (ball_subset_ball (by nlinarith))).of_le (by norm_num)
  have hd : ∀ y ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) y,
      ‖mvfderiv 𝓘(ℝ, E3) (fun y => (ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj y) y w -
          A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) y w)‖ ≤
        θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner y w w) := by
    intro y hy w
    have hyj : y ∈ ball j (200 * ρ j) := hsub2 (hsub1 hy)
    have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord P.toLocalChartFamily j hj) y :=
      ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).contMDiffAt
        (isOpen_ball.mem_nhds hyj)).mdifferentiableAt (by simp)
    have hsm : mvfderiv 𝓘(ℝ, E3)
        (fun y => (ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj y) y w =
        (ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) y w :=
      mvfderiv_clm_comp hdiff ((ρ j / ρ i) • ContinuousLinearMap.id ℝ ℝ²) w
    rw [hsm]
    exact (hTC y hy).2 w
  have hc := centered_c1_of_pointwise_derivative g hmetric
    (fun y => (ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj y)
    (cgpCircleCoord P.toLocalChartFamily i hi) A i hri (by norm_num : (0 : ℝ) < 10)
    (by positivity : (0 : ℝ) ≤ θ / 2) hFsm hGsm hd x hx
  have hmax : max 1 (10 : ℝ) * (θ / 2) = 5 * θ := by
    rw [max_eq_right (by norm_num)]
    ring
  rw [← hmax]
  exact hc.2

end DifferentialGeometry.Geometry.Collapse
