import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphBlocks
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment

/-!
# TCP05: the actual blocks of `R_i⁻¹𝓔⁰` near a point of `D_i` and their (TG) errors

Blueprint `master207B.tex`, TCP05 (B:5537–5594), on `P : LocalChartPackets`, `F = 𝓔⁰`
(`cgpGlobalMap`). Near a point `x` of a circle reference ball, each listed block of `F` is a fixed
`C²` map of actual inputs: a circle block `ρ(j)(ψ(η_j) η_j, ψ(η_j))` is
`R • scaledCutoffBlock s_j ψ (s_j η_j)` (`s_j = ρ(j)/R`); a slim block is
`R • blockLift (sgpModelBlock (10⁵Δ) s_j (s_j η_j))`; a zero block is
`R • blockLift (zeroModelBlock s₀ (s₀ η₀))`. With TCP03's `C¹` comparison of the inputs, the generic
`tg_block_pointwise_KA6` bounds the block errors.

* `cgpGlobalMap_circle_eq_KA6`, `tg_circle_tag_KA6`: listed circle blocks.
* `norm_mvfderiv_circleCoord_le_KA6`: `‖dη_i(w)‖ ≤ 2|w|` on `B(i, 200R)` (`|w|` of `R⁻²g`).
* `tg_own_tag_KA6`: the own block on `{|η_i| ≤ 8}`: no error (the bump plateau).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA6T : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Profiles

/-- The `C²` bounds `50(P + 1)` of a circle model block `scaledCutoffBlock s ψ`, `s ∈ [1/2, 2]`. -/
theorem circle_scaledBlock_bounds_KA6 {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 2) (y : ℝ²) :
    ‖fderiv ℝ (scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ)) y‖ ≤
        50 * (tcpProfileBound + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ))) y‖ ≤
        50 * (tcpProfileBound + 1) := by
  obtain ⟨hP, -, -, hbump, -⟩ := tcpProfileBound_spec
  have hs0 : 0 < s := by linarith [hs.1]
  have hsupp : tsupport (circleCutoffBump_LC87 : ℝ² → ℝ) ⊆ closedBall 0 9 := by
    rw [circleCutoffBump_LC87.tsupport_eq]
    exact le_rfl
  have hW := scaledCutoffBlock_derivative_bounds circleCutoffBump_LC87.contDiff
    hs0 (by norm_num : (0 : ℝ) ≤ 9) (by linarith : (0 : ℝ) ≤ tcpProfileBound)
    (by linarith : (0 : ℝ) ≤ tcpProfileBound)
    (fun y => ⟨circleCutoffBump_LC87.nonneg, circleCutoffBump_LC87.le_one⟩) hsupp
    (fun y => (hbump y).1) (fun y => (hbump y).2) y
  refine ⟨hW.1.trans (by linarith), hW.2.trans ?_⟩
  rw [div_le_iff₀ hs0]
  nlinarith [hs.1]

end Profiles

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The circle coordinate has `‖dη_i(w)‖ ≤ 2|w|` on `B(i, 200R)` (`|w|` of `R⁻²g`). -/
theorem norm_mvfderiv_circleCoord_le_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) {x : X} (hx : x ∈ ball i (200 * ρ i))
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w‖ ≤
      2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord P.toLocalChartFamily i hi) x :=
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hi).contMDiffAt
      (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx hd (by positivity)
    (cgpCircleCoord_lipschitz P.toLocalChartFamily hi) w
  have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) = (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
  rw [hsq]
  calc _ ≤ 2 / ρ i * Real.sqrt (g.inner x w w) := h
    _ = 2 * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by ring

/-- A circle block of `𝓔⁰` where its cutoff is `ψ ∘ η_j`:
`R • scaledCutoffBlock s_j ψ (s_j η_j)`. -/
theorem cgpGlobalMap_circle_eq_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.circle.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) {y : X}
    (hy : P.circle.cutoff j.1 y = circleCutoffBump_LC87
      (cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) y)) :
    cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j) =
      R • scaledCutoffBlock (ρ j.1 / R) (circleCutoffBump_LC87 : ℝ² → ℝ)
        ((ρ j.1 / R) • cgpCircleCoord P.toLocalChartFamily j.1
          ((Set.Finite.mem_toFinset _).mp j.2) y) := by
  have hrj := hρ j.1
  set η := cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) y
    with hη
  have hs : ρ j.1 / R ≠ 0 := (div_pos hrj hR).ne'
  change WithLp.toLp 2 ((ρ j.1 * P.circle.cutoff j.1 y) • η, ρ j.1 * P.circle.cutoff j.1 y) = _
  have hinv : (ρ j.1 / R)⁻¹ • (ρ j.1 / R) • η = η := by
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hR0 : R ≠ 0 := hR.ne'
  have e1 : R * circleCutoffBump_LC87 η * (ρ j.1 / R) = ρ j.1 * circleCutoffBump_LC87 η := by
    field_simp
  have e2 : R * (ρ j.1 / R * circleCutoffBump_LC87 η) = ρ j.1 * circleCutoffBump_LC87 η := by
    field_simp
  have hsm : ∀ (c : ℝ) (u : ℝ²) (t : ℝ),
      c • (WithLp.toLp 2 (u, t) : WithLp 2 (ℝ² × ℝ)) = WithLp.toLp 2 (c • u, c * t) :=
    fun c u t => rfl
  rw [hy, scaledCutoffBlock, hinv, hsm, smul_smul, smul_smul, e1, e2]

/-- **(TG) for a listed circle block** at a point `x` of `B(j, 200ρ(j)) ∩ B(i, 200R)`: from
TCP03's comparison `‖s_jη_j − Aη_i − c‖ ≤ ε`, `‖s_j dη_j − A dη_i‖ ≤ ε|·|` (`‖A‖ ≤ 1`,
`s_j ∈ [1/2, 2]`) against the model block `scaledCutoffBlock s_j ψ (A a + c)`. -/
theorem tg_circle_tag_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) {x : X}
    (hxj : x ∈ ball j.1 (200 * ρ j.1)) (hxi : x ∈ ball i (200 * ρ i))
    (hs : ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2) (A : ℝ² →L[ℝ] ℝ²) (hA : ‖A‖ ≤ 1) (c : ℝ²) {ε₀ : ℝ}
    (hval : ‖(ρ j.1 / ρ i) • cgpCircleCoord P.toLocalChartFamily j.1
        ((Set.Finite.mem_toFinset _).mp j.2) x - A (cgpCircleCoord P.toLocalChartFamily i hi x) -
        c‖ ≤ ε₀)
    (hder : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ j.1 / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j.1
          ((Set.Finite.mem_toFinset _).mp j.2)) x w -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
        ε₀ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inl j) -
        scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
          (A (cgpCircleCoord P.toLocalChartFamily i hi x) + c)‖ ≤
        50 * (tcpProfileBound + 1) * ε₀ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j)) x w -
          fderiv ℝ (fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
            (A a + c)) (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
          (50 * (tcpProfileBound + 1) + 50 * (tcpProfileBound + 1) * 2) * ε₀ *
            Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  set sj := ρ j.1 / ρ i with hsj
  set ηj := cgpCircleCoord P.toLocalChartFamily j.1 hj with hηj
  set ηi := cgpCircleCoord P.toLocalChartFamily i hi with hηi
  have hf : (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j)) =ᶠ[𝓝 x]
      fun y => ρ i • scaledCutoffBlock sj (circleCutoffBump_LC87 : ℝ² → ℝ) (sj • ηj y) := by
    filter_upwards [circle_cutoff_eventuallyEq_KA2 P.toLocalChartFamilyE.toLocalChartFamilyQ hj
      hxj] with y hy
    exact cgpGlobalMap_circle_eq_KA6 P j hri hy
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ηj x :=
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).contMDiffAt
      (isOpen_ball.mem_nhds hxj)).mdifferentiableAt (by simp)
  have hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => sj • ηj y) x := hηd.const_smul sj
  have hdV : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      mvfderiv 𝓘(ℝ, E3) (fun y => sj • ηj y) x w = sj • mvfderiv 𝓘(ℝ, E3) ηj x w := fun w =>
    mvfderiv_comp_hasFDerivAt hηd (sj • ContinuousLinearMap.id ℝ ℝ²).hasFDerivAt w
  have hb := circle_scaledBlock_bounds_KA6 hs
  refine tg_block_pointwise_KA6 (I := 𝓘(ℝ, E3))
    (contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff sj) (fun y => (hb y).1)
    (fun y => (hb y).2) hri.ne' hf hV ηi A c (fun w => Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    ?_ (fun w => ?_) (fun w => ?_)
  · rw [← sub_sub]
    exact hval
  · rw [hdV]
    exact hder w
  · refine (A.le_opNorm _).trans ?_
    have h2 := norm_mvfderiv_circleCoord_le_KA6 P hi hxi w
    calc ‖A‖ * ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 1 * (2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :=
          mul_le_mul hA h2 (norm_nonneg _) zero_le_one
      _ = 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := one_mul _

/-- A scalar block `(ρ_j φ e₀η, ρ_j φ)` of `𝓔⁰` as `R • blockLift (φ s_jη, s_jφ)`, `s_j = ρ_j/R`. -/
theorem scalar_block_eq_KA6 (R ρj φ η : ℝ) (hR : R ≠ 0) :
    (WithLp.toLp 2 ((ρj * φ) • planeAxis η, ρj * φ) : WithLp 2 (ℝ² × ℝ)) =
      R • blockLift_KC3 (WithLp.toLp 2 (φ * (ρj / R * η), ρj / R * φ)) := by
  have hsm : ∀ (c : ℝ) (u : ℝ²) (t : ℝ),
      c • (WithLp.toLp 2 (u, t) : WithLp 2 (ℝ² × ℝ)) = WithLp.toLp 2 (c • u, c * t) :=
    fun c u t => rfl
  have e1 : R * (φ * (ρj / R * η)) = ρj * φ * η := by field_simp
  have e2 : R * (ρj / R * φ) = ρj * φ := by field_simp
  rw [blockLift_apply_KC3, hsm, planeAxis_apply, planeAxis_apply]
  simp only [smul_smul, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [e1, e2]

/-- A slim block of `𝓔⁰` where its cutoff is `f(η_j/(10⁵Δ))`:
`R • blockLift (sgpModelBlock (10⁵Δ) s_j (s_j η_j))`. -/
theorem cgpGlobalMap_slim_eq_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.slim.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) (hΔ : 0 < Δ) {y : X}
    (hy : P.slim.cutoff j.1 y = slimCutoffProfile_LC87
      ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord y / (10 ^ 5 * Δ))) :
    cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inl j)) =
      R • blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / R)
        (ρ j.1 / R * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord y)) := by
  have hrj := hρ j.1
  set η := (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord y with hη
  have hs : ρ j.1 / R ≠ 0 := (div_pos hrj hR).ne'
  change WithLp.toLp 2 ((ρ j.1 * P.slim.cutoff j.1 y) • planeAxis η,
    ρ j.1 * P.slim.cutoff j.1 y) = _
  have hq : ρ j.1 / R * η / (ρ j.1 / R * (10 ^ 5 * Δ)) = η / (10 ^ 5 * Δ) := by
    field_simp
  rw [hy, sgpModelBlock_apply, hq, scalar_block_eq_KA6 R _ _ η hR.ne']

/-- A zero block of `𝓔⁰`: `R • blockLift (zeroModelBlock s₀ (s₀ η₀))`, `s₀ = R₀/R`. -/
theorem cgpGlobalMap_zero_eq_KA6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (k : P.zero.finite_centres.toFinset) {R : ℝ} (hR : 0 < R) (y : X) :
    cgpGlobalMap P.toLocalChartFamily P.zero y (.inr (.inr (.inr (.inl k)))) =
      R • blockLift_KC3 (zeroModelBlock
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / R)
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / R *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial y)) := by
  set Zb := P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2) with hZb
  have hr := Zb.radius_pos
  set η := Zb.radial y with hη
  have hs : Zb.radius / R ≠ 0 := (div_pos hr hR).ne'
  change WithLp.toLp 2 ((Zb.radius * annularCutoff cutoffProfile η) • planeAxis η,
    Zb.radius * annularCutoff cutoffProfile η) = _
  have hq : (Zb.radius / R)⁻¹ * (Zb.radius / R * η) = η := by
    field_simp
  rw [zeroModelBlock_apply, hq, scalar_block_eq_KA6 R _ _ η hR.ne']

omit [CompactSpace X] [IsManifold 𝓘(ℝ, E3) ∞ X] in
/-- **(TG) for a lifted scalar block** (slim or zero): an actual block
`f = R • blockLift (W (s_j η_j))` near `x` against the model block `blockLift (W (A₁ a + c))`, from
`|s_jη_j − A₁η_i − c| ≤ ε`, `|s_j dη_j − A₁ dη_i| ≤ εν`, `‖A₁‖ ≤ 1`, `‖dη_i‖ ≤ 2ν`. -/
theorem tg_scalar_tag_KA6 {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W) {B : ℝ}
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B)
    {f : X → WithLp 2 (ℝ² × ℝ)} {ηs : X → ℝ} {ηi : X → ℝ²} {x : X} {R sj : ℝ} (hR : R ≠ 0)
    (hf : f =ᶠ[𝓝 x] fun y => R • blockLift_KC3 (W (sj * ηs y)))
    (hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ηs x) (A₁ : ℝ² →L[ℝ] ℝ) (hA₁ : ‖A₁‖ ≤ 1) (c : ℝ)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ : ℝ}
    (hval : |sj * ηs x - A₁ (ηi x) - c| ≤ ε₀)
    (hder : ∀ w, |sj * mvfderiv 𝓘(ℝ, E3) ηs x w - A₁ (mvfderiv 𝓘(ℝ, E3) ηi x w)| ≤ ε₀ * ν w)
    (hηi : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 2 * ν w) :
    ‖R⁻¹ • f x - blockLift_KC3 (W (A₁ (ηi x) + c))‖ ≤ B * ε₀ ∧
      ∀ w, ‖R⁻¹ • mvfderiv 𝓘(ℝ, E3) f x w -
        fderiv ℝ (fun a => blockLift_KC3 (W (A₁ a + c))) (ηi x)
          (mvfderiv 𝓘(ℝ, E3) ηi x w)‖ ≤ (B + B * 2) * ε₀ * ν w := by
  have hb := clm_comp_bounds_KA6 blockLift_KC3 norm_blockLift_le_KC3 hW h1 h2
  have hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => sj * ηs y) x :=
    (mdifferentiableAt_const (c := sj)).mul hηd
  have hdV : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      mvfderiv 𝓘(ℝ, E3) (fun y => sj * ηs y) x w = sj * mvfderiv 𝓘(ℝ, E3) ηs x w := by
    intro w
    rw [mvfderiv_mul_apply_KA2 mdifferentiableAt_const hηd, mvfderiv_const]
    simp
  refine tg_block_pointwise_KA6 (I := 𝓘(ℝ, E3)) (G := fun z => blockLift_KC3 (W z))
    (blockLift_KC3.contDiff.comp hW) (fun y => (hb y).1) (fun y => (hb y).2) hR hf hV ηi A₁ c ν
    ?_ (fun w => ?_) (fun w => ?_)
  · rw [Real.norm_eq_abs, ← sub_sub]
    exact hval
  · rw [hdV, Real.norm_eq_abs]
    exact hder w
  · refine (A₁.le_opNorm _).trans ?_
    calc ‖A₁‖ * ‖mvfderiv 𝓘(ℝ, E3) ηi x w‖ ≤ 1 * (2 * ν w) :=
          mul_le_mul hA₁ (hηi w) (norm_nonneg _) zero_le_one
      _ = 2 * ν w := one_mul _

end DifferentialGeometry.Geometry.Collapse
