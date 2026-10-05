import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows

/-!
# Boundary port (lane B-DFB, G1): CGP02 (b) block budgets (circle, slim, zero, edge, `E'`)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualBlockBudgets.lean` by `build-logs/scratch/B-DFB/gen_g1.py` (engine: lane B-PORT-A's
`build-logs/scratch/B-PORT-A/portlib2.py`); do not edit by hand, re-run the script. Closed family →
boundary family (`LocalPacketsOnB`, complete σ-compact carrier, regional `…On` families, ACTIVE edge
`edgeB` with BAUG-A's actual cutoff `cutoff_BAUGA` = the closed formula `f(η/Δ) g(F/(ρΔ))`); every
ported declaration `x` ↦ `x_BDFB` (namespaced `T.m` ↦ `TOn.m_BDFB`); B-PORT-A's ports keep `_BAUGP`.
Closed generic lemmas (profiles `cgpProfileBound`, Leibniz / chain rules, the arithmetic budgets,
`zeroModelBall_radial_facts_KA2`) are reused from the closed import.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Profiles

end Profiles

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Generic

section Families

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **CGP02 (b), circle block.** At a point of the closed support of the circle cutoff `ζ_j`, the
circle block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` has Riemannian derivative at most `(2 + 20P₀) ν`
(`R|dη| ≤ 2`, `R|dζ| ≤ 2P₀`, `‖η‖ ≤ 9`). -/
theorem circle_block_budget_KA2_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.circle.centres) {x : X} (hx : x ∈ tsupport (L.circle.cutoff j))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * L.circle.cutoff j y) •
        cgpCircleCoord_BAUGP L j hj y, ρ j * L.circle.cutoff j y)) x v‖ ≤
      (2 + 20 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  have hxb : x ∈ ball j (200 * ρ j) := L.circle.tsupport_subset_ball j hj hx
  obtain ⟨hP1, hψ, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  set η := cgpCircleCoord_BAUGP L j hj with hηdef
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) η x :=
    ((cgpCircleCoord_contMDiffOn_BAUGP L hj).contMDiffAt
      (isOpen_ball.mem_nhds hxb)).mdifferentiableAt (by simp)
  have hη : ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ 2 / ρ j * Real.sqrt (g.inner x v v) :=
    norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hxb hηd (by positivity)
      (cgpCircleCoord_lipschitz_BAUGP L hj) v
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.circle.cutoff j) x :=
    (L.circle.contMDiff_cutoff j hj x).mdifferentiableAt (by simp)
  have hψd : HasFDerivAt (circleCutoffBump_LC87 : ℝ² → ℝ)
      (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) (η x)) (η x) :=
    ((circleCutoffBump_LC87.contDiff (n := 1)).differentiable (by simp) (η x)).hasFDerivAt
  have hζ : |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
      cgpProfileBound * (2 / ρ j * Real.sqrt (g.inner x v v)) := by
    rw [mvfderiv_apply_congr_KA2 (circle_cutoff_eventuallyEq_KA2_BAUGP L hj hxb) v,
      mvfderiv_comp_hasFDerivAt hηd hψd v, ← Real.norm_eq_abs]
    exact ((fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) (η x)).le_opNorm _).trans
      (mul_le_mul (hψ _) hη (norm_nonneg _) (by linarith))
  have hC : ‖η x‖ ≤ 9 :=
    le_of_mem_tsupport_KA2 (u := fun y => ‖η y‖) hx hηd.continuousAt.norm
      (fun y hy => (L.circle.coord_lt_of_cutoff_ne_zero j hj y hy).2)
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ 2 * Real.sqrt (g.inner x v v) := by
    calc ρ j * ‖mvfderiv 𝓘(ℝ, E3) η x v‖ ≤ ρ j * (2 / ρ j * Real.sqrt (g.inner x v v)) :=
          mul_le_mul_of_nonneg_left hη hrj.le
      _ = 2 * Real.sqrt (g.inner x v v) := by field_simp
  have hb : ρ j * |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
      2 * cgpProfileBound * Real.sqrt (g.inner x v v) := by
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (L.circle.cutoff j) x v| ≤
          ρ j * (cgpProfileBound * (2 / ρ j * Real.sqrt (g.inner x v v))) :=
          mul_le_mul_of_nonneg_left hζ hrj.le
      _ = 2 * cgpProfileBound * Real.sqrt (g.inner x v v) := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * Real.sqrt (g.inner x v v) := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := L.circle.cutoff j)
    (η := η) mdifferentiableAt_const hζd hηd v hrj.le (L.circle.cutoff_mem_Icc j hj x) hC ha hb hl
  have he : (2 + (9 + 1) * (2 * cgpProfileBound + 0)) * Real.sqrt (g.inner x v v) =
      (2 + 20 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by ring
  rw [he] at h
  exact h

/-- **CGP02 (b), slim block.** At a point of the closed support of the slim cutoff `ζ_j`, the slim
block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` (`η_j` on the axis of `ℝ²`) has Riemannian derivative at most
`((1 + σ) + (89·10⁴Δ + 1)·P₀(1 + σ)/(10⁵Δ)) ν` (`ℓ = 10⁵Δ`: `R|dη| ≤ 1 + σ`,
`R|dζ| ≤ P₀(1 + σ)/ℓ`, `|η| ≤ 8.9ℓ`). -/
theorem slim_block_budget_KA2_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (hΔ : 0 < Δ) (hσs : 0 ≤ σs) {j : X} (hj : j ∈ L.slim.centres) {x : X}
    (hx : x ∈ tsupport (L.slim.cutoff_BCNT j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * L.slim.cutoff_BCNT j y) •
        planeAxis ((L.slim.centre j hj).coord_BCG2 y), ρ j * L.slim.cutoff_BCNT j y)) x v‖ ≤
      ((1 + σs) + (89 * 10 ^ 4 * Δ + 1) * (cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ))) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  obtain ⟨h1, h2, h3, hcm⟩ := fc18_slim_row_BAUGP L hΔ hj
  have hxb : x ∈ ball j (10 ^ 6 * Δ * ρ j) := h3 (h2 (h1 hx))
  obtain ⟨hP1, -, hφ, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hc0 : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  set u := (L.slim.centre j hj).coord_BCG2 with hudef
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    (hcm.contMDiffAt (isOpen_ball.mem_nhds hxb)).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + σs) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hxb hud
      (fun y _ z _ => slimCentre_coord_lipschitz_KA2_BAUGP _ (by linarith) y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (u y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hη : ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ = |mvfderiv 𝓘(ℝ, E3) u x v| := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.slim.cutoff_BCNT j) x := by
    rw [slimFamily_cutoff_eq_KA2_BAUGP L hj]
    exact ((L.slim.centre j hj).contMDiff_cutoff_BCNT x).mdifferentiableAt (by simp)
  have hφd : HasDerivAt (fun t => slimCutoffProfile_LC87 (t / (10 ^ 5 * Δ)))
      (deriv slimCutoffProfile_LC87 (u x / (10 ^ 5 * Δ)) * (1 / (10 ^ 5 * Δ))) (u x) := by
    have hd : DifferentiableAt ℝ slimCutoffProfile_LC87 (u x / (10 ^ 5 * Δ)) :=
      ((contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).differentiable
        (by simp)) _
    exact hd.hasDerivAt.comp (u x) ((hasDerivAt_id' (u x)).div_const (10 ^ 5 * Δ))
  have hζ : |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff_BCNT j) x v| ≤
      cgpProfileBound * (1 / (10 ^ 5 * Δ)) * ((1 + σs) / ρ j * ν) := by
    rw [mvfderiv_apply_congr_KA2 (slim_cutoff_eventuallyEq_KA2_BAUGP L hj hxb) v,
      mvfderiv_comp_hasDerivAt hud hφd v, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hc0)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hφ _) (one_div_pos.mpr hc0).le) hu
      (abs_nonneg _) (by positivity)
  have hC : ‖planeAxis (u x)‖ ≤ 89 * 10 ^ 4 * Δ := by
    rw [norm_planeAxis]
    refine le_of_mem_tsupport_KA2 (u := fun y => |u y|) hx hud.continuousAt.abs fun y hy => ?_
    rw [slimFamily_cutoff_eq_KA2_BAUGP L hj] at hy
    exact slimCentre_abs_coord_lt_of_cutoff_ne_zero_KA2_BAUGP _ hy
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ ≤ (1 + σs) * ν := by
    rw [hη]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) u x v| ≤ ρ j * ((1 + σs) / ρ j * ν) :=
          mul_le_mul_of_nonneg_left hu hrj.le
      _ = (1 + σs) * ν := by field_simp
  have hb : ρ j * |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff_BCNT j) x v| ≤
      cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ) * ν := by
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (L.slim.cutoff_BCNT j) x v| ≤
          ρ j * (cgpProfileBound * (1 / (10 ^ 5 * Δ)) * ((1 + σs) / ρ j * ν)) :=
          mul_le_mul_of_nonneg_left hζ hrj.le
      _ = cgpProfileBound * (1 + σs) / (10 ^ 5 * Δ) * ν := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := L.slim.cutoff_BCNT j)
    (η := fun y => planeAxis (u y)) mdifferentiableAt_const hζd hηd v hrj.le
    ((slimFamily_cutoff_eq_KA2_BAUGP L hj) ▸ (L.slim.centre j hj).cutoff_mem_Icc_BCNT x)
    hC ha hb hl
  rw [add_zero] at h
  exact h

/-- **CGP02 (b), zero block.** At a point of the closed support of LC31's annular cutoff
`Φ ∘ r` of a zero-model ball (`e ≤ 1/8`), the zero block `(R Φ(r) r, R Φ(r))` (`r` on the axis of
`ℝ²`, `R` the ball's radius) has Riemannian derivative at most
`((1 + ε) + (9/10 + 2e + 1)·P₀(1 + ε)) ν` (`R|dr| ≤ 1 + ε`, `R|dζ| ≤ P₀(1 + ε)`,
`|r| ≤ 9/10 + 2e`). -/
theorem zero_block_budget_KA2_BDFB {N' C' : X → Type} [∀ a, MetricSpace (N' a)]
    [∀ a, ChartedSpace E3 (N' a)] [∀ a, MetricSpace (C' a)] {o' : ∀ a, C' a} {δ' εr e : ℝ}
    (Zb : ZeroModelBall 𝓘(ℝ, E3) X g N' C' o' δ' εr e)
    (hmet : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (hεr : 0 ≤ εr)
    (he : e ≤ 1 / 8) {x : X} (hx : x ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2
        ((Zb.radius * Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)) •
          planeAxis (Zb.radial y),
        Zb.radius * Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y))) x v‖ ≤
      ((1 + εr) + (9 / 10 + 2 * e + 1) * (cgpProfileBound * (1 + εr))) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  obtain ⟨hlip, hnn, hclose, hts, O, hO, hOsub, hOsm⟩ :=
    zeroModelBall_radial_facts_KA2 Zb (by linarith)
  have hxs := hts hx
  have hxO : x ∈ O := hOsub ⟨by linarith [hxs.1], by linarith [hxs.2]⟩
  obtain ⟨hP1, -, -, -, -, hΦ, -⟩ := cgpProfileBound_spec
  have hr := Zb.radius_pos
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  set u := Zb.radial with hudef
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    (hOsm.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + εr) / Zb.radius * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmet isOpen_univ (mem_univ x) hud
      (fun y _ z _ => hlip y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (u y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hη : ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ = |mvfderiv 𝓘(ℝ, E3) u x v| := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
  have hΦd : HasDerivAt (Calculus.annularCutoff Calculus.cutoffProfile)
      (deriv (Calculus.annularCutoff Calculus.cutoffProfile) (u x)) (u x) :=
    ((Calculus.annularCutoff_contDiff Calculus.cutoffProfile_contDiff).differentiable (by simp)
      (u x)).hasDerivAt
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x :=
    hΦd.differentiableAt.comp_mdifferentiableAt hud
  have hζ : |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v|
      ≤ cgpProfileBound * ((1 + εr) / Zb.radius * ν) := by
    rw [mvfderiv_comp_hasDerivAt hud hΦd v, abs_mul]
    exact mul_le_mul (hΦ _) hu (abs_nonneg _) (by linarith)
  have hC : ‖planeAxis (u x)‖ ≤ 9 / 10 + 2 * e := by
    rw [norm_planeAxis, abs_of_nonneg (hnn x)]
    have h := abs_lt.mp (hclose x)
    linarith [hxs.2]
  have ha : Zb.radius * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (u y)) x v‖ ≤ (1 + εr) * ν := by
    rw [hη]
    calc Zb.radius * |mvfderiv 𝓘(ℝ, E3) u x v| ≤ Zb.radius * ((1 + εr) / Zb.radius * ν) :=
          mul_le_mul_of_nonneg_left hu hr.le
      _ = (1 + εr) * ν := by field_simp
  have hb : Zb.radius *
      |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v| ≤
      cgpProfileBound * (1 + εr) * ν := by
    calc Zb.radius *
          |mvfderiv 𝓘(ℝ, E3) (fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y)) x v|
        ≤ Zb.radius * (cgpProfileBound * ((1 + εr) / Zb.radius * ν)) :=
          mul_le_mul_of_nonneg_left hζ hr.le
      _ = cgpProfileBound * (1 + εr) * ν := by field_simp
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => Zb.radius) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have hz : Calculus.annularCutoff Calculus.cutoffProfile (u x) ∈ Icc (0 : ℝ) 1 :=
    Calculus.annularCutoff_mem_Icc Calculus.cutoffProfile_mem_Icc _
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => Zb.radius)
    (ζ := fun y => Calculus.annularCutoff Calculus.cutoffProfile (u y))
    (η := fun y => planeAxis (u y)) mdifferentiableAt_const hζd hηd v hr.le hz hC ha hb hl
  rw [add_zero] at h
  exact h

/-- **The actual edge cutoff's derivative budget** on the physical chart ball (CGP02's
`R|dζ| ≤ 5P₀/Δ`, here `P₀((1 + σ) + (100/99)(1 + γ))/Δ`): the cutoff is
`f(η_j/Δ) g(t/Δ)`; where `g` varies the point is a collar point (`ρ(x) ≥ (99/100)ρ(j)`,
`ρ|dt| ≤ 1 + γ`). -/
theorem EdgeFamilyOn.cutoff_deriv_budget_KA2_BDFB {β : ℕ → ℝ}
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hΔ : 0 < Δ) (hσc : 0 ≤ σc)
    (hγc : 0 ≤ γc) (hρc : Continuous ρ) {j : X} (hj : j ∈ F.centres) {x : X}
    (hxb : x ∈ ball j (100 * Δ * ρ j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ρ j * |mvfderiv 𝓘(ℝ, E3) (F.cutoff_BAUGA j) x v| ≤
      cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  obtain ⟨hP1, -, -, hf, hg, -⟩ := cgpProfileBound_spec
  have hrj := hρ j
  have hrx := hρ x
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hK : 0 ≤ cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by positivity
  have hfd : Differentiable ℝ edgeCoordinateProfile :=
    edgeProfiles_contDiff.1.differentiable (by simp)
  have hgd : Differentiable ℝ edgeHeightProfile :=
    edgeProfiles_contDiff.2.1.differentiable (by simp)
  set u := F.coord_BAUGA j with hudef
  set t : X → ℝ := fun y => F.smoothing y / ρ y with htdef
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have heq : F.cutoff_BAUGA j =ᶠ[𝓝 x] fun y => edgeCoordinateProfile (u y / Δ) *
      edgeHeightProfile (t y / Δ) := by
    filter_upwards [hball] with y hy
    exact F.cutoff_eq_formula_BAUGA hj hy
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) u x :=
    ((F.contMDiffOn_coord_BAUGA hj).contMDiffAt hball).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) u x v| ≤ (1 + σc) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
      (fun y _ z _ => F.coord_lipschitz_KA2_BAUGP (by linarith) hj y z) v
  obtain ⟨hAd, hA⟩ := abs_mvfderiv_profile_div_le_KA2 hfd hf hΔ hud v
  have htc : Continuous fun y => t y / Δ :=
    (F.lipschitz_smoothing.continuous.div hρc fun y => (hρ y).ne').div_const Δ
  have hzero : F.cutoff_BAUGA j =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) →
      ρ j * |mvfderiv 𝓘(ℝ, E3) (F.cutoff_BAUGA j) x v| ≤
        cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by
    intro h0
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [mvfderiv_apply_congr_KA2 heq v]
  -- case analysis
  by_cases hcx : 9 * Δ < |u x|
  · have hA0 : (fun y => edgeCoordinateProfile (u y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      have hcc : ContinuousAt u x := hud.continuousAt
      rcases lt_abs.mp hcx with hpos | hneg
      · filter_upwards [hcc.eventually (lt_mem_nhds hpos)] with y hy
        refine intervalPlateauProfile_zero_right (by norm_num) ?_
        rw [le_div_iff₀ hΔ]
        linarith
      · have hneg' : u x < -(9 * Δ) := by linarith
        filter_upwards [hcc.eventually (gt_mem_nhds hneg')] with y hy
        refine intervalPlateauProfile_zero_left (by norm_num) ?_
        rw [div_le_iff₀ hΔ]
        linarith
    have h0 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [hA0] with y hy
      rw [hy, zero_mul]
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [not_lt] at hcx
  by_cases h9 : 9 < t x / Δ
  · have h0 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [htc.continuousAt.eventually (lt_mem_nhds h9)] with y hy
      rw [show edgeHeightProfile (t y / Δ) = 0 from
        descendingIntervalProfile_zero (by norm_num) hy.le, mul_zero]
    rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_const]
    simpa using hK
  rw [not_lt] at h9
  by_cases h8 : t x / Δ < 8
  · have h1 : (fun y => edgeCoordinateProfile (u y / Δ) * edgeHeightProfile (t y / Δ)) =ᶠ[𝓝 x]
        fun y => edgeCoordinateProfile (u y / Δ) := by
      filter_upwards [htc.continuousAt.eventually (gt_mem_nhds h8)] with y hy
      rw [show edgeHeightProfile (t y / Δ) = 1 from
        descendingIntervalProfile_one (by norm_num) hy.le, mul_one]
    rw [mvfderiv_apply_congr_KA2 h1 v]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
        ≤ ρ j * (cgpProfileBound / Δ * ((1 + σc) / ρ j * ν)) :=
          mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hu (by positivity)))
            hrj.le
      _ = cgpProfileBound * (1 + σc) / Δ * ν := by field_simp
      _ ≤ cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by
          have h0 : 0 ≤ cgpProfileBound * (100 / 99 * (1 + γc)) / Δ * ν := by positivity
          have he : cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν =
              cgpProfileBound * (1 + σc) / Δ * ν +
                cgpProfileBound * (100 / 99 * (1 + γc)) / Δ * ν := by ring
          linarith
  rw [not_lt] at h8
  -- collar case
  have htx : t x = Δ * (t x / Δ) := by field_simp
  have hc1 : Δ / 10 ≤ F.smoothing x / ρ x := by
    change Δ / 10 ≤ t x
    rw [htx]
    nlinarith
  have hc2 : F.smoothing x / ρ x ≤ 10 * Δ := by
    change t x ≤ 10 * Δ
    rw [htx]
    nlinarith
  have hcoord10 : |F.coord_BAUGA j x| ≤ 10 * Δ := by
    change |u x| ≤ 10 * Δ
    linarith
  obtain ⟨hratio, htlip⟩ := F.height_lipschitz_of_collar_KA2_BAUGP hj hxb hcoord10 hc1 hc2
  have htd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) t x :=
    (F.contMDiffAt_height_of_collar_BAUGA hj hxb hcoord10 hc1 hc2).mdifferentiableAt (by simp)
  have hx100 : x ∈ ball x (100 * ρ x) := mem_ball_self (by positivity)
  have ht : |mvfderiv 𝓘(ℝ, E3) t x v| ≤ (1 + γc) / ρ x * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100 htd htlip v
  obtain ⟨hBd, hB⟩ := abs_mvfderiv_profile_div_le_KA2 hgd hg hΔ htd v
  rw [mvfderiv_mul_apply_KA2 hAd hBd v]
  have hfx := (edgeProfiles_mem_Icc (u x / Δ)).1
  have hgx := (edgeProfiles_mem_Icc (t x / Δ)).2.1
  have hratio' : ρ j / ρ x ≤ 100 / 99 := by
    rw [div_le_iff₀ hrx]
    rw [le_div_iff₀ hrj] at hratio
    linarith
  have hT1 : |edgeCoordinateProfile (u x / Δ) *
      mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v| ≤
      cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) := by
    rw [abs_mul, abs_of_nonneg hfx.1]
    calc edgeCoordinateProfile (u x / Δ) *
          |mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v|
        ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) t x v|) :=
          mul_le_mul hfx.2 hB (abs_nonneg _) zero_le_one
      _ ≤ cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hT2 : |edgeHeightProfile (t x / Δ) *
      mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v| ≤
      cgpProfileBound / Δ * ((1 + σc) / ρ j * ν) := by
    rw [abs_mul, abs_of_nonneg hgx.1]
    calc edgeHeightProfile (t x / Δ) *
          |mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
        ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) u x v|) :=
          mul_le_mul hgx.2 hA (abs_nonneg _) zero_le_one
      _ ≤ cgpProfileBound / Δ * ((1 + σc) / ρ j * ν) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hsum := (abs_add_le _ _).trans (add_le_add hT1 hT2)
  have hrjx : ρ j * ((1 + γc) / ρ x) ≤ 100 / 99 * (1 + γc) := by
    rw [mul_div_assoc', mul_comm (ρ j), mul_div_assoc]
    calc (1 + γc) * (ρ j / ρ x) ≤ (1 + γc) * (100 / 99) :=
          mul_le_mul_of_nonneg_left hratio' (by linarith)
      _ = 100 / 99 * (1 + γc) := by ring
  calc ρ j * |edgeCoordinateProfile (u x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => edgeHeightProfile (t y / Δ)) x v +
        edgeHeightProfile (t x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => edgeCoordinateProfile (u y / Δ)) x v|
      ≤ ρ j * (cgpProfileBound / Δ * ((1 + γc) / ρ x * ν) +
          cgpProfileBound / Δ * ((1 + σc) / ρ j * ν)) := mul_le_mul_of_nonneg_left hsum hrj.le
    _ = cgpProfileBound / Δ * ν * (ρ j * ((1 + γc) / ρ x)) +
          cgpProfileBound * (1 + σc) / Δ * ν := by field_simp
    _ ≤ cgpProfileBound / Δ * ν * (100 / 99 * (1 + γc)) +
          cgpProfileBound * (1 + σc) / Δ * ν := by gcongr
    _ = cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ * ν := by ring

/-- **CGP02 (b), edge block.** At a point of the closed support of the actual edge cutoff `ζ_j`
(with the zero-extension margin), the edge block `(ρ(j) ζ_j η_j, ρ(j) ζ_j)` has Riemannian
derivative at most `((1 + σ) + (9Δ + 1) K) ν`, `K = P₀((1 + σ) + (100/99)(1 + γ))/Δ`
(`R|dη| ≤ 1 + σ`, `R|dζ| ≤ K`, `|η| ≤ 9Δ`). -/
theorem edge_block_budget_KA2_BDFB {β : ℕ → ℝ}
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hΔ : 0 < Δ) (hσc : 0 ≤ σc)
    (hγc : 0 ≤ γc) (hρc : Continuous ρ) {j : X} (hj : j ∈ F.centres)
    (hm : tsupport (F.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) {x : X}
    (hx : x ∈ tsupport (F.cutoff_BAUGA j)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ j * F.cutoff_BAUGA j y) • planeAxis (F.coord_BAUGA j y),
        ρ j * F.cutoff_BAUGA j y)) x v‖ ≤
      ((1 + σc) + (9 * Δ + 1) * (cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ)) *
        Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  have hxb := hm hx
  have hrj := hρ j
  set ν := Real.sqrt (g.inner x v v) with hνdef
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.coord_BAUGA j) x :=
    ((F.contMDiffOn_coord_BAUGA hj).contMDiffAt hball).mdifferentiableAt (by simp)
  have hu : |mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v| ≤ (1 + σc) / ρ j * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
      (fun y _ z _ => F.coord_lipschitz_KA2_BAUGP (by linarith) hj y z) v
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (F.coord_BAUGA j y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hud
  have hζd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.cutoff_BAUGA j) x :=
    (F.contMDiff_cutoff_of_margin_BAUGA hΔ hρc hm x).mdifferentiableAt (by simp)
  have ha : ρ j * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (F.coord_BAUGA j y)) x v‖ ≤
      (1 + σc) * ν := by
    rw [mvfderiv_clm_comp hud planeAxis v, norm_planeAxis]
    calc ρ j * |mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v| ≤ ρ j * ((1 + σc) / ρ j * ν) :=
          mul_le_mul_of_nonneg_left hu hrj.le
      _ = (1 + σc) * ν := by field_simp
  have hb := F.cutoff_deriv_budget_KA2_BDFB hΔ hσc hγc hρc hj hxb v
  have hC : ‖planeAxis (F.coord_BAUGA j x)‖ ≤ 9 * Δ := by
    rw [norm_planeAxis]
    exact le_of_mem_tsupport_KA2 (u := fun y => |F.coord_BAUGA j y|) hx hud.continuousAt.abs
      fun y hy => (F.mem_of_cutoff_ne_zero_BAUGA hΔ hy).2.2.1
  have hl : |mvfderiv 𝓘(ℝ, E3) (fun _ : X => ρ j) x v| ≤ 0 * ν := by
    rw [mvfderiv_const]
    simp
  have h := norm_mvfderiv_block_apply_le (R := fun _ : X => ρ j) (ζ := F.cutoff_BAUGA j)
    (η := fun y => planeAxis (F.coord_BAUGA j y)) mdifferentiableAt_const hζd hηd v hrj.le
    (F.cutoff_mem_Icc_BAUGA hΔ j x) hC ha hb hl
  rw [add_zero] at h
  exact h

open Classical in
/-- **CGP02 (b), the `E'` block** `(ρ z₀ t, ρ z₀)`, `z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i)`, at a point of
its closed support (with the edge zero-extension margin): its Riemannian derivative is at most
`((1 + γ) + (10Δ + 1)(b_E + Λ)) ν` with
`b_E = P₀(1 + γ)/Δ + P₀ n (1 + 100ΔΛ) K` (`n` = number of edge cutoffs whose closed support contains
the point, `K` the edge budget): `ρ|dt| ≤ 1 + γ` (collar), `|dρ| ≤ Λ`, `t ≤ 10Δ`,
`ρ(x) ≤ (1 + 100ΔΛ)ρ(i)` on `B̄(i, 100Δρ(i))`. -/
theorem edgeMarker_block_budget_KA2_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hσc : 0 ≤ σc) (hγc : 0 ≤ γc)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j))
    {x : X} (hx : x ∈ tsupport (cgpEdgeMarker_BAUGP L)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => WithLp.toLp 2 ((ρ y * cgpEdgeMarker_BAUGP L y) •
        planeAxis (cgpHeight_BAUGP L y), ρ y * cgpEdgeMarker_BAUGP L y)) x v‖ ≤
      ((1 + γc) + (10 * Δ + 1) * (cgpProfileBound * (1 + γc) / Δ +
        cgpProfileBound * ((Finset.univ.filter fun i : L.edgeB.finite_centres.toFinset =>
          x ∈ tsupport (L.edgeB.cutoff_BAUGA i)).card : ℝ) *
          ((1 + 100 * Δ * Λ) * (cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ)) +
        Λ)) * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  obtain ⟨hP1, -, -, -, -, -, hH, hRmp⟩ := cgpProfileBound_spec
  set Kb := cgpProfileBound * ((1 + σc) + 100 / 99 * (1 + γc)) / Δ with hKdef
  set ν := Real.sqrt (g.inner x v v) with hνdef
  set n : ℝ := ((Finset.univ.filter fun i : L.edgeB.finite_centres.toFinset =>
    x ∈ tsupport (L.edgeB.cutoff_BAUGA i)).card : ℝ) with hndef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Kb := by positivity
  have hrx := hρ x
  have hρc : Continuous ρ := L.contMDiff_scale.continuous
  obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := tsupport_cgpEdgeMarker_subset_BAUGP L hΔ hmargin hx
  obtain ⟨-, htlip⟩ := L.edgeB.height_lipschitz_of_collar_KA2_BAUGP hk hxk hck.le hk1.le hk2.le
  have htd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpHeight_BAUGP L) x :=
    (L.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le hk1.le hk2.le).mdifferentiableAt (by simp)
  have hx100 : x ∈ ball x (100 * ρ x) := mem_ball_self (by positivity)
  have ht : |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| ≤ (1 + γc) / ρ x * ν :=
    abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx100 htd htlip v
  have hρd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ρ x :=
    (L.contMDiff_scale x).mdifferentiableAt (by simp)
  have hρv : |mvfderiv 𝓘(ℝ, E3) ρ x v| ≤ Λ * ν :=
    Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf g hmetric hΛ L.lipschitz_scale
      hρd v
  -- the edge sum
  have hcut_d : ∀ i : L.edgeB.finite_centres.toFinset,
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (L.edgeB.cutoff_BAUGA i) x := fun i =>
    (L.edgeB.contMDiff_cutoff_of_margin_BAUGA hΔ hρc (hmargin i.1 ((Set.Finite.mem_toFinset _).mp i.2))
      x).mdifferentiableAt (by simp)
  have hSd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpEdgeSum_BAUGP L) x :=
    (continuous_cgpEdgeSum_BAUGP L hΔ hmargin x).mdifferentiableAt (by simp)
  have hSv : mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v =
      ∑ i : L.edgeB.finite_centres.toFinset, mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v :=
    mvfderiv_sum_apply_KA2 Finset.univ (f := fun i : L.edgeB.finite_centres.toFinset =>
      L.edgeB.cutoff_BAUGA i) (fun i _ => hcut_d i) v
  have hterm : ∀ i : L.edgeB.finite_centres.toFinset,
      ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v| ≤
        if x ∈ tsupport (L.edgeB.cutoff_BAUGA i) then (1 + 100 * Δ * Λ) * Kb * ν else 0 := by
    intro i
    have hi' := (Set.Finite.mem_toFinset _).mp i.2
    split_ifs with hi
    · have hxbi := hmargin i.1 hi' hi
      have hbi := L.edgeB.cutoff_deriv_budget_KA2_BDFB hΔ hσc hγc hρc hi' hxbi v
      have hri := hρ i.1
      have hlip := L.lipschitz_scale.dist_le_mul x i.1
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
      have hdi : dist x i.1 < 100 * Δ * ρ i.1 := mem_ball.mp hxbi
      have hratio : ρ x ≤ (1 + 100 * Δ * Λ) * ρ i.1 := by
        have h1 := (abs_le.mp hlip).2
        have h2 : Λ * dist x i.1 ≤ Λ * (100 * Δ * ρ i.1) :=
          mul_le_mul_of_nonneg_left hdi.le hΛ
        nlinarith
      calc ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v|
          ≤ (1 + 100 * Δ * Λ) * ρ i.1 * |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
        _ = (1 + 100 * Δ * Λ) * (ρ i.1 * |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v|) := by ring
        _ ≤ (1 + 100 * Δ * Λ) * (Kb * ν) :=
            mul_le_mul_of_nonneg_left hbi (by positivity)
        _ = (1 + 100 * Δ * Λ) * Kb * ν := by ring
    · have h0 := notMem_tsupport_iff_eventuallyEq.mp hi
      rw [mvfderiv_apply_congr_KA2 h0 v, mvfderiv_zero]
      simp
  have hS : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v| ≤ n * ((1 + 100 * Δ * Λ) * Kb * ν) := by
    rw [hSv]
    calc ρ x * |∑ i : L.edgeB.finite_centres.toFinset, mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v|
        ≤ ρ x * ∑ i : L.edgeB.finite_centres.toFinset,
            |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hrx.le
      _ = ∑ i : L.edgeB.finite_centres.toFinset,
            ρ x * |mvfderiv 𝓘(ℝ, E3) (L.edgeB.cutoff_BAUGA i) x v| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ i : L.edgeB.finite_centres.toFinset, (if x ∈ tsupport (L.edgeB.cutoff_BAUGA i) then
            (1 + 100 * Δ * Λ) * Kb * ν else 0) := Finset.sum_le_sum fun i _ => hterm i
      _ = n * ((1 + 100 * Δ * Λ) * Kb * ν) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the marker
  obtain ⟨hAd, hA⟩ := abs_mvfderiv_profile_div_le_KA2 (cgpEdgeH_contDiff.differentiable (by simp))
    hH hΔ htd v
  have hRd : HasDerivAt (cfsRamp lc87EdgeTransition (1 / 2) 1)
      (deriv (cfsRamp lc87EdgeTransition (1 / 2) 1) (cgpEdgeSum_BAUGP L x)) (cgpEdgeSum_BAUGP L x) :=
    (((contDiff_cfsRamp lc87EdgeTransition_contDiff (1 / 2) 1).differentiable (by simp))
      (cgpEdgeSum_BAUGP L x)).hasDerivAt
  have hBd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y)) x :=
    hRd.differentiableAt.comp_mdifferentiableAt hSd
  have hB : |mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y))
      x v| ≤ cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v| := by
    rw [mvfderiv_comp_hasDerivAt hSd hRd v, abs_mul]
    exact mul_le_mul_of_nonneg_right (hRmp _) (abs_nonneg _)
  have hzv : mvfderiv 𝓘(ℝ, E3) (cgpEdgeMarker_BAUGP L) x v =
      cgpEdgeH (cgpHeight_BAUGP L x / Δ) *
          mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y)) x v +
        cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x) *
          mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight_BAUGP L y / Δ)) x v :=
    mvfderiv_mul_apply_KA2 hAd hBd v
  have hHx := cgpEdgeH_mem_Icc (cgpHeight_BAUGP L x / Δ)
  have hRx := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 2) 1 (cgpEdgeSum_BAUGP L x)
  have hzd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (cgpEdgeMarker_BAUGP L) x :=
    (contMDiff_cgpEdgeMarker_BAUGP L hΔ hmargin x).mdifferentiableAt (by simp)
  have hb : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeMarker_BAUGP L) x v| ≤
      (cgpProfileBound * (1 + γc) / Δ + cgpProfileBound * n * ((1 + 100 * Δ * Λ) * Kb)) * ν := by
    rw [hzv]
    have hT1 : |cgpEdgeH (cgpHeight_BAUGP L x / Δ) *
        mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y)) x v| ≤
        cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v| := by
      rw [abs_mul, abs_of_nonneg hHx.1]
      calc cgpEdgeH (cgpHeight_BAUGP L x / Δ) *
            |mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y))
              x v| ≤ 1 * (cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v|) :=
            mul_le_mul hHx.2 hB (abs_nonneg _) zero_le_one
        _ = cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v| := one_mul _
    have hT2 : |cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x) *
        mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight_BAUGP L y / Δ)) x v| ≤
        cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| := by
      rw [abs_mul, abs_of_nonneg hRx.1]
      calc cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x) *
            |mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight_BAUGP L y / Δ)) x v|
          ≤ 1 * (cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v|) :=
            mul_le_mul hRx.2 hA (abs_nonneg _) zero_le_one
        _ = cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| := one_mul _
    have hsum := (abs_add_le _ _).trans (add_le_add hT1 hT2)
    have hρt : ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| ≤ (1 + γc) * ν := by
      calc ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| ≤ ρ x * ((1 + γc) / ρ x * ν) :=
            mul_le_mul_of_nonneg_left ht hrx.le
        _ = (1 + γc) * ν := by field_simp
    have hP0 : 0 ≤ cgpProfileBound := by linarith
    calc ρ x * |cgpEdgeH (cgpHeight_BAUGP L x / Δ) *
            mvfderiv 𝓘(ℝ, E3) (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y))
              x v +
          cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x) *
            mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeH (cgpHeight_BAUGP L y / Δ)) x v|
        ≤ ρ x * (cgpProfileBound * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v| +
            cgpProfileBound / Δ * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v|) :=
          mul_le_mul_of_nonneg_left hsum hrx.le
      _ = cgpProfileBound * (ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpEdgeSum_BAUGP L) x v|) +
            cgpProfileBound / Δ * (ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v|) := by ring
      _ ≤ cgpProfileBound * (n * ((1 + 100 * Δ * Λ) * Kb * ν)) +
            cgpProfileBound / Δ * ((1 + γc) * ν) := by
          gcongr
      _ = (cgpProfileBound * (1 + γc) / Δ + cgpProfileBound * n * ((1 + 100 * Δ * Λ) * Kb)) *
            ν := by ring
  -- the block
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun y => planeAxis (cgpHeight_BAUGP L y)) x :=
    planeAxis.hasFDerivAt.differentiableAt.comp_mdifferentiableAt htd
  have ha : ρ x * ‖mvfderiv 𝓘(ℝ, E3) (fun y => planeAxis (cgpHeight_BAUGP L y)) x v‖ ≤
      (1 + γc) * ν := by
    rw [mvfderiv_clm_comp htd planeAxis v, norm_planeAxis]
    calc ρ x * |mvfderiv 𝓘(ℝ, E3) (cgpHeight_BAUGP L) x v| ≤ ρ x * ((1 + γc) / ρ x * ν) :=
          mul_le_mul_of_nonneg_left ht hrx.le
      _ = (1 + γc) * ν := by field_simp
  have hC : ‖planeAxis (cgpHeight_BAUGP L x)‖ ≤ 10 * Δ := by
    rw [norm_planeAxis, abs_of_nonneg (cgpHeight_nonneg_BAUGP L x)]
    exact hk2.le
  have h := norm_mvfderiv_block_apply_le (R := ρ) (ζ := cgpEdgeMarker_BAUGP L)
    (η := fun y => planeAxis (cgpHeight_BAUGP L y)) hρd hzd hηd v hrx.le (cgpEdgeMarker_mem_Icc_BAUGP L x)
    hC ha hb hρv
  exact h

end Families


end DifferentialGeometry.Geometry.Collapse
