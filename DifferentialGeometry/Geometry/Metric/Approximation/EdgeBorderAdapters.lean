import DifferentialGeometry.Geometry.Metric.HalfPlanePacking
import DifferentialGeometry.Geometry.Metric.Approximation.IntervalTargetExtension
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCoarseBorder
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# Edge border producer: adapters for LFR29–LFR32

Blueprint 207A, `sec:collapse-edge-border-producer` (A:27499–27768). The metric kernels of these rows are
already in the tree; this module states them in the rows' own form.

* LFR29 (`lem:collapse-half-plane-four-point-obstruction`, A:27551): `not_four_half_plane_border_directions`,
  the four named points, from `WithLp.not_approximate_orthogonal_cross_in_half_plane`.
* LFR30 (`lem:collapse-composite-edge-chart`, A:27579), last assertion: `exists_endpoint_extension_strict`, the
  SAME point function into `[0, max C (200Δ + s)]` is a KL `4s`-map with length `> 200Δ`
  (from `enlargeIntervalTarget`; the row's `s < 1/8` is relaxed to `s < 1/4`). (LFR30.1) is
  `stripMap_estimates`/`product_factor_composition_estimates`, (LFR30.2) is `exists_strip_border_lift`.
* LFR31 (`lem:collapse-edge-rescale-recenter`, A:27627) in physical units:
  `isEdgePoint_of_physical_lipschitz_scale` (the kernel `isEdgePoint_of_lipschitz_scale` has `ρ p = 1`).
* LFR32 (`thm:collapse-edge-coarse-border-producer`, A:27695) in physical units:
  `coarse_border_of_physical_lipschitz_scale`; the weak set uses every point's OWN physical scale
  `d / ρ(x)` and the chart lives in `d_p = d / ρ(p)`, exactly as in the row.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

/-- LFR29, verbatim: no four points of the closed upper half-plane form an approximate orthogonal
cross of unit vectors (all four cross distances tested). -/
theorem not_four_half_plane_border_directions {q₁p q₁m q₂p q₂m : WithLp 2 (ℝ × ℝ)} {e : ℝ}
    (he : 0 ≤ e) (hesmall : e ≤ 1 / 1000)
    (h₁p : 0 ≤ q₁p.snd) (h₁m : 0 ≤ q₁m.snd) (h₂p : 0 ≤ q₂p.snd) (h₂m : 0 ≤ q₂m.snd)
    (n₁p : |‖q₁p‖ - 1| ≤ e) (n₁m : |‖q₁m‖ - 1| ≤ e) (n₂p : |‖q₂p‖ - 1| ≤ e) (n₂m : |‖q₂m‖ - 1| ≤ e)
    (o₁ : |dist q₁p q₁m - 2| ≤ e) (o₂ : |dist q₂p q₂m - 2| ≤ e)
    (cpp : |dist q₁p q₂p - Real.sqrt 2| ≤ e) (cpm : |dist q₁p q₂m - Real.sqrt 2| ≤ e)
    (cmp : |dist q₁m q₂p - Real.sqrt 2| ≤ e) (cmm : |dist q₁m q₂m - Real.sqrt 2| ≤ e) : False := by
  let q : Fin 2 × Bool → WithLp 2 (ℝ × ℝ) := fun i =>
    if i.1 = 0 then (if i.2 then q₁m else q₁p) else (if i.2 then q₂m else q₂p)
  refine WithLp.not_approximate_orthogonal_cross_in_half_plane q he hesmall ?_ ?_ ?_ ?_
  · rintro ⟨i, t⟩
    fin_cases i <;> cases t <;> simpa [q]
  · rintro ⟨i, t⟩
    fin_cases i <;> cases t <;> simpa [q]
  · intro i
    fin_cases i <;> simpa [q]
  · intro s t
    cases s <;> cases t <;> simpa [q]

namespace KleinerLottApprox

variable {Y : Type*} [MetricSpace Y] {q : Y} {C s Δ : ℝ}

/-- LFR30, last assertion: if `C ≥ 200Δ` and `0 < s < 1/4`, the SAME point function `G`, regarded as
taking values in `[0, max C (200Δ + s)]`, is a KL `4s`-approximation whose target has length strictly
greater than `200Δ`. -/
theorem exists_endpoint_extension_strict (hC : 0 ≤ C)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hlength : 200 * Δ ≤ C) (hs : s < 1 / 4) :
    ∃ (L : ℝ) (hL : 0 ≤ L), L = max C (200 * Δ + s) ∧ 200 * Δ < L ∧
      ∃ G' : KleinerLottApprox q (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) L) (4 * s),
        ∀ y, (G'.toFun y : ℝ) = G.toFun y := by
  have hs0 := G.error_pos
  have hCL : C ≤ max C (200 * Δ + s) := le_max_left _ _
  have hLC : max C (200 * Δ + s) ≤ C + s := max_le (by linarith) (by linarith)
  refine ⟨max C (200 * Δ + s), hC.trans hCL, rfl,
    (show 200 * Δ < 200 * Δ + s by linarith).trans_le (le_max_right _ _),
    G.enlargeIntervalTarget hC hCL hLC hs, fun y => rfl⟩

end KleinerLottApprox

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]

/-- LFR31 in physical units. The strong maps at `p` live in `d_p = d / ρ(p)`; a point `a` with
`d(a,p) ≤ 101 Δ ρ(p)` whose residual image is `2b`-close to the residual basepoint is a weak edge
point in its OWN normalization `d / ρ(a)`, with endpoint length `> 200Δ`. -/
theorem isEdgePoint_of_physical_lipschitz_scale {p a : X} {q : Y}
    {Δ C β σ β' σ' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x)
    (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) σ)
    (hβ' : 0 < β') (hσ' : 0 < σ')
    (hsmallβ' : β' < 1 / 10000) (hsmallσ' : σ' < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < σ' / (100000000 * Δ ^ 2))
    (hβΔ : β' < 1 / (1000000 * Δ))
    (hσβ : σ < β' / 100000) (hσσ : σ < σ' / 100000)
    (hβσ : β < σ / 100000) (hββ : β < β' / 100000)
    (hlength : 200 * Δ ≤ C) (ha : dist a p ≤ 101 * Δ * ρ p)
    (hqa : dist (@KleinerLottApprox.toFun X (WithLp 2 (ℝ × Y))
      (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p _ β F a).snd q < 2 * β) :
    @isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ β' σ' := by
  have hrpos : 0 < ρ a / ρ p := div_pos (hρpos a) (hρpos p)
  have hr := @lipschitzWith_normalized_scale X mX ρ Λ hρ p (hρpos p)
  have hra : @dist X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toDist a p ≤ 101 * Δ := by
    rw [MetricSpace.rescale_dist, ← div_eq_inv_mul, div_le_iff₀ (hρpos p)]
    exact ha
  have h := @isEdgePoint_of_lipschitz_scale X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Y _
    p a q Δ C β σ β' σ' Λ
    (fun x => ρ x / ρ p) hr (div_self (hρpos p).ne') hrpos hΔ hC F G hβ' hσ' hsmallβ' hsmallσ'
    hscale hend hβΔ hσβ hσσ hβσ hββ hlength hra hqa
  have heq := mX.rescale_inv_ratio (hρpos p) (hρpos a)
  simp only at h
  rw [heq] at h
  exact h

/-- LFR32 in physical units: for a strong edge point `p` (maps in `d_p = d / ρ(p)`), the actual composite
`Q_p = stripMap F G` and the closure of the weak edge set `E'` (each point at its own scale `d / ρ(x)`)
satisfy every clause of the coarse-border hypothesis LFR25.1, with all distances in `d_p`. -/
theorem coarse_border_of_physical_lipschitz_scale {p : X} {q : Y} {C b s : ℝ} {hC : 0 ≤ C}
    {Δ τ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000)
    (hbs : b < s / 100000) (hlength : 200 * Δ ≤ C) :
    let E : Set X := {x | @isEdgePoint.{u, v} X
      (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
    letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    IsClosed (closure E) ∧ p ∈ closure E ∧ F.stripMap G p = 0 ∧
      (∀ x, 0 ≤ (F.stripMap G x).snd) ∧
      (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
        |dist (F.stripMap G x) (F.stripMap G y) - dist x y| ≤ τ * Δ) ∧
      (∀ y : WithLp 2 (ℝ × ℝ), |y.fst| ≤ 100 * Δ → y.snd ∈ Icc 0 (100 * Δ) →
        ∃ x ∈ ball p (200 * Δ), dist (F.stripMap G x) y < τ * Δ) ∧
      (∀ a ∈ closure E ∩ ball p (190 * Δ), (F.stripMap G a).snd ≤ τ * Δ) ∧
      ∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ E ∩ ball p (190 * Δ),
        dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) < τ * Δ := by
  have hr := @lipschitzWith_normalized_scale X mX ρ Λ hρ p (hρpos p)
  have h := @KleinerLottApprox.coarse_border_of_lipschitz_scale X Y
    (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p q C b s hC Δ τ b' s'
    Λ (fun x => ρ x / ρ p) F G hr (fun x => div_pos (hρpos x) (hρpos p))
    (div_self (hρpos p).ne') hΔ hτ hτsmall hscale hend hb'domain hs'domain hb'error hs'error
    hsb' hss' hbs hlength
  intro E
  have hE : {x | @isEdgePoint.{u, v} X ((mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale
      (ρ x / ρ p)⁻¹ (inv_pos.mpr (div_pos (hρpos x) (hρpos p)))) x Δ b' s'} = E := by
    ext x
    simp only [mem_ofPred_eq, E]
    rw [mX.rescale_inv_ratio (hρpos p) (hρpos x)]
  simp only at h
  rw [hE] at h
  exact h

end GC.MetricGeometry
