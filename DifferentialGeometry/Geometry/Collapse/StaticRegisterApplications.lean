import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples
import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalRankApplications

/-!
# Consumers of the static registers and the counterexample framework

* LC18 bound into the closed register: with the β₃ slot equal to LC18's actual obstruction
  (`exists_uniform_three_splitting_exclusion`), the register's β₃ satisfies the uniform
  three-splitting exclusion at every σ ≤ β₃ (PR12, B:10136).
* The register's analytic data on a closed counterexample member: at `w'` and
  `C = 2R + 2 < n` the member satisfies `|∇^k Rm| ≤ 2^{-(K+2)} 𝒜(R) r_p(w')^{-(k+2)}` with PR20's
  `𝒜(R) = 2^{K+2} A'(2R+2, w')` (B:10200).
* The literal DI certificate of the merged LFR50 design (§8) in the counterexample framework.
* A concrete inhabited early-data/threshold pair, showing the register types are not vacuous.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open DifferentialGeometry GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u v w

/-- PR12 (B:10136) bound to LC18: the closed register whose β₃ slot is LC18's actual obstruction
`η` has a β₃ at which the three-splitting exclusion holds for every `σ ≤ β₃`. -/
theorem exists_closedRegister_three_splitting_exclusion (D : ClosedEarlyData)
    (T : ClosedThresholds D) :
    ∃ (η : ℝ) (hη : 0 < η), η < 1 / 10 ∧
      ∃ R : ClosedRegister D { T with lc18 := η, lc18_pos := hη },
        R.later.excl.β₃ < η ∧
        ∀ (Z : Type u) [MetricSpace Z] (z : Z) (C : Type v) [MetricSpace C] [CompleteSpace C]
          (c : C),
          (∀ x y : C, ∃ γ : Icc (0 : ℝ) 1 → C, Continuous γ ∧
            γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
            ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) →
          dimH (univ : Set C) ≤ 2 →
          DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison 0
            (univ : Set C) →
          ∀ σ : ℝ, σ ≤ R.later.excl.β₃ → GC.MetricGeometry.KleinerLottApprox z c σ →
            ¬ GC.MetricGeometry.HasEuclideanSplitting.{u, w} z 3 R.later.excl.β₃ := by
  obtain ⟨η, hη, hηsmall, hex⟩ := GC.MetricGeometry.exists_uniform_three_splitting_exclusion.{u, v, w}
  obtain ⟨R⟩ := exists_closedRegister D { T with lc18 := η, lc18_pos := hη }
  have hβ₃ : R.later.excl.β₃ < η := R.later.β₃_lt
  refine ⟨η, hη, hηsmall, R, hβ₃, ?_⟩
  intro Z _ z C _ _ c hseg hdim hcomp σ hσ
  exact hex Z z C c hseg hdim hcomp σ R.later.excl.β₃ (hσ.trans hβ₃.le) hβ₃.le

/-- PR20 (B:10198–10200) on a closed counterexample member: for an index `n ≥ 2` with
`1/n ≤ w'` and a radius `ρ ≥ 0` with `2ρ + 2 < n`, the member's whole-ball bounds on
`B(p, (2ρ+2) r_p(w'))` are `2^{-(K+2)} 𝒜(ρ) r_p(w')^{-(k+2)}`, with the register's
`𝒜(ρ) = 2^{K+2} A'(2ρ+2, w')`. -/
theorem curvatureDerivativeNorm_le_closedAnalyticBound {D : ClosedEarlyData}
    {T : ClosedThresholds D} (R : ClosedRegister D T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : closedCollapseHypotheses W g K A (closedCounterexampleRatio n))
    (hw' : (n : ℝ)⁻¹ ≤ closedWPrime R.later.scale) (p : W.Carrier) {ρ : ℝ}
    (hρ : 2 * ρ + 2 < n) :
    ∀ k ≤ K, ∀ q ∈ riemannianBallOf g p
        ((2 * ρ + 2) * firstVolumeScale g p (closedWPrime R.later.scale)),
      curvatureDerivativeNorm g k q ≤
        (2 ^ (K + 2))⁻¹ * closedAnalyticBound K (boundaryDerivativeConstant A K) R.later.scale ρ *
          (firstVolumeScale g p (closedWPrime R.later.scale) ^ (k + 2))⁻¹ := by
  intro k hk q hq
  have hwc : closedWPrime R.later.scale < euclideanThreeUnitBallVolume :=
    R.later.wPrime_lt_w.trans R.later.w_lt_volume
  have hb := closed_reduce_of_closedCollapseHypotheses hn h p hρ hw' hwc k hk q hq
  unfold closedAnalyticBound
  rwa [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The merged LFR50/DI design (§8): the literal certificate of the finite-scale producer. -/
theorem exists_closed_standing_sequence_of_no_aux_threshold (K : ℕ) (A : ℝ → ℝ)
    (h : ¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
          (Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
                DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0))) :
    ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      ∀ n, (∀ p, curvatureRadius (g n) p ≠ ⊤) ∧
        closedCollapseHypotheses (W n) (g n) K A (closedCounterexampleRatio (n + 2)) ∧
        IsEmpty (RawGraphPresentation (W n)) ∧
        (∀ g' : SmoothRiemannianMetric (W n).model (W n).Carrier,
          ¬ DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) ∧
        ∀ p, ENNReal.ofReal (2 * ((n + 2 : ℕ) : ℝ) *
          firstVolumeScale (g n) p ((n + 2 : ℕ) : ℝ)⁻¹) < curvatureRadius (g n) p := by
  obtain ⟨W, hW, g, hg⟩ := exists_closed_standing_sequence_of_no_threshold K A _ h
  refine ⟨W, hW, g, fun n => ⟨(hg n).1, (hg n).2.1, ?_, ?_, (hg n).2.2.2.1⟩⟩
  · exact not_nonempty_iff.mp fun hne => (hg n).2.2.1 (Or.inl hne)
  · exact fun g' hg' => (hg n).2.2.1 (Or.inr ⟨(hg n).2.1.1, g', hg'⟩)

/-- A concrete early datum (`N = 0`, `P = 1`, `C_j = 1`, `L₀ = 1`, `Ξ_j = id`). -/
def unitClosedEarlyData : ClosedEarlyData where
  N := 0
  P := 1
  one_le_P := le_rfl
  C := fun _ => 1
  C_pos := fun _ => one_pos
  L₀ := 1
  one_le_L₀ := le_rfl
  Ξ := fun _ Γ => Γ
  Ξ_pos := fun _ _ hΓ => hΓ
  Ξ_tendsto := fun _ => tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

/-- A concrete threshold record on `unitClosedEarlyData` (every upper slot `1`, LPA02 output
`V = T₀`, test radius `H_α = α`). -/
def unitClosedThresholds : ClosedThresholds unitClosedEarlyData where
  Nb := fun _ => 0
  Nb_nonneg := fun _ => le_rfl
  cw := fun _ => 0
  cw_nonneg := fun _ => le_rfl
  circleUp := fun _ _ _ _ => 1
  circleUp_pos := fun _ _ _ _ => one_pos
  lc18 := 1
  lc18_pos := one_pos
  β₂Up := fun _ _ _ => 1
  β₂Up_pos := fun _ _ _ => one_pos
  ΔLow := fun _ _ _ _ => 0
  errorsUp := fun _ _ _ => 1
  errorsUp_pos := fun _ _ _ => one_pos
  sectionUp := fun _ _ _ => 1
  sectionUp_pos := fun _ _ _ => one_pos
  lfr29W := fun _ _ _ => 1
  lfr29W_pos := fun _ _ _ => one_pos
  endpointUp := fun _ _ _ => 1
  endpointUp_pos := fun _ _ _ => one_pos
  σcol := 1 / 2
  σcol_pos := by norm_num
  σcol_lt_one := by norm_num
  I₁ := 1
  I₁_pos := one_pos
  scaleUp := fun _ _ _ _ => 1
  scaleUp_pos := fun _ _ _ _ => one_pos
  wUp := fun _ _ _ _ _ => 1
  wUp_pos := fun _ _ _ _ _ => one_pos
  splitUp := fun _ _ _ _ _ => 1
  splitUp_pos := fun _ _ _ _ _ => one_pos
  β₁Up := fun _ _ _ _ _ _ => 1
  β₁Up_pos := fun _ _ _ _ _ _ => one_pos
  T₀Low := fun _ _ _ _ _ _ _ => 0
  lpa02V := fun _ _ _ _ _ _ _ T₀ => T₀
  T₀_le_lpa02V := fun _ _ _ _ _ _ _ _ => le_rfl
  tailLow := fun _ _ _ _ _ _ => 0
  H := fun α => (α : ℝ)
  H_tendsto := tendsto_natCast_atTop_atTop

/-- The concrete pair admits a register; its edge error is below `10⁻³` (CAA01). -/
theorem unit_closedRegister_edgeError :
    ∃ R : ClosedRegister unitClosedEarlyData unitClosedThresholds,
      5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 1 / 1000 := by
  obtain ⟨R, -, h⟩ := exists_closedRegister_edgeError_lt unitClosedEarlyData unitClosedThresholds
  exact ⟨R, h⟩

end DifferentialGeometry.Geometry.Collapse
