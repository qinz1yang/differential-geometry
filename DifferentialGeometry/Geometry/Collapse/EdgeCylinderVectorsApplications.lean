import DifferentialGeometry.Geometry.Collapse.EdgeCylinderVectors
import DifferentialGeometry.Geometry.Collapse.EdgeCylinderVerticalDirection

/-!
# Consumers of LFR28 B4 / B4b: the vector conditions from the product chart and the vertical field

* `mfderiv_edgeCylinder_eq_verticalField` (B4b + LFR18's uniqueness form): if the minimizing
  directions from `y` to its vertical shift are exactly `{V y}` (the `hVdir` clause of LFR18's
  `exists_vertical_field_eventually_inverse_directions_close`), then the product chart of
  `exists_edgeCylinderProductChart_vertical` carries `∂_t` to the vertical field: `dΘ_p(1, 0) = V (Θ p)`.
* `edgeCylinder_vectors_of_productChart` (B4 with the product pull-back): with `Θ^*G = dt² + κ`
  and `dΘ(1, 0) = V ∘ Θ`, the `(LFR28.3)` bound in its F7-DOWN form (against `G(V, ·)`), the
  `(LFR28.4)` bound, the model derivative identity and a `κ`-unit-ball model direction `Y` with
  `Δ dh(Y) ≥ 1/2` give the eight `hpair` clauses of `edgeSourceSlab_disk_bundle_of_model` at `x`;
  `edgeCylinder_row_of_productChart` gives the two `hrow` clauses.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open Bundle

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **B4b + LFR18.** If the minimizing directions to the vertical shift by `ℓ > 0` are the
singletons `{V y}`, a chart `Θ` whose time derivative is such a minimizing direction carries `∂_t`
to `V`. -/
theorem mfderiv_edgeCylinder_eq_verticalField {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [MetricSpace W] [TopologicalSpace S]
    [ChartedSpace E2 S] {n : ℕ∞ω}
    {r : WithTop ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (e : N ≃ᵢ WithLp 2 (ℝ × W))
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) {ℓ : ℝ}
    (hΘV : ∀ p : ℝ × S,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) ∈
        G.finiteMinimizingDirectionsTo
          {e.symm (WithLp.toLp 2 ((e (Θ p)).fst + ℓ, (e (Θ p)).snd))} (Θ p))
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (hVdir : ∀ y, G.finiteMinimizingDirectionsTo
      {e.symm (WithLp.toLp 2 ((e y).fst + ℓ, (e y).snd))} y = {V y}) (p : ℝ × S) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) = V (Θ p) := by
  have h := hΘV p
  rw [hVdir (Θ p)] at h
  exact h

/-- **LFR28 B4 with the product chart (pair).** -/
theorem edgeCylinder_vectors_of_productChart {S : Type*} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] {X : Type*}
    {z₀ : S} {h : S → ℝ} {Δ : ℝ} {r : WithTop ℕ∞}
    (hr : r ≠ 0) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) (j : N → X)
    {f H : X → ℝ} {GN : N → ℝ} {n n' : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (x : edgeModelCylinder z₀ Δ)
    (hΘV : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)) =
      V (Θ x))
    (hhx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2)
    (hfj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f (j y)) (Θ x))
    (hHj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => H (j y)) (Θ x))
    (h3 : ∀ Z : TangentSpace 𝓘(ℝ, E3) (Θ x),
      |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z - G.inner (Θ x) (V (Θ x)) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z))
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 1000)
    (h4 : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => H (j y)) (Θ x) Z - mvfderiv 𝓘(ℝ, E3) GN (Θ x) Z| ≤
      c * Real.sqrt (G.inner (Θ x) Z Z))
    (hGN : ∀ (a : ℝ) (Y : E2), mvfderiv 𝓘(ℝ, E3) GN (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) (a, Y)) =
        Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 Y)
    {Y : E2} (hY1 : κ.inner (x : ℝ × S).2 Y Y ≤ 1)
    (hY2 : 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 Y) :
    ∃ X₁ X₂ : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₁).1 = 1 ∧
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₂).1 = 0 ∧
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₁).2 = 0 ∧
      1 / 2 ≤ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₂).2 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₁).1 - 1|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₂).1|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₁).2|
          ≤ 1 / 1000 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₂).2 -
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₂).2| ≤ 1 / 1000 := by
  have hVV : G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) = 1 := by
    rw [hpull (x : ℝ × S) ((1 : ℝ), (0 : E2)) ((1 : ℝ), (0 : E2))]
    have hz : κ.inner (x : ℝ × S).2 (0 : E2) = 0 := (κ.inner (x : ℝ × S).2).map_zero
    rw [hz]
    change (1 : ℝ) * 1 + 0 = 1
    norm_num
  have hVY : ∀ Y : E2, G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)) = 0 := by
    intro Y
    rw [hpull (x : ℝ × S) ((1 : ℝ), (0 : E2)) ((0 : ℝ), Y)]
    have hz : κ.inner (x : ℝ × S).2 (0 : E2) = 0 := (κ.inner (x : ℝ × S).2).map_zero
    rw [hz]
    change (1 : ℝ) * 0 + 0 = 0
    norm_num
  have hY1' : G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((0 : ℝ), Y)) ≤ 1 := by
    rw [hpull (x : ℝ × S) ((0 : ℝ), Y) ((0 : ℝ), Y)]
    change (0 : ℝ) * 0 + κ.inner (x : ℝ × S).2 Y Y ≤ 1
    rw [mul_zero, zero_add]
    exact hY1
  have h3' : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z -
      G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z) := by
    intro Z
    rw [hΘV]
    exact h3 Z
  exact edgeCylinder_vectors_of_covector_bounds hr Θ j G x hhx hfj hHj hVV hVY h3' hc0 hc h4 hGN
    hY1' hY2

/-- **LFR28 B4 with the product chart (row).** -/
theorem edgeCylinder_row_of_productChart {S : Type*} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] {X : Type*}
    {z₀ : S} {h : S → ℝ} {Δ : ℝ} {r : WithTop ℕ∞}
    (hr : r ≠ 0) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r) (j : N → X)
    {f H : X → ℝ} {n n' : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (x : edgeModelCylinder z₀ Δ)
    (hΘV : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)) =
      V (Θ x))
    (hhx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2)
    (hfj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f (j y)) (Θ x))
    (hHj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => H (j y)) (Θ x))
    (h3 : ∀ Z : TangentSpace 𝓘(ℝ, E3) (Θ x),
      |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z - G.inner (Θ x) (V (Θ x)) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z)) :
    ∃ X₀ : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
        x X₀).1 = 1 ∧
      |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun z : edgeModelCylinder z₀ Δ => ((f (j (Θ z)), H (j (Θ z))) : ℝ × ℝ)) x X₀).1 - 1|
        ≤ 1 / 1000 := by
  have hVV : G.inner (Θ x)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2)))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) = 1 := by
    rw [hpull (x : ℝ × S) ((1 : ℝ), (0 : E2)) ((1 : ℝ), (0 : E2))]
    have hz : κ.inner (x : ℝ × S).2 (0 : E2) = 0 := (κ.inner (x : ℝ × S).2).map_zero
    rw [hz]
    change (1 : ℝ) * 1 + 0 = 1
    norm_num
  have h3' : ∀ Z : E3, |mvfderiv 𝓘(ℝ, E3) (fun y => f (j y)) (Θ x) Z -
      G.inner (Θ x) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) ((1 : ℝ), (0 : E2))) Z| ≤
        1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z) := by
    intro Z
    rw [hΘV]
    exact h3 Z
  exact edgeCylinder_row_of_covector_bound (h := h) hr Θ j G x hhx hfj hHj hVV h3'

end DifferentialGeometry.Geometry.Collapse
