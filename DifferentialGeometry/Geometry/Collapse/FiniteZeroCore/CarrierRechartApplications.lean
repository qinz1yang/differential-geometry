import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierRechart

/-!
# Consumers of the re-charted carrier (lane LFR49-A, group G2)

* `exists_carrierRechart_riemannian`: for LFR47's data — a smooth total space `X` (model
  `EB × F`), a finite model `(N, G)` with `G ∈ C^{r+1}`, `6 ≤ r`, a Riemannian manifold for `G`,
  complete and proper, and LFR46's `C^{r-2}` diffeomorphism `e : X ≃ N` — and any linear
  equivalence `Λ : EB × F ≃L E`, the re-charted carrier `N'` is a complete proper Riemannian
  manifold over `𝓘(ℝ, E)` for the transported metric `G' ∈ C^{(r-4)+1}`, with the tangent norm
  `√G'`, an isometry `κ : N' ≃ᵢ N` of class `C¹` with `G' = κ^* G`, and a SMOOTH
  `D' : X ≃ N'` with `κ ∘ D' = e`.
* Non-vacuity: `carrierRechartExample` — the product `ℝ² × ℝ` (a trivial line bundle over the
  plane) carried onto `ℝ³` by the linear equivalence `productModelEquiv 2` and re-charted by the
  same equivalence; the carrier is a smooth Riemannian three-manifold for the transported
  Euclidean metric (`carrierRechartExample_isRiemannianManifold`), and the identity of the points
  sends `⟨0⟩` to `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology (productModelEquiv)

universe uN

/-- `(r - 4) + 1 ≤ r + 1` in the orders of differentiability. -/
theorem carrierRechart_order_le (r : ℕ∞) :
    (((r - 4 : ℕ∞) : ℕ∞ω) + 1) ≤ (r : ℕ∞ω) + 1 := by
  have h : ((r - 4 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast tsub_le_self
  exact add_le_add_left h 1

/-- `(r - 4) + 1 + 1 ≤ r - 2` for `4 ≤ r`. -/
theorem carrierRechart_order_add_one_le {r : ℕ∞} (hr : 4 ≤ r) :
    (((r - 4 : ℕ∞) : ℕ∞ω) + 1) + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω) := by
  have h : r - 4 + 1 + 1 ≤ r - 2 := by
    induction r using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have hn : 4 ≤ n := by exact_mod_cast hr
      have h4 : ((n : ℕ∞) - 4) = ((n - 4 : ℕ) : ℕ∞) := by norm_cast
      have h2 : ((n : ℕ∞) - 2) = ((n - 2 : ℕ) : ℕ∞) := by norm_cast
      rw [h4, h2]
      exact_mod_cast (show n - 4 + 1 + 1 ≤ n - 2 by omega)
  exact_mod_cast h

/-- `2 ≤ r - 4` for `6 ≤ r`. -/
theorem carrierRechart_two_le_order {r : ℕ∞} (hr : 6 ≤ r) : (2 : ℕ∞) ≤ r - 4 := by
  induction r using ENat.recTopCoe with
  | top => simp
  | coe n =>
    have hn : 6 ≤ n := by exact_mod_cast hr
    have h4 : ((n : ℕ∞) - 4) = ((n - 4 : ℕ) : ℕ∞) := by norm_cast
    rw [h4]
    exact_mod_cast (show 2 ≤ n - 4 by omega)

section Soul

variable {EB F E : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
  [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]
  {N : Type uN} [MetricSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x)] [IsRiemannianManifold 𝓘(ℝ, E) N]

/-- **The re-charted LFR47 carrier is a complete proper Riemannian manifold over `𝓘(ℝ, E)`.** -/
theorem exists_carrierRechart_riemannian [CompleteSpace N] [ProperSpace N] {r : ℕ∞}
    (hr : 6 ≤ r)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((r : ℕ∞ω) + 1) E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (e : X ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N)
    (Λ : (EB × F) ≃L[ℝ] E) :
    ∃ (N' : Type uN) (mN' : MetricSpace N') (cN' : ChartedSpace E N'),
      letI := mN'
      letI := cN'
      ∃ (_ : IsManifold 𝓘(ℝ, E) ∞ N') (_ : RiemannianBundle (fun y : N' => TangentSpace 𝓘(ℝ, E) y))
        (_ : IsRiemannianManifold 𝓘(ℝ, E) N') (r' : ℕ∞) (_ : 2 ≤ r')
        (G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((r' : ℕ∞ω) + 1) E
          (TangentSpace 𝓘(ℝ, E) : N' → Type _))
        (κ : N' ≃ᵢ N) (D' : Diffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, E) X N' ∞),
        CompleteSpace N' ∧ ProperSpace N' ∧
        (∀ (y : N') (w : TangentSpace 𝓘(ℝ, E) y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner y w w))) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (κ : N' → N) ∧
        (∀ (y : N') (v w : TangentSpace 𝓘(ℝ, E) y), G'.inner y v w =
          G.inner (κ y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (κ : N' → N) y v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (κ : N' → N) y w)) ∧
        ∀ z, κ (D' z) = e z := by
  have hmn := carrierRechart_order_le r
  have hms := carrierRechart_order_add_one_le (le_trans (by norm_num) hr : (4 : ℕ∞) ≤ r)
  set G' := CarrierRechart.metric Λ e G hmn hms with hG'
  let rb : RiemannianBundle
      (fun y : CarrierRechart e.toHomeomorph Λ => TangentSpace 𝓘(ℝ, E) y) := ⟨G'.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ) :=
    CarrierRechart.isRiemannianManifold Λ e G hmn hms hGnorm
  have hκ : (CarrierRechart.isometryEquiv e.toHomeomorph Λ : CarrierRechart e.toHomeomorph Λ → N) =
      CarrierRechart.identity Λ e := rfl
  have h1 : (1 : ℕ∞ω) ≤ ((r - 2 : ℕ∞) : ℕ∞ω) := le_trans le_add_self hms
  refine ⟨CarrierRechart e.toHomeomorph Λ, inferInstance, inferInstance, inferInstance, rb, hRM,
    r - 4, carrierRechart_two_le_order hr, G', CarrierRechart.isometryEquiv e.toHomeomorph Λ,
    CarrierRechart.diffeomorph e.toHomeomorph Λ, inferInstance, inferInstance,
    CarrierRechart.enorm_eq Λ e G hmn hms, ?_, fun y v w => ?_, fun z => ?_⟩
  · rw [hκ]
    exact (CarrierRechart.identity Λ e).contMDiff.of_le h1
  · rw [hκ]
    rfl
  · rfl

end Soul

section Example

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The linear equivalence `ℝ² × ℝ ≃ ℝ³`, as a smooth diffeomorphism from the PRODUCT manifold
`ℝ² × ℝ` (model `𝓘(ℝ, ℝ²).prod 𝓘(ℝ, ℝ)`) onto `ℝ³`. -/
def carrierRechartExampleDiffeomorph :
    (E2 × ℝ) ≃ₘ⟮𝓘(ℝ, E2).prod 𝓘(ℝ, ℝ), 𝓘(ℝ, E3)⟯ E3 where
  toEquiv := (productModelEquiv 2).toEquiv
  contMDiff_toFun := by
    have h : ContMDiff (𝓘(ℝ, E2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) ∞ (fun p : E2 × ℝ => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (productModelEquiv 2).contDiff.contMDiff.comp h
  contMDiff_invFun := by
    have h1 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ (fun x => ((productModelEquiv 2).symm x).1) :=
      (contDiff_fst.comp (productModelEquiv 2).symm.contDiff).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun x => ((productModelEquiv 2).symm x).2) :=
      (contDiff_snd.comp (productModelEquiv 2).symm.contDiff).contMDiff
    exact h1.prodMk h2

/-- **Non-vacuity of `CarrierRechart`.** The product `ℝ² × ℝ`, carried onto `ℝ³` and re-charted
by `productModelEquiv 2`. -/
abbrev carrierRechartExample : Type :=
  CarrierRechart carrierRechartExampleDiffeomorph.toHomeomorph (productModelEquiv 2)

/-- The transported Euclidean metric (order three) on the example carrier. -/
def carrierRechartExampleMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, E3) 3 E3
      (TangentSpace 𝓘(ℝ, E3) : carrierRechartExample → Type _) :=
  CarrierRechart.metric (productModelEquiv 2) carrierRechartExampleDiffeomorph
    (riemannianMetricVectorSpace E3) le_top (by norm_num)

/-- **The example carrier is a smooth Riemannian three-manifold** for the transported Euclidean
metric, proper and complete, and its identity of the points sends `⟨0⟩` to `0`. -/
theorem carrierRechartExample_isRiemannianManifold :
    IsManifold 𝓘(ℝ, E3) ∞ carrierRechartExample ∧ ProperSpace carrierRechartExample ∧
      CompleteSpace carrierRechartExample ∧
      (letI : RiemannianBundle (fun y : carrierRechartExample => TangentSpace 𝓘(ℝ, E3) y) :=
        ⟨carrierRechartExampleMetric.toRiemannianMetric⟩
       IsRiemannianManifold 𝓘(ℝ, E3) carrierRechartExample) ∧
      CarrierRechart.identity (productModelEquiv 2) carrierRechartExampleDiffeomorph
        (⟨0⟩ : carrierRechartExample) = 0 :=
  ⟨inferInstance, inferInstance, inferInstance,
    CarrierRechart.isRiemannianManifold (productModelEquiv 2) carrierRechartExampleDiffeomorph
      (riemannianMetricVectorSpace E3) _ _
      (fun x w => DifferentialGeometry.Topology.Manifold.enorm_tangent_eq_sqrt_inner
        (riemannianMetricVectorSpace E3) x w), rfl⟩

end Example

end DifferentialGeometry.Geometry.Collapse
