import DifferentialGeometry.Geometry.Collapse.FiniteSurface.CarrierRescale

/-!
# Consumer of R2: minimizing directions of the rescaled carrier

The instance package of `exists_rescaled_carrier_metric` is exactly what the finite-order
minimizing-direction theory needs: on `(S, Δ⁻¹ d, ⟨Δ⁻² κ⟩)` the minimizing directions to a closed
nonempty set are nonempty and compact (CM3.a run in the rescaled carrier), and every one of them is
`Δ •` a minimizing direction of `κ`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The rescaled carrier has minimizing directions.** For the carrier of R2, the metric
`κΔ = Δ⁻² κ` has `sec ≥ 0` and, in `(S, Δ⁻¹ d)`, nonempty compact minimizing directions to every
closed nonempty `Y`, each of them `Δ •` a `κ`-minimizing direction. -/
theorem rescaledCarrier_minimizingDirections {S : Type} [mS : MetricSpace S] [ChartedSpace E2 S]
    [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r : ℕ∞} (κ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr : 2 ≤ r)
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (hκsec : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w)
    {Δ : ℝ} (hΔ : 0 < Δ) {Y : Set S} (hY : IsClosed Y) (hYne : Y.Nonempty) (s : S) :
    ∃ κΔ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
        (TangentSpace (𝓡 2) : S → Type _),
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κΔ.sectionalCurvature x v w) ∧
      (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
       (κΔ.finiteMinimizingDirectionsTo Y s).Nonempty ∧
         IsCompact (κΔ.finiteMinimizingDirectionsTo Y s)) ∧
      ∀ u : TangentSpace (𝓡 2) s,
        (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
         u ∈ κΔ.finiteMinimizingDirectionsTo Y s) →
          Δ⁻¹ • u ∈ κ.finiteMinimizingDirectionsTo Y s := by
  obtain ⟨κΔ, -, hsec, -, hback, hpack⟩ := exists_rescaled_carrier_metric κ hκnorm hκsec hΔ
  refine ⟨κΔ, hsec, ?_, fun u hu => hback Y s u hu⟩
  have neZero_LFR28R12 : NeZero (Module.finrank ℝ E2) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  let metric_LFR28R12 := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
  let bundle_LFR28R12 : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) :=
    ⟨κΔ.toRiemannianMetric⟩
  obtain ⟨hRiem, hcomp, hnorm⟩ := hpack
  have hYc : IsClosed Y := hY
  exact κΔ.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm hYc hYne s

end DifferentialGeometry.Geometry.Collapse
