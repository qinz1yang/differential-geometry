import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.AxisMinimizingDirections

/-!
# Consumers of R1a and R1 (lane LFR28-R12)

* `expMap_axisDirection_endpoint` (from R1a): the minimizing geodesic from `x` to the axis
  `e⁻¹{snd = z₀}` ends at the point `e⁻¹(t_x, z₀)` of the time slice of `x` (the foot point is the
  orthogonal projection).
* `inner_mfderiv_axisMinimizingDirection` (from R1, with the product pull-back `Θ^*G = dt² + κ`):
  against a minimizing direction `v` to the axis, every lifted vector `dΘ(a, w)` pairs as
  `κ(w, u)` for a `κ`-minimizing direction `u` from `s` to `s₀`; in particular the time direction
  `dΘ(1, 0)` is `G`-orthogonal to `v` (the shape of the model gradient clause of LFR28.4 for
  `Δ · F_S ∘ (Θ⁻¹ ·).2`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The foot point on the axis is in the time slice.** For a minimizing direction `v` from `x` to
the axis `e⁻¹{snd = z₀}`, `exp_x(d(x, axis) v) = e⁻¹(t_x, z₀)`. -/
theorem expMap_axisDirection_endpoint {N W : Type} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W] {r : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) (x : N) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {p | p.snd = z₀}) x) :
    G.expMap (⟨x, infDist x (e ⁻¹' {p | p.snd = z₀}) • v⟩ : TangentBundle 𝓘(ℝ, E3) N) =
      e.symm (WithLp.toLp 2 ((e x).fst, z₀)) := by
  have hfst := expMap_axisDirection_fst_eq G hr hGnorm e z₀ x v hv
    (infDist x (e ⁻¹' {p | p.snd = z₀})) ⟨infDist_nonneg, le_rfl⟩
  have hsnd : (e (G.expMap (⟨x, infDist x (e ⁻¹' {p | p.snd = z₀}) • v⟩ :
      TangentBundle 𝓘(ℝ, E3) N))).snd = z₀ := hv.2
  apply e.injective
  rw [e.apply_symm_apply]
  exact congrArg (WithLp.toLp 2) (Prod.ext hfst hsnd)

/-- **Pairing with a minimizing direction to the axis.** With `Θ^*G = dt² + κ`, for every
`G`-minimizing direction `v` from `Θ(t, s)` (`s ≠ s₀`) to the axis `e⁻¹{snd = ψ s₀}` there is a
`κ`-minimizing direction `u` from `s` to `s₀` with `G(dΘ(a, w), v) = κ(w, u)` for all `(a, w)`; in
particular `G(dΘ(1, 0), v) = 0`. -/
theorem inner_mfderiv_axisMinimizingDirection {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W]
    [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r r' : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ : ContMDiffRiemannianMetric (𝓡 2) ((r' : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr' : 2 ≤ r')
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W)
    (Θ : ℝ × S → N) (Θinv : N → ℝ × S) (hΘl : ∀ p, Θinv (Θ p) = p) (hΘr : ∀ x, Θ (Θinv x) = x)
    (hΘ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) 2 Θ)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (s₀ : S) (t : ℝ) (s : S) (hs : s ≠ s₀) :
    ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {p | p.snd = ψ s₀}) (Θ (t, s)),
      ∃ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s,
        ∀ (a : ℝ) (w : TangentSpace (𝓡 2) s),
          G.inner (Θ (t, s))
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s)
              ((a, w) : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) (t, s))) v = κ.inner s w u := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := axisMinimizingDirection_eq_mfderiv_horizontal G hr hGnorm κ hr' hκnorm
    e ψ Θ Θinv hΘl hΘr hΘ he s₀ t s hs v hv
  refine ⟨u, hu, fun a w => ?_⟩
  rw [hpull (t, s) (a, w) ((0 : ℝ), u)]
  change a * 0 + κ.inner s w u = κ.inner s w u
  rw [mul_zero, zero_add]

end DifferentialGeometry.Geometry.Collapse
