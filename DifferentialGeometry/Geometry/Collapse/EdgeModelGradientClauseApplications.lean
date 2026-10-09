import DifferentialGeometry.Geometry.Collapse.EdgeModelGradientClause

/-!
# Consumer of LFR28 B7: `hGgrad` of (LFR28.4) from LFR24's rescaled gradient clause

`edgeModel_gradient_clause_of_rescaled_carrier`: on the isometric product chart
`Θ : ℝ × S → N` (`e ∘ Θ = (t, ψ ·)`, `Θ^*G = dt² + κ`), with R2's rescaled carrier metric
`κΔ = Δ⁻² κ` and its direction transfer, a smoothing `F` of the distance to `s₀` on the rescaled
carrier `(S, Δ⁻¹ d)` that is smooth on an open `O_F ⊇ {3/4 ≤ Δ⁻¹ d(·, s₀) ≤ 91/10}` with the
all-direction gradient clause of error `ε` there (the exported clause of
`finiteSurface_edge_model_core_global`, B6) gives the model gradient clause `hGgrad` of
`eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le` (F7-LFR28B G3) VERBATIM, for
`G_N = Δ · F ∘ (Θ⁻¹ ·).2`, `Φ = e`, `z₀ = ψ s₀`, `ε_N = ε`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **LFR28 B7 (binding).** The model gradient clause `hGgrad` of `(LFR28.4)` for
`G_N = Δ · F ∘ (Θ⁻¹ ·).2` from the rescaled gradient clause of LFR24's smoothing `F`. -/
theorem edgeModel_gradient_clause_of_rescaled_carrier {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W]
    [mS : MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r r' : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ κΔ : ContMDiffRiemannianMetric (𝓡 2) ((r' : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr' : 2 ≤ r')
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W) {m : WithTop ℕ∞} (hm : 2 ≤ m)
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N m)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hκΔ : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κΔ.inner x v w = Δ⁻¹ ^ 2 * κ.inner x v w)
    (htrans : ∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
      u ∈ κ.finiteMinimizingDirectionsTo Y s →
        letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
        Δ • u ∈ κΔ.finiteMinimizingDirectionsTo Y s)
    (s₀ : S) {F : S → ℝ} {OF : Set S} {ε : ℝ} (hε : 0 ≤ ε) (hOFo : IsOpen OF)
    (hOF : letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
      {x | 3 / 4 ≤ dist x s₀ ∧ dist x s₀ ≤ 91 / 10} ⊆ OF)
    (hFs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ F OF)
    (hgrad : letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
      ∀ x ∈ OF, ∀ v ∈ κΔ.finiteMinimizingDirectionsTo ({s₀} : Set S) x,
        ∀ w : TangentSpace (𝓡 2) x,
          |mvfderiv (𝓡 2) F x w + κΔ.inner x v w| ≤ ε * Real.sqrt (κΔ.inner x w w)) :
    ∀ x : N, |(e x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (e x).snd (ψ s₀) →
      dist (e x).snd (ψ s₀) ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {z | z.snd = ψ s₀}) x,
        ∀ X : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y => Δ * F (Θ.symm y).2) x X + G.inner x v X| ≤
            ε * Real.sqrt (G.inner x X X) := by
  have hF : ∀ s : S, 5 / 2 * Δ ≤ dist s s₀ → dist s s₀ ≤ 13 / 2 * Δ →
      MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) F s ∧
        ∀ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s, ∀ w : TangentSpace (𝓡 2) s,
          |Δ * mvfderiv (𝓡 2) F s w + κ.inner s u w| ≤ ε * Real.sqrt (κ.inner s w w) := by
    intro s h1 h2
    have hsO : s ∈ OF := by
      apply hOF
      have hd : Δ⁻¹ * dist s s₀ ∈ Icc (5 / 2 : ℝ) (13 / 2) := by
        constructor
        · rw [le_inv_mul_iff₀ hΔ]
          linarith
        · rw [inv_mul_le_iff₀ hΔ]
          linarith
      have hl : (3 / 4 : ℝ) ≤ Δ⁻¹ * dist s s₀ := le_trans (by norm_num) hd.1
      have hu : Δ⁻¹ * dist s s₀ ≤ 91 / 10 := le_trans hd.2 (by norm_num)
      exact ⟨hl, hu⟩
    refine ⟨((hFs s hsO).contMDiffAt (hOFo.mem_nhds hsO)).mdifferentiableAt (by simp), ?_⟩
    exact gradient_clause_of_rescaled κ κΔ hΔ hκΔ htrans s₀ s (hgrad s hsO)
  intro x _ h1 h2
  exact edgeModel_gradient_clause_of_product G hr hGnorm κ hr' hκnorm e ψ hm Θ he hpull s₀ hΔ
    hε hF x h1 h2

end DifferentialGeometry.Geometry.Collapse
