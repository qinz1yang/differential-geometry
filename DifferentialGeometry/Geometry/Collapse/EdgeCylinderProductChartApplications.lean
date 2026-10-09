import DifferentialGeometry.Geometry.Collapse.EdgeCylinderProductChart

/-!
# Consumer: the product chart on the actual oriented carrier

B2 (`surfaceFactor_smoothCarrier_oriented_noncompact`, lane LFR28-B12) composed with R5
(`exists_edgeCylinderProductChart`): on an oriented complete nonnegatively curved `3`-manifold with an
exact line splitting `e : N ≃ᵢ ℓ²(ℝ × W)` there are an oriented complete connected smooth carrier
surface `S` with its `C^{k+1}` metric `κ` (sec `≥ 0`, Riemannian for `⟨κ⟩`), an isometry
`ψ : S ≃ᵢ W` and a `C^{k+2}` diffeomorphism `Θ : ℝ × S → N` with `e ∘ Θ = (t, ψ)` and
`Θ^*G = dt² + κ` — exactly the data of R1 (`he`, `hpull`) and of B3
(`edgeCylinderProductChart_of_carrier`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **Concrete consumer.** The product chart of the model on its actual oriented carrier. -/
theorem edgeCylinderProductChart_of_carrier {N W : Type} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N]
    [SecondCountableTopology N] [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    ∃ (S : Type) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S)
      (ψ : S ≃ᵢ W) (κ : ContMDiffRiemannianMetric (𝓡 2) ((k + 1 : ℕ) : ℕ∞ω) E2
        (TangentSpace (𝓡 2) : S → Type _))
      (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N ((k + 2 : ℕ) : ℕ∞ω)),
      CompleteSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
      (letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
       IsRiemannianManifold (𝓡 2) S ∧
         ∀ (x : S) (w : TangentSpace (𝓡 2) x),
           ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w))) ∧
      (∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2)) ∧
      ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
        G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2 := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  obtain ⟨S, mS, cS, iS, hc, hconn, ho, φ, hφ, hφs, -, ⟨ψ, hψ⟩, κ, hκ, hsecS, hR⟩ :=
    surfaceFactor_smoothCarrier_oriented_noncompact G hk hnorm hsec oN e
  obtain ⟨Θ, he, hpull⟩ := exists_edgeCylinderProductChart G hk hnorm hsec e φ hφ hφs κ hκ
  refine ⟨S, mS, cS, iS, ψ, κ, Θ, hc, hconn, ho, hsecS, hR, fun p => ?_, hpull⟩
  rw [he, hψ]

end DifferentialGeometry.Geometry.Collapse
