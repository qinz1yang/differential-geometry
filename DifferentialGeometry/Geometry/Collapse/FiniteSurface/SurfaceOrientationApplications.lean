import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientation

/-!
# Consumer: LFR16 orientable clause and LFR17 for a finite Cheeger–Gromov limit

`surfaceFactor_sphere_or_flat_torus_of_finite_limit`: an oriented finite limit in the L-CONS shape
(metric of natural order `K - 1`, `K ≥ 4`, carried by `⟨G.toRiemannianMetric⟩`, proper, connected)
with `sec ≥ 0` and an exact line splitting with compact residual factor of diameter `≤ D`: the
surface factor has an oriented compact connected smooth carrier on `𝓡 2`, homeomorphic to the
factor, which is diffeomorphic to the round `S²` or to a flat `ℝ²/ℤ²`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

universe u

/-- LFR16 (orientable surface factor) and LFR17 (its smooth type) for an oriented finite limit. -/
theorem surfaceFactor_sphere_or_flat_torus_of_finite_limit {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N] [ConnectedSpace N]
    [MetricSpace W] [CompactSpace W] (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      Nonempty (S ≃ₜ {x : N // (e x).fst = 0}) ∧
      (Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
        Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x),
      0 ≤ (finiteMetricReindex K hK G).sectionalCurvature x v w := fun x v w => hsec x v w
  obtain ⟨S, mS, cS, iS, hc, hconn, ho, φ, -, -, κ, -, -, htype⟩ :=
    surfaceFactor_smoothCarrier_oriented (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) hsec' oN hD e
  exact ⟨S, mS, cS, iS, hc, hconn, ho, ⟨φ⟩, Or.imp id And.left htype⟩

end DifferentialGeometry.Geometry.Collapse
