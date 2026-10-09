import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrier

/-!
# Consumer: LFR17 on the surface factor of a finite Cheeger–Gromov limit

`surfaceFactor_smoothCarrier_of_finite_limit`: for a finite limit in the L-CONS shape (metric of
natural order `K - 1`, `K ≥ 4`, carried by `⟨G.toRiemannianMetric⟩`, proper, connected), with
`sec ≥ 0` and an exact line splitting with compact residual factor of diameter `≤ D`, the surface
factor has a compact connected smooth carrier on `𝓡 2` with a nonnegatively curved metric, which
is `S²` or a flat `T²` as soon as it is orientable.
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

local instance nezero_finrank_euclidean_three_carrier_app_F7LFR11b :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u

/-- LFR17 on the surface factor of a finite limit, for every orientation of its carrier. -/
theorem surfaceFactor_smoothCarrier_of_finite_limit {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N] [ConnectedSpace N]
    [MetricSpace W] [CompactSpace W] (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧
      Nonempty (S ≃ₜ {x : N // (e x).fst = 0}) ∧
      ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 2 + 1 : ℕ) : ℕ∞ω) E2
          (TangentSpace (𝓡 2) : S → Type _),
        (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
        (Nonempty (ManifoldOrientation (𝓡 2) S 2) →
          Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
            (Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
              ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κ.sectionalCurvature x v w = 0)) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x),
      0 ≤ (finiteMetricReindex K hK G).sectionalCurvature x v w := fun x v w => hsec x v w
  obtain ⟨S, mS, cS, iS, hc, hconn, φ, -, -, κ, -, hκ, hor⟩ :=
    surfaceFactor_smoothCarrier (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) hsec' hD e
  exact ⟨S, mS, cS, iS, hc, hconn, ⟨φ⟩, κ, hκ, hor⟩

end DifferentialGeometry.Geometry.Collapse
