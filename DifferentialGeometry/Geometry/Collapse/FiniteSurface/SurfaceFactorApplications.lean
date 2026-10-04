import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceFactor

/-!
# Consumers of the LFR16 surface clause

* `surfaceFactor_diam_le`: the surface factor of a finite limit is a nonempty compact set of
  diameter at most `D` (the form used by the slim-packet constants of LFR20);
* `surfaceFactor_isometric_residual`: the same factor is isometric to the residual factor `W`.
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

local instance nezero_finrank_euclidean_three_app_F7LFR11b :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {N W : Type*} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
  [MetricSpace W]

/-- The surface factor of a finite limit is nonempty, compact, of diameter at most `D`. -/
theorem surfaceFactor_diam_le [ProperSpace N] [ConnectedSpace N] [CompactSpace W]
    (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    Nonempty {x : N // (e x).fst = 0} ∧ IsCompact (univ : Set {x : N // (e x).fst = 0}) ∧
      Metric.diam (univ : Set {x : N // (e x).fst = 0}) ≤ D := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  obtain ⟨hc, hconn, hdiam, -⟩ := surfaceFactor_of_finite_limit K hK G hRiem hsec hD e
  obtain ⟨z⟩ := hconn.toNonempty
  have hD0 : 0 ≤ D := (dist_self z ▸ hdiam z z)
  exact ⟨⟨z⟩, isCompact_univ, Metric.diam_le_of_forall_dist_le hD0 fun a _ b _ => hdiam a b⟩

omit [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] in
/-- The surface factor is isometric to the residual factor. -/
theorem surfaceFactor_isometric_residual (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    Nonempty (W ≃ᵢ {x : N // (e x).fst = 0}) :=
  ⟨splittingFactorEquiv e⟩

end DifferentialGeometry.Geometry.Collapse
