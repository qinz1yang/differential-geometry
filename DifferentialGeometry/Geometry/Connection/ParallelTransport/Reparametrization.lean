import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covDerivAlong_smul_reparam_geodesic_velocity
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {φ f : ℝ → ℝ} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ (φ t))
    (hgeo : Geodesic.HasGeodesicEquationAt g γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) (hf : DifferentiableAt ℝ f t) :
    covDerivAlong g (fun s => γ (φ s))
        (fun s => f s • mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) t =
      deriv f t • mfderiv 𝓘(ℝ, ℝ) I γ (φ t) (1 : ℝ) := by
  have hV := differentiableAt_chartRepAt_curveVelocity hγ
  have hVφ : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s => γ (φ s))
        (fun s => mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) t) t :=
    hV.comp t hφ
  rw [covDerivAlong_smulFun g _ f _ t hf hVφ,
    covDerivAlong_comp g γ _ φ t (hγ.mdifferentiableAt (by norm_num)) hV hφ,
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ (φ t) hγ hgeo,
    smul_zero, smul_zero, add_zero]

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
