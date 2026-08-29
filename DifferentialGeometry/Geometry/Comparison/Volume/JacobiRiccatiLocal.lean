import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Matrix Set
open scoped Matrix Manifold ContDiff Topology Matrix.Norms.Operator

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Volume

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem mean_riccati_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t q a : ℝ)
    (u : TangentSpace I (γ t))
    (huvel : curveVelocity (I := I) γ t = u)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (ha : 0 < a)
    (hu : g.inner (γ t) u u = a ^ 2)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t)
    (e : Fin (Module.finrank ℝ E - 1) → TangentSpace I (γ t))
    (hON : ∀ i j, g.inner (γ t) (e i) (e j) = if i = j then 1 else 0)
    (hEperp : ∀ i, g.inner (γ t) (e i) u = 0)
    (hRic :
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (γ t) u u ≤
        ricciTensor (I := I) g (γ t) u u) :
    HasDerivAt (curveMean (I := I) g γ V)
        (-trace ((curveGram (I := I) g γ V t)⁻¹ *
            curveCurvGram (I := I) g γ V t) -
          trace ((curveShape (I := I) g γ V t) ^ 2)) t ∧
      -trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        trace ((curveShape (I := I) g γ V t) ^ 2) ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q * a) ^ 2 -
        (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
  have hupos : 0 < g.inner (γ t) u u := by
    rw [hu]
    positivity
  have hderiv := hasDerivAt_mean_perp (I := I) hn g γ V t u hcard hupos
    hVperp hDVperp hγ hVdiff hDVdiff hLI hW hJ
  refine ⟨hderiv, ?_⟩
  have hcurv := curvTrace_eq_ricci (I := I) g γ V t u huvel hcard hupos
    hVperp hLI e hON hEperp
  have hshape := mean_sq_le_shape (I := I) g γ V t u hcard hupos hVperp
    hDVperp hLI hW e hON hEperp
  have hric := hRic
  rw [hu] at hric
  have hdR : (0 : ℝ) < ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hshapeDiv :
      (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) ≤
        trace ((curveShape (I := I) g γ V t) ^ 2) := by
    rw [div_le_iff₀ hdR]
    simpa only [mul_comm] using hshape
  rw [hcurv]
  nlinarith

end Volume
end Riemannian
end Geometry
end DifferentialGeometry
