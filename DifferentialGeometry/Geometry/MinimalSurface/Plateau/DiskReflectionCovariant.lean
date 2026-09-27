import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionDifferential



noncomputable section

open Bundle Manifold DifferentialGeometry Function
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Bundle Manifold ContDiff Topology ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem diskMapCovariantPartial_comp_conj_one (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    diskMapCovariantPartial g (U ∘ conj) z 1 1 =
      diskMapCovariantPartial g U (conj z) 1 1 := by
  have hc (t : ℝ) : conj (z + t • (1 : ℂ)) = conj z + t • (1 : ℂ) := by
    simp [Complex.real_smul]
  unfold diskMapCovariantPartial
  simp only [Function.comp_apply, diskMapPartial_comp_conj_one]
  congr 1 <;> funext t
  · exact congrArg U (hc t)
  · exact congrArg (fun w : ℂ => (diskMapPartial U w 1 : E)) (hc t)




theorem diskMapCovariantPartial_comp_conj_I (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    diskMapCovariantPartial g (U ∘ conj) z Complex.I Complex.I =
      diskMapCovariantPartial g U (conj z) Complex.I Complex.I := by
  let γ : ℝ → M := fun t => U (conj z + t • Complex.I)
  let V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t) :=
    fun t => diskMapPartial U (conj z + t • Complex.I) Complex.I
  have he : diskMapCovariantPartial g (U ∘ conj) z Complex.I Complex.I =
      covDerivAlong g (fun t => γ ((-1) * t)) (fun t => (-1 : ℝ) • V ((-1) * t)) 0 := by
    unfold diskMapCovariantPartial
    simp only [Function.comp_apply, diskMapPartial_comp_conj_I]
    have hc (t : ℝ) : conj (z + t • Complex.I) = conj z + ((-1 : ℝ) * t) • Complex.I := by
      simp [Complex.real_smul]
    congr 1 <;> funext t
    · exact congrArg U (hc t)
    · change -diskMapPartial U (conj (z + t • Complex.I)) Complex.I =
        (-1 : ℝ) • diskMapPartial U (conj z + ((-1 : ℝ) * t) • Complex.I) Complex.I
      rw [neg_one_smul]
      exact congrArg (fun w : ℂ => -(diskMapPartial U w Complex.I : E)) (hc t)
  rw [he, covDerivAlong_smul, covDeriv_comp_mul]
  simp only [neg_smul, one_smul, neg_neg]
  change (covDerivAlong g γ V ((-1 : ℝ) * 0) : E) = covDerivAlong g γ V 0
  exact congrArg (fun t : ℝ => (covDerivAlong g γ V t : E)) (mul_zero (-1 : ℝ))



theorem diskMapTension_comp_conj (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    diskMapTension g (U ∘ conj) z = diskMapTension g U (conj z) := by
  unfold diskMapTension
  rw [diskMapCovariantPartial_comp_conj_one, diskMapCovariantPartial_comp_conj_I]

end DifferentialGeometry.Geometry
