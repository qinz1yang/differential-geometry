import DifferentialGeometry.Geometry.Metric.CompactSourceCurves



noncomputable section

open Set Function Manifold Bundle DifferentialGeometry MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def riemannianCurveSpeed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)))

theorem riemannianCurveSpeed_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (t : ℝ) : 0 ≤ riemannianCurveSpeed g γ t := Real.sqrt_nonneg _

set_option backward.isDefEq.respectTransparency false in


theorem riemannianCurveSpeed_comp (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {r : V → M} {v : ℝ → V} {t : ℝ}
    (hr : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t)) (hv : DifferentiableAt ℝ v t) :
    riemannianCurveSpeed g (r ∘ v) t = Real.sqrt (g.inner (r (v t))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (deriv v t))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (deriv v t))) := by
  have hD := mfderiv_comp t hr hv.mdifferentiableAt
  have hDv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ) = deriv v t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := v) (x := t)
  unfold riemannianCurveSpeed
  rw [hD]
  change Real.sqrt (g.inner (r (v t))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))) = _
  rw [hDv]



def riemannianCurveELength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (riemannianCurveSpeed g γ t)


theorem riemannianCurveELength_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, riemannianCurveSpeed g γ t ≤ C) :
    riemannianCurveELength g γ a b ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  unfold riemannianCurveELength
  calc
    (∫⁻ t in Icc a b, ENNReal.ofReal (riemannianCurveSpeed g γ t)) ≤
        ∫⁻ _t in Icc a b, (C : ℝ≥0∞) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (h t ht)
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem riemannianCurveELength_eq_pathELength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveELength g γ a b =
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩;
        Manifold.pathELength 𝓘(ℝ, E) γ a b) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr_ae
  filter_upwards [] with t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

end DifferentialGeometry.Geometry
