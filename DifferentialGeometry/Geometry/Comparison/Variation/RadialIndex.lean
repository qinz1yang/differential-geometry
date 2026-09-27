import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma indexFormIntegrand_radial_parallel_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (γ t)) (L t : ℝ)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVparallel : covDerivAlong (I := I) g γ V t = 0)
    (hVunit : g.inner (γ t) (V t) (V t) = 1) :
    indexFormIntegrand (I := I) g γ
        (fun u : ℝ => (u / L) • V u)
        (fun u : ℝ => (u / L) • V u) t =
      (1 / L) ^ 2 - (t / L) ^ 2 *
        g.inner (γ t)
          ((riemannOp (LeviCivita (I := I) g) (γ t))
            (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
          (V t) := by
  have hscalar : DifferentiableAt ℝ (fun u : ℝ => u / L) t := by
    fun_prop
  have hscalarDeriv : deriv (fun u : ℝ => u / L) t = 1 / L := by
    simpa only [id_eq] using ((hasDerivAt_id t).div_const L).deriv
  have hcov := covDerivAlong_smulFun (I := I) g γ
    (fun u : ℝ => u / L) V t hscalar hVdiff
  rw [hscalarDeriv, hVparallel, smul_zero, add_zero] at hcov
  unfold indexFormIntegrand
  rw [hcov]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [hVunit]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma indexFormIntegrand_eq_of_radial_data
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (W V : ∀ t : ℝ, TangentSpace I (γ t)) (L t : ℝ)
    (hW : W t = (t / L) • V t)
    (hWcov : covDerivAlong (I := I) g γ W t = (1 / L) • V t)
    (hVunit : g.inner (γ t) (V t) (V t) = 1) :
    indexFormIntegrand (I := I) g γ W W t =
      (1 / L) ^ 2 - (t / L) ^ 2 *
        g.inner (γ t)
          ((riemannOp (LeviCivita (I := I) g) (γ t))
            (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
          (V t) := by
  unfold indexFormIntegrand
  rw [hWcov, hW]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [hVunit]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem indexForm_radial_parallel_le_inv
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (γ t)) (L : ℝ)
    (hL : 0 < L)
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVparallel : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ V t = 0)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
        (V t))
    (hInt : IntervalIntegrable
      (fun t : ℝ => indexFormIntegrand (I := I) g γ
        (fun u : ℝ => (u / L) • V u)
        (fun u : ℝ => (u / L) • V u) t)
      MeasureTheory.volume 0 L) :
    indexForm (I := I) g γ 0 L
        (fun u : ℝ => (u / L) • V u)
        (fun u : ℝ => (u / L) • V u) ≤ 1 / L := by
  rw [indexForm_eq_intervalIntegral]
  calc
    (∫ t in (0 : ℝ)..L, indexFormIntegrand (I := I) g γ
        (fun u : ℝ => (u / L) • V u)
        (fun u : ℝ => (u / L) • V u) t) ≤
        ∫ _t in (0 : ℝ)..L, (1 / L) ^ 2 := by
      apply intervalIntegral.integral_mono_on (le_of_lt hL) hInt
        intervalIntegrable_const
      intro t ht
      rw [indexFormIntegrand_radial_parallel_eq (I := I) g γ V L t
        (hVdiff t ht) (hVparallel t ht) (hVunit t ht)]
      have hnonneg : 0 ≤ (t / L) ^ 2 *
          g.inner (γ t)
            ((riemannOp (LeviCivita (I := I) g) (γ t))
              (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
            (V t) := mul_nonneg (sq_nonneg _) (hcurv t ht)
      linarith
    _ = 1 / L := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem indexForm_le_inv_of_radial_data
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (W V : ∀ t : ℝ, TangentSpace I (γ t)) (L : ℝ)
    (hL : 0 < L)
    (hW : ∀ t ∈ Set.Icc (0 : ℝ) L, W t = (t / L) • V t)
    (hWcov : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ W t = (1 / L) • V t)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
        (V t))
    (hInt : IntervalIntegrable
      (fun t : ℝ => indexFormIntegrand (I := I) g γ W W t)
      MeasureTheory.volume 0 L) :
    indexForm (I := I) g γ 0 L W W ≤ 1 / L := by
  rw [indexForm_eq_intervalIntegral]
  calc
    (∫ t in (0 : ℝ)..L, indexFormIntegrand (I := I) g γ W W t) ≤
        ∫ _t in (0 : ℝ)..L, (1 / L) ^ 2 := by
      apply intervalIntegral.integral_mono_on (le_of_lt hL) hInt
        intervalIntegrable_const
      intro t ht
      rw [indexFormIntegrand_eq_of_radial_data (I := I) g γ W V L t
        (hW t ht) (hWcov t ht) (hVunit t ht)]
      have hnonneg : 0 ≤ (t / L) ^ 2 *
          g.inner (γ t)
            ((riemannOp (LeviCivita (I := I) g) (γ t))
              (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
            (V t) := mul_nonneg (sq_nonneg _) (hcurv t ht)
      linarith
    _ = 1 / L := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem centralVariation_indexForm_le_inv_of_radial_parallel
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (f 0 t)) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hfield : ∀ t : ℝ,
      centralVariationField (I := I) f t = (t / L) • V t)
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (fun u : ℝ => f 0 u) V t) t)
    (hVparallel : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u) V t = 0)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (V t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
        (V t)) :
    indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) ≤ 1 / L := by
  have hfieldFun : (fun u : ℝ => centralVariationField (I := I) f u) =
      (fun u : ℝ => (u / L) • V u) := funext hfield
  have hInt : IntervalIntegrable
      (fun t : ℝ => indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) t)
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hL)]
    exact centralVariation_indexFormIntegrand_continuousOn
      (I := I) (M := M) g f hf L
  rw [hfieldFun] at hInt ⊢
  exact indexForm_radial_parallel_le_inv (I := I) g
    (fun u : ℝ => f 0 u) V L hL hVdiff hVparallel hVunit hcurv hInt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem centralVariation_indexForm_le_inv_of_radial_data
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (f 0 t)) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hfield : ∀ t ∈ Set.Icc (0 : ℝ) L,
      centralVariationField (I := I) f t = (t / L) • V t)
    (hfieldCov : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u) t =
          (1 / L) • V t)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (V t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
        (V t)) :
    indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) ≤ 1 / L := by
  have hInt : IntervalIntegrable
      (fun t : ℝ => indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) t)
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hL)]
    exact centralVariation_indexFormIntegrand_continuousOn
      (I := I) (M := M) g f hf L
  exact indexForm_le_inv_of_radial_data (I := I) g
    (fun u : ℝ => f 0 u)
    (fun u : ℝ => centralVariationField (I := I) f u) V L hL
    hfield hfieldCov hVunit hcurv hInt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem secondVariation_half_curveEnergy_deriv_le_inv_of_radial_parallel
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (f 0 t)) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g
      (fun u : ℝ => f 0 u) (Set.Icc 0 L))
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0)
    (hterminal : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => f s L) 0)
    (hfield : ∀ t : ℝ,
      centralVariationField (I := I) f t = (t / L) • V t)
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (fun u : ℝ => f 0 u) V t) t)
    (hVparallel : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u) V t = 0)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (V t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
        (V t)) :
    deriv
      (fun s : ℝ => deriv
        (fun r : ℝ => (1 / 2 : ℝ) *
          curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s) 0 ≤
      1 / L := by
  have hsecond :=
    secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal
      (I := I) (M := M) g f L hf hL hcentral hfix0 hterminal
  rw [hsecond.deriv]
  exact centralVariation_indexForm_le_inv_of_radial_parallel
    (I := I) (M := M) g f V L hf hL hfield hVdiff hVparallel hVunit hcurv

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem secondVariation_half_curveEnergy_deriv_le_inv_of_radial_data
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (V : ∀ t : ℝ, TangentSpace I (f 0 t)) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g
      (fun u : ℝ => f 0 u) (Set.Icc 0 L))
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0)
    (hterminal : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => f s L) 0)
    (hfield : ∀ t ∈ Set.Icc (0 : ℝ) L,
      centralVariationField (I := I) f t = (t / L) • V t)
    (hfieldCov : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u) t =
          (1 / L) • V t)
    (hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t) (V t) (V t) = 1)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (V t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
        (V t)) :
    deriv
      (fun s : ℝ => deriv
        (fun r : ℝ => (1 / 2 : ℝ) *
          curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s) 0 ≤
      1 / L := by
  have hsecond :=
    secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal
      (I := I) (M := M) g f L hf hL hcentral hfix0 hterminal
  rw [hsecond.deriv]
  exact centralVariation_indexForm_le_inv_of_radial_data
    (I := I) (M := M) g f V L hf hL hfield hfieldCov hVunit hcurv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
