import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.SpeedDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.CurvatureCommutation
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def firstEnergyDensity
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s t : ℝ) : ℝ :=
  fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s, t) (1, 0)

def secondEnergyDensity
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s t : ℝ) : ℝ :=
  fderiv ℝ (fun p : ℝ × ℝ => firstEnergyDensity (I := I) g f p.1 p.2)
    (s, t) (1, 0)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma curveEnergy_slice_eq_integral_speedSq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s a b : ℝ) :
    curveEnergy (I := I) g (fun t : ℝ => f s t) a b =
      ∫ t in a..b, speedSq (I := I) g f s t := by
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma firstEnergyDensity_contDiff
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiff ℝ (6 : ℕ)
      (fun p : ℝ × ℝ => firstEnergyDensity (I := I) g f p.1 p.2) := by
  have hspeed : ContDiff ℝ (7 : ℕ)
      (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_contDiff (I := I) (M := M) g f hf
  have hfd : ContDiff ℝ (6 : ℕ)
      (fun p : ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) p) :=
    hspeed.fderiv_right (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secondEnergyDensity_contDiff
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiff ℝ (5 : ℕ)
      (fun p : ℝ × ℝ => secondEnergyDensity (I := I) g f p.1 p.2) := by
  have hfirst : ContDiff ℝ (6 : ℕ)
      (fun p : ℝ × ℝ => firstEnergyDensity (I := I) g f p.1 p.2) :=
    firstEnergyDensity_contDiff (I := I) (M := M) g f hf
  have hfd : ContDiff ℝ (5 : ℕ)
      (fun p : ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => firstEnergyDensity (I := I) g f q.1 q.2) p) :=
    hfirst.fderiv_right (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd

lemma hasDerivAt_intervalIntegral_fst_of_contDiff
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 1 F) (a b s : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ t in a..b, F (u, t))
      (∫ t in a..b, fderiv ℝ F (s, t) (1, 0)) s := by
  have hparam :=
    DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
      (fun u t : ℝ => F (u, t)) Set.univ isOpen_univ a b Set.univ isOpen_univ
      (by simp) s (by simp) hF.contDiffOn
  have hslice : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => F (u, t)) (fderiv ℝ F (s, t) (1, 0)) s := by
    intro t
    exact TwoParameterDerivative.hasDerivAt_slice_fst (fun u t : ℝ => F (u, t)) s t
      ((hF.differentiable (by norm_num)).differentiableAt)
  have hpartial_eq : ∀ t : ℝ,
      fderiv ℝ (fun u : ℝ => F (u, t)) s =
        ContinuousLinearMap.toSpanSingleton ℝ (fderiv ℝ F (s, t) (1, 0)) := by
    intro t
    exact (hslice t).hasFDerivAt.fderiv
  have hD : Continuous (fun t : ℝ => fderiv ℝ F (s, t) (1, 0)) := by
    have hfd : ContDiff ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ F p) :=
      hF.fderiv_right (by norm_num)
    have happ : ContDiff ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ F p (1, 0)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd
    exact happ.continuous.comp (continuous_const.prodMk continuous_id)
  have hpartial : Continuous
      (fun t : ℝ => fderiv ℝ (fun u : ℝ => F (u, t)) s) := by
    rw [show (fun t : ℝ => fderiv ℝ (fun u : ℝ => F (u, t)) s) =
        (fun t : ℝ => ContinuousLinearMap.toSpanSingleton ℝ
          (fderiv ℝ F (s, t) (1, 0))) by
      funext t
      exact hpartial_eq t]
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp hD
  have hcomm :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).intervalIntegral_comp_comm
      (hpartial.intervalIntegrable (μ := volume) a b)
  have heval :
      (∫ t in a..b, fderiv ℝ (fun u : ℝ => F (u, t)) s) (1 : ℝ) =
        ∫ t in a..b, fderiv ℝ F (s, t) (1, 0) := by
    calc
      (∫ t in a..b, fderiv ℝ (fun u : ℝ => F (u, t)) s) (1 : ℝ) =
          ∫ t in a..b, (fderiv ℝ (fun u : ℝ => F (u, t)) s) (1 : ℝ) := hcomm.symm
      _ = ∫ t in a..b, fderiv ℝ F (s, t) (1, 0) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change (fderiv ℝ (fun u : ℝ => F (u, t)) s) (1 : ℝ) =
          fderiv ℝ F (s, t) (1, 0)
        rw [fderiv_apply_one_eq_deriv, (hslice t).deriv]
  have hresult := hparam.hasDerivAt
  rw [heval] at hresult
  exact hresult

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma firstEnergyDensity_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    HasDerivAt (fun u : ℝ => speedSq (I := I) g f u t)
      (firstEnergyDensity (I := I) g f s t) s := by
  exact TwoParameterDerivative.hasDerivAt_slice_fst
    (fun u t : ℝ => speedSq (I := I) g f u t) s t
    (((speedSq_contDiff (I := I) (M := M) g f hf).differentiable (by norm_num)).differentiableAt)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma secondEnergyDensity_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    HasDerivAt (fun u : ℝ => firstEnergyDensity (I := I) g f u t)
      (secondEnergyDensity (I := I) g f s t) s := by
  exact TwoParameterDerivative.hasDerivAt_slice_fst
    (fun u t : ℝ => firstEnergyDensity (I := I) g f u t) s t
    (((firstEnergyDensity_contDiff (I := I) (M := M) g f hf).differentiable
      (by norm_num)).differentiableAt)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem curveEnergy_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (a b s : ℝ) :
    HasDerivAt
      (fun u : ℝ => curveEnergy (I := I) g (fun t : ℝ => f u t) a b)
      (∫ t in a..b, firstEnergyDensity (I := I) g f s t) s := by
  rw [show (fun u : ℝ => curveEnergy (I := I) g (fun t : ℝ => f u t) a b) =
      (fun u : ℝ => ∫ t in a..b, speedSq (I := I) g f u t) by
    funext u
    rfl]
  exact hasDerivAt_intervalIntegral_fst_of_contDiff
    (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2)
    ((speedSq_contDiff (I := I) (M := M) g f hf).of_le (by norm_num)) a b s

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem firstEnergyIntegral_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (a b s : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∫ t in a..b, firstEnergyDensity (I := I) g f u t)
      (∫ t in a..b, secondEnergyDensity (I := I) g f s t) s := by
  exact hasDerivAt_intervalIntegral_fst_of_contDiff
    (fun p : ℝ × ℝ => firstEnergyDensity (I := I) g f p.1 p.2)
    ((firstEnergyDensity_contDiff (I := I) (M := M) g f hf).of_le (by norm_num)) a b s

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem curveEnergy_deriv_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (a b s : ℝ) :
    HasDerivAt
      (fun u : ℝ => deriv
        (fun r : ℝ => curveEnergy (I := I) g (fun t : ℝ => f r t) a b) u)
      (∫ t in a..b, secondEnergyDensity (I := I) g f s t) s := by
  rw [show (fun u : ℝ => deriv
      (fun r : ℝ => curveEnergy (I := I) g (fun t : ℝ => f r t) a b) u) =
      (fun u : ℝ => ∫ t in a..b, firstEnergyDensity (I := I) g f u t) by
    funext u
    exact (curveEnergy_hasDerivAt (I := I) (M := M) g f hf a b u).deriv]
  exact firstEnergyIntegral_hasDerivAt (I := I) (M := M) g f hf a b s

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
lemma firstEnergyDensity_eq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    firstEnergyDensity (I := I) g f s t =
      2 * g.inner (f s t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g (fun r : ℝ => f r t)
          (fun r : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f r u) t (1 : ℝ)) s)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s + a) b with hfsh
  have hfshSmooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (s + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  have hgeom := speedSq_hasDerivAt (I := I) g fsh t hfshSmooth
  have hshiftDeriv : HasDerivAt (fun a : ℝ => s + a) (1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add s
  have hbase : HasDerivAt (fun u : ℝ => speedSq (I := I) g f u t)
      (firstEnergyDensity (I := I) g f s t) (s + 0) := by
    simpa using firstEnergyDensity_hasDerivAt (I := I) (M := M) g f hf s t
  have hraw := hbase.comp 0 hshiftDeriv
  have hraw' : HasDerivAt (fun a : ℝ => speedSq (I := I) g fsh a t)
      (firstEnergyDensity (I := I) g f s t) 0 := by
    have heq : (fun a : ℝ => speedSq (I := I) g fsh a t) =
        (fun a : ℝ => speedSq (I := I) g f (s + a) t) := by
      funext a
      rfl
    rw [heq]
    rw [show ((fun u : ℝ => speedSq (I := I) g f u t) ∘ HAdd.hAdd s) =
      (fun a : ℝ => speedSq (I := I) g f (s + a) t) by rfl, mul_one] at hraw
    exact hraw
  have hvalue := hraw'.unique hgeom
  have hcovShift :
      covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
          (fun a : ℝ =>
            mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0 =
        covDerivAlong (I := I) g (fun r : ℝ => f r t)
          (fun r : ℝ =>
            mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f r u) t (1 : ℝ)) s := by
    rw [hfsh]
    exact covDerivAlong_const_add_shift (I := I) g (fun r : ℝ => f r t)
      (fun r : ℝ =>
        mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f r u) t (1 : ℝ)) s
  have hfoot : fsh 0 t = f s t := by
    rw [hfsh]
    simp
  have hcentral : (fun u : ℝ => fsh 0 u) = (fun u : ℝ => f s u) := by
    funext u
    rw [hfsh]
    simp
  rw [hvalue, hcovShift, hfoot, hcentral]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
lemma firstEnergyDensity_zero_eq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    firstEnergyDensity (I := I) g f 0 t =
      2 * g.inner (f 0 t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) := by
  exact (firstEnergyDensity_hasDerivAt (I := I) (M := M) g f hf 0 t).unique
    (speedSq_hasDerivAt (I := I) g f t hf)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem firstVariation_curveEnergy
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (a b : ℝ) :
    HasDerivAt
      (fun s : ℝ => curveEnergy (I := I) g (fun t : ℝ => f s t) a b)
      (∫ t in a..b,
        2 * g.inner (f 0 t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) 0 := by
  convert curveEnergy_hasDerivAt (I := I) (M := M) g f hf a b 0 using 1
  apply intervalIntegral.integral_congr
  intro t _ht
  exact (firstEnergyDensity_zero_eq (I := I) (M := M) g f hf t).symm

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem firstVariation_curveEnergy_freeEndpoints_of_unitSpeed
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1) :
    HasDerivAt
      (fun s : ℝ => curveEnergy (I := I) g (fun t : ℝ => f s t) 0 L)
      (2 *
        ((g.inner (f 0 L)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) L (1 : ℝ))
          - g.inner (f 0 0)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) 0 (1 : ℝ)))
        - ∫ t in (0 : ℝ)..L,
          g.inner (f 0 t)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
            (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
              (I := I) g (fun v : ℝ => f 0 v)
              (fun v : ℝ =>
                mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t))) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  set A : ℝ → ℝ := fun t : ℝ =>
    g.inner (f 0 t)
      (covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hA
  set D : ℝ :=
    (g.inner (f 0 L)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) L (1 : ℝ))
      - g.inner (f 0 0)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) 0 (1 : ℝ)))
      - ∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ =>
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t) with hD
  have henergy := firstVariation_curveEnergy (I := I) (M := M) g f hf 0 L
  have henergy' : HasDerivAt
      (fun s : ℝ => curveEnergy (I := I) g (fun t : ℝ => f s t) 0 L)
      (2 * ∫ t in (0 : ℝ)..L, A t) 0 := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [hA] using henergy
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L,
      speedSq (I := I) g f 0 t = 1 := hUnit
  have hspeed := speedIntegral_hasDerivAt (I := I) g f L hf hL hUnit'
  have hspeedA : HasDerivAt
      (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      (∫ t in (0 : ℝ)..L, A t) 0 := by
    rw [show (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L) =
        (fun s : ℝ => ∫ t in (0 : ℝ)..L,
          Real.sqrt (speedSq (I := I) g f s t)) by
      funext s
      rfl]
    convert hspeed using 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hL)] at ht
    change A t = 2 * A t / (2 * Real.sqrt (speedSq (I := I) g f 0 t))
    rw [hUnit' t ht, Real.sqrt_one]
    ring
  have harc := first_variation_of_arcLength_free_endpoints (I := I) g f L hf hL hUnit
  have hAD : (∫ t in (0 : ℝ)..L, A t) = D := by
    exact hspeedA.unique (by simpa only [hD] using harc)
  rw [hAD] at henergy'
  simpa only [hD] using henergy'

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem firstVariation_curveEnergy_geodesic_fixedInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfix0 : ∀ s : ℝ, f s 0 = γ 0)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    HasDerivAt
      (fun s : ℝ => curveEnergy (I := I) g (fun t : ℝ => f s t) 0 L)
      (2 * g.inner (γ L)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I γ L (1 : ℝ))) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  have hfγ : (fun t : ℝ => f 0 t) = γ := by
    funext t
    exact hfc t
  have hfree := firstVariation_curveEnergy_freeEndpoints_of_unitSpeed
    (I := I) g f L hf hL (by
      intro t ht
      rw [hfc t, hfγ]
      exact hUnit t ht)
  have hγsmooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hfγ ▸ (hf : ContMDiff _ _ _ _).comp hincl
  have haccel : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t = 0 := by
    intro t ht
    have hzero : covDerivAlong (I := I) g γ
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I γ v (1 : ℝ)) t = 0 :=
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t
        (hγsmooth.contMDiffAt.of_le
          (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8)))
        (hγ t ht)
    rw [hfγ]
    exact hzero
  have hV0 : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ) = 0 := by
    have hconst : (fun u : ℝ => f u 0) = (fun _ : ℝ => γ 0) := by
      funext u
      exact hfix0 u
    rw [hconst, mfderiv_const]
    rfl
  have hint0 : (∫ t in (0 : ℝ)..L,
      g.inner (f 0 t)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
        (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
          (fun v : ℝ =>
            mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) = 0 := by
    calc
      (∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ =>
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) =
          ∫ _t in (0 : ℝ)..L, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [Set.uIcc_of_le (le_of_lt hL)] at ht
            change g.inner (f 0 t)
              (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
              (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
                (fun v : ℝ =>
                  mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t) = 0
            rw [haccel t ht, ContinuousLinearMap.map_zero]
      _ = 0 := intervalIntegral.integral_zero
  apply hfree.congr_deriv
  rw [hint0, hV0, ContinuousLinearMap.map_zero, zero_apply, hfc L, hfγ]
  ring

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
