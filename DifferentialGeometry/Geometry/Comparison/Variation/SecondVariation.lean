import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.Variation.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.CurvatureCommutation
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Basic

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

def centralVariationField (f : ℝ → ℝ → M) (t : ℝ) :
    TangentSpace I (f 0 t) :=
  mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ)

def centralVelocity (f : ℝ → ℝ → M) (t : ℝ) :
    TangentSpace I (f 0 t) :=
  mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)

def centralVariationAcceleration
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) :
    TangentSpace I (f 0 t) :=
  covDerivAlong (I := I) g (fun s : ℝ => f s t)
    (fun s : ℝ =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun r : ℝ => f r t) s (1 : ℝ)) 0

def secondVariationVelocity
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) :
    TangentSpace I (f 0 t) :=
  covDerivAlong (I := I) g (fun s : ℝ => f s t)
    (fun s : ℝ =>
      covDerivAlong (I := I) g (fun r : ℝ => f r t)
        (fun r : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f r u) t (1 : ℝ)) s) 0

def secondVariationBoundary
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) : ℝ :=
  g.inner (f 0 t)
    (centralVariationAcceleration (I := I) g f t)
    (centralVelocity (I := I) f t)

def secondVariationBoundaryDensity
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) : ℝ :=
  g.inner (f 0 t)
    (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
      (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t)
    (centralVelocity (I := I) f t)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
lemma secondEnergyDensity_zero_div_two_eq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    secondEnergyDensity (I := I) g f 0 t / 2 =
      g.inner (f 0 t)
          (secondVariationVelocity (I := I) g f t)
          (centralVelocity (I := I) f t)
        + g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
            (fun u : ℝ => centralVariationField (I := I) f u) t)
          (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
            (fun u : ℝ => centralVariationField (I := I) f u) t) := by
  classical
  set c : ℝ → M := fun s : ℝ => f s t with hc
  set velT : ∀ s : ℝ, TangentSpace I (c s) := fun s : ℝ =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ) with hvelT
  set mixed : ∀ s : ℝ, TangentSpace I (c s) := fun s : ℝ =>
    covDerivAlong (I := I) g (fun r : ℝ => f r t)
      (fun r : ℝ => velT r) s with hmixed
  have hcSmooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) c := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun s : ℝ => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hvelDiff : DifferentiableAt ℝ (chartRepAt (I := I) c velT 0) 0 := by
    exact slice_longitudinalField_transverse_chartRep_differentiableAt
      (I := I) f hf t
  have hmixedDiff : DifferentiableAt ℝ (chartRepAt (I := I) c mixed 0) 0 := by
    exact slice_secondCovDeriv_chartRep_differentiableAt (I := I) g f hf t
  have hmetric := metric_compat_hasDerivAt_inner (I := I)
    (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8))
    g c mixed velT 0 hcSmooth hmixedDiff hvelDiff
  have hcovMixed : covDerivAlong (I := I) g c mixed 0 =
      secondVariationVelocity (I := I) g f t := by
    rw [secondVariationVelocity, hc, hmixed, hvelT]
  have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
  have hmixed0 : mixed 0 =
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u) t := by
    rw [hmixed, hvelT]
    change covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 =
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s u) 0 (1 : ℝ)) t
    exact hcomm
  have hcovVel : covDerivAlong (I := I) g c velT 0 =
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u) t := by
    rw [hc, hvelT]
    change covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 =
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ =>
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s u) 0 (1 : ℝ)) t
    exact hcomm
  have hvel0 : velT 0 = centralVelocity (I := I) f t := by
    rfl
  have hmetric' : HasDerivAt
      (fun s : ℝ => g.inner (c s) (mixed s) (velT s))
      (g.inner (f 0 t)
          (secondVariationVelocity (I := I) g f t)
          (centralVelocity (I := I) f t)
        + g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
            (fun u : ℝ => centralVariationField (I := I) f u) t)
          (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
            (fun u : ℝ => centralVariationField (I := I) f u) t)) 0 := by
    simpa only [hcovMixed, hcovVel, hmixed0, hvel0, hc] using hmetric
  have hfirstEq : (fun s : ℝ => firstEnergyDensity (I := I) g f s t) =
      (fun s : ℝ => 2 * g.inner (c s) (mixed s) (velT s)) := by
    funext s
    rw [firstEnergyDensity_eq (I := I) (M := M) g f hf s t]
  have hsecondRaw := secondEnergyDensity_hasDerivAt
    (I := I) (M := M) g f hf 0 t
  have hsecondGeom : HasDerivAt
      (fun s : ℝ => firstEnergyDensity (I := I) g f s t)
      (2 *
        (g.inner (f 0 t)
            (secondVariationVelocity (I := I) g f t)
            (centralVelocity (I := I) f t)
          + g.inner (f 0 t)
            (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
              (fun u : ℝ => centralVariationField (I := I) f u) t)
            (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
              (fun u : ℝ => centralVariationField (I := I) f u) t))) 0 := by
    rw [hfirstEq]
    exact hmetric'.const_mul 2
  have heq := hsecondRaw.unique hsecondGeom
  rw [heq]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma secondVariationVelocity_eq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    secondVariationVelocity (I := I) g f t =
      covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t
        + (riemannOp (LeviCivita (I := I) g) (f 0 t))
          (centralVariationField (I := I) f t)
          (centralVelocity (I := I) f t)
          (centralVariationField (I := I) f t) := by
  classical
  set velS : ℝ → ℝ → E := fun s v : ℝ =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ) with hvelS
  set velT : ℝ → ℝ → E := fun s v : ℝ =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ) with hvelT
  set A : ∀ u : ℝ, TangentSpace I (f 0 u) := fun u : ℝ =>
    covDerivAlong (I := I) g (fun s : ℝ => f s u)
      (fun s : ℝ => velS s u) 0 with hA
  set B : ∀ u : ℝ, TangentSpace I (f 0 u) := fun u : ℝ =>
    covDerivAlong (I := I) g (fun v : ℝ => f 0 v) A u with hB
  set R : TangentSpace I (f 0 t) :=
    (riemannOp (LeviCivita (I := I) g) (f 0 t))
      (centralVariationField (I := I) f t)
      (centralVelocity (I := I) f t)
      (centralVariationField (I := I) f t) with hR
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => velS s v) t) 0) 0 := by
    have hsecEq :
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => velS s v) t) =
        (fun s : ℝ => covDerivAlong (I := I) g (fun r : ℝ => f r t)
          (fun r : ℝ => velT r t) s) :=
      (commute_ds_dt_intrinsic_shifted (I := I) g f hf t).symm
    rw [hsecEq]
    exact slice_secondCovDeriv_chartRep_differentiableAt (I := I) g f hf t
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun s : ℝ => f s v)
          (fun s : ℝ => velS s v) 0) t) t :=
    slice_secondCovDeriv_central_chartRep_differentiableAt (I := I) g f hf t
  have hcomm := commute_ds_dt_curvature_innerS (I := I) g f hf t houterL houterR
  have hfirst :
      covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => velS s v) t) 0 =
        secondVariationVelocity (I := I) g f t := by
    have hsecEq :
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => velS s v) t) =
        (fun s : ℝ => covDerivAlong (I := I) g (fun r : ℝ => f r t)
          (fun r : ℝ => velT r t) s) :=
      (commute_ds_dt_intrinsic_shifted (I := I) g f hf t).symm
    rw [hsecEq, secondVariationVelocity, hvelT]
  have hsecond :
      covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun s : ℝ => f s v)
          (fun s : ℝ => velS s v) 0) t = B t := by
    rw [hB, hA]
  have hcurvature :
      (riemannOp (LeviCivita (I := I) g) (f 0 t))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ)) = R := by
    rw [hR, centralVariationField, centralVelocity]
  rw [hfirst, hsecond, hcurvature] at hcomm
  have hB' : B t = covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
      (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t := by
    rw [hB, hA]
    rfl
  rw [← hB']
  rw [← hcomm]
  abel

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    secondEnergyDensity (I := I) g f 0 t / 2 =
      indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationField (I := I) f u)
          (fun u : ℝ => centralVariationField (I := I) f u) t
        + g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
            (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t)
          (centralVelocity (I := I) f t) := by
  rw [secondEnergyDensity_zero_div_two_eq (I := I) (M := M) g f hf t]
  rw [secondVariationVelocity_eq (I := I) (M := M) g f hf t]
  rw [map_add, add_apply]
  have hskew := riemannOp_metric_skew (I := I) g (f 0 t)
    (centralVariationField (I := I) f t)
    (centralVelocity (I := I) f t)
    (centralVariationField (I := I) f t)
    (centralVelocity (I := I) f t)
  have hsymm :
      g.inner (f 0 t) (centralVariationField (I := I) f t)
          ((riemannOp (LeviCivita (I := I) g) (f 0 t))
            (centralVariationField (I := I) f t)
            (centralVelocity (I := I) f t)
            (centralVelocity (I := I) f t)) =
        g.inner (f 0 t)
          ((riemannOp (LeviCivita (I := I) g) (f 0 t))
            (centralVariationField (I := I) f t)
            (centralVelocity (I := I) f t)
            (centralVelocity (I := I) f t))
          (centralVariationField (I := I) f t) :=
    g.symm (f 0 t) _ _
  rw [hsymm] at hskew
  change
    g.inner (f 0 t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t)
        (centralVelocity (I := I) f t)
      + g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (centralVariationField (I := I) f t)
          (centralVelocity (I := I) f t)
          (centralVariationField (I := I) f t))
        (centralVelocity (I := I) f t)
      + g.inner (f 0 t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationField (I := I) f u) t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationField (I := I) f u) t) =
    (g.inner (f 0 t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationField (I := I) f u) t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationField (I := I) f u) t)
      - g.inner (f 0 t)
        ((riemannOp (LeviCivita (I := I) g) (f 0 t))
          (centralVariationField (I := I) f t)
          (centralVelocity (I := I) f t)
          (centralVelocity (I := I) f t))
        (centralVariationField (I := I) f t))
      + g.inner (f 0 t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t)
        (centralVelocity (I := I) f t)
  linarith [hskew]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
lemma secondVariationBoundary_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (L t : ℝ)
    (hγ : IsGeodesicOn (I := I) g (fun u : ℝ => f 0 u) (Set.Icc 0 L))
    (ht : t ∈ Set.Icc (0 : ℝ) L) :
    HasDerivAt (fun u : ℝ => secondVariationBoundary (I := I) g f u)
      (g.inner (f 0 t)
        (covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
          (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t)
        (centralVelocity (I := I) f t)) t := by
  have hcentralSmooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun u : ℝ => f 0 u) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun u : ℝ => ((0 : ℝ), u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hADiff : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationAcceleration (I := I) g f u) t) t := by
    simpa only [centralVariationAcceleration] using
      (slice_secondCovDeriv_central_chartRep_differentiableAt
        (I := I) g f hf t)
  have hTDiff : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVelocity (I := I) f u) t) t := by
    simpa only [centralVelocity] using
      (velocityField_chartRep_differentiableAt (I := I) f hf t)
  have hmetric := metric_compat_hasDerivAt_inner (I := I)
    (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g
    (fun u : ℝ => f 0 u)
    (fun u : ℝ => centralVariationAcceleration (I := I) g f u)
    (fun u : ℝ => centralVelocity (I := I) f u) t
    hcentralSmooth hADiff hTDiff
  have haccel : covDerivAlong (I := I) g (fun u : ℝ => f 0 u)
      (fun u : ℝ => centralVelocity (I := I) f u) t = 0 := by
    apply covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g (fun u : ℝ => f 0 u) t
      (hcentralSmooth.contMDiffAt.of_le
        (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8)))
      (hγ t ht)
  apply hmetric.congr_deriv
  rw [haccel, ContinuousLinearMap.map_zero, add_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma centralVariation_indexFormIntegrand_continuousOn
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (L : ℝ) :
    ContinuousOn
      (fun t : ℝ => indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) t)
      (Set.Icc 0 L) := by
  let γ : ℝ → M := fun u : ℝ => f 0 u
  let V : ∀ u : ℝ, TangentSpace I (γ u) := fun u : ℝ =>
    centralVariationField (I := I) f u
  let T : ∀ u : ℝ, TangentSpace I (γ u) := fun u : ℝ =>
    centralVelocity (I := I) f u
  have hγSmooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun u : ℝ => ((0 : ℝ), u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hγC1On : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Set.Icc 0 L) :=
    (hγSmooth.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8))).contMDiffOn
  have hVDiff : ∀ t : ℝ,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
    intro t
    simpa only [γ, V, centralVariationField] using
      (variationField_chartRep_differentiableAt (I := I) f hf t)
  have hTDiff : ∀ t : ℝ,
      DifferentiableAt ℝ (chartRepAt (I := I) γ T t) t := by
    intro t
    simpa only [γ, T, centralVelocity] using
      (velocityField_chartRep_differentiableAt (I := I) f hf t)
  have hVTotal : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (V t) : TangentBundle I M))
      (Set.Icc 0 L) :=
    sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) γ V hγC1On (fun t _ht => hVDiff t)
  have hTTotal : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (T t) : TangentBundle I M))
      (Set.Icc 0 L) :=
    sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) γ T hγC1On (fun t _ht => hTDiff t)
  have hnablaVDiff : ∀ t : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (covDerivAlong (I := I) g γ V) t) t := by
    intro t
    simpa only [γ, V, centralVariationField] using
      (variationField_covDeriv_chartRep_differentiableAt (I := I) g f hf t)
  have hnablaVTotal : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t)
        (covDerivAlong (I := I) g γ V t) : TangentBundle I M))
      (Set.Icc 0 L) :=
    sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) γ (covDerivAlong (I := I) g γ V) hγC1On
      (fun t _ht => hnablaVDiff t)
  have hnablaVSq : ContinuousOn
      (fun t : ℝ => g.inner (γ t)
        (covDerivAlong (I := I) g γ V t)
        (covDerivAlong (I := I) g γ V t)) (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g
      hnablaVTotal hnablaVTotal
  have hRTotal : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (V t) (T t) (T t)) : TangentBundle I M))
      (Set.Icc 0 L) :=
    riemannOp_along_curve_continuousOn (I := I) g
      hγC1On.continuousOn hVTotal hTTotal hTTotal
  have hCurvature : ContinuousOn
      (fun t : ℝ => g.inner (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (V t) (T t) (T t)) (V t)) (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g hRTotal hVTotal
  change ContinuousOn
    (fun t : ℝ => g.inner (γ t)
        (covDerivAlong (I := I) g γ V t)
        (covDerivAlong (I := I) g γ V t)
      - g.inner (γ t)
        ((riemannOp (LeviCivita (I := I) g) (γ t))
          (V t) (T t) (T t)) (V t)) (Set.Icc 0 L)
  exact hnablaVSq.sub hCurvature

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma secondVariationBoundaryDensity_continuousOn
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (L : ℝ) :
    ContinuousOn (fun t : ℝ => secondVariationBoundaryDensity (I := I) g f t)
      (Set.Icc 0 L) := by
  have hsecond : ContinuousOn
      (fun t : ℝ => secondEnergyDensity (I := I) g f 0 t / 2)
      (Set.Icc 0 L) := by
    have hslice : Continuous
        (fun t : ℝ => secondEnergyDensity (I := I) g f 0 t) :=
      (secondEnergyDensity_contDiff (I := I) (M := M) g f hf).continuous.comp
        (continuous_const.prodMk continuous_id)
    exact hslice.continuousOn.div_const 2
  have hindex := centralVariation_indexFormIntegrand_continuousOn
    (I := I) (M := M) g f hf L
  apply (hsecond.sub hindex).congr
  intro t _ht
  have hpoint := secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add
    (I := I) (M := M) g f hf t
  change secondVariationBoundaryDensity (I := I) g f t =
    secondEnergyDensity (I := I) g f 0 t / 2 -
      indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) t
  rw [hpoint]
  unfold secondVariationBoundaryDensity
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem secondVariation_curveEnergy_eq_indexForm_add_boundary
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g (fun u : ℝ => f 0 u) (Set.Icc 0 L)) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun r : ℝ => curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s)
      (2 *
        (indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
            (fun u : ℝ => centralVariationField (I := I) f u)
            (fun u : ℝ => centralVariationField (I := I) f u)
          + secondVariationBoundary (I := I) g f L
          - secondVariationBoundary (I := I) g f 0)) 0 := by
  have hraw := curveEnergy_deriv_hasDerivAt
    (I := I) (M := M) g f hf 0 L 0
  have hindexInt : IntervalIntegrable
      (fun t : ℝ => indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u) t)
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hL)]
    exact centralVariation_indexFormIntegrand_continuousOn
      (I := I) (M := M) g f hf L
  have hboundaryInt : IntervalIntegrable
      (fun t : ℝ => secondVariationBoundaryDensity (I := I) g f t)
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hL)]
    exact secondVariationBoundaryDensity_continuousOn
      (I := I) (M := M) g f hf L
  have hFTC :
      (∫ t in (0 : ℝ)..L, secondVariationBoundaryDensity (I := I) g f t) =
        secondVariationBoundary (I := I) g f L -
          secondVariationBoundary (I := I) g f 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      simpa only [secondVariationBoundaryDensity] using
        secondVariationBoundary_hasDerivAt (I := I) (M := M)
          g f hf L t hγ ht
    · exact hboundaryInt
  have hcoeff :
      (∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g f 0 t) =
        2 *
          (indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
              (fun u : ℝ => centralVariationField (I := I) f u)
              (fun u : ℝ => centralVariationField (I := I) f u)
            + secondVariationBoundary (I := I) g f L
            - secondVariationBoundary (I := I) g f 0) := by
    calc
      (∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g f 0 t) =
          ∫ t in (0 : ℝ)..L,
            2 *
              (indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
                  (fun u : ℝ => centralVariationField (I := I) f u)
                  (fun u : ℝ => centralVariationField (I := I) f u) t
                + secondVariationBoundaryDensity (I := I) g f t) := by
            apply intervalIntegral.integral_congr
            intro t _ht
            have hpoint := secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add
              (I := I) (M := M) g f hf t
            change secondEnergyDensity (I := I) g f 0 t = 2 *
              (indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
                  (fun u : ℝ => centralVariationField (I := I) f u)
                  (fun u : ℝ => centralVariationField (I := I) f u) t
                + secondVariationBoundaryDensity (I := I) g f t)
            change secondEnergyDensity (I := I) g f 0 t / 2 =
              indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
                  (fun u : ℝ => centralVariationField (I := I) f u)
                  (fun u : ℝ => centralVariationField (I := I) f u) t
                + secondVariationBoundaryDensity (I := I) g f t at hpoint
            linarith [hpoint]
      _ = 2 *
          ((∫ t in (0 : ℝ)..L,
              indexFormIntegrand (I := I) g (fun u : ℝ => f 0 u)
                (fun u : ℝ => centralVariationField (I := I) f u)
                (fun u : ℝ => centralVariationField (I := I) f u) t)
            + ∫ t in (0 : ℝ)..L,
              secondVariationBoundaryDensity (I := I) g f t) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add hindexInt hboundaryInt]
      _ = 2 *
          (indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
              (fun u : ℝ => centralVariationField (I := I) f u)
              (fun u : ℝ => centralVariationField (I := I) f u)
            + secondVariationBoundary (I := I) g f L
            - secondVariationBoundary (I := I) g f 0) := by
            rw [indexForm_eq_intervalIntegral, hFTC]
            ring
  rw [hcoeff] at hraw
  exact hraw

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma centralVariationAcceleration_eq_zero_of_fixed
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hfix : ∀ s : ℝ, f s t = f 0 t) :
    centralVariationAcceleration (I := I) g f t = 0 := by
  change covDerivAlong (I := I) g (fun s : ℝ => f s t)
    (fun s : ℝ =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun r : ℝ => f r t) s (1 : ℝ)) 0 = 0
  have hvel : (fun s : ℝ =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun r : ℝ => f r t) s (1 : ℝ)) =
      (fun _ : ℝ => (0 : E)) := by
    funext s
    have hconst : (fun r : ℝ => f r t) = (fun _ : ℝ => f 0 t) := by
      funext r
      exact hfix r
    rw [hconst, mfderiv_const]
    rfl
  rw [hvel]
  exact covDerivAlong_zero (I := I) g (fun s : ℝ => f s t) 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma centralVariationAcceleration_eq_zero_of_geodesicEndpoint
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ)
    (hgeo : HasGeodesicEquationAt (I := I) g (fun s : ℝ => f s t) 0) :
    centralVariationAcceleration (I := I) g f t = 0 := by
  have hcurve : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun s : ℝ => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    (I := I) g (fun s : ℝ => f s t) 0
    (hcurve.contMDiffAt.of_le
      (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))) hgeo

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem secondVariation_curveEnergy_geodesic_fixedInitial_geodesicTerminal
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g (fun u : ℝ => f 0 u) (Set.Icc 0 L))
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s : ℝ => f s L) 0) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun r : ℝ => curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s)
      (2 * indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u)) 0 := by
  have hgeneral := secondVariation_curveEnergy_eq_indexForm_add_boundary
    (I := I) (M := M) g f L hf hL hcentral
  have hA0 : centralVariationAcceleration (I := I) g f 0 = 0 :=
    centralVariationAcceleration_eq_zero_of_fixed (I := I) g f 0 hfix0
  have hAL : centralVariationAcceleration (I := I) g f L = 0 :=
    centralVariationAcceleration_eq_zero_of_geodesicEndpoint
      (I := I) (M := M) g f hf L hterminal
  have hboundary0 : secondVariationBoundary (I := I) g f 0 = 0 := by
    rw [secondVariationBoundary, hA0, ContinuousLinearMap.map_zero, zero_apply]
  have hboundaryL : secondVariationBoundary (I := I) g f L = 0 := by
    rw [secondVariationBoundary, hAL, ContinuousLinearMap.map_zero, zero_apply]
  apply hgeneral.congr_deriv
  rw [hboundary0, hboundaryL]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g (fun u : ℝ => f 0 u) (Set.Icc 0 L))
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s : ℝ => f s L) 0) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun r : ℝ => (1 / 2 : ℝ) *
          curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s)
      (indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
        (fun u : ℝ => centralVariationField (I := I) f u)
        (fun u : ℝ => centralVariationField (I := I) f u)) 0 := by
  let energy : ℝ → ℝ := fun r : ℝ =>
    curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L
  let J : ℝ := indexForm (I := I) g (fun u : ℝ => f 0 u) 0 L
    (fun u : ℝ => centralVariationField (I := I) f u)
    (fun u : ℝ => centralVariationField (I := I) f u)
  have hsecond : HasDerivAt (fun s : ℝ => deriv energy s) (2 * J) 0 := by
    simpa only [energy, J] using
      secondVariation_curveEnergy_geodesic_fixedInitial_geodesicTerminal
        (I := I) (M := M) g f L hf hL hcentral hfix0 hterminal
  have hscaled : HasDerivAt
      (fun s : ℝ => (1 / 2 : ℝ) * deriv energy s)
      ((1 / 2 : ℝ) * (2 * J)) 0 := hsecond.const_mul (1 / 2 : ℝ)
  have hderivEq : (fun s : ℝ => deriv
      (fun r : ℝ => (1 / 2 : ℝ) * energy r) s) =
      (fun s : ℝ => (1 / 2 : ℝ) * deriv energy s) := by
    funext s
    have henergy := curveEnergy_hasDerivAt
      (I := I) (M := M) g f hf 0 L s
    have hmul := henergy.const_mul (1 / 2 : ℝ)
    rw [hmul.deriv, henergy.deriv]
  rw [show (fun s : ℝ => deriv
      (fun r : ℝ => (1 / 2 : ℝ) *
        curveEnergy (I := I) g (fun t : ℝ => f r t) 0 L) s) =
      (fun s : ℝ => deriv (fun r : ℝ => (1 / 2 : ℝ) * energy r) s) by
    rfl]
  rw [hderivEq]
  apply hscaled.congr_deriv
  ring

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

namespace Poincare.Geometry.Riemannian.Variation

@[reducible] alias centralVariationField := DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationField
@[reducible] alias centralVelocity := DifferentialGeometry.Geometry.Riemannian.Variation.centralVelocity
@[reducible] alias centralVariationAcceleration := DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration
@[reducible] alias secondVariationVelocity := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationVelocity
@[reducible] alias secondVariationBoundary := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationBoundary
@[reducible] alias secondVariationBoundaryDensity := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationBoundaryDensity
alias secondEnergyDensity_zero_div_two_eq := DifferentialGeometry.Geometry.Riemannian.Variation.secondEnergyDensity_zero_div_two_eq
alias secondVariationVelocity_eq := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationVelocity_eq
alias secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add := DifferentialGeometry.Geometry.Riemannian.Variation.secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add
alias secondVariationBoundary_hasDerivAt := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationBoundary_hasDerivAt
alias centralVariation_indexFormIntegrand_continuousOn := DifferentialGeometry.Geometry.Riemannian.Variation.centralVariation_indexFormIntegrand_continuousOn
alias secondVariationBoundaryDensity_continuousOn := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationBoundaryDensity_continuousOn
alias secondVariation_curveEnergy_eq_indexForm_add_boundary := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariation_curveEnergy_eq_indexForm_add_boundary
alias centralVariationAcceleration_eq_zero_of_fixed := DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_zero_of_fixed
alias centralVariationAcceleration_eq_zero_of_geodesicEndpoint := DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_zero_of_geodesicEndpoint
alias secondVariation_curveEnergy_geodesic_fixedInitial_geodesicTerminal := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariation_curveEnergy_geodesic_fixedInitial_geodesicTerminal
alias secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal := DifferentialGeometry.Geometry.Riemannian.Variation.secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal

end Poincare.Geometry.Riemannian.Variation
