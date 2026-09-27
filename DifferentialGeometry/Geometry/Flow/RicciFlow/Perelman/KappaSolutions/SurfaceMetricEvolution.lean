import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRicciAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

theorem eq_linear_scale_of_ancient_reciprocal_ode
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Iic (0 : ℝ)))
    (hderiv : ∀ s : ℝ, s < 0 → HasDerivAt f (-f s / (T - s)) s)
    {t : ℝ} (ht : t ≤ 0) :
    f t = ((T - t) / T) * f 0 := by
  let F : ℝ → ℝ := fun s => f s / (T - s)
  have hden (s : ℝ) (hs : s ≤ 0) : T - s ≠ 0 := ne_of_gt (by linarith)
  have hFcont : ContinuousOn F (Iic (0 : ℝ)) :=
    hcont.div (continuous_const.sub continuous_id).continuousOn hden
  have hFderiv (s : ℝ) (hs : s < 0) : HasDerivAt F 0 s := by
    have hd : HasDerivAt (fun r : ℝ => T - r) (-1) s :=
      (hasDerivAt_id s).const_sub T
    have hquot := (hderiv s hs).fun_div hd (hden s hs.le)
    have hcoeff : ((-f s / (T - s)) * (T - s) - f s * (-1)) /
        (T - s) ^ 2 = 0 := by
      rw [div_mul_cancel₀ _ (hden s hs.le)]
      simp
    rw [hcoeff] at hquot
    exact hquot
  have hFdiff : DifferentiableOn ℝ F (interior (Iic (0 : ℝ))) := by
    intro s hs
    rw [interior_Iic] at hs
    exact (hFderiv s hs).differentiableAt.differentiableWithinAt
  have hFzero : ∀ s ∈ interior (Iic (0 : ℝ)), deriv F s = 0 := by
    intro s hs
    rw [interior_Iic] at hs
    exact (hFderiv s hs).deriv
  have hmono : MonotoneOn F (Iic (0 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Iic 0) hFcont hFdiff
      (fun s hs => by rw [hFzero s hs])
  have hanti : AntitoneOn F (Iic (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hFcont hFdiff
      (fun s hs => by rw [hFzero s hs])
  have hratio : f t / (T - t) = f 0 / T := by
    have heq : F t = F 0 :=
      le_antisymm (hmono ht (by simp) ht) (hanti ht (by simp) ht)
    simpa only [F, sub_zero] using heq
  calc
    f t = (f t / (T - t)) * (T - t) := (div_mul_cancel₀ _ (hden t ht)).symm
    _ = (f 0 / T) * (T - t) := by rw [hratio]
    _ = ((T - t) / T) * f 0 := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

theorem surfaceMetric_hasDerivAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {t : ℝ} (ht : t ∈ D.regular)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s : ℝ => (S.family.metric s).inner x v w)
      (-S.scalar t x * (S.family.metric t).inner x v w) t := by
  have h := metricDerivAt S hS ⟨t, ht⟩ x v w
  have hr : S.ricciAt t x (vec2 v w) =
      (S.scalar t x / 2) * (S.family.metric t).inner x v w :=
    metricRicciAt_apply_of_finrank_two (S.family.metric t) hdim x v w
  change HasDerivAt (fun s : ℝ => (S.family.metric s).inner x v w)
    ((-2 : ℝ) * S.ricciAt t x (vec2 v w)) t at h
  rw [hr] at h
  have hcoeff : (-2 : ℝ) * ((S.scalar t x / 2) *
      (S.family.metric t).inner x v w) =
      -S.scalar t x * (S.family.metric t).inner x v w := by ring
  rw [hcoeff] at h
  exact h

theorem surfaceMetric_eq_scale_of_scalar_profile
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2)
    (hcarrier : D.carrier = Iic (0 : ℝ)) (hregular : D.regular = Iio (0 : ℝ))
    {T : ℝ} (hT : 0 < T)
    (hscalar : ∀ t : ℝ, t ≤ 0 → ∀ x : M, S.scalar t x = 1 / (T - t))
    {t : ℝ} (ht : t ≤ 0) :
    S.family.metric t = scaleMetric ((T - t) / T)
      (div_pos (by linarith) hT) (S.family.metric 0) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner]
  refine eq_linear_scale_of_ancient_reciprocal_ode
    (f := fun s : ℝ => (S.family.metric s).inner x v w) hT ?_ ?_ ht
  · simpa only [← hcarrier] using hS.smoothMetric.coeff_cont x v w
  · intro s hs
    have hsreg : s ∈ D.regular := by simpa only [hregular, mem_Iio] using hs
    have hd := surfaceMetric_hasDerivAt S hS hdim hsreg x v w
    rw [hscalar s hs.le x] at hd
    have hcoeff : -(1 / (T - s)) * (S.family.metric s).inner x v w =
        -(S.family.metric s).inner x v w / (T - s) := by ring
    rw [hcoeff] at hd
    exact hd

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
