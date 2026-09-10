import DifferentialGeometry.Geometry.Comparison.Soul.SbrRightFirstVariation
import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

private theorem antitoneOn_max_of_upper_right_slope_nonpos_on_pos
    {f : ℝ → ℝ} {a b eps : ℝ}
    (hf : ContinuousOn f (Icc a b)) (heps : 0 < eps)
    (hbound : ∀ t ∈ Ico a b, 0 < f t → ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    AntitoneOn (fun t => max (f t) eps) (Icc a b) := by
  apply antitoneOn_of_upper_right_slope_nonpos
    (fun t ht => (hf t ht).max tendsto_const_nhds)
  intro t ht r hr
  by_cases hlarge : eps ≤ f t
  · have hpositive : 0 < f t := heps.trans_le hlarge
    filter_upwards [hbound t ht hpositive r hr, self_mem_nhdsWithin] with s hs hst
    have hts : 0 < s - t := sub_pos.mpr hst
    rw [slope_def_field] at hs
    have hnum : f s - f t < r * (s - t) := (div_lt_iff₀ hts).mp hs
    have hprod : 0 < r * (s - t) := mul_pos hr hts
    have hmax : max (f s) eps < r * (s - t) + f t :=
      max_lt_iff.mpr ⟨by linarith, by linarith⟩
    rw [slope_def_field, max_eq_left hlarge]
    apply (div_lt_iff₀ hts).mpr
    linarith
  · have hsmall : f t < eps := lt_of_not_ge hlarge
    have hnear : ∀ᶠ s in 𝓝[Icc a b] t, f s < eps :=
      (hf t (Ico_subset_Icc_self ht)).eventually (Iio_mem_nhds hsmall)
    have hright : ∀ᶠ s in 𝓝[>] t, f s < eps :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht) hnear
    filter_upwards [hright] with s hs
    rw [slope_def_field]
    simpa only [max_eq_right hs.le, max_eq_right hsmall.le, sub_self, zero_div] using hr

theorem antitoneOn_of_upper_right_slope_nonpos_on_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hbound : ∀ t ∈ Ico a b, 0 < f t → ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  by_contra hnot
  have hlt : f x < f y := lt_of_not_ge hnot
  have hypos : 0 < f y := (hnonneg x hx).trans_lt hlt
  have hanti := antitoneOn_max_of_upper_right_slope_nonpos_on_pos
    hf (half_pos hypos) hbound
  have hh : max (f y) (f y / 2) ≤ max (f x) (f y / 2) := hanti hx hy hxy
  have hmax : max (f x) (f y / 2) < f y :=
    max_lt_iff.mpr ⟨hlt, half_lt_self hypos⟩
  exact (not_lt_of_ge ((le_max_left (f y) (f y / 2)).trans hh)) hmax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsRiemannianManifold I M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem tangent_cast_model_eq {p q : M} (h : p = q)
    (v : TangentSpace I p) : (h ▸ v : TangentSpace I q) = (v : E) := by
  cases h
  rfl

theorem antitoneOn_dist_of_right_first_variation_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (Icc a b)) (hzeta : ContinuousOn zeta (Icc a b))
    (X : (t : ℝ) → ℝ →L[ℝ] TangentSpace I (xi t))
    (Y : (t : ℝ) → ℝ →L[ℝ] TangentSpace I (zeta t))
    (hX : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t (X t))
    (hY : ∀ t ∈ Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t (Y t))
    (hangle : ∀ t ∈ Ico a b, xi t ≠ zeta t →
      ∀ u : TangentSpace I (xi t), g.inner (xi t) u u = 1 →
      ∀ hend : intrinsicGeodesic g hEnorm (xi t) u (dist (xi t) (zeta t)) = zeta t,
        -g.inner (xi t) (X t 1) u + g.inner (zeta t) (Y t 1)
          (hend ▸ curveVelocity (I := I) (intrinsicGeodesic g hEnorm (xi t) u)
            (dist (xi t) (zeta t))) ≤ 0) :
    AntitoneOn (fun t => dist (xi t) (zeta t)) (Icc a b) := by
  apply antitoneOn_of_upper_right_slope_nonpos_on_pos
    (fun t ht => (hxi t ht).dist (hzeta t ht))
    (fun _ _ => dist_nonneg)
  intro t ht hpos r hr
  have hne : xi t ≠ zeta t := dist_pos.mp hpos
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm (xi t) (zeta t) hpos
  have hmin : dist (xi t)
      (intrinsicGeodesic g hEnorm (xi t) u (dist (xi t) (zeta t))) =
        dist (xi t) (zeta t) := by rw [hend]
  have hcoeff := hangle t ht hne u hu hend
  rw [tangent_cast_model_eq] at hcoeff
  have hcoeff' :
      -g.inner (xi t) (X t 1) u +
        g.inner (intrinsicGeodesic g hEnorm (xi t) u (dist (xi t) (zeta t))) (Y t 1)
          (curveVelocity (I := I) (intrinsicGeodesic g hEnorm (xi t) u)
            (dist (xi t) (zeta t))) ≤ 0 := by
    rw [hend]
    exact hcoeff
  exact upper_right_first_variation_of_minimizing_geodesic g hEnorm (xi t) u
    (dist (xi t) (zeta t)) hpos hu hmin xi zeta t rfl hend.symm
    (X t) (Y t) (hX t ht) (hY t ht) r (hcoeff'.trans_lt hr)

end DifferentialGeometry.Geometry.Topology
