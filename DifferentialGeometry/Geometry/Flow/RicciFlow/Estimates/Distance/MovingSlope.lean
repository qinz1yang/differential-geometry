import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.UpperSupport
import DifferentialGeometry.Geometry.Metric.Family.CurveDistance
import DifferentialGeometry.Geometry.Metric.Family.MovingEndpoints

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped ENNReal Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem eventually_displacement_div_sub_lt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    {T tau : Real} (ht : T - tau ∈ D.regular)
    {x : Real → M}
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      (riemannianEDistOf (I := I) (S.base.metric (T - s))
        (x tau) (x s)).toReal / (s - tau) <
      Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
        (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
        (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon := by
  let J : Set Real := {s | T - s ∈ D.carrier}
  have hJ : J ∈ 𝓝 tau := by
    have hpre := (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      (D.regular_isOpen.mem_nhds ht)
    exact mem_of_superset hpre (fun _ hs => D.regular_subset hs)
  have hG' : Continuous (metricTimeBundleQuad (I := I)
      (fun s => S.base.metric (T - s)) J) := by
    have hbase := metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      S.family.metric hG (Subset.refl D.carrier)
    have htime : Continuous (fun q : J × TangentBundle I M =>
        (⟨T - q.1.1, q.1.2⟩ : D.carrier)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    exact hbase.comp (htime.prodMk continuous_snd)
  intro epsilon hepsilon
  have hevent := eventually_riemannianEDistOf_le_mul_abs_sub
    (fun s => S.base.metric (T - s)) hJ hG' hx (epsilon / 2) (by linarith)
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with s hs htaus
  have hden : 0 < s - tau := sub_pos.mpr htaus
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (add_nonneg (Real.sqrt_nonneg _) (by linarith)) (abs_nonneg _)),
    abs_of_pos hden] at hr
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr hr
  rw [mul_div_cancel_right₀ _ hden.ne'] at hdiv
  exact hdiv.trans_lt (add_lt_add_right (by linarith : epsilon / 2 < epsilon) _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_slope_riemannianEDistOf_lt_of_lt_two_mul
    [PreconnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hK : 0 ≤ K) (hr : 0 < r)
    (x y : Real → M)
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau)
    (hy : ContMDiffAt 𝓘(Real, Real) I 1 y tau)
    (hshort :
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal < 2 * r)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (x tau) z < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (y tau) z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      slope (fun u ↦
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau s <
      2 * ((Module.finrank Real E : Real) - 1) * K * r +
        Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) +
        Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))) + epsilon := by
  rcases exists_upper_support_riemannianEDistOf_of_lt_two_mul (I := I) S hS ht hcomplete hK hr
      (x tau) (y tau) hshort hRic with
    ⟨phi, d, hcontact, hupper, hphi, hd⟩
  have hmove := eventually_slope_riemannianEDistOf_lt (I := I)
    (fun s ↦ S.base.metric (T - s)) x y phi hcontact hupper
    hphi.hasDerivWithinAt
    (vx := Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
      (mfderiv 𝓘(Real, Real) I x tau 1) (mfderiv 𝓘(Real, Real) I x tau 1)))
    (vy := Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
      (mfderiv 𝓘(Real, Real) I y tau 1) (mfderiv 𝓘(Real, Real) I y tau 1)))
    ?_ ?_
  · intro epsilon hepsilon
    filter_upwards [hmove epsilon hepsilon] with s hs
    exact hs.trans_le (add_le_add (add_le_add (add_le_add hd le_rfl) le_rfl) le_rfl)
  · intro epsilon hepsilon
    filter_upwards [eventually_displacement_div_sub_lt (I := I) S hS.smoothMetric ht hx
      epsilon hepsilon] with s hs
    rw [riemannianEDistOf_comm (I := I) (S.base.metric (T - s)) (x s) (x tau)]
    exact hs
  · exact eventually_displacement_div_sub_lt (I := I) S hS.smoothMetric ht hy

omit [NeZero (Module.finrank Real E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_slope_riemannianEDistOf_lt_of_two_mul_le
    [PreconnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hr : 0 < r)
    (x y : Real → M)
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau)
    (hy : ContMDiffAt 𝓘(Real, Real) I 1 y tau)
    (hlong : 2 * r ≤
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (x tau) z < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (y tau) z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      slope (fun u ↦
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau s <
      2 * ((Module.finrank Real E : Real) - 1) *
          ((2 / 3 : Real) * K * r + 1 / r) +
        Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) +
        Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))) + epsilon := by
  rcases exists_upper_support_riemannianEDistOf_of_two_mul_le (I := I) S hS ht hcomplete hr
      (x tau) (y tau) hlong hRic with
    ⟨phi, d, hcontact, hupper, hphi, hd⟩
  have hmove := eventually_slope_riemannianEDistOf_lt (I := I)
    (fun s ↦ S.base.metric (T - s)) x y phi hcontact hupper
    hphi.hasDerivWithinAt
    (vx := Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
      (mfderiv 𝓘(Real, Real) I x tau 1) (mfderiv 𝓘(Real, Real) I x tau 1)))
    (vy := Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
      (mfderiv 𝓘(Real, Real) I y tau 1) (mfderiv 𝓘(Real, Real) I y tau 1)))
    ?_ ?_
  · intro epsilon hepsilon
    filter_upwards [hmove epsilon hepsilon] with s hs
    exact hs.trans_le (add_le_add (add_le_add (add_le_add hd le_rfl) le_rfl) le_rfl)
  · intro epsilon hepsilon
    filter_upwards [eventually_displacement_div_sub_lt (I := I) S hS.smoothMetric ht hx
      epsilon hepsilon] with s hs
    rw [riemannianEDistOf_comm (I := I) (S.base.metric (T - s)) (x s) (x tau)]
    exact hs
  · exact eventually_displacement_div_sub_lt (I := I) S hS.smoothMetric ht hy

end DifferentialGeometry.PDE.RicciFlow
