import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartMetric
import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceGradient

/-!
# Minimizing directions to a closed set, read in a chart (LC28, tier T2)

Let `Y` be a closed nonempty set, `V_z(Y) = minimizingDirectionsTo g hEnorm Y z` (initial unit
velocities of minimizing geodesics from `z` to nearest points of `Y`), `b` a chart centre and
`e = trivializationAt E (TangentSpace I) b`.

* `infDist_upper_support_of_isClosed`: at every `q ∉ Y` the distance `d_Y` has a smooth upper
  support function whose gradient is `-u` for some `u ∈ V_q(Y)` (nearest points exist because the
  closed balls are compact).
* `eventually_minimizingDirectionsTo_chart_close` (upper semicontinuity of `V(Y)` in a chart): if
  every `u ∈ V_b(Y)` is within `a` of a fixed `u₀` in `g_b`, then near `b`, for every `u ∈ V_z(Y)`
  and every `w ∈ E`, `|g_z(u, e.symmL z w) - g_b(u₀, w)| ≤ a N_b(w)`.
* `eventually_infDist_chart_increment_le` (directional upper bound): the right difference
  quotients of `t ↦ d_Y(φ.symm(φ z + t w))` at `0` are eventually below any `c` exceeding
  `-g_z(u, e.symmL z w)` for all `u ∈ V_z(Y)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Smooth upper support of the distance to a closed set, with gradient `-u`, `u ∈ V_q(Y)`. -/
theorem infDist_upper_support_of_isClosed (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) {q : M}
    (hq : 0 < Metric.infDist q Y) :
    ∃ ρ : M → ℝ, ∃ u : TangentSpace I q,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ q ∧ ρ q = Metric.infDist q Y ∧
      (∀ᶠ y in 𝓝 q, Metric.infDist y Y ≤ ρ y) ∧
      u ∈ minimizingDirectionsTo g hEnorm Y q ∧ gradientFun g ρ q = -u := by
  have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨y₀, hy₀, hd⟩ := hY.exists_infDist_eq_dist hYne q
  have hsingle : Metric.infDist q {y₀} = Metric.infDist q Y := by
    rw [Metric.infDist_singleton, hd]
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hup, hgrad⟩ :=
    infDist_upper_support g hEnorm isCompact_singleton (singleton_nonempty y₀) q
      (hsingle ▸ hq)
  refine ⟨ρ, u, hρ, hval.trans hsingle, ?_, ⟨hu, ?_⟩, hgrad⟩
  · filter_upwards [hupper] with y hy
    exact (Metric.infDist_le_infDist_of_subset (singleton_subset_iff.mpr hy₀)
      (singleton_nonempty y₀)).trans hy
  · rw [← hsingle]
    have := mem_singleton_iff.mp hup
    rw [this]
    exact hy₀

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem continuous_tangentBundle_smul
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hf : Continuous f) :
    Continuous (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp (hv.continuousAt (x := x))
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))
  apply (hf.continuousAt.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

/-- Upper semicontinuity of the minimizing directions, read through the chart at `b`. -/
theorem eventually_minimizingDirectionsTo_chart_close (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Set M} (hY : IsClosed Y) (b : M) {u₀ : TangentSpace I b}
    {a : ℝ}
    (hclose : ∀ u ∈ minimizingDirectionsTo g hEnorm Y b,
      Real.sqrt (g.inner b (u - u₀) (u - u₀)) < a) :
    ∀ᶠ z in 𝓝 b, ∀ u ∈ minimizingDirectionsTo g hEnorm Y z, ∀ w : E,
      |g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) -
          metricFormAt g b u₀ w| ≤ a * metricSeminormAt g b w := by
  obtain ⟨K, hKc, hKb, hKsrc⟩ : ∃ K : Set M, IsCompact K ∧ K ∈ 𝓝 b ∧ K ⊆ (chartAt H b).source := by
    have : LocallyCompactSpace M := by
      have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
      infer_instance
    obtain ⟨K, hK1, hK2, hK3⟩ := local_compact_nhds
      ((chartAt H b).open_source.mem_nhds (mem_chart_source H b))
    exact ⟨K, hK3, hK1, hK2⟩
  let base : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let vec : (p : MetricUnitTangent (I := I) g) → TangentSpace I (base p) := MetricUnitTangent.vec
  have hbase : Continuous base :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hvec : Continuous (fun p => (⟨base p, vec p⟩ : TangentBundle I M)) := continuous_subtype_val
  let Sph : Set E := {w : E | metricFormAt g b w w = 1}
  have hSph : IsCompact Sph := gUnitSphere_isCompact g b
  let D : Set (MetricUnitTangent (I := I) g × E) := {p | base p ∈ K} ×ˢ Sph
  have hD : IsCompact D := (metricUnitOn_compact g hKc).prod hSph
  let F : MetricUnitTangent (I := I) g × E → ℝ := fun x =>
    g.inner (base x.1) (vec x.1) ((trivializationAt E (TangentSpace I) b).symmL ℝ (base x.1) x.2) -
      metricFormAt g b u₀ x.2
  have hF : ContinuousOn F D := by
    refine ContinuousOn.sub ?_ ((metricFormAt g b u₀).continuous.comp continuous_snd).continuousOn
    refine continuousOn_gInner_of_bundle (b := fun x : MetricUnitTangent (I := I) g × E => base x.1)
      (hvec.comp continuous_fst).continuousOn ?_
    refine (continuousOn_trivializationAt_symm b).comp
      ((hbase.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro x hx
    exact ⟨hKsrc hx.1, mem_univ _⟩
  have hscale := continuous_tangentBundle_smul (I := I)
    (f := fun p => Metric.infDist (base p) Y) hvec ((Metric.continuous_infDist_pt Y).comp hbase)
  have hend : Continuous (fun p => expMapIntrinsic g hEnorm (base p)
      (Metric.infDist (base p) Y • vec p)) :=
    (intrinsicExp_smooth g hEnorm).continuous.comp hscale
  let bad : Set (MetricUnitTangent (I := I) g × E) :=
    (D ∩ F ⁻¹' {r | a ≤ |r|}) ∩
      {x | expMapIntrinsic g hEnorm (base x.1) (Metric.infDist (base x.1) Y • vec x.1) ∈ Y}
  have : T2Space (MetricUnitTangent (I := I) g) :=
    inferInstanceAs (T2Space {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1})
  have hbadc : IsCompact bad := by
    refine hD.of_isClosed_subset ?_ (fun x hx => hx.1.1)
    exact (hF.preimage_isClosed_of_isClosed hD.isClosed
      (isClosed_le continuous_const continuous_abs)).inter (hY.preimage (hend.comp continuous_fst))
  have himg : IsClosed ((fun x => base x.1) '' bad) :=
    (hbadc.image (hbase.comp continuous_fst)).isClosed
  have hbnot : b ∉ (fun x => base x.1) '' bad := by
    rintro ⟨⟨⟨⟨y, u⟩, hu⟩, w⟩, ⟨⟨hxD, hxF⟩, hxY⟩, hyb⟩
    change y = b at hyb
    subst hyb
    have hw : metricFormAt g y w w = 1 := hxD.2
    have huV : u ∈ minimizingDirectionsTo g hEnorm Y y := by
      refine ⟨hu, ?_⟩
      change expMapIntrinsic g hEnorm y (Metric.infDist y Y • u) ∈ Y at hxY
      simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hxY
    have hFval : F (⟨⟨y, u⟩, hu⟩, w) = g.inner y (u - u₀) w := by
      change g.inner y u ((trivializationAt E (TangentSpace I) y).symmL ℝ y w) -
        g.inner y u₀ w = _
      rw [trivializationAt_symmL_self, map_sub]
      rfl
    have hle : a ≤ |F (⟨⟨y, u⟩, hu⟩, w)| := hxF
    rw [hFval] at hle
    have hcs := abs_inner_le_sqrt_mul_sqrt g y (u - u₀) w
    have hw' : g.inner y w w = 1 := hw
    rw [hw', Real.sqrt_one, mul_one] at hcs
    have := hclose u huV
    linarith
  filter_upwards [himg.isOpen_compl.mem_nhds hbnot, hKb] with z hz hzK
  intro u hu w
  have hsph : ∀ w₁ : E, metricFormAt g b w₁ w₁ = 1 →
      |g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w₁) -
          metricFormAt g b u₀ w₁| < a := by
    intro w₁ hw₁
    by_contra hcon
    apply hz
    refine ⟨(⟨⟨z, u⟩, hu.1⟩, w₁), ⟨⟨⟨hzK, hw₁⟩, le_of_not_gt hcon⟩, ?_⟩, rfl⟩
    change expMapIntrinsic g hEnorm z (Metric.infDist z Y • u) ∈ Y
    simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hu.2
  by_cases hq : metricFormAt g b w w = 0
  · have hw0 : w = 0 := by
      by_contra hw
      exact lt_irrefl _ (hq ▸ g.pos b w hw)
    subst hw0
    simp
  · have hqpos : 0 < metricFormAt g b w w :=
      lt_of_le_of_ne (metricFormAt_self_nonneg g b w) (Ne.symm hq)
    set s := metricSeminormAt g b w with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hqpos
    have hs2 : s ^ 2 = metricFormAt g b w w := metricSeminormAt_sq g b w
    have hw₁ : metricFormAt g b (s⁻¹ • w) (s⁻¹ • w) = 1 := by
      rw [metricFormAt_smul_self, inv_pow, ← hs2, inv_mul_cancel₀ (by positivity)]
    have h1 := hsph _ hw₁
    have hlin : g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) -
        metricFormAt g b u₀ w = s * (g.inner z u
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z (s⁻¹ • w)) -
          metricFormAt g b u₀ (s⁻¹ • w)) := by
      simp only [map_smul, smul_eq_mul]
      field_simp
    rw [hlin, abs_mul, abs_of_pos hspos, mul_comm a s]
    exact mul_le_mul_of_nonneg_left h1.le hspos.le

/-- Directional upper bound for the distance to a closed set read through the chart at `b`. -/
theorem eventually_infDist_chart_increment_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) (b : M) {z : M}
    (hz : z ∈ (chartAt H b).source) (hzY : 0 < Metric.infDist z Y) (w : E) {c : ℝ}
    (hc : ∀ u ∈ minimizingDirectionsTo g hEnorm Y z,
      -g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Metric.infDist ((extChartAt I b).symm (extChartAt I b z + t • w)) Y -
        Metric.infDist z Y ≤ t * c := by
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hgrad⟩ :=
    infDist_upper_support_of_isClosed g hEnorm hY hYne hzY
  set φ := extChartAt I b with hφ
  set y₀ := φ z with hy₀def
  have hzs : z ∈ φ.source := by rw [hφ, extChartAt_source]; exact hz
  have hy₀ : y₀ ∈ φ.target := φ.map_source hzs
  have hzinv : φ.symm y₀ = z := φ.left_inv hzs
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I φ.symm y₀ := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := b) hy₀
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hmd : mfderiv 𝓘(ℝ, E) I φ.symm y₀ =
      (trivializationAt E (TangentSpace I) b).symmL ℝ z := by
    rw [TangentBundle.symmL_trivializationAt hz, ModelWithCorners.Boundaryless.range_eq_univ,
      mfderivWithin_univ]
  have hρ' : HasMFDerivAt I 𝓘(ℝ, ℝ) ρ (φ.symm y₀) (mfderiv I 𝓘(ℝ, ℝ) ρ z) := by
    rw [hzinv]
    exact (hρ.mdifferentiableAt (by simp)).hasMFDerivAt
  have hF := hasMFDerivAt_iff_hasFDerivAt.mp (hρ'.comp y₀ hsymm.hasMFDerivAt)
  have hline : HasDerivAt (fun t : ℝ => y₀ + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y₀
  have hk := hF.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  set k : ℝ → ℝ := (ρ ∘ φ.symm) ∘ fun t : ℝ => y₀ + t • w with hkdef
  have hder : (mfderiv I 𝓘(ℝ, ℝ) ρ z).comp (mfderiv 𝓘(ℝ, E) I φ.symm y₀) w =
      -g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) := by
    change mfderiv I 𝓘(ℝ, ℝ) ρ z (mfderiv 𝓘(ℝ, E) I φ.symm y₀ w) = _
    rw [hmd]
    have h := inner_gradientFun g ρ z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
    rw [hgrad, map_neg, neg_apply] at h
    have h' : mvfderiv (I := I) ρ z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) =
        mfderiv I 𝓘(ℝ, ℝ) ρ z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) := rfl
    exact (h.trans h').symm
  have hlt : @LT.lt ℝ _ ((mfderiv I 𝓘(ℝ, ℝ) ρ z).comp (mfderiv 𝓘(ℝ, E) I φ.symm y₀) w) c := by
    rw [hder]; exact hc u hu
  have hslope := (hk.hasDerivWithinAt (s := Ioi 0)).limsup_slope_le' (lt_irrefl 0) hlt
  have hk0 : k 0 = Metric.infDist z Y := by
    simp only [hkdef, Function.comp_apply, zero_smul, add_zero, hzinv, hval]
  have hcont : ContinuousAt (fun t : ℝ => φ.symm (y₀ + t • w)) 0 := by
    have hl : ContinuousAt (fun t : ℝ => y₀ + t • w) 0 := hline.continuousAt
    refine ContinuousAt.comp_of_eq hsymm.continuousAt hl (by simp)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Metric.infDist (φ.symm (y₀ + t • w)) Y ≤ ρ (φ.symm (y₀ + t • w)) := by
    have ht := hcont.tendsto
    simp only [zero_smul, add_zero, hzinv] at ht
    exact ht.eventually hupper
  filter_upwards [hslope, nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t hs hle ht
  have htpos : 0 < t := ht
  rw [slope_def_field, sub_zero, div_lt_iff₀ htpos] at hs
  have hkt : k t = ρ (φ.symm (y₀ + t • w)) := rfl
  rw [hk0, hkt] at hs
  linarith

end DifferentialGeometry.Geometry.Collapse
