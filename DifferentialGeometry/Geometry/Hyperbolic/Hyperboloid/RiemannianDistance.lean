import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianGeodesic
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.Metric.CurveSpeed

noncomputable section

open scoped _root_.Manifold ContDiff Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def coshDist (x y : Hyperboloid E) : ℝ := Real.cosh (dist x y)

private theorem one_le_coshDist (x y : Hyperboloid E) : 1 ≤ coshDist x y :=
  Real.one_le_cosh (dist x y)

private theorem contMDiff_coshDist (x : Hyperboloid E) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coshDist x) := by
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y : Hyperboloid E => inner ℝ x.space y.space) :=
    (innerSL ℝ x.space).contDiff.contMDiff.comp contMDiff_space
  have hfun : coshDist x = fun y : Hyperboloid E =>
      x.time * y.time - inner ℝ x.space y.space := funext fun y => cosh_dist x y
  rw [hfun]
  exact ((contMDiff_const (c := x.time)).mul contMDiff_time).sub hi

private theorem mvfderiv_coshDist (x y : Hyperboloid E) (v : TangentSpace 𝓘(ℝ, E) y) :
    mvfderiv 𝓘(ℝ, E) (coshDist x) y v =
      x.time * (inner ℝ y.space
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) y.space
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph y v)) / y.time) -
        inner ℝ x.space
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) y.space
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph y v)) := by
  let u : E := NormedSpace.fromTangentSpace (𝕜 := ℝ) (spaceDiffeomorph y)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph y v)
  have ht := (contMDiff_time (E := E) (n := ∞)).mdifferentiableAt (x := y) (by decide)
  have hs := (spaceDiffeomorph (E := E)).contMDiff.mdifferentiableAt (x := y) (by decide)
  let L : E →L[ℝ] ℝ := innerSL ℝ x.space
  have hi := L.differentiableAt.mdifferentiableAt.comp y hs
  have hfun : coshDist x = (fun z : Hyperboloid E => x.time) * time -
      (L ∘ (spaceDiffeomorph : Hyperboloid E → E)) := by
    funext z
    exact cosh_dist x z
  have hinner : mvfderiv 𝓘(ℝ, E) (L ∘ (spaceDiffeomorph : Hyperboloid E → E)) y v =
      inner ℝ x.space u := by
    rw [mvfderiv_comp_apply (f := (spaceDiffeomorph : Hyperboloid E → E)) (g := L)
      y L.differentiableAt.mdifferentiableAt hs, mvfderiv_eq_fderiv, L.fderiv]
    rfl
  change mvfderiv 𝓘(ℝ, E) (coshDist x) y v =
    x.time * (inner ℝ y.space u / y.time) - inner ℝ x.space u
  rw [hfun, mvfderiv_sub (mdifferentiableAt_const.mul ht) hi,
    mvfderiv_mul mdifferentiableAt_const ht]
  simp only [sub_apply, smul_apply, mvfderiv_const,
    smul_zero, add_zero, smul_eq_mul]
  rw [hinner]
  have htime := mfderiv_time_apply y v
  change mvfderiv 𝓘(ℝ, E) time y v = inner ℝ y.space u / y.time at htime
  rw [htime]

private theorem mvfderiv_coshDist_sq_le (x y : Hyperboloid E) (v : TangentSpace 𝓘(ℝ, E) y) :
    (mvfderiv 𝓘(ℝ, E) (coshDist x) y v) ^ 2 ≤
      (coshDist x y ^ 2 - 1) * riemannianMetric.inner y v v := by
  let u : E := NormedSpace.fromTangentSpace (𝕜 := ℝ) (spaceDiffeomorph y)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph y v)
  let a : ℝ × E := (inner ℝ y.space u / y.time, u)
  let p : ℝ × E := (y.time, y.space)
  let q : ℝ × E := (x.time, x.space) - coshDist x y • p
  have hp : lorentzForm E p p = -1 := by
    change inner ℝ y.space y.space - y.time * y.time = -1
    nlinarith [y.time_sq_sub_inner_self]
  have hx : lorentzForm E (x.time, x.space) (x.time, x.space) = -1 := by
    change inner ℝ x.space x.space - x.time * x.time = -1
    nlinarith [x.time_sq_sub_inner_self]
  have hpx : lorentzForm E p (x.time, x.space) = -coshDist x y := by
    change inner ℝ y.space x.space - y.time * x.time = -Real.cosh (dist x y)
    rw [cosh_dist, real_inner_comm x.space y.space]
    ring
  have hxp : lorentzForm E (x.time, x.space) p = -coshDist x y :=
    ((lorentzForm_isSymm E).eq _ _).trans hpx
  have hpa : lorentzForm E p a = 0 := by
    change inner ℝ y.space u - y.time * (inner ℝ y.space u / y.time) = 0
    field_simp [y.time_pos.ne']
    ring
  have hpq : lorentzForm E p q = 0 := by
    simp only [q, map_sub, map_smul, hpx, hp, smul_eq_mul]
    ring
  have hqq : lorentzForm E q q = coshDist x y ^ 2 - 1 := by
    simp only [q, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hp, hx, hpx, hxp]
    ring
  have haa : lorentzForm E a a = riemannianMetric.inner y v v := by
    rw [riemannianMetric_inner]
    change inner ℝ u u - (inner ℝ y.space u / y.time) * (inner ℝ y.space u / y.time) =
      inner ℝ u u - inner ℝ y.space u * inner ℝ y.space u / (1 + ‖y.space‖ ^ 2)
    rw [← y.time_sq]
    field_simp [y.time_pos.ne']
  have hqa : lorentzForm E q a = -mvfderiv 𝓘(ℝ, E) (coshDist x) y v := by
    rw [mvfderiv_coshDist]
    simp only [q, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hpa,
      smul_eq_mul, mul_zero, sub_zero]
    change inner ℝ x.space u - x.time * (inner ℝ y.space u / y.time) =
      -(x.time * (inner ℝ y.space u / y.time) - inner ℝ x.space u)
    ring
  have hp0 : p ≠ 0 := by
    intro h
    exact y.time_pos.ne' (congrArg Prod.fst h)
  have h := lorentzForm_sq_le_of_orthogonal (hp.le.trans (by norm_num)) hp0 hpq hpa
  rw [hqq, haa, hqa, neg_sq] at h
  exact h

private def distancePotential (x : Hyperboloid E) (ε : ℝ) (y : Hyperboloid E) : ℝ :=
  Real.arcosh (coshDist x y + ε)

private theorem contMDiff_distancePotential (x : Hyperboloid E) {ε : ℝ} (hε : 0 < ε) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (distancePotential x ε) := by
  have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (fun y : Hyperboloid E => coshDist x y + ε) :=
    ((contMDiff_coshDist x).of_le (by simp)).add contMDiff_const
  intro y
  have harg : 1 < coshDist x y + ε := by linarith [one_le_coshDist x y]
  exact (Real.contDiffAt_arcosh (n := 1) harg).contMDiffAt.comp y hc.contMDiffAt

private theorem mvfderiv_distancePotential (x y : Hyperboloid E) {ε : ℝ} (hε : 0 < ε)
    (v : TangentSpace 𝓘(ℝ, E) y) :
    mvfderiv 𝓘(ℝ, E) (distancePotential x ε) y v =
      mvfderiv 𝓘(ℝ, E) (coshDist x) y v / Real.sqrt ((coshDist x y + ε) ^ 2 - 1) := by
  let f : Hyperboloid E → ℝ := fun z => coshDist x z + ε
  have hc := (contMDiff_coshDist x).mdifferentiableAt (x := y) (by decide)
  have hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f y := hc.add mdifferentiableAt_const
  have harg : f y ∈ Set.Ioi 1 := by
    change 1 < coshDist x y + ε
    linarith [one_le_coshDist x y]
  have ha := Real.hasDerivAt_arcosh harg
  change mvfderiv 𝓘(ℝ, E) (Real.arcosh ∘ f) y v = _
  rw [mvfderiv_comp_apply (f := f) (g := Real.arcosh) y
    ha.differentiableAt.mdifferentiableAt hf, mvfderiv_eq_fderiv, ha.hasFDerivAt.fderiv]
  change mvfderiv 𝓘(ℝ, E) (coshDist x + fun _ : Hyperboloid E => ε) y v *
    (Real.sqrt ((coshDist x y + ε) ^ 2 - 1))⁻¹ = _
  rw [mvfderiv_add hc mdifferentiableAt_const, mvfderiv_const]
  simp only [add_zero, div_eq_mul_inv]

private theorem abs_div_sqrt_le_sqrt {a b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c)
    (ha : a ^ 2 ≤ b * c) : |a / Real.sqrt b| ≤ Real.sqrt c := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg b)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hb)).2
  have hs : (Real.sqrt c * Real.sqrt b) ^ 2 = b * c := by
    rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hb.le]
    ring
  nlinarith [sq_abs a, abs_nonneg a,
    mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg b)]

private theorem abs_mvfderiv_distancePotential_le (x y : Hyperboloid E) {ε : ℝ}
    (hε : 0 < ε) (v : TangentSpace 𝓘(ℝ, E) y) :
    |mvfderiv 𝓘(ℝ, E) (distancePotential x ε) y v| ≤
      Real.sqrt (riemannianMetric.inner y v v) := by
  have hC := one_le_coshDist x y
  have hpos : 0 < (coshDist x y + ε) ^ 2 - 1 := by
    nlinarith [sq_nonneg (coshDist x y + ε - 1)]
  have hmul : coshDist x y ^ 2 - 1 ≤ (coshDist x y + ε) ^ 2 - 1 := by
    have hprod : 0 ≤ coshDist x y * ε := mul_nonneg (by linarith) hε.le
    nlinarith [sq_nonneg ε]
  rw [mvfderiv_distancePotential x y hε]
  exact abs_div_sqrt_le_sqrt hpos (metric_inner_self_nonneg riemannianMetric y v)
    ((mvfderiv_coshDist_sq_le x y v).trans
      (mul_le_mul_of_nonneg_right hmul (metric_inner_self_nonneg riemannianMetric y v)))

private theorem edist_distancePotential_le (x y : Hyperboloid E) {ε : ℝ} (hε : 0 < ε) :
    edist (distancePotential x ε x) (distancePotential x ε y) ≤
      riemannianEDistOf (I := 𝓘(ℝ, E)) riemannianMetric x y := by
  have h := Geometry.edist_map_le_of_metric_mfderiv_bound riemannianMetric
    (C := 1) (by norm_num) (contMDiff_distancePotential x hε) (fun z v => ?_) x y
  · simpa only [ENNReal.coe_one, one_mul] using h
  · change |mvfderiv 𝓘(ℝ, E) (distancePotential x ε) z v| ≤
      (1 : ℝ) * Real.sqrt (riemannianMetric.inner z v v)
    simpa only [one_mul] using abs_mvfderiv_distancePotential_le x z hε v

private theorem tendsto_distancePotential (x y : Hyperboloid E) :
    Filter.Tendsto (fun ε : ℝ => distancePotential x ε y)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist x y)) := by
  have hid : Filter.Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have harg : Filter.Tendsto (fun ε : ℝ => coshDist x y + ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (coshDist x y)) := by
    simpa only [add_zero] using hid.const_add (coshDist x y)
  have hmem : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), coshDist x y + ε ∈ Set.Ici 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 1 ≤ coshDist x y + ε
    have hp : 0 < ε := hε
    linarith [one_le_coshDist x y]
  have harcosh : Filter.Tendsto Real.arcosh
      (𝓝[Set.Ici 1] (coshDist x y)) (𝓝 (Real.arcosh (coshDist x y))) :=
    Real.continuousOn_arcosh (coshDist x y) (one_le_coshDist x y)
  have h := harcosh.comp (tendsto_nhdsWithin_iff.mpr ⟨harg, hmem⟩)
  change Filter.Tendsto (fun ε : ℝ => distancePotential x ε y)
    (𝓝[>] (0 : ℝ)) (𝓝 (Real.arcosh (coshDist x y))) at h
  have heq : Real.arcosh (coshDist x y) = dist x y := Real.arcosh_cosh dist_nonneg
  rwa [heq] at h

private theorem edist_le_riemannianEDistOf (x y : Hyperboloid E) :
    edist x y ≤ riemannianEDistOf (I := 𝓘(ℝ, E)) riemannianMetric x y := by
  have hlim : Filter.Tendsto
      (fun ε : ℝ => edist (distancePotential x ε x) (distancePotential x ε y))
      (𝓝[>] (0 : ℝ)) (𝓝 (edist x y)) := by
    have h := (tendsto_distancePotential x x).edist (tendsto_distancePotential x y)
    simpa only [dist_self, edist_dist, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (dist_nonneg : 0 ≤ dist x y)] using h
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact edist_distancePotential_le x y hε

private theorem riemannianEDistOf_le_edist (x y : Hyperboloid E) :
    riemannianEDistOf (I := 𝓘(ℝ, E)) riemannianMetric x y ≤ edist x y := by
  by_cases hxy : x = y
  · subst y
    simp only [riemannianEDistOf_self, edist_self, le_refl]
  obtain ⟨v, hv, ho, he⟩ := exists_geodesicLine_through hxy
  have hspeed : ∀ t ∈ Set.Ioo (0 : ℝ) (dist x y),
      Real.sqrt (riemannianMetric.inner (geodesicLine x v hv ho t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t 1)) ≤ 1 := by
    intro t _ht
    have h := geodesicLine_unit_speed x v hv ho t
    change riemannianMetric.inner (geodesicLine x v hv ho t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t 1)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicLine x v hv ho) t 1) = 1 at h
    rw [h, Real.sqrt_one]
  have h := Geometry.riemannianEDistOf_le_of_curve_speed_bound riemannianMetric
    dist_nonneg (contMDiff_geodesicLine (n := 1) x v hv ho).contMDiffOn hspeed
  simpa only [geodesicLine_zero, he, ENNReal.ofReal_one, sub_zero, one_mul, edist_dist] using h

theorem riemannianEDistOf_eq_edist (x y : Hyperboloid E) :
    riemannianEDistOf (I := 𝓘(ℝ, E)) riemannianMetric x y = edist x y :=
  le_antisymm (riemannianEDistOf_le_edist x y) (edist_le_riemannianEDistOf x y)

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.Hyperboloid

open scoped Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetric_complete :
    RiemannianMetricComplete (I := 𝓘(ℝ, E)) (riemannianMetric (E := E)) := by
  let m₀ : EMetricSpace (Hyperboloid E) := inferInstance
  have h₀ : @CompleteSpace (Hyperboloid E) m₀.toUniformSpace := inferInstance
  constructor
  let _ : IsManifold 𝓘(ℝ, E) 1 (Hyperboloid E) :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := Hyperboloid E) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (Hyperboloid E) :=
    Manifold.metrizableSpace 𝓘(ℝ, E) (Hyperboloid E)
  let _ : T3Space (Hyperboloid E) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(riemannianMetric (E := E)).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨⟨riemannianMetric.inner, riemannianMetric.contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  have heq : EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) (Hyperboloid E) = m₀ := by
    apply EMetricSpace.ext
    ext x y
    exact riemannianEDistOf_eq_edist x y
  change @CompleteSpace (Hyperboloid E)
    (EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) (Hyperboloid E)).toUniformSpace
  rw [heq]
  exact h₀

end DifferentialGeometry.Hyperboloid
