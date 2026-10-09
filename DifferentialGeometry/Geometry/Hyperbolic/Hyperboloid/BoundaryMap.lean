import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.QuasiGeodesicBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinCompactification
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def originRay (u : Metric.sphere (0 : E) 1) (t : ℝ) : Hyperboloid E :=
  ofSpace (Real.sinh t • (u : E))

private theorem originRay_eq_geodesicLine (u : Metric.sphere (0 : E) 1) (t : ℝ) :
    originRay u t = geodesicLine origin (0, (u : E))
      (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
        ← dist_zero_right, Metric.mem_sphere.mp u.property, one_pow])
      (by simp [lorentzForm_apply]) t := by
  apply ext
  simp only [originRay, space_ofSpace, geodesicLine_space, origin_space, smul_zero, zero_add]

private theorem originRay_zero (u : Metric.sphere (0 : E) 1) : originRay u 0 = origin := by
  simp [originRay, origin]

private theorem originRay_isometry (u : Metric.sphere (0 : E) 1) : Isometry (originRay u) := by
  rw [funext (originRay_eq_geodesicLine u)]
  exact isometry_geodesicLine _ _ _ _

private theorem continuous_originRay (t : ℝ) :
    Continuous (fun u : Metric.sphere (0 : E) 1 => originRay u t) :=
  continuous_ofSpace.comp (continuous_const.smul continuous_subtype_val)

private theorem kleinHomeomorph_originRay (u : Metric.sphere (0 : E) 1) (t : ℝ) :
    (kleinHomeomorph (originRay u t) : E) = Real.tanh t • (u : E) := by
  rw [originRay_eq_geodesicLine, kleinHomeomorph_geodesicLine]
  simp only [origin_time, origin_space, mul_zero, add_zero, zero_add, inv_one, one_smul]

private theorem originRay_time (u : Metric.sphere (0 : E) 1) (t : ℝ) :
    (originRay u t).time = Real.cosh t := by
  rw [originRay_eq_geodesicLine, geodesicLine_time]
  simp only [origin_time, mul_one, mul_zero, add_zero]

private theorem tendsto_kleinHomeomorph_originRay (u : Metric.sphere (0 : E) 1) :
    Filter.Tendsto (fun t => (kleinHomeomorph (originRay u t) : E)) Filter.atTop (𝓝 (u : E)) := by
  rw [funext (originRay_eq_geodesicLine u)]
  simpa only [origin_time, origin_space, add_zero, zero_add, inv_one, one_smul] using
    tendsto_kleinHomeomorph_geodesicLine_atTop (origin : Hyperboloid E) (0, (u : E))
      (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
        ← dist_zero_right, Metric.mem_sphere.mp u.property, one_pow])
      (by simp [lorentzForm_apply])

private theorem norm_kleinHomeomorph_sub_endpoint_sq_le (x : Hyperboloid E)
    (u : Metric.sphere (0 : E) 1) {K : ℝ}
    (hxu : dist x (originRay u (dist origin x)) ≤ K) :
    ‖(kleinHomeomorph x : E) - (u : E)‖ ^ 2 ≤
      (4 * Real.cosh K + 2) * x.time⁻¹ := by
  let r := dist (origin : Hyperboloid E) x
  have hr : 0 ≤ r := dist_nonneg
  have hu : ‖(u : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have htime : Real.cosh r = x.time := cosh_dist_origin x
  have htimeone : 1 ≤ x.time := by rw [← htime]; exact Real.one_le_cosh r
  have hinv0 : 0 ≤ x.time⁻¹ := inv_nonneg.mpr x.time_pos.le
  have hinv1 : x.time⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) htimeone
  have hinvsq : x.time⁻¹ ^ 2 ≤ x.time⁻¹ := by
    simpa only [mul_one, ← sq] using mul_le_mul_of_nonneg_left hinv1 hinv0
  have htanh0 : 0 ≤ Real.tanh r := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le
  have htanh1 : Real.tanh r ≤ 1 := (Real.tanh_lt_one r).le
  have htanh_sq : (Real.tanh r - 1) ^ 2 ≤ 1 - Real.tanh r ^ 2 := by
    nlinarith only [mul_nonneg htanh0 (sub_nonneg.mpr htanh1)]
  have hidentity : 1 - Real.tanh r ^ 2 = x.time⁻¹ ^ 2 := by
    rw [← htime, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hnorm : ‖(kleinHomeomorph (originRay u r) : E) - (u : E)‖ ^ 2 =
      (Real.tanh r - 1) ^ 2 := by
    rw [kleinHomeomorph_originRay]
    have hv : Real.tanh r • (u : E) - (u : E) = (Real.tanh r - 1) • (u : E) := by
      rw [sub_smul, one_smul]
    rw [hv, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hsecond : ‖(kleinHomeomorph (originRay u r) : E) - (u : E)‖ ^ 2 ≤ x.time⁻¹ := by
    rw [hnorm]
    exact (htanh_sq.trans_eq hidentity).trans hinvsq
  have hfirst := norm_kleinHomeomorph_sub_sq_le x (originRay u r) hxu
  have htri := norm_sub_le_norm_sub_add_norm_sub (kleinHomeomorph x : E)
    (kleinHomeomorph (originRay u r) : E) (u : E)
  have htri2 := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
  have hsquare := sq_nonneg (‖(kleinHomeomorph x : E) - (kleinHomeomorph (originRay u r) : E)‖ -
    ‖(kleinHomeomorph (originRay u r) : E) - (u : E)‖)
  nlinarith only [hfirst, hsecond, htri2, hsquare]

private theorem norm_kleinHomeomorph_sub_endpoint_sq_le_exp (x : Hyperboloid E)
    (u : Metric.sphere (0 : E) 1) {K : ℝ}
    (hxu : dist x (originRay u (dist origin x)) ≤ K) :
    ‖(kleinHomeomorph x : E) - (u : E)‖ ^ 2 ≤
      (8 * Real.cosh K + 4) * Real.exp (-dist origin x) := by
  let r := dist (origin : Hyperboloid E) x
  have htime : Real.cosh r = x.time := cosh_dist_origin x
  have hlow : Real.exp r ≤ 2 * x.time := by
    rw [← htime, Real.cosh_eq]
    linarith [Real.exp_pos (-r)]
  have hinv : x.time⁻¹ ≤ 2 * Real.exp (-r) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos r)).mpr
    have hm := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr x.time_pos.le)
    have hc : x.time⁻¹ * x.time = 1 := inv_mul_cancel₀ x.time_pos.ne'
    nlinarith only [hm, hc]
  calc
    _ ≤ (4 * Real.cosh K + 2) * x.time⁻¹ := norm_kleinHomeomorph_sub_endpoint_sq_le x u hxu
    _ ≤ (4 * Real.cosh K + 2) * (2 * Real.exp (-r)) :=
      mul_le_mul_of_nonneg_left hinv (by linarith [Real.cosh_pos K])
    _ = _ := by ring

private theorem exists_originRay_close_of_quasi_geodesic [FiniteDimensional ℝ E]
    (q : ℝ → Hyperboloid E) {L C : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hq : ContinuousOn q (Set.Ici 0)) (hq0 : q 0 = origin)
    (hquasi : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧ dist (q s) (q t) ≤ L * dist s t + C) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    let B := L ^ 2 * D + (L ^ 2 + 1) * C
    ∃ u : Metric.sphere (0 : E) 1, ∀ t ∈ Set.Ici (0 : ℝ),
      dist (q t) (originRay u (dist origin (q t))) ≤ 2 * (B + 1) := by
  obtain ⟨v, hv, ho, hclose⟩ := exists_geodesicLine_close_of_quasi_geodesic q hL hC hq hquasi
  have hvt : v.1 = 0 := by
    rw [hq0] at ho
    simpa only [lorentzForm_apply, origin_time, origin_space, inner_zero_left,
      one_mul, zero_sub, neg_eq_zero] using ho
  have hvnorm : ‖v.2‖ = 1 := by
    have hvv := hv
    rw [lorentzForm_apply, hvt, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hvv
    nlinarith [norm_nonneg v.2]
  let u : Metric.sphere (0 : E) 1 := ⟨v.2, by simpa only [Metric.mem_sphere, dist_zero_right] using hvnorm⟩
  refine ⟨u, ?_⟩
  intro t ht
  have heq : geodesicLine (q 0) v hv ho (dist (q 0) (q t)) = originRay u (dist origin (q t)) := by
    apply ext
    simp only [originRay, geodesicLine_space, hq0, origin_space, smul_zero, zero_add, space_ofSpace]
    rfl
  simpa only [heq] using hclose t ht

theorem norm_kleinHomeomorph_sub_limit_sq_le [FiniteDimensional ℝ E]
    (q : ℝ → Hyperboloid E) {L C : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hq : ContinuousOn q (Set.Ici 0)) (hq0 : q 0 = origin)
    (hquasi : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧ dist (q s) (q t) ≤ L * dist s t + C)
    (u : Metric.sphere (0 : E) 1)
    (hu : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (u : E)))
    (t : ℝ) (ht : 0 ≤ t) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    let B := L ^ 2 * D + (L ^ 2 + 1) * C
    ‖(kleinHomeomorph (q t) : E) - (u : E)‖ ^ 2 ≤
      (8 * Real.cosh (2 * (B + 1)) + 4) * Real.exp (C - t / L) := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  let K := 2 * (B + 1)
  obtain ⟨v, hv⟩ := exists_originRay_close_of_quasi_geodesic q hL hC hq hq0 hquasi
  change ∀ s ∈ Set.Ici (0 : ℝ), dist (q s) (originRay v (dist origin (q s))) ≤ K at hv
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hradial (s : ℝ) (hs : 0 ≤ s) : s / L - C ≤ dist origin (q s) := by
    have h := (hquasi 0 (by change (0 : ℝ) ≤ 0; exact le_rfl) s hs).1
    rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hs] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hr : Filter.Tendsto (fun s => dist (origin : Hyperboloid E) (q s))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop (max 0 (L * (b + C)))] with s hs
    have hs0 : 0 ≤ s := (le_max_left _ _).trans hs
    have hsb : L * (b + C) ≤ s := (le_max_right _ _).trans hs
    have hb : b + C ≤ s / L := (le_div_iff₀ hLpos).mpr (by simpa only [mul_comm] using hsb)
    linarith [hradial s hs0]
  have hvlimit : Filter.Tendsto (fun s => (kleinHomeomorph (q s) : E)) Filter.atTop (𝓝 (v : E)) := by
    apply tendsto_kleinHomeomorph_of_dist_bounded
      (x := fun s => originRay v (dist origin (q s))) (C := K)
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
      simpa only [dist_comm] using hv s hs
    · exact (tendsto_kleinHomeomorph_originRay v).comp hr
  have huv : u = v := Subtype.ext (tendsto_nhds_unique hu hvlimit)
  subst u
  change ‖(kleinHomeomorph (q t) : E) - (v : E)‖ ^ 2 ≤
    (8 * Real.cosh K + 4) * Real.exp (C - t / L)
  refine (norm_kleinHomeomorph_sub_endpoint_sq_le_exp (q t) v (hv t ht)).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith [Real.cosh_pos K])
  linarith only [hradial t ht]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem exists_endpoint (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (u : Metric.sphere (0 : E) 1) :
    ∃! v : Metric.sphere (0 : F) 1,
      Filter.Tendsto (fun t => (kleinHomeomorph (f (originRay u t)) : F))
        Filter.atTop (𝓝 (v : F)) := by
  obtain ⟨L, C, hL, hC, hdist⟩ := hf
  apply exists_unique_tendsto_kleinHomeomorph_of_quasi_geodesic
    (fun t => f (originRay u t)) hL hC
    (f.continuous.comp (originRay_isometry u).continuous).continuousOn
  intro s hs t ht
  simpa only [(originRay_isometry u).dist_eq] using hdist (originRay u s) (originRay u t)

private def endpoint (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (u : Metric.sphere (0 : E) 1) : Metric.sphere (0 : F) 1 :=
  (exists_endpoint f hf u).exists.choose

private theorem tendsto_endpoint (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (u : Metric.sphere (0 : E) 1) :
    Filter.Tendsto (fun t => (kleinHomeomorph (f (originRay u t)) : F))
      Filter.atTop (𝓝 (endpoint f hf u : F)) :=
  (exists_endpoint f hf u).exists.choose_spec

private theorem tendsto_visual_error (L C K : ℝ) (hL : 0 < L) :
    Filter.Tendsto (fun t : ℝ => (8 * Real.cosh K + 4) * Real.exp (C - t / L))
      Filter.atTop (𝓝 0) := by
  have hr : Filter.Tendsto (fun t : ℝ => t / L - C) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop (L * (b + C))] with t ht
    have hh : b + C ≤ t / L := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using ht)
    linarith
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hr
  have hh := h.const_mul (8 * Real.cosh K + 4)
  simpa only [Function.comp_def, neg_sub, mul_zero] using hh

private theorem continuous_endpoint_of_origin_fixed (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hf0 : f origin = origin) : Continuous (endpoint f hf) := by
  obtain ⟨L, C, hL, hC, hdist⟩ := hf
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  let K := 2 * (B + 1)
  let A (t : ℝ) (u : Metric.sphere (0 : E) 1) := (kleinHomeomorph (f (originRay u t)) : F)
  have hA (t : ℝ) : Continuous (A t) :=
    continuous_subtype_val.comp (kleinHomeomorph.continuous.comp
      (f.continuous.comp (continuous_originRay t)))
  have hbound (t : ℝ) (ht : 0 ≤ t) (u : Metric.sphere (0 : E) 1) :
      ‖A t u - (endpoint f ⟨L, C, hL, hC, hdist⟩ u : F)‖ ^ 2 ≤
        (8 * Real.cosh K + 4) * Real.exp (C - t / L) := by
    apply norm_kleinHomeomorph_sub_limit_sq_le (fun s => f (originRay u s)) hL hC
      (f.continuous.comp (originRay_isometry u).continuous).continuousOn
      (by rw [originRay_zero, hf0]) _ _ (tendsto_endpoint f ⟨L, C, hL, hC, hdist⟩ u) t ht
    intro s hs v hv
    simpa only [(originRay_isometry u).dist_eq] using hdist (originRay u s) (originRay u v)
  have huniform : TendstoUniformly A
      (fun u => (endpoint f ⟨L, C, hL, hC, hdist⟩ u : F)) Filter.atTop := by
    apply (Metric.uniformity_basis_dist.tendstoUniformly_iff_of_uniformity).mpr
    intro ε hε
    have hevent := (tendsto_visual_error L C K (lt_of_lt_of_le zero_lt_one hL)).eventually
      (gt_mem_nhds (sq_pos_of_pos hε))
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ), hevent] with t ht herr
    intro u
    rw [dist_comm, dist_eq_norm]
    have hsq := (hbound t ht u).trans_lt herr
    nlinarith [norm_nonneg (A t u - (endpoint f ⟨L, C, hL, hC, hdist⟩ u : F))]
  have hcontinuous := huniform.continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hA))
  exact hcontinuous.subtype_mk _

private theorem continuous_endpoint (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C) :
    Continuous (endpoint f hf) := by
  let g := boost (f origin)
  let f' : C(Hyperboloid E, Hyperboloid F) := (g.symm : C(Hyperboloid F, Hyperboloid F)).comp f
  have hf' : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f' x) (f' y) ∧ dist (f' x) (f' y) ≤ L * dist x y + C := by
    obtain ⟨L, C, hL, hC, hd⟩ := hf
    refine ⟨L, C, hL, hC, ?_⟩
    intro x y
    simpa only [f', ContinuousMap.comp_apply, ContinuousMap.coe_apply, g.symm.dist_eq] using hd x y
  have hf0 : f' origin = origin := by
    change (boost (f origin)).symm (f origin) = origin
    simpa only [boost_origin] using (boost (f origin)).symm_apply_apply (origin : Hyperboloid F)
  have heq : endpoint f hf = boundaryHomeomorph g ∘ endpoint f' hf' := by
    funext u
    apply Subtype.ext
    apply tendsto_nhds_unique (tendsto_endpoint f hf u)
    have h := tendsto_kleinHomeomorph_isometry g (tendsto_endpoint f' hf' u)
    simpa only [f', ContinuousMap.comp_apply, ContinuousMap.coe_apply, g.apply_symm_apply,
      Function.comp_apply] using h
  rw [heq]
  exact (boundaryHomeomorph g).continuous.comp (continuous_endpoint_of_origin_fixed f' hf' hf0)

def boundaryMap (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) where
  toFun := endpoint f hf
  continuous_toFun := continuous_endpoint f hf

theorem tendsto_kleinHomeomorph_boundaryMap_origin_ray
    (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (u : E) (hu : ‖u‖ = 1) :
    Filter.Tendsto
      (fun t : ℝ => (kleinHomeomorph (f (geodesicLine origin (0, u)
        (by simp [lorentzForm_apply, hu]) (by simp [lorentzForm_apply]) t)) : F))
      Filter.atTop
      (𝓝 (boundaryMap f hf ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩ : F)) := by
  let ξ : Metric.sphere (0 : E) 1 :=
    ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩
  have h := tendsto_endpoint f hf ξ
  simpa only [originRay_eq_geodesicLine, ξ, boundaryMap, ContinuousMap.coe_mk] using h

omit [FiniteDimensional ℝ F] in
private theorem tendsto_radial_of_kleinHomeomorph {α : Type*} {l : Filter α}
    {x : α → Hyperboloid E} {u : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (u : E))) :
    Filter.Tendsto (fun i => dist (origin : Hyperboloid E) (x i)) l Filter.atTop := by
  have hu : ‖(u : E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hid (z : Hyperboloid E) : z.time⁻¹ ^ 2 = 1 - ‖(kleinHomeomorph z : E)‖ ^ 2 := by
    rw [kleinHomeomorph_apply_coe, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr z.time_pos)]
    field_simp [z.time_pos.ne']
    nlinarith [z.time_sq]
  have hinvsq : Filter.Tendsto (fun i => (x i).time⁻¹ ^ 2) l (𝓝 0) := by
    simpa only [hid, hu, one_pow, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hx.norm.pow 2)
  have hinv : Filter.Tendsto (fun i => (x i).time⁻¹) l (𝓝 0) := by
    simpa only [Real.sqrt_sq (inv_nonneg.mpr (time_pos _).le), Real.sqrt_zero] using hinvsq.sqrt
  apply Filter.tendsto_atTop.2
  intro b
  let m := max b 0
  have hm : 0 ≤ m := le_max_right _ _
  have hevent := hinv.eventually (gt_mem_nhds (inv_pos.mpr (Real.cosh_pos m)))
  filter_upwards [hevent] with i hi
  have htime : Real.cosh m < (x i).time := by
    by_contra hnot
    have hh := one_div_le_one_div_of_le (x i).time_pos (le_of_not_gt hnot)
    have hh' : (x i).time⁻¹ ≥ (Real.cosh m)⁻¹ := by simpa only [one_div] using hh
    linarith
  rw [← cosh_dist_origin] at htime
  have hr : m < dist origin (x i) := by
    have hh := Real.cosh_lt_cosh.mp htime
    simpa only [abs_of_nonneg hm, abs_of_nonneg dist_nonneg] using hh
  exact (le_max_left _ _).trans hr.le

omit [FiniteDimensional ℝ F] in
private theorem tendsto_direction_of_kleinHomeomorph {α : Type*} {l : Filter α}
    {x : α → Hyperboloid E} {u : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (u : E))) :
    Filter.Tendsto (fun i => NormedSpace.normalize (x i).space) l (𝓝 (u : E)) := by
  have hu : ‖(u : E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hnorm := hx.norm
  have hnormalize := (hnorm.inv₀ (by rw [hu]; exact one_ne_zero)).smul hx
  have hn (z : Hyperboloid E) : NormedSpace.normalize (kleinHomeomorph z : E) =
      NormedSpace.normalize z.space := by
    rw [kleinHomeomorph_apply_coe]
    exact NormedSpace.normalize_smul_of_pos (inv_pos.mpr z.time_pos) z.space
  have hn' (z : Hyperboloid E) :
      ‖(kleinHomeomorph z : E)‖⁻¹ • (kleinHomeomorph z : E) = NormedSpace.normalize z.space := hn z
  simpa only [hn', hu, inv_one, one_smul] using hnormalize

private theorem tendsto_endpoint_of_origin_fixed (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hf0 : f origin = origin) {α : Type*} {l : Filter α} {x : α → Hyperboloid E}
    {u : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (u : E))) :
    Filter.Tendsto (fun i => (kleinHomeomorph (f (x i)) : F)) l (𝓝 (endpoint f hf u : F)) := by
  classical
  obtain ⟨L, C, hL, hC, hd⟩ := hf
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  let K := 2 * (B + 1)
  let r (i : α) := dist (origin : Hyperboloid E) (x i)
  let v (i : α) : Metric.sphere (0 : E) 1 :=
    if h : (x i).space = 0 then u else
      ⟨NormedSpace.normalize (x i).space, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize h⟩
  have hr : Filter.Tendsto r l Filter.atTop := tendsto_radial_of_kleinHomeomorph hx
  have hnonzero : ∀ᶠ i in l, (x i).space ≠ 0 := by
    have hevent := hr.eventually (Filter.eventually_gt_atTop (0 : ℝ))
    filter_upwards [hevent] with i hi hzero
    have hx0 : x i = origin := by apply ext; exact hzero
    change 0 < dist origin (x i) at hi
    rw [hx0, dist_self] at hi
    exact (lt_irrefl 0) hi
  have hv : Filter.Tendsto v l (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    apply (tendsto_direction_of_kleinHomeomorph hx).congr'
    filter_upwards [hnonzero] with i hi
    simp only [v, dite_eq_right hi]
  have hray (i : α) (hi : (x i).space ≠ 0) : originRay (v i) (r i) = x i := by
    apply ext
    simp only [originRay, space_ofSpace, v, dite_eq_right hi, r, sinh_dist_origin]
    exact NormedSpace.norm_smul_normalize (x i).space
  have herr : ∀ᶠ i in l,
      ‖(kleinHomeomorph (f (x i)) : F) - (endpoint f ⟨L, C, hL, hC, hd⟩ (v i) : F)‖ ^ 2 ≤
        (8 * Real.cosh K + 4) * Real.exp (C - r i / L) := by
    filter_upwards [hnonzero] with i hi
    have hb := norm_kleinHomeomorph_sub_limit_sq_le (fun t => f (originRay (v i) t)) hL hC
      (f.continuous.comp (originRay_isometry (v i)).continuous).continuousOn
      (by rw [originRay_zero, hf0]) (fun s hs t ht => by
        simpa only [(originRay_isometry (v i)).dist_eq] using hd (originRay (v i) s) (originRay (v i) t))
      (endpoint f ⟨L, C, hL, hC, hd⟩ (v i)) (tendsto_endpoint f ⟨L, C, hL, hC, hd⟩ (v i))
      (r i) dist_nonneg
    simpa only [hray i hi] using hb
  have herror0 := (tendsto_visual_error L C K (lt_of_lt_of_le zero_lt_one hL)).comp hr
  have hsquare : Filter.Tendsto
      (fun i => ‖(kleinHomeomorph (f (x i)) : F) - (endpoint f ⟨L, C, hL, hC, hd⟩ (v i) : F)‖ ^ 2)
      l (𝓝 0) := squeeze_zero' (Filter.Eventually.of_forall fun i => sq_nonneg _) herr herror0
  have hsub : Filter.Tendsto
      (fun i => (kleinHomeomorph (f (x i)) : F) - (endpoint f ⟨L, C, hL, hC, hd⟩ (v i) : F))
      l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsquare.sqrt
  have hep := ((continuous_subtype_val.comp
    (continuous_endpoint_of_origin_fixed f ⟨L, C, hL, hC, hd⟩ hf0)).tendsto u).comp hv
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hsub.add hep

theorem tendsto_kleinHomeomorph_boundaryMap
    (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    {α : Type*} {l : Filter α} {x : α → Hyperboloid E}
    {u : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (u : E))) :
    Filter.Tendsto (fun i => (kleinHomeomorph (f (x i)) : F)) l
      (𝓝 (boundaryMap f hf u : F)) := by
  let g := boost (f origin)
  let f' : C(Hyperboloid E, Hyperboloid F) := (g.symm : C(Hyperboloid F, Hyperboloid F)).comp f
  have hf' : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f' x) (f' y) ∧ dist (f' x) (f' y) ≤ L * dist x y + C := by
    obtain ⟨L, C, hL, hC, hd⟩ := hf
    refine ⟨L, C, hL, hC, ?_⟩
    intro z w
    simpa only [f', ContinuousMap.comp_apply, ContinuousMap.coe_apply, g.symm.dist_eq] using hd z w
  have hf0 : f' origin = origin := by
    change (boost (f origin)).symm (f origin) = origin
    simpa only [boost_origin] using (boost (f origin)).symm_apply_apply (origin : Hyperboloid F)
  have heq : endpoint f hf u = boundaryHomeomorph g (endpoint f' hf' u) := by
    apply Subtype.ext
    apply tendsto_nhds_unique (tendsto_endpoint f hf u)
    have h := tendsto_kleinHomeomorph_isometry g (tendsto_endpoint f' hf' u)
    simpa only [f', ContinuousMap.comp_apply, ContinuousMap.coe_apply, g.apply_symm_apply] using h
  have h := tendsto_kleinHomeomorph_isometry g (tendsto_endpoint_of_origin_fixed f' hf' hf0 hx)
  simpa only [f', ContinuousMap.comp_apply, ContinuousMap.coe_apply, g.apply_symm_apply,
    ← heq, boundaryMap, ContinuousMap.coe_mk] using h

@[simp]
theorem boundaryMap_isometryEquiv (e : Hyperboloid E ≃ᵢ Hyperboloid F) :
    boundaryMap (e : C(Hyperboloid E, Hyperboloid F))
      (by
        refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
        intro x y
        simp only [ContinuousMap.coe_apply, e.dist_eq, inv_one, one_mul, sub_zero, add_zero,
          le_refl, and_self]) =
      (boundaryHomeomorph e : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1)) := by
  have hd : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (e x) (e y) ∧ dist (e x) (e y) ≤ L * dist x y + C := by
    refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    intro x y
    simp only [e.dist_eq, inv_one, one_mul, sub_zero, add_zero, le_refl, and_self]
  change boundaryMap (e : C(Hyperboloid E, Hyperboloid F)) hd = _
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  have hleft : Filter.Tendsto
      (fun t => (kleinHomeomorph (e (originRay u t)) : F)) Filter.atTop
      (𝓝 (boundaryMap (e : C(Hyperboloid E, Hyperboloid F)) hd u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap (e : C(Hyperboloid E, Hyperboloid F)) hd
      (x := originRay u) (u := u) (tendsto_kleinHomeomorph_originRay u)
  have hright : Filter.Tendsto
      (fun t => (kleinHomeomorph (e (originRay u t)) : F)) Filter.atTop
      (𝓝 (boundaryHomeomorph e u : F)) :=
    tendsto_kleinHomeomorph_isometry e (tendsto_kleinHomeomorph_originRay u)
  exact tendsto_nhds_unique hleft hright

variable {G K : Type*} [Group G] [Group K]
  [MulAction G (Hyperboloid E)] [IsIsometricSMul G (Hyperboloid E)]
  [MulAction K (Hyperboloid F)] [IsIsometricSMul K (Hyperboloid F)]

theorem boundaryMap_smul (f : C(Hyperboloid E, Hyperboloid F))
    (hdist : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (φ : G → K) (hf : ∀ γ x, f (γ • x) = φ γ • f x)
    (γ : G) (u : Metric.sphere (0 : E) 1) :
    boundaryMap f hdist (boundaryHomeomorph (IsometryEquiv.constSMul γ) u) =
      boundaryHomeomorph (IsometryEquiv.constSMul (φ γ)) (boundaryMap f hdist u) := by
  let a : Hyperboloid E ≃ᵢ Hyperboloid E := IsometryEquiv.constSMul γ
  let b : Hyperboloid F ≃ᵢ Hyperboloid F := IsometryEquiv.constSMul (φ γ)
  have ha : Filter.Tendsto (fun t => (kleinHomeomorph (a (originRay u t)) : E))
      Filter.atTop (𝓝 (boundaryHomeomorph a u : E)) :=
    tendsto_kleinHomeomorph_isometry a (tendsto_kleinHomeomorph_originRay u)
  have hleft : Filter.Tendsto (fun t => (kleinHomeomorph (f (a (originRay u t))) : F))
      Filter.atTop (𝓝 (boundaryMap f hdist (boundaryHomeomorph a u) : F)) :=
    tendsto_kleinHomeomorph_boundaryMap f hdist ha
  have hfu : Filter.Tendsto (fun t => (kleinHomeomorph (f (originRay u t)) : F))
      Filter.atTop (𝓝 (boundaryMap f hdist u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap f hdist (tendsto_kleinHomeomorph_originRay u)
  have hright : Filter.Tendsto (fun t => (kleinHomeomorph (b (f (originRay u t))) : F))
      Filter.atTop (𝓝 (boundaryHomeomorph b (boundaryMap f hdist u) : F)) :=
    tendsto_kleinHomeomorph_isometry b hfu
  have heq (t : ℝ) : f (a (originRay u t)) = b (f (originRay u t)) := hf γ (originRay u t)
  apply Subtype.ext
  exact tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall fun t =>
    congrArg (fun z : Hyperboloid F => (kleinHomeomorph z : F)) (heq t).symm))

theorem boundaryMap_comp_constSMul (f : C(Hyperboloid E, Hyperboloid F))
    (hdist : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (φ : G → K) (hf : ∀ γ x, f (γ • x) = φ γ • f x) (γ : G) :
    (boundaryMap f hdist).comp
      (boundaryHomeomorph (IsometryEquiv.constSMul γ : Hyperboloid E ≃ᵢ Hyperboloid E) :
        C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1)) =
      (boundaryHomeomorph (IsometryEquiv.constSMul (φ γ) : Hyperboloid F ≃ᵢ Hyperboloid F) :
        C(Metric.sphere (0 : F) 1, Metric.sphere (0 : F) 1)).comp (boundaryMap f hdist) := by
  apply ContinuousMap.ext
  intro u
  exact boundaryMap_smul f hdist φ hf γ u

omit [FiniteDimensional ℝ F] in
private theorem exists_distortion_comp {T : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    (f : C(Hyperboloid E, Hyperboloid F)) (g : C(Hyperboloid F, Hyperboloid T))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid F,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist ((g.comp f) x) ((g.comp f) y) ∧
        dist ((g.comp f) x) ((g.comp f) y) ≤ L * dist x y + C := by
  obtain ⟨L₁, C₁, hL₁, hC₁, hd₁⟩ := hf
  obtain ⟨L₂, C₂, hL₂, hC₂, hd₂⟩ := hg
  have hL₂pos : 0 < L₂ := lt_of_lt_of_le zero_lt_one hL₂
  have hinv : L₂⁻¹ ≤ L₂ := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL₂
    have hh' : L₂⁻¹ ≤ 1 := by simpa only [one_div, inv_one] using hh
    exact hh'.trans hL₂
  have herror : L₂⁻¹ * C₁ ≤ L₂ * C₁ := mul_le_mul_of_nonneg_right hinv hC₁
  refine ⟨L₂ * L₁, L₂ * C₁ + C₂, ?_, ?_, ?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hL₁) (sub_nonneg.mpr hL₂), hL₁, hL₂]
  · exact add_nonneg (mul_nonneg hL₂pos.le hC₁) hC₂
  · intro x y
    obtain ⟨hfxyl, hfxyu⟩ := hd₁ x y
    obtain ⟨hgxyl, hgxyu⟩ := hd₂ (f x) (f y)
    change (L₂ * L₁)⁻¹ * dist x y - (L₂ * C₁ + C₂) ≤ dist (g (f x)) (g (f y)) ∧
      dist (g (f x)) (g (f y)) ≤ L₂ * L₁ * dist x y + (L₂ * C₁ + C₂)
    constructor
    · have hm := mul_le_mul_of_nonneg_left hfxyl (inv_nonneg.mpr hL₂pos.le)
      calc
        _ = L₂⁻¹ * (L₁⁻¹ * dist x y) - L₂ * C₁ - C₂ := by rw [mul_inv_rev]; ring
        _ ≤ L₂⁻¹ * (L₁⁻¹ * dist x y) - L₂⁻¹ * C₁ - C₂ := by linarith only [herror]
        _ = L₂⁻¹ * (L₁⁻¹ * dist x y - C₁) - C₂ := by ring
        _ ≤ dist (g (f x)) (g (f y)) := by linarith only [hm, hgxyl]
    · have hm := mul_le_mul_of_nonneg_left hfxyu hL₂pos.le
      nlinarith only [hm, hgxyu]

theorem boundaryMap_comp {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T]
    (f : C(Hyperboloid E, Hyperboloid F)) (g : C(Hyperboloid F, Hyperboloid T))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid F,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C) :
    boundaryMap (g.comp f) (exists_distortion_comp f g hf hg) =
      (boundaryMap g hg).comp (boundaryMap f hf) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  have hfu : Filter.Tendsto (fun t => (kleinHomeomorph (f (originRay u t)) : F))
      Filter.atTop (𝓝 (boundaryMap f hf u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap f hf (tendsto_kleinHomeomorph_originRay u)
  have hright : Filter.Tendsto (fun t => (kleinHomeomorph (g (f (originRay u t))) : T))
      Filter.atTop (𝓝 (boundaryMap g hg (boundaryMap f hf u) : T)) :=
    tendsto_kleinHomeomorph_boundaryMap g hg hfu
  have hleft : Filter.Tendsto (fun t => (kleinHomeomorph ((g.comp f) (originRay u t)) : T))
      Filter.atTop (𝓝 (boundaryMap (g.comp f) (exists_distortion_comp f g hf hg) u : T)) :=
    tendsto_kleinHomeomorph_boundaryMap (g.comp f) (exists_distortion_comp f g hf hg)
      (tendsto_kleinHomeomorph_originRay u)
  exact tendsto_nhds_unique hleft hright

theorem boundaryMap_eq_of_dist_bounded (f g : C(Hyperboloid E, Hyperboloid F))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
    (hfg : ∃ C : ℝ, ∀ x : Hyperboloid E, dist (f x) (g x) ≤ C) :
    boundaryMap f hf = boundaryMap g hg := by
  obtain ⟨C, hC⟩ := hfg
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  have hfu : Filter.Tendsto (fun t => (kleinHomeomorph (f (originRay u t)) : F))
      Filter.atTop (𝓝 (boundaryMap f hf u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap f hf (tendsto_kleinHomeomorph_originRay u)
  have hgu : Filter.Tendsto (fun t => (kleinHomeomorph (g (originRay u t)) : F))
      Filter.atTop (𝓝 (boundaryMap g hg u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap g hg (tendsto_kleinHomeomorph_originRay u)
  have hclose : Filter.Tendsto (fun t => (kleinHomeomorph (g (originRay u t)) : F))
      Filter.atTop (𝓝 (boundaryMap f hf u : F)) :=
    tendsto_kleinHomeomorph_of_dist_bounded
      (x := fun t => f (originRay u t)) (y := fun t => g (originRay u t))
      (ξ := boundaryMap f hf u) (C := C)
      (Filter.Eventually.of_forall fun t => hC (originRay u t)) hfu
  exact tendsto_nhds_unique hclose hgu

end DifferentialGeometry.Hyperboloid
