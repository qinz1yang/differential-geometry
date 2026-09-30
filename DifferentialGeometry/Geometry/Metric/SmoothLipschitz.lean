import DifferentialGeometry.Geometry.Metric.CompactDerivative
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.LocalChartDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff



noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_radius_slack {B r rho a : ℝ} (hB : 0 ≤ B)
    (hrho : r < rho) (ha : B * r < a) :
    ∃ s : ℝ, r < s ∧ s < rho ∧ B * s ≤ a := by
  have hB1 : 0 < B + 1 := by linarith
  have hgap : 0 < (a - B * r) / (B + 1) := div_pos (by linarith) hB1
  obtain ⟨s, hrs, hs⟩ := exists_between
    (lt_min hrho (lt_add_of_pos_right r hgap))
  refine ⟨s, hrs, hs.trans_le (min_le_left _ _), ?_⟩
  have hdist : s - r < (a - B * r) / (B + 1) := by
    have hh := hs.trans_le (min_le_right _ _)
    linarith
  have hmul := (lt_div_iff₀ hB1).mp hdist
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_lintegral_of_metric_mfderiv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {f : M → F} {γ : ℝ → M} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (hf : ∀ t ∈ Icc a b, ContMDiffAt I 𝓘(ℝ, F) 1 f (γ t))
    (hbound : ∀ t ∈ Ioo a b, ∀ v : TangentSpace I (γ t),
      ‖(mfderiv I 𝓘(ℝ, F) f (γ t) v : F)‖ ≤ L * Real.sqrt (g.inner (γ t) v v)) :
    edist (f (γ a)) (f (γ b)) ≤ ENNReal.ofReal L *
      ∫⁻ t in Ioo a b, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)))) := by
  have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, F) 1 (f ∘ γ) (Icc a b) := by
    intro t ht
    exact (hf t ht).comp_contMDiffWithinAt t (hγ t ht)
  have hη : ContDiffOn ℝ 1 (f ∘ γ) (Icc a b) := contMDiffOn_iff_contDiffOn.mp hcomp
  have hh := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hη hab
  rw [← edist_eq_enorm_sub, edist_comm] at hh
  apply hh.trans
  rw [← restrict_Ioo_eq_restrict_Icc]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hγt := (hγ t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hD := mfderiv_comp t ((hf t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt one_ne_zero)
    (hγt.mdifferentiableAt one_ne_zero)
  have hder : deriv (f ∘ γ) t =
      (mfderiv I 𝓘(ℝ, F) f (γ t)) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) := by
    rw [mfderiv_eq_fderiv] at hD
    have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (γ t))
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)))) hD
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv] using! hv
  rw [hder]
  have hb := ENNReal.ofReal_le_ofReal
    (hbound t ht (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)))
  simpa only [ofReal_norm, ENNReal.ofReal_mul hL] using hb

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem edist_comp_le_metric_path_length_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f U)
    (hbound : ∀ (x : M), x ∈ U → ∀ (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) :
    edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) *
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
  have h := edist_comp_le_lintegral_of_metric_mfderiv_bound g (by norm_num : (0 : ℝ) ≤ 1)
    C.coe_nonneg hγ
    (fun t ht => (hf (γ t) (hγU ht)).contMDiffAt (hU.mem_nhds (hγU ht)))
    (fun t ht => hbound (γ t) (hγU ⟨ht.1.le, ht.2.le⟩))
  rw [restrict_Ioo_eq_restrict_Icc, ENNReal.ofReal_coe_nnreal] at h
  exact h


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_metric_path_length
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) *
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
  exact edist_comp_le_metric_path_length_of_contMDiffOn g isOpen_univ hf.contMDiffOn
    (fun z _ v => hbound z v) hγ (mapsTo_univ γ _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_map_le_of_metric_mfderiv_bound
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0} (hC : 0 < C)
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v)) (x y : M) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  change edist (f x) (f y) ≤ (C : ℝ≥0∞) * Manifold.riemannianEDist I x y
  rw [Manifold.riemannianEDist, ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro hγ
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc, pathELength_eq_lintegral_mfderiv_Icc]
  have hc := edist_comp_le_metric_path_length g hf hbound
    (hγ.comp_contMDiffOn contMDiffOn_projIcc)
  have hn (p : M) (v : TangentSpace I p) :
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp only [Function.comp_apply, projIcc_left, projIcc_right, hn] at hc
  change edist (f (γ 0)) (f (γ 1)) ≤ _ at hc
  simp only [γ.source, γ.target] at hc
  convert! hc using 1

theorem exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (hcompact : HasCompactSupport f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y,
      edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g hf hcompact
  have hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ (B + 1 : ℝ≥0) * Real.sqrt (g.inner x v v) := by
    intro x v
    exact (hB x v).trans
      (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))
  exact ⟨B + 1, by positivity,
    edist_map_le_of_metric_mfderiv_bound g (by positivity) hf hbound⟩

theorem exists_riemannian_lipschitz_of_contMDiff
    [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound g hf
  have hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ (B + 1 : ℝ≥0) * Real.sqrt (g.inner x v v) := by
    intro x v
    exact (hB x v).trans (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))
  exact ⟨B + 1, by positivity, edist_map_le_of_metric_mfderiv_bound g (by positivity) hf hbound⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem norm_sub_le_mul_of_mfderiv_bound_on_ball
    (g : SmoothRiemannianMetric I M) {f : M → F} (x : M) {ρ B r : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f {z | riemannianEDistOf g x z < ENNReal.ofReal ρ})
    (hB : 0 ≤ B)
    (hbound : ∀ z, riemannianEDistOf g x z < ENNReal.ofReal ρ →
      ∀ v : TangentSpace I z,
        ‖(mfderiv I 𝓘(ℝ, F) f z v : F)‖ ≤ B * Real.sqrt (g.inner z v v))
    (hr : 0 ≤ r) (hrρ : r < ρ) {y : M}
    (hy : riemannianEDistOf g x y ≤ ENNReal.ofReal r) :
    ‖f y - f x‖ ≤ B * r := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hopen : IsOpen {z | riemannianEDistOf g x z < ENNReal.ofReal ρ} := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨δ, hδ, hzδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hz
    have hlocal := eventually_riemannianEDist_lt I z
      (c := (δ : ℝ≥0∞)) (by exact_mod_cast hδ)
    filter_upwards [hlocal] with w hw
    exact (riemannianEDistOf_triangle g x z w).trans_lt
      ((add_le_add_right hw.le _).trans_lt hzδ)
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  obtain ⟨s, hrs, hsρ, hBsa⟩ := exists_radius_slack hB hrρ ha
  have hs : 0 < s := hr.trans_lt hrs
  have hsmall : riemannianEDist I x y < ENNReal.ofReal s :=
    hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hrs)
  obtain ⟨γ, hγx, hγy, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hsmall
  have hmaps : MapsTo γ (Icc 0 1)
      {z | riemannianEDistOf g x z < ENNReal.ofReal ρ} := by
    apply Metric.mapsTo_of_riemannianEDistOf_add_pathELength_lt g x _
      (ENNReal.ofReal ρ) (fun _ hz => hz) γ hγ
    rw [hγx, riemannianEDistOf_self, zero_add]
    exact hlen.trans ((ENNReal.ofReal_lt_ofReal_iff (hs.trans hsρ)).mpr hsρ)
  let C : ℝ≥0 := ⟨B, hB⟩
  have hpath := edist_comp_le_metric_path_length_of_contMDiffOn g
    (C := C) hopen hf hbound hγ hmaps
  have hn (z : M) (v : TangentSpace I z) :
      ENNReal.ofReal (Real.sqrt (g.inner z v v)) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp only [hγx, hγy, hn] at hpath
  rw [← pathELength_eq_lintegral_mfderiv_Icc] at hpath
  have hle := hpath.trans (mul_le_mul_right hlen.le (C : ℝ≥0∞))
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal B := by
    rw [ENNReal.ofReal_eq_coe_nnreal hB]
    rfl
  rw [hC, ← ENNReal.ofReal_mul hB, edist_comm, edist_eq_enorm_sub, ← ofReal_norm] at hle
  exact ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hs.le)).mp hle).trans hBsa

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem abs_sub_le_mul_of_mfderiv_bound_on_ball
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (x : M) {ρ B r : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z, riemannianEDistOf g x z < ENNReal.ofReal ρ →
      ∀ v : TangentSpace I z,
        |(show ℝ from mfderiv I 𝓘(ℝ) f z v)| ≤ B * Real.sqrt (g.inner z v v))
    (hr : 0 ≤ r) (hrρ : r < ρ) {y : M}
    (hy : riemannianEDistOf g x y ≤ ENNReal.ofReal r) :
    |f y - f x| ≤ B * r := by
  exact norm_sub_le_mul_of_mfderiv_bound_on_ball g x hf.contMDiffOn hB hbound hr hrρ hy

end DifferentialGeometry.Geometry
