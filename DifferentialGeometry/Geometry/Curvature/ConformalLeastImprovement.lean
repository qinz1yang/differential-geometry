import DifferentialGeometry.Geometry.Curvature.ConformalRoundCylinderComparison
import DifferentialGeometry.Geometry.Curvature.ConformalOperatorIncrement
import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.ScaledLowSpectralCluster
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Curvature

private theorem exponential_bounds {F : ℝ} (hF : F ≤ 0) (hFsmall : |F| ≤ 1 / 10000) :
    1 ≤ Real.exp (-2 * F) ∧ Real.exp (-2 * F) ≤ 2 ∧
      Real.exp (-2 * F) - 1 ≤ 4 * |F| := by
  have ht : 1 ≤ Real.exp (-2 * F) := Real.one_le_exp_iff.mpr (by linarith)
  have hx : |-2 * F| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have he := Real.abs_exp_sub_one_le hx
  rw [abs_of_nonneg (sub_nonneg.mpr ht), abs_mul] at he
  norm_num at he
  simp only [neg_mul] at ht ⊢
  exact ⟨ht, by linarith, by linarith⟩

private theorem rounding_numeric_bounds {F p D ε s : ℝ}
    (hF : F ≤ 0) (hFsmall : |F| ≤ 1 / 10000)
    (hFrel : |F| ≤ D / 10000)
    (hp : 0 ≤ p) (hpsmall : p ≤ 1 / 10000) (hprel : p ≤ D / 10000)
    (hD : 0 ≤ D) (hDsmall : D ≤ 1 / 10000)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 100000000) (hs : 1 / 2 ≤ s) :
    let t := Real.exp (-2 * F)
    1 ≤ t ∧
      t * 7207 * ε + |t - 1| + 2 * t * (4 * D + 96 * ε * p + 2 * p ^ 2) ≤ 1 / 8 ∧
      D / 2 ≤ 2 * t * D * s * (1 - 2 * (1 / 8 : ℝ)) -
        2 * t * (96 * ε * p + 2 * p ^ 2) - (t - 1) * (7207 * ε) := by
  dsimp only
  obtain ⟨ht, ht2, htdiff⟩ := exponential_bounds hF hFsmall
  let t := Real.exp (-2 * F)
  change 1 ≤ t at ht
  change t ≤ 2 at ht2
  change t - 1 ≤ 4 * |F| at htdiff
  change 1 ≤ t ∧ _ ∧ _
  have ht0 : 0 ≤ t := by linarith
  have hεhalf : ε ≤ 1 / 2 := by linarith
  have hεη : ε ≤ 1 / 10000 := by linarith
  have hp2 : p ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := by nlinarith
  have hεp : ε * p ≤ (1 / 2 : ℝ) * (1 / 10000) :=
    (mul_le_mul_of_nonneg_right hεhalf hp).trans
      (mul_le_mul_of_nonneg_left hpsmall (by norm_num))
  have hC0 : 0 ≤ 4 * D + 96 * ε * p + 2 * p ^ 2 := by positivity
  have hC : 4 * D + 96 * ε * p + 2 * p ^ 2 ≤ 52 / 10000 + 2 / 100000000 := by
    nlinarith
  have hCt := mul_le_mul_of_nonneg_right ht2 hC0
  have hte := mul_le_mul_of_nonneg_right ht2 hε
  have hclose : t * 7207 * ε + |t - 1| +
      2 * t * (4 * D + 96 * ε * p + 2 * p ^ 2) ≤ 1 / 8 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    nlinarith only [hCt, hC, hte, hεsmall, htdiff, hFsmall]
  have hpp : p ^ 2 ≤ D / 100000000 := by
    have hh := mul_le_mul hpsmall hprel hp (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    nlinarith only [hh]
  have heprel : ε * p ≤ D / 100000000 := by
    have hh := mul_le_mul hεη hprel hp (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    nlinarith only [hh]
  have hrem0 : 0 ≤ 96 * ε * p + 2 * p ^ 2 := by positivity
  have hrem := mul_le_mul_of_nonneg_right ht2 hrem0
  have hremD : 2 * t * (96 * ε * p + 2 * p ^ 2) ≤ D / 100 := by
    nlinarith only [hrem, heprel, hpp, hD]
  have hdelta : 7207 * ε ≤ 1 := by linarith
  have hpen := mul_le_mul_of_nonneg_left hdelta (sub_nonneg.mpr ht)
  have hpenD : (t - 1) * (7207 * ε) ≤ D / 100 := by
    nlinarith only [hpen, htdiff, hFrel, hD]
  have hts : 1 / 2 ≤ t * s := by
    have hh := mul_le_mul_of_nonneg_left hs ht0
    nlinarith only [hh, ht]
  have hmain := mul_le_mul_of_nonneg_right hts hD
  exact ⟨ht, hclose, by nlinarith only [hmain, hremD, hpenD, hD]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem restricted_height_smooth (U : TopologicalSpace.Opens (Cyl (E := E))) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun y : U => (y : Cyl (E := E)).2) :=
  contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U))

private theorem restricted_height_geometry (U : TopologicalSpace.Opens (Cyl (E := E))) (x : U) :
    let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
    let u := fun y : U => (y : Cyl (E := E)).2
    g.inner x (gradFun g u x) (gradFun g u x) = 1 ∧
      ∀ v w : TangentSpace IC x, hessFun g u x v w = 0 := by
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  constructor
  · have h := gradFun_restrictOpen (roundCylinderMetric (E := E) (n := 2))
      U Prod.snd x mdifferentiableAt_snd
    rw [mfderiv_subtype_val_apply] at h
    have haxis := gradFun_height_eq_cylinderAxis gS (x : Cyl (E := E))
    have hgrad : gradFun ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        (fun y : U => (y : Cyl (E := E)).2) x =
        cylinderAxis (I := 𝓡 2) (x : Cyl (E := E)) := h.trans haxis
    change (roundCylinderMetric (E := E) (n := 2)).inner (x : Cyl (E := E)) _ _ = 1
    erw [hgrad]
    exact cylinderMetric_axis_unit gS (x : Cyl (E := E))
  · intro v w
    apply (hessFun_restrictOpen_of_contMDiff (roundCylinderMetric (E := E) (n := 2))
      U Prod.snd contMDiff_snd x v w).trans
    have h := hessFun_comp_height_cylinderMetric gS (f := id) contDiff_id (x : Cyl (E := E))
      (mfderiv IC IC (Subtype.val : U → Cyl (E := E)) x v)
      (mfderiv IC IC (Subtype.val : U → Cyl (E := E)) x w)
    rw [deriv_id', deriv_const] at h
    simpa only [id_eq, roundCylinderMetric, gS, zero_mul] using! h

theorem least_curvature_conformal_improvement_of_roundCylinder_metric_jets
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 100000000)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf0 : f (x : Cyl (E := E)).2 ≤ 0)
    (hfsmall : |f (x : Cyl (E := E)).2| ≤ 1 / 10000)
    (hfrel : |f (x : Cyl (E := E)).2| ≤ -deriv (deriv f) (x : Cyl (E := E)).2 / 10000)
    (hp0 : 0 ≤ deriv f (x : Cyl (E := E)).2)
    (hpsmall : deriv f (x : Cyl (E := E)).2 ≤ 1 / 10000)
    (hprel : deriv f (x : Cyl (E := E)).2 ≤ -deriv (deriv f) (x : Cyl (E := E)).2 / 10000)
    (hdsmall : -deriv (deriv f) (x : Cyl (E := E)).2 ≤ 1 / 10000) :
    let h' := conformalMetricOfContDiff h (fun y : U => f (y : Cyl (E := E)).2)
      (hf.contMDiff.comp (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := U))))
    2 * leastCurvatureOperatorEigenvalueAt h x (metricAlgebraicCurvatureTensorAt h x) +
        (-deriv (deriv f) (x : Cyl (E := E)).2) / 2 ≤
      2 * leastCurvatureOperatorEigenvalueAt h' x (metricAlgebraicCurvatureTensorAt h' x) := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let u := fun y : U => (y : Cyl (E := E)).2
  let F := fun y : U => f (u y)
  let hF : ContMDiff IC 𝓘(ℝ) ∞ F := hf.contMDiff.comp (restricted_height_smooth U)
  let h' := conformalMetricOfContDiff h F hF
  let p := deriv f (u x)
  let D := -deriv (deriv f) (u x)
  let t := Real.exp (-(2 * f (u x)))
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hhalf : ε ≤ 1 / 2 := hε.trans (by norm_num)
  have hD : 0 ≤ D := by change 0 ≤ -deriv (deriv f) (x : Cyl (E := E)).2; linarith
  let B : Module.Basis (Fin 3) ℝ (TangentSpace IC x) :=
    (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis h x).choose.reindex (finCongr (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3
      simp))
  have hB : OrthonormalBasisAt h x B := by
    intro i j
    unfold B
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply,
      (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis h x).choose_spec]
    simp only [Equiv.apply_eq_iff_eq, delta3]
  let B' := conformalBasisAt F x B
  have hB' : OrthonormalBasisAt h' x B' := conformalBasisAt_orthonormal h F hF x B hB
  let q := bivectorDifferentialAt u x B
  let v := NormedSpace.normalize q
  let s := ‖q‖ ^ 2
  let Aop := traceNormalizedCurvatureOperatorAt h x B
  let Bop := traceNormalizedCurvatureOperatorAt h' x B'
  let Q := InnerProductSpace.rankOne ℝ v v
  have hunit := (restricted_height_geometry U x).1
  have hparallel := (restricted_height_geometry U x).2
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using (hsmall 0 (by norm_num)).trans hhalf)
  have hl := inner_gradFun_le_of_metricUniformEquivalentOn h g
    (metricUniformEquivalentOn_symm heq) u (Set.mem_singleton x)
  have hq := norm_sq_bivectorDifferentialAt h u x B hB
  rw [hunit, ← hq] at hl
  have hs : 1 / 2 ≤ s := by change 1 / 2 ≤ ‖bivectorDifferentialAt u x B‖ ^ 2; linarith
  have hn := rounding_numeric_bounds hf0 hfsmall hfrel hp0 hpsmall hprel hD hdsmall hε0 hε hs
  simp only [neg_mul] at hn
  change 1 ≤ t ∧
    t * 7207 * ε + |t - 1| + 2 * t * (4 * D + 96 * ε * p + 2 * p ^ 2) ≤ 1 / 8 ∧
    D / 2 ≤ 2 * t * D * s * (1 - 2 * (1 / 8 : ℝ)) -
      2 * t * (96 * ε * p + 2 * p ^ 2) - (t - 1) * (7207 * ε) at hn
  obtain ⟨hv, hOld⟩ := normalized_height_rankOne_approx_of_roundCylinder_metric_jets
    U h x ε hhalf hsmall B hB
  change ‖v‖ = 1 at hv
  change ‖Aop - Q‖ ≤ 7207 * ε at hOld
  have hNew := norm_conformal_roundCylinder_operator_sub_height_rankOne_le
    U h x ε hhalf hsmall B hB f hf
  change ‖Bop - Q‖ ≤ t * 7207 * ε + |t - 1| +
    2 * t * (4 * |deriv (deriv f) (u x)| + 96 * ε * |p| + 2 * p ^ 2) at hNew
  have hpabs : |p| = p := abs_of_nonneg hp0
  have hdabs : |deriv (deriv f) (u x)| = D := abs_of_nonpos (neg_nonneg.mp hD)
  rw [hdabs, hpabs] at hNew
  have hNewNorm : ‖Bop - Q‖ ≤ 1 / 8 := hNew.trans hn.2.1
  have hcloseA (c : E3) : ‖(Aop - Q) c‖ ≤ (7207 * ε) * ‖c‖ :=
    ((Aop - Q).le_opNorm c).trans (mul_le_mul_of_nonneg_right hOld (norm_nonneg c))
  have hcloseB (c : E3) : ‖(Bop - Q) c‖ ≤ (1 / 8 : ℝ) * ‖c‖ :=
    ((Bop - Q).le_opNorm c).trans (mul_le_mul_of_nonneg_right hNewNorm (norm_nonneg c))
  have hinc (c : E3) :
      2 * t * D * s * (‖c‖ ^ 2 - ⟪v, c⟫_ℝ ^ 2) -
        2 * t * (96 * ε * p + 2 * p ^ 2) * ‖c‖ ^ 2 ≤ ⟪(Bop - t • Aop) c, c⟫_ℝ := by
    have hh := traceNormalizedCurvatureOperatorAt_comp_increment_lower
      g h u (restricted_height_smooth U) f hf x ε hhalf
      (fun k hk => hsmall k (hk.trans (by norm_num))) hunit hparallel B hB c
    change 2 * t * D * s * (‖c‖ ^ 2 - ⟪v, c⟫_ℝ ^ 2) -
      2 * t * (96 * ε * |p| + 2 * p ^ 2) * ‖c‖ ^ 2 ≤
        ⟪Bop c, c⟫_ℝ - t * ⟪Aop c, c⟫_ℝ at hh
    rw [hpabs] at hh
    simpa only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] using hh
  have hgain := iInf_rayleigh_ge_scaled_relative_low_cluster Aop Bop
    (traceNormalizedCurvatureOperatorAt_isSelfAdjoint h x B)
    (traceNormalizedCurvatureOperatorAt_isSelfAdjoint h' x B') hv hcloseA hcloseB hn.1
    (show 0 ≤ 2 * t * D * s by dsimp only [t, s]; positivity) hinc
  have hfinal : (⨅ c : {c : E3 // c ≠ 0}, Aop.rayleighQuotient c) + D / 2 ≤
      (⨅ c : {c : E3 // c ≠ 0}, Bop.rayleighQuotient c) := by linarith [hn.2.2]
  rw [iInf_rayleigh_traceNormalizedCurvatureOperatorAt h x B hB,
    iInf_rayleigh_traceNormalizedCurvatureOperatorAt h' x B' hB'] at hfinal
  exact hfinal

end DifferentialGeometry.Geometry.Curvature
