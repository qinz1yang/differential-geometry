import DifferentialGeometry.Geometry.Comparison.DistanceCutoff
import DifferentialGeometry.Analysis.Calculus.Manifold.LipschitzApproximation

noncomputable section

open Bundle Manifold Filter Set DifferentialGeometry
open scoped Manifold ContDiff Topology NNReal ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cutoff_clamp_mfderiv_bound
    (g : SmoothRiemannianMetric I M) {h : M → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    {B : ℝ}
    (hb : ∀ x (v : TangentSpace I x),
      |(show ℝ from mfderiv I 𝓘(ℝ) h x v)| ≤ B * Real.sqrt (g.inner x v v))
    (x : M) (v : TangentSpace I x) :
    |(show ℝ from mfderiv I 𝓘(ℝ) (fun y => Analysis.CutoffProfile.value (5 / 2 - 2 * h y)) x v)| ≤
      2 * Analysis.CutoffProfile.derivBound * B * Real.sqrt (g.inner x v v) := by
  let φ : ℝ → ℝ := fun s => Analysis.CutoffProfile.value (5 / 2 - 2 * s)
  have hφ (s : ℝ) : HasDerivAt φ
      (deriv Analysis.CutoffProfile.value (5 / 2 - 2 * s) * (-2)) s := by
    have hlin : HasDerivAt (fun y : ℝ => 5 / 2 - 2 * y) (-2) s := by
      convert (hasDerivAt_const s (5 / 2)).sub ((hasDerivAt_id s).const_mul 2) using 1 <;> first | rfl | norm_num
    exact ((Analysis.CutoffProfile.contDiff.differentiable (by simp) _).hasDerivAt).comp s hlin
  have hchain := mfderiv_comp x (hφ (h x)).hasFDerivAt.hasMFDerivAt.mdifferentiableAt
    (hh.mdifferentiable (by simp) x)
  have heq : (show ℝ from mfderiv I 𝓘(ℝ) (fun y => Analysis.CutoffProfile.value (5 / 2 - 2 * h y)) x v) =
      (deriv Analysis.CutoffProfile.value (5 / 2 - 2 * h x) * (-2)) *
        (show ℝ from mfderiv I 𝓘(ℝ) h x v) := by
    change (show ℝ from mfderiv I 𝓘(ℝ) (φ ∘ h) x v) = _
    rw [hchain, mfderiv_eq_fderiv, (hφ (h x)).hasFDerivAt.fderiv]
    change (show ℝ from mfderiv I 𝓘(ℝ) h x v) *
      (deriv Analysis.CutoffProfile.value (5 / 2 - 2 * h x) * (-2)) = _
    exact mul_comm _ _
  rw [heq, abs_mul, abs_mul]
  have hd := Analysis.CutoffProfile.abs_deriv_le_derivBound (5 / 2 - 2 * h x)
  calc
    _ ≤ (Analysis.CutoffProfile.derivBound * |(-2 : ℝ)|) *
        (B * Real.sqrt (g.inner x v v)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hd (abs_nonneg _)) (hb x v)
        (abs_nonneg _) (mul_nonneg Analysis.CutoffProfile.derivBound_nonneg (abs_nonneg _))
    _ = _ := by norm_num; ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_distance_cutoff
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g) (o : M) :
    ∃ C : ℝ≥0, ∀ a : ℝ≥0, 0 < a → ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc 0 1) ∧
      (∀ x, (a : ℝ≥0∞) * riemannianEDistOf g o x ≤ 1 → χ x = 1) ∧
      (∀ x, 2 ≤ (a : ℝ≥0∞) * riemannianEDistOf g o x → χ x = 0) ∧
      ∀ x (v : TangentSpace I x),
        |(show ℝ from mfderiv I 𝓘(ℝ) χ x v)| ≤ C * a * Real.sqrt (g.inner x v v) := by
  let D : ℝ≥0 := ⟨Analysis.CutoffProfile.derivBound, Analysis.CutoffProfile.derivBound_nonneg⟩
  refine ⟨2 * D * (D + 1), fun a ha => ?_⟩
  let f : M → ℝ := fun x => Analysis.CutoffProfile.evalue
    ((a : ℝ≥0∞) * riemannianEDistOf g o x)
  have hfc : HasCompactSupport f := hasCompactSupport_distance_cutoff g hg o ha
  have hf : ∀ x y, edist (f x) (f y) ≤ ((D * a : ℝ≥0) : ℝ≥0∞) * riemannianEDistOf g x y := by
    let : LocallyCompactSpace M := _root_.Manifold.locallyCompact_of_finiteDimensional (M := M) I
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    exact Analysis.CutoffProfile.lipschitzWith_edist a o
  let ε : ℝ := min (1 / 4) (a : ℝ)
  have hε : 0 < ε := lt_min (by norm_num) ha
  obtain ⟨h, hh, _, _, herr, hbound⟩ := exists_contMDiff_approximation_of_lipschitz_hasCompactSupport
    g hf hfc isOpen_univ (subset_univ _) hε
  let χ : M → ℝ := fun x => Analysis.CutoffProfile.value (5 / 2 - 2 * h x)
  have hχs : ContMDiff I 𝓘(ℝ) ∞ χ :=
    Analysis.CutoffProfile.contDiff.contMDiff.comp (contMDiff_const.sub (contMDiff_const.mul hh))
  have hχzero (x : M) (hx : f x = 0) : χ x = 0 := by
    have he : h x < 1 / 4 := by
      have := (abs_lt.mp (herr x)).2
      rw [hx, sub_zero] at this
      exact this.trans_le (min_le_left _ _)
    exact Analysis.CutoffProfile.zero_of_two_le (by linarith)
  have hsupp : tsupport χ ⊆ tsupport f :=
    closure_mono (fun x hx hfzero => hx (hχzero x hfzero))
  refine ⟨χ, hχs, hfc.of_isClosed_subset (isClosed_tsupport _) hsupp,
    fun x => Analysis.CutoffProfile.mem_Icc _, ?_, ?_, ?_⟩
  · intro x hx
    have hone : f x = 1 := Analysis.CutoffProfile.evalue_one_of_le hx
    have he : 3 / 4 < h x := by
      have := (abs_lt.mp (herr x)).1
      have hεle : ε ≤ 1 / 4 := min_le_left _ _
      rw [hone] at this
      linarith
    exact Analysis.CutoffProfile.one_of_le_one (by linarith)
  · intro x hx
    exact hχzero x (Analysis.CutoffProfile.evalue_zero_of_ge hx)
  · intro x v
    have hb := cutoff_clamp_mfderiv_bound g hh (B := (D + 1) * a)
      (fun y w => (hbound y w).trans (mul_le_mul_of_nonneg_right
        (by simp only [NNReal.coe_mul]; nlinarith [min_le_right (1 / 4 : ℝ) (a : ℝ)])
        (Real.sqrt_nonneg _))) x v
    change |(show ℝ from mfderiv I 𝓘(ℝ) χ x v)| ≤
      (2 * (D : ℝ) * (D + 1)) * a * Real.sqrt (g.inner x v v)
    convert hb using 1
    change (2 * (D : ℝ) * (D + 1)) * a * Real.sqrt (g.inner x v v) =
      2 * (D : ℝ) * ((D + 1) * a) * Real.sqrt (g.inner x v v)
    ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_distance_cutoff_sequence [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g) (o : M) :
    ∃ C : ℝ≥0, ∃ χ : ℕ → C^∞⟮I, M; ℝ⟯,
      (∀ n, HasCompactSupport (χ n : M → ℝ)) ∧
      (∀ n x, χ n x ∈ Icc 0 1) ∧
      (∀ n x, ((1 / 4 : ℝ≥0∞) ^ n) * riemannianEDistOf g o x ≤ 1 → χ n x = 1) ∧
      (∀ x, ∃ n, χ n x = 1) ∧
      (∀ n x, 2 ≤ ((1 / 4 : ℝ≥0∞) ^ n) * riemannianEDistOf g o x → χ n x = 0) ∧
      ∀ n x (v : TangentSpace I x),
        |(show ℝ from mfderiv I 𝓘(ℝ) (χ n) x v)| ≤
          C * χ (n + 1) x * Real.sqrt (g.inner x v v) := by
  classical
  obtain ⟨C, hC⟩ := exists_contMDiff_distance_cutoff g hg o
  let a : ℕ → ℝ≥0 := fun n => (1 / 4) ^ n
  have ha (n : ℕ) : 0 < a n := pow_pos (by norm_num) _
  choose χ hχs hχc hχrange hχone hχzero hχbound using fun n => hC (a n) (ha n)
  have hacoe (n : ℕ) : (a n : ℝ≥0∞) = (1 / 4 : ℝ≥0∞) ^ n := by
    simp [a, ENNReal.inv_pow]
  have hale (n : ℕ) : (a n : ℝ) ≤ 1 := by
    change (1 / 4 : ℝ) ^ n ≤ 1
    exact pow_le_one₀ (by positivity) (by norm_num)
  refine ⟨C, fun n => ⟨χ n, hχs n⟩, hχc, hχrange, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    exact hχone n x (by rwa [hacoe])
  · intro x
    have ht : Tendsto (fun n => (a n : ℝ) * (riemannianEDistOf g o x).toReal)
        atTop (𝓝 0) := by
      have hp : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa only [a, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, zero_mul]
        using hp.mul_const (riemannianEDistOf g o x).toReal
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
    refine ⟨n, hχone n x ?_⟩
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (riemannianEDistOf_ne_top g o x)) ENNReal.one_ne_top).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] using hn.le
  · intro n x hx
    exact hχzero n x (by rwa [hacoe])
  · intro n x v
    by_cases hx : χ (n + 1) x = 1
    · change |(show ℝ from mfderiv I 𝓘(ℝ) (χ n) x v)| ≤ C * χ (n + 1) x * _
      rw [hx, mul_one]
      exact (hχbound n x v).trans (mul_le_mul_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hale n) C.coe_nonneg)
        (Real.sqrt_nonneg _))
    · have hnext : 1 < (a (n + 1) : ℝ≥0∞) * riemannianEDistOf g o x :=
        lt_of_not_ge (fun h => hx (hχone (n + 1) x h))
      have heq : 4 * (a (n + 1) : ℝ≥0∞) = (a n : ℝ≥0∞) := by
        simp only [hacoe, pow_succ, one_div]
        rw [mul_left_comm, ENNReal.mul_inv_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0)
          (by norm_num), mul_one]
      have hlarge : 2 < (a n : ℝ≥0∞) * riemannianEDistOf g o x := by
        calc
          (2 : ℝ≥0∞) < 4 := by norm_num
          _ = 4 * 1 := (mul_one _).symm
          _ ≤ 4 * ((a (n + 1) : ℝ≥0∞) * riemannianEDistOf g o x) :=
            mul_le_mul_right hnext.le _
          _ = _ := by rw [← mul_assoc, heq]
      have hdist : Continuous (fun y => (a n : ℝ≥0∞) * riemannianEDistOf g o y) :=
        (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (continuous_riemannianEDist g o)
      have hzero : χ n =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hdist.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hlarge)] with y hy
        exact hχzero n y hy.le
      have hd : mfderiv I 𝓘(ℝ) (χ n) x = 0 := by
        rw [hzero.mfderiv_eq, mfderiv_const]
        rfl
      change |(show ℝ from mfderiv I 𝓘(ℝ) (χ n) x v)| ≤ _
      rw [hd]
      change |(0 : ℝ)| ≤ C * χ (n + 1) x * _
      rw [abs_zero]
      exact mul_nonneg (mul_nonneg C.coe_nonneg (hχrange (n + 1) x).1) (Real.sqrt_nonneg _)

end DifferentialGeometry.Geometry.Riemannian
