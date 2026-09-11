import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.Rellich
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Intrinsic.EquivalenceReverse
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Banach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma eLpNorm_smoothScalarDirichlet_le_norm
    {g : SmoothRiemannianMetric (I_half n) M} (s : SmoothScalarDirichlet g) :
    eLpNorm s.toFun 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≤
      ENNReal.ofReal ‖s‖ := by
  have h_norm_le : ‖smoothToLpDirichlet g s‖ ≤ ‖s‖ := s.norm_smoothToLp_le
  have h_lp_norm_def :
      ‖smoothToLpDirichlet g s‖ =
        (eLpNorm s.toFun 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) g)).toReal := by
    unfold smoothToLpDirichlet
    rw [smoothToLpInterior_apply, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp s.memLp_two)
  have h_finite : eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≠ ⊤ :=
    s.memLp_two.eLpNorm_ne_top
  have h_real : (eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g)).toReal ≤ ‖s‖ := by
    rw [← h_lp_norm_def]
    exact h_norm_le
  rw [show eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) =
      ENNReal.ofReal (eLpNorm s.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g)).toReal from
    (ENNReal.ofReal_toReal h_finite).symm]
  exact ENNReal.ofReal_le_ofReal h_real

lemma sqrt_g_inner_grad_smoothScalarDirichlet_memLp_two
    {g : SmoothRiemannianMetric (I_half n) M} (s : SmoothScalarDirichlet g) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)))
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  have h_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x))) :=
    Real.continuous_sqrt.comp
      (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
        (M := M) g s.smooth s.smooth)
  exact h_cont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem eLpNorm_sqrt_g_inner_grad_smoothScalarDirichlet_le_norm
    {g : SmoothRiemannianMetric (I_half n) M} (s : SmoothScalarDirichlet g) :
    eLpNorm (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)))
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≤
        ENNReal.ofReal ‖s‖ := by
  set f : M → ℝ := fun x : M => Real.sqrt
    (g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)) with hf_def
  have hf_memLp : MemLp f 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    sqrt_g_inner_grad_smoothScalarDirichlet_memLp_two s
  set Fp : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    hf_memLp.toLp f with hFp_def
  have h_norm_sq : ‖Fp‖ ^ 2 = ∫ x, f x * f x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    have h := real_inner_self_eq_norm_sq Fp
    rw [L2.inner_def (𝕜 := ℝ)] at h
    have hae : (fun x : M =>
        @inner ℝ _ _ ((Fp : Lp ℝ 2 _) x) ((Fp : Lp ℝ 2 _) x)) =ᵐ[
          riemannianVolumeMeasure (I := I_half n) (M := M) g]
        (fun x : M => f x * f x) := by
      filter_upwards [MemLp.coeFn_toLp hf_memLp] with x hx
      rw [hx]
      rfl
    rw [integral_congr_ae hae] at h
    exact h.symm
  have h_f_sq : ∀ x : M, f x * f x =
      g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x) := by
    intro x
    have h_nonneg : 0 ≤ g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x) :=
      SmoothRiemannianMetric_inner_self_nonneg g x _
    rw [hf_def, show Real.sqrt _ * Real.sqrt _ = (Real.sqrt _) ^ 2 from (sq _).symm]
    exact Real.sq_sqrt h_nonneg
  rw [show (fun x : M => f x * f x) = fun x => g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x) from
    funext h_f_sq] at h_norm_sq
  have h_decomp : ‖s‖ ^ 2 =
      (∫ x, s.toFun x * s.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
    rw [s.norm_sq_eq_inner_self]
    rfl
  have h_grad_le : (∫ x, g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_half n) g s.toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) ≤ ‖s‖ ^ 2 := by
    linarith [s.integral_mul_self_nonneg]
  have h_Fp_norm_le : ‖Fp‖ ≤ ‖s‖ := by
    have h_sq : ‖Fp‖ ^ 2 ≤ ‖s‖ ^ 2 := by
      rw [h_norm_sq]
      exact h_grad_le
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg _)).2
  have h_lp_norm_def : ‖Fp‖ =
      (eLpNorm f 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g)).toReal := by
    rw [hFp_def, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp hf_memLp)
  have h_finite : eLpNorm f 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≠ ⊤ :=
    hf_memLp.eLpNorm_ne_top
  rw [show eLpNorm f 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) =
      ENNReal.ofReal (eLpNorm f 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) g)).toReal from
    (ENNReal.ofReal_toReal h_finite).symm]
  apply ENNReal.ofReal_le_ofReal
  rw [← h_lp_norm_def]
  exact h_Fp_norm_le

theorem smoothScalarDirichlet_memWkpChart
    {g : SmoothRiemannianMetric (I_half n) M} (s : SmoothScalarDirichlet g) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart
      (n := n) (M := M) 1 (2 : ℝ≥0∞) s.toFun := by
  apply DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_of_contMDiff_AllChartsInteriorSupport
    (n := n) (M := M) (p := (2 : ℝ≥0∞))
  · norm_num
  · exact s.smooth
  · exact DifferentialGeometry.Analysis.Sobolev.WithBoundary.allChartsInteriorSupport_of_tsupport_subset_interior
      (n := n) (M := M) s.interior_support

theorem exists_smoothScalarDirichlet_wkpNormChart_bound
    (g : SmoothRiemannianMetric (I_half n) M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : SmoothScalarDirichlet g,
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
            (n := n) (M := M) 1 2 s.toFun ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖s‖ := by
  obtain ⟨C₀, hC₀_nonneg, hC₀_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (n := n) (M := M) g
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀_nonneg, ?_⟩
  intro s
  have hC := hC₀_bound s.smooth
    (DifferentialGeometry.Analysis.Sobolev.WithBoundary.allChartsInteriorSupport_of_tsupport_subset_interior
      (n := n) (M := M) s.interior_support)
  have hsum :
      eLpNorm s.toFun 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) g) +
        eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Geometry.Operator.gradFun
              (I := I_half n) g s.toFun x)
            (DifferentialGeometry.Geometry.Operator.gradFun
              (I := I_half n) g s.toFun x))) 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≤
      ENNReal.ofReal ‖s‖ + ENNReal.ofReal ‖s‖ :=
    add_le_add (eLpNorm_smoothScalarDirichlet_le_norm s)
      (eLpNorm_sqrt_g_inner_grad_smoothScalarDirichlet_le_norm s)
  have hnorm : ENNReal.ofReal ‖s‖ + ENNReal.ofReal ‖s‖ =
      ENNReal.ofReal (2 * ‖s‖) := by
    rw [← ENNReal.ofReal_add (norm_nonneg s) (norm_nonneg s)]
    congr 1
    ring
  rw [hnorm] at hsum
  calc
    _ ≤ ENNReal.ofReal C₀ *
        (eLpNorm s.toFun 2
            (riemannianVolumeMeasure (I := I_half n) (M := M) g) +
          eLpNorm (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I_half n) g s.toFun x)
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I_half n) g s.toFun x))) 2
            (riemannianVolumeMeasure (I := I_half n) (M := M) g)) := hC
    _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (2 * ‖s‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ENNReal.ofReal (2 * C₀) * ENNReal.ofReal ‖s‖ := by
      rw [← ENNReal.ofReal_mul hC₀_nonneg]
      simp [ENNReal.ofReal_mul, hC₀_nonneg]
      ring

abbrev DirichletChartWkp
    : Type _ :=
  DifferentialGeometry.Analysis.Sobolev.WithBoundary.WkpChart
    (n := n) (M := M) 1 2 (by norm_num)

abbrev H1ComplDirichletChartWkp
    : Type _ :=
  UniformSpace.Completion (DirichletChartWkp (n := n) (M := M))

noncomputable def smoothToDirichletChartWkpLin
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →ₗ[ℝ] DirichletChartWkp (n := n) (M := M) :=
  { toFun := fun s =>
      ⟨s.toFun, smoothScalarDirichlet_memWkpChart (n := n) (M := M) s⟩
    map_add' := by
      intro s t
      apply Subtype.ext
      rfl
    map_smul' := by
      intro c s
      apply Subtype.ext
      rfl }

theorem smoothToDirichletChartWkpLin_norm_le
    (g : SmoothRiemannianMetric (I_half n) M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalarDirichlet g,
      ‖smoothToDirichletChartWkpLin (n := n) (M := M) g s‖ ≤ C * ‖s‖ := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_smoothScalarDirichlet_wkpNormChart_bound (n := n) (M := M) g
  refine ⟨C, hC_nonneg, ?_⟩
  intro s
  have h_bound := hC_bound s
  change (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
      (n := n) (M := M) 1 2 s.toFun).toReal ≤ C * ‖s‖
  have h_rhs_top : ENNReal.ofReal C * ENNReal.ofReal ‖s‖ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h_toReal := ENNReal.toReal_mono h_rhs_top h_bound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg s)] at h_toReal
  simpa [ENNReal.toReal_ofReal hC_nonneg] using h_toReal

noncomputable def smoothToDirichletChartWkp
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ] DirichletChartWkp (n := n) (M := M) := by
  classical
  let h := smoothToDirichletChartWkpLin_norm_le (n := n) (M := M) g
  exact (smoothToDirichletChartWkpLin (n := n) (M := M) g).mkContinuous
    (Classical.choose h) (Classical.choose_spec h).2

noncomputable def smoothToH1ComplDirichletChartWkp
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ]
      H1ComplDirichletChartWkp (n := n) (M := M) :=
  (UniformSpace.Completion.toComplL :
      DirichletChartWkp (n := n) (M := M) →L[ℝ]
        H1ComplDirichletChartWkp (n := n) (M := M)).comp
    (smoothToDirichletChartWkp (n := n) (M := M) g)

private lemma isUniformInducing_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsUniformInducing (smoothToH1ComplDirichlet g) := by
  change IsUniformInducing (UniformSpace.Completion.toComplL :
    SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g)
  rw [show (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g → H1ComplDirichlet g) =
      ((↑) : SmoothScalarDirichlet g →
        UniformSpace.Completion (SmoothScalarDirichlet g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalarDirichlet g)

noncomputable def H1ComplDirichletToChartWkp
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g →L[ℝ]
      H1ComplDirichletChartWkp (n := n) (M := M) :=
  ContinuousLinearMap.extend
    (smoothToH1ComplDirichletChartWkp (n := n) (M := M) g)
    (smoothToH1ComplDirichlet g)

@[simp] theorem H1ComplDirichletToChartWkp_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (s : SmoothScalarDirichlet g) :
    H1ComplDirichletToChartWkp (n := n) (M := M) g
        (smoothToH1ComplDirichlet g s) =
      (smoothToDirichletChartWkp (n := n) (M := M) g s :
        H1ComplDirichletChartWkp (n := n) (M := M)) := by
  unfold H1ComplDirichletToChartWkp
  rw [ContinuousLinearMap.extend_eq
    (smoothToH1ComplDirichletChartWkp (n := n) (M := M) g)
    (e := smoothToH1ComplDirichlet g)
    (denseRange_smoothToH1ComplDirichlet g)
    (isUniformInducing_smoothToH1ComplDirichlet (n := n) (M := M) g) s]
  rfl

private lemma exists_smooth_close_to_H1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (v : H1ComplDirichlet g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : SmoothScalarDirichlet g,
      ‖v - smoothToH1ComplDirichlet g s‖ < δ := by
  have h_dense : DenseRange (smoothToH1ComplDirichlet g) :=
    denseRange_smoothToH1ComplDirichlet g
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall] at h_dense
  have hv_in : v ∈ closure (Set.range (smoothToH1ComplDirichlet g)) := h_dense v
  rw [Metric.mem_closure_iff] at hv_in
  obtain ⟨q, ⟨s, hs_eq⟩, hs_close⟩ := hv_in δ hδ
  refine ⟨s, ?_⟩
  rw [show smoothToH1ComplDirichlet g s = q from hs_eq]
  rwa [dist_eq_norm] at hs_close

theorem norm_H1ComplDirichletToLp_apply_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (v : H1ComplDirichlet g) :
    ‖H1ComplDirichletToLp g v‖ ≤ ‖v‖ := by
  refine UniformSpace.Completion.induction_on
    (α := SmoothScalarDirichlet g) v ?_ ?_
  · exact isClosed_le (H1ComplDirichletToLp g).continuous.norm continuous_norm
  · intro s
    have h_eq : H1ComplDirichletToLp g ((s : H1ComplDirichlet g)) =
        smoothToLpDirichlet g s := by
      change H1ComplDirichletToLp g (smoothToH1ComplDirichlet g s) =
        smoothToLpDirichlet g s
      exact H1ComplDirichletToLp_smoothToH1ComplDirichlet g s
    have h_norm : ‖((s : H1ComplDirichlet g) : H1ComplDirichlet g)‖ = ‖s‖ := by
      exact UniformSpace.Completion.norm_coe s
    rw [h_eq, h_norm]
    exact s.norm_smoothToLp_le

theorem H1ComplDirichletToLp_isCompactOperator
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCompactOperator (H1ComplDirichletToLp g) := by
  classical
  have h_iff := isCompactOperator_iff_isCompact_closure_image_closedBall
    (H1ComplDirichletToLp g : H1ComplDirichlet g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) zero_lt_one
  refine h_iff.mpr ?_
  rw [isCompact_iff_isSeqCompact]
  set T : H1ComplDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    H1ComplDirichletToLp g with hT_def
  intro y hy_in_closure
  have h_choose_z : ∀ k : ℕ,
      ∃ z ∈ T '' Metric.closedBall (0 : H1ComplDirichlet g) 1,
        dist (y k) z < 1 / (k + 1 : ℝ) := by
    intro k
    have h_pos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hy_k := hy_in_closure k
    rw [Metric.mem_closure_iff] at hy_k
    exact hy_k _ h_pos
  choose z hz_mem hz_close using h_choose_z
  have h_choose_x : ∀ k : ℕ,
      ∃ x ∈ Metric.closedBall (0 : H1ComplDirichlet g) 1, T x = z k :=
    fun k => hz_mem k
  choose x hx_mem hx_eq using h_choose_x
  have h_choose_s : ∀ k : ℕ, ∃ s : SmoothScalarDirichlet g,
      ‖x k - smoothToH1ComplDirichlet g s‖ < 1 / (k + 1 : ℝ) := by
    intro k
    exact exists_smooth_close_to_H1ComplDirichlet g (x k) (by positivity)
  choose s hs_close using h_choose_s
  have h_x_norm : ∀ k : ℕ, ‖x k‖ ≤ 1 := by
    intro k
    have hx_k := hx_mem k
    rwa [Metric.mem_closedBall, dist_zero_right] at hx_k
  have h_s_isometric : ∀ k : ℕ,
      ‖smoothToH1ComplDirichlet g (s k)‖ = ‖s k‖ := by
    intro k
    change ‖((s k : H1ComplDirichlet g) : H1ComplDirichlet g)‖ = ‖s k‖
    exact UniformSpace.Completion.norm_coe (s k)
  have h_s_norm_le_two : ∀ k : ℕ, ‖s k‖ ≤ 2 := by
    intro k
    have h_close : ‖x k - smoothToH1ComplDirichlet g (s k)‖ ≤ 1 := by
      have h_inv_le_one : (1 : ℝ) / (k + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.le_add_left 1 k
      exact (hs_close k).le.trans h_inv_le_one
    have h_tri : ‖smoothToH1ComplDirichlet g (s k)‖ ≤
        ‖x k‖ + ‖x k - smoothToH1ComplDirichlet g (s k)‖ := by
      have h_id : smoothToH1ComplDirichlet g (s k) =
          x k - (x k - smoothToH1ComplDirichlet g (s k)) := by abel
      calc
        ‖smoothToH1ComplDirichlet g (s k)‖ =
            ‖x k - (x k - smoothToH1ComplDirichlet g (s k))‖ := congrArg norm h_id
        _ ≤ ‖x k‖ + ‖x k - smoothToH1ComplDirichlet g (s k)‖ :=
          norm_sub_le (x k) (x k - smoothToH1ComplDirichlet g (s k))
    rw [← h_s_isometric k]
    linarith [h_x_norm k]
  obtain ⟨C₀, hC₀_nonneg, hC₀_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (n := n) (M := M) g
  have h_wkp_bound : ∀ k : ℕ,
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
          (n := n) (M := M) 1 2 (s k).toFun ≤
        ENNReal.ofReal (4 * C₀) := by
    intro k
    have h := hC₀_bound (s k).smooth
      (DifferentialGeometry.Analysis.Sobolev.WithBoundary.allChartsInteriorSupport_of_tsupport_subset_interior
        (n := n) (M := M) (s k).interior_support)
    have h_l2 := eLpNorm_smoothScalarDirichlet_le_norm (s k)
    have h_grad := eLpNorm_sqrt_g_inner_grad_smoothScalarDirichlet_le_norm (s k)
    have h_sum_le :
        eLpNorm (s k).toFun 2
            (riemannianVolumeMeasure (I := I_half n) (M := M) g) +
          eLpNorm (fun q : M => Real.sqrt
            (g.inner q
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I_half n) g (s k).toFun q)
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I_half n) g (s k).toFun q))) 2
            (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≤
          ENNReal.ofReal ‖s k‖ + ENNReal.ofReal ‖s k‖ :=
      add_le_add h_l2 h_grad
    have h_norm_sum : ENNReal.ofReal ‖s k‖ + ENNReal.ofReal ‖s k‖ ≤
        ENNReal.ofReal 4 := by
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [h_s_norm_le_two k])
    have h_step :
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
            (n := n) (M := M) 1 2 (s k).toFun ≤
          ENNReal.ofReal C₀ * ENNReal.ofReal 4 := by
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left (h_sum_le.trans h_norm_sum) zero_le
    rw [← ENNReal.ofReal_mul hC₀_nonneg] at h_step
    simpa [mul_comm] using h_step
  obtain ⟨φ, hφ, u_lim, hu_lim, hu_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.rellich_kondrachov_chart_seq_of_tsupport_subset_interior
      (n := n) (M := M) g (fun k => (s k).smooth)
      (fun k => (s k).interior_support) h_wkp_bound
  set L : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    hu_lim.toLp u_lim with hL_def
  have h_smooth_tendsto :
      Tendsto (fun k => smoothToLpDirichlet g (s (φ k))) atTop (𝓝 L) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f := fun k => (s (φ k)).toFun)
      (f_ℒp := fun k => (s (φ k)).memLp_two)
      (f_lim := u_lim) (f_lim_ℒp := hu_lim)).mpr hu_tendsto
    rw [hL_def]
    refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
    unfold smoothToLpDirichlet
    exact smoothToLpInterior_apply g (s (φ k))
  have h_y_tendsto : Tendsto (fun k => y (φ k)) atTop (𝓝 L) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h_vanish : Tendsto
        (fun k : ℕ => (2 : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 2 * 0 by ring]
      exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    have h_dist : Tendsto
        (fun k => dist (smoothToLpDirichlet g (s (φ k))) L) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp h_smooth_tendsto
    have h_upper : Tendsto
        (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) +
          dist (smoothToLpDirichlet g (s (φ k))) L) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 0 + 0 by ring]
      exact h_vanish.add h_dist
    refine squeeze_zero (fun k => dist_nonneg) ?_ h_upper
    intro k
    have h_yz : dist (y (φ k)) (z (φ k)) < 1 / ((φ k : ℝ) + 1) := hz_close (φ k)
    have hT_s_eq : smoothToLpDirichlet g (s (φ k)) =
        T (smoothToH1ComplDirichlet g (s (φ k))) := by
      rw [hT_def]
      exact (H1ComplDirichletToLp_smoothToH1ComplDirichlet g (s (φ k))).symm
    have h_zs_eq : z (φ k) - smoothToLpDirichlet g (s (φ k)) =
        T (x (φ k) - smoothToH1ComplDirichlet g (s (φ k))) := by
      rw [← hx_eq (φ k), hT_s_eq, ← T.map_sub]
    have h_zs_le :
        dist (z (φ k)) (smoothToLpDirichlet g (s (φ k))) ≤
          ‖x (φ k) - smoothToH1ComplDirichlet g (s (φ k))‖ := by
      rw [dist_eq_norm, h_zs_eq, hT_def]
      exact norm_H1ComplDirichletToLp_apply_le g _
    have h_inv_le : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hφ.le_apply 1
    calc
      dist (y (φ k)) L ≤
          dist (y (φ k)) (z (φ k)) + dist (z (φ k)) L := dist_triangle _ _ _
      _ ≤ dist (y (φ k)) (z (φ k)) +
          (dist (z (φ k)) (smoothToLpDirichlet g (s (φ k))) +
            dist (smoothToLpDirichlet g (s (φ k))) L) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ 1 / ((φ k : ℝ) + 1) + 1 / ((φ k : ℝ) + 1) +
          dist (smoothToLpDirichlet g (s (φ k))) L := by
        linarith [h_yz, h_zs_le.trans_lt (hs_close (φ k))]
      _ ≤ 2 * (1 / ((k : ℝ) + 1)) +
          dist (smoothToLpDirichlet g (s (φ k))) L := by
        linarith
  refine ⟨L, ?_, φ, hφ, h_y_tendsto⟩
  exact IsClosed.mem_of_tendsto isClosed_closure h_y_tendsto
    (Filter.Eventually.of_forall fun k => hy_in_closure (φ k))

noncomputable def resolventDirichletL2
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (H1ComplDirichletToLp g).comp (resolventDirichlet g)

@[simp] lemma resolventDirichletL2_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    resolventDirichletL2 g f =
      H1ComplDirichletToLp g (resolventDirichlet g f) := rfl

theorem resolventDirichletL2_isCompactOperator
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCompactOperator (resolventDirichletL2 g) := by
  change IsCompactOperator
    ((fun v => H1ComplDirichletToLp g v) ∘ fun f => resolventDirichlet g f)
  exact (H1ComplDirichletToLp_isCompactOperator g).comp_clm (resolventDirichlet g)

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
