import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1EigenBasis
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.HilbertBasis
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private abbrev DirichletL2
    (q : SmoothRiemannianMetric (I_half n) M) :=
  Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)

private noncomputable def uniformCauchySeqOnLimit
    {ι α β : Type*} [Nonempty ι] [SemilatticeSup ι]
    [UniformSpace β] [CompleteSpace β] [Nonempty β]
    (F : ι → α → β) (s : Set α)
    (hF : UniformCauchySeqOn F atTop s) (x : α) : β := by
  let _ := Classical.propDecidable
  exact if hx : x ∈ s then
      Classical.choose (cauchySeq_tendsto_of_complete (hF.cauchySeq hx))
    else Classical.choice inferInstance

private theorem tendsto_uniformCauchySeqOnLimit
    {ι α β : Type*} [Nonempty ι] [SemilatticeSup ι]
    [UniformSpace β] [CompleteSpace β] [Nonempty β]
    {F : ι → α → β} {s : Set α}
    (hF : UniformCauchySeqOn F atTop s) {x : α} (hx : x ∈ s) :
    Tendsto (fun i => F i x) atTop
      (𝓝 (uniformCauchySeqOnLimit F s hF x)) := by
  rw [uniformCauchySeqOnLimit, dif_pos hx]
  exact Classical.choose_spec
    (cauchySeq_tendsto_of_complete (hF.cauchySeq hx))

private theorem tendstoUniformlyOn_uniformCauchySeqOnLimit
    {ι α β : Type*} [Nonempty ι] [SemilatticeSup ι]
    [UniformSpace β] [CompleteSpace β] [Nonempty β]
    {F : ι → α → β} {s : Set α}
    (hF : UniformCauchySeqOn F atTop s) :
    TendstoUniformlyOn F (uniformCauchySeqOnLimit F s hF) atTop s :=
  hF.tendstoUniformlyOn_of_tendsto fun x hx =>
    tendsto_uniformCauchySeqOnLimit hF (x := x) hx

private theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn
    {ι α β : Type*} [Nonempty ι] [SemilatticeSup ι]
    [UniformSpace β] [CompleteSpace β] [Nonempty β]
    {F : ι → α → β} {s : Set α}
    (hF : UniformCauchySeqOn F atTop s) :
    ∃ f : α → β, TendstoUniformlyOn F f atTop s :=
  ⟨uniformCauchySeqOnLimit F s hF,
    tendstoUniformlyOn_uniformCauchySeqOnLimit hF⟩

private theorem intervalIntegrable_inner_timeL2
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {T : ℝ} (f g : timeL2 X T)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun t => inner ℝ (f t) (g t)) volume a b := by
  let ν : Measure ℝ := volume.restrict (uIoc a b)
  have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have hν : ν ≤ timeMeasure T := by
    exact Measure.restrict_mono hsub le_rfl
  have hf : MemLp (fun t => f t) 2 ν :=
    (Lp.memLp f).mono_measure hν
  have hg : MemLp (fun t => g t) 2 ν :=
    (Lp.memLp g).mono_measure hν
  have hprod : Integrable (fun t => ‖f t‖ * ‖g t‖) ν := by
    change Integrable ((fun t => ‖f t‖) * fun t => ‖g t‖) ν
    exact hf.norm.integrable_mul hg.norm
  have hinner : Integrable (fun t => inner ℝ (f t) (g t)) ν := by
    refine hprod.mono' (hf.1.inner hg.1) ?_
    filter_upwards [] with t
    exact norm_inner_le_norm _ _
  rw [intervalIntegrable_iff]
  change Integrable (fun t => inner ℝ (f t) (g t))
    (volume.restrict (uIoc a b))
  simpa only [ν] using hinner

private theorem dist_two_intervalIntegral_inner_le
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {T : ℝ} (v u w : timeL2 X T)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    dist (∫ t in a..b, 2 * inner ℝ (v t) (w t))
        (∫ t in a..b, 2 * inner ℝ (u t) (w t)) ≤
      2 * ‖v - u‖ * ‖w‖ := by
  have hvInt := intervalIntegrable_inner_timeL2 v w ha hb
  have huInt := intervalIntegrable_inner_timeL2 u w ha hb
  have hpair := abs_intervalIntegral_inner_le_norm (v - u) w ha hb
  have hsub :
      ((v - u : timeL2 X T) : ℝ → X) =ᵐ[timeMeasure T]
        fun t => v t - u t := Lp.coeFn_sub v u
  have hsubVolume :
      ((v - u : timeL2 X T) : ℝ → X) =ᵐ[
          volume.restrict (Icc (0 : ℝ) T)]
        fun t => v t - u t := by
    simpa only [timeMeasure] using hsub
  have hsubSet : uIoc a b ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have hsubInterval := hsubVolume.filter_mono
    (ae_mono (Measure.restrict_mono hsubSet le_rfl))
  have hintegralSub :
      (∫ t in a..b, inner ℝ ((v - u) t) (w t)) =
        ∫ t in a..b, inner ℝ (v t) (w t) - inner ℝ (u t) (w t) := by
    apply intervalIntegral.integral_congr_ae
    have hae := ae_imp_of_ae_restrict hsubInterval
    filter_upwards [hae] with t ht htu
    rw [ht htu, inner_sub_left]
  have hdiff :
      dist (∫ t in a..b, 2 * inner ℝ (v t) (w t))
          (∫ t in a..b, 2 * inner ℝ (u t) (w t)) =
        2 * |∫ t in a..b, inner ℝ ((v - u) t) (w t)| := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, Real.dist_eq, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      ← intervalIntegral.integral_sub hvInt huInt]
    rw [hintegralSub]
  rw [hdiff]
  nlinarith

private theorem finset_sum_le_tsum_compl
    {α : Type*} (f : α → ℝ)
    (hf : Summable f) (hfnn : ∀ i, 0 ≤ f i)
    (s d : Finset α) (hd : ∀ i ∈ d, i ∉ s) :
    ∑ i ∈ d, f i ≤ ∑' i : {x // x ∉ s}, f i := by
  classical
  let g : α → ℝ := fun i => if i ∉ s then f i else 0
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    by_cases hi : i ∉ s
    · simp only [g, if_pos hi]
      exact hfnn i
    · simp only [g, if_neg hi]
      exact le_rfl
  have hgle : ∀ i, g i ≤ f i := by
    intro i
    by_cases hi : i ∉ s
    · simp only [g, if_pos hi]
      exact le_rfl
    · simp only [g, if_neg hi]
      exact hfnn i
  have hg : Summable g :=
    Summable.of_nonneg_of_le hgnn hgle hf
  calc
    ∑ i ∈ d, f i = ∑ i ∈ d, g i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [g, if_pos (hd i hi)]
    _ ≤ ∑' i, g i := hg.sum_le_tsum d fun i hi => hgnn i
    _ = ∑' i, ({x | x ∉ s} : Set α).indicator f i := by
      apply tsum_congr
      intro i
      by_cases hi : i ∉ s
      · rw [show g i = f i by simp only [g, if_pos hi],
          Set.indicator_of_mem (show i ∈ {x | x ∉ s} from hi)]
      · rw [show g i = 0 by simp only [g, if_neg hi],
          Set.indicator_of_notMem (show i ∉ {x | x ∉ s} from hi)]
    _ = ∑' i : {x // x ∉ s}, f i :=
      (tsum_subtype {x | x ∉ s} f).symm

private noncomputable def dirichletMassPartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q)) :
    H1ComplDirichlet q →L[ℝ] DirichletL2 q :=
  ∑ i ∈ s, (Real.sqrt i.1.1)⁻¹ •
    InnerProductSpace.rankOne ℝ (dirichletLaplacianHilbertBasis q i)
      (dirichletH1HilbertBasis q i)

private noncomputable def dirichletH1PartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q)) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℝ (dirichletH1HilbertBasis q i)
    (dirichletH1HilbertBasis q i)

private noncomputable def dirichletL2PartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q)) :
    DirichletL2 q →L[ℝ] DirichletL2 q :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℝ (dirichletLaplacianHilbertBasis q i)
    (dirichletLaplacianHilbertBasis q i)

private theorem dirichletMassPartialSum_apply
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (v : H1ComplDirichlet q) :
    dirichletMassPartialSum q s v =
      ∑ i ∈ s, ((Real.sqrt i.1.1)⁻¹ *
        inner ℝ (dirichletH1HilbertBasis q i) v) •
          dirichletLaplacianHilbertBasis q i := by
  classical
  rw [dirichletMassPartialSum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply, InnerProductSpace.rankOne_apply, smul_smul]

private theorem dirichletH1PartialSum_apply
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (v : H1ComplDirichlet q) :
    dirichletH1PartialSum q s v =
      ∑ i ∈ s, inner ℝ (dirichletH1HilbertBasis q i) v •
        dirichletH1HilbertBasis q i := by
  classical
  rw [dirichletH1PartialSum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact InnerProductSpace.rankOne_apply _ _ _

private theorem dirichletL2PartialSum_apply
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (f : DirichletL2 q) :
    dirichletL2PartialSum q s f =
      ∑ i ∈ s, inner ℝ (dirichletLaplacianHilbertBasis q i) f •
        dirichletLaplacianHilbertBasis q i := by
  classical
  rw [dirichletL2PartialSum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact InnerProductSpace.rankOne_apply _ _ _

private theorem dirichletMassPartialSum_union_sub
    (q : SmoothRiemannianMetric (I_half n) M)
    [DecidableEq (DirichletLaplacianEigenIndex q)]
    (s r : Finset (DirichletLaplacianEigenIndex q))
    (v : H1ComplDirichlet q) :
    dirichletMassPartialSum q (s ∪ r) v -
        dirichletMassPartialSum q s v =
      dirichletMassPartialSum q (r \ s) v := by
  classical
  rw [dirichletMassPartialSum_apply, dirichletMassPartialSum_apply,
    dirichletMassPartialSum_apply,
    ← Finset.sum_sdiff (show s ⊆ s ∪ r by simp),
    Finset.union_sdiff_left, add_sub_cancel_right]

private theorem norm_sq_dirichletH1PartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (v : H1ComplDirichlet q) :
    ‖dirichletH1PartialSum q s v‖ ^ 2 =
      ∑ i ∈ s, (inner ℝ (dirichletH1HilbertBasis q i) v) ^ 2 := by
  classical
  rw [dirichletH1PartialSum_apply,
    ← real_inner_self_eq_norm_sq]
  rw [(dirichletH1HilbertBasis q).orthonormal.inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [starRingEnd_apply, star_trivial]
  ring

private theorem norm_sq_dirichletL2PartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (f : DirichletL2 q) :
    ‖dirichletL2PartialSum q s f‖ ^ 2 =
      ∑ i ∈ s,
        (inner ℝ (dirichletLaplacianHilbertBasis q i) f) ^ 2 := by
  classical
  rw [dirichletL2PartialSum_apply,
    ← real_inner_self_eq_norm_sq]
  rw [(dirichletLaplacianHilbertBasis q).orthonormal.inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [starRingEnd_apply, star_trivial]
  ring

private theorem inner_dirichletH1PartialSum_eq_norm_sq
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (v : H1ComplDirichlet q) :
    inner ℝ (dirichletH1PartialSum q s v) v =
      ‖dirichletH1PartialSum q s v‖ ^ 2 := by
  classical
  rw [norm_sq_dirichletH1PartialSum,
    dirichletH1PartialSum_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left]
  ring

private theorem tendsto_dirichletL2PartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (f : DirichletL2 q) :
    Tendsto (fun s : Finset (DirichletLaplacianEigenIndex q) =>
      dirichletL2PartialSum q s f) atTop (𝓝 f) := by
  have h := (dirichletLaplacianHilbertBasis q).hasSum_repr f
  change Tendsto (fun s : Finset (DirichletLaplacianEigenIndex q) =>
    ∑ i ∈ s, (dirichletLaplacianHilbertBasis q).repr f i •
      dirichletLaplacianHilbertBasis q i) atTop (𝓝 f) at h
  simpa only [dirichletL2PartialSum_apply,
    (dirichletLaplacianHilbertBasis q).repr_apply_apply] using h

private theorem norm_sq_dirichletH1PartialSum_compLpL
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T) :
    ‖(dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u‖ ^ 2 =
      ∑ i ∈ s,
        ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2 := by
  classical
  rw [TimeSobolev.norm_sq_eq_integral]
  have hproj := (dirichletH1PartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) u
  have hcoeff : ∀ᵐ t ∂(timeMeasure T), ∀ i ∈ s,
      hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i t =
        inner ℝ (dirichletH1HilbertBasis q i) (u t) :=
    (Finset.eventually_all (I := s)).2 fun i hi =>
      hilbertBasisTimeCoeff_coeFn (dirichletH1HilbertBasis q) u i
  have hpoint : ∀ᵐ t ∂(timeMeasure T),
      ‖((dirichletH1PartialSum q s).compLpL 2
        (timeMeasure T) u) t‖ ^ 2 =
        ∑ i ∈ s,
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i t‖ ^ 2 := by
    filter_upwards [hproj, hcoeff] with t htproj htcoeff
    rw [htproj, norm_sq_dirichletH1PartialSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [htcoeff i hi, Real.norm_eq_abs, sq_abs]
  have hpointIcc : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      ‖((dirichletH1PartialSum q s).compLpL 2
        (timeMeasure T) u) t‖ ^ 2 =
        ∑ i ∈ s,
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i t‖ ^ 2 := by
    simpa only [timeMeasure] using hpoint
  rw [integral_congr_ae hpointIcc]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact (TimeSobolev.norm_sq_eq_integral
      (hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i)).symm
  · intro i hi
    simpa only [timeMeasure, Real.norm_eq_abs, sq_abs] using
      (Lp.memLp
        (hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i)).integrable_sq

private theorem inner_dirichletH1PartialSum_compLpL_eq_norm_sq
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T) :
    inner ℝ
        ((dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u) u =
      ‖(dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u‖ ^ 2 := by
  rw [TimeSobolev.inner_def, TimeSobolev.norm_sq_eq_integral]
  apply integral_congr_ae
  have hproj := (dirichletH1PartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) u
  have hprojIcc :
      ((dirichletH1PartialSum q s).compLpL 2
        (timeMeasure T) u : ℝ → H1ComplDirichlet q) =ᵐ[
          volume.restrict (Icc (0 : ℝ) T)]
        fun t => dirichletH1PartialSum q s (u t) := by
    simpa only [timeMeasure, Function.comp_apply] using hproj
  filter_upwards [hprojIcc] with t ht
  rw [ht, inner_dirichletH1PartialSum_eq_norm_sq]

private theorem norm_sq_dirichletH1PartialSum_compLpL_sub
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T) :
    ‖(dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u - u‖ ^ 2 =
      ‖u‖ ^ 2 -
        ∑ i ∈ s,
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2 := by
  rw [norm_sub_sq_real,
    inner_dirichletH1PartialSum_compLpL_eq_norm_sq,
    norm_sq_dirichletH1PartialSum_compLpL]
  ring

private theorem tendsto_dirichletH1PartialSum_compLpL
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (u : timeL2 (H1ComplDirichlet q) T) :
    Tendsto (fun s : Finset (DirichletLaplacianEigenIndex q) =>
      (dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u)
      atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        ∑ i ∈ s,
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2)
      atTop (𝓝 (‖u‖ ^ 2)) := by
    have h := (summable_norm_hilbertBasisTimeCoeff_sq
      (dirichletH1HilbertBasis q) u).hasSum
    change Tendsto
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        ∑ i ∈ s,
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2)
      atTop (𝓝 (∑' i,
        ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2)) at h
    simpa only [← norm_sq_eq_tsum_norm_hilbertBasisTimeCoeff
      (dirichletH1HilbertBasis q) u] using h
  have hsq : Tendsto
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        ‖(dirichletH1PartialSum q s).compLpL 2
          (timeMeasure T) u - u‖ ^ 2) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub hsum using 1
    · funext s
      exact norm_sq_dirichletH1PartialSum_compLpL_sub q s u
    · ring_nf
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

private theorem inner_dirichletH1HilbertBasis_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex q)
    (v : H1ComplDirichlet q) :
    inner ℝ (dirichletH1HilbertBasis q i) v =
      (Real.sqrt i.1.1)⁻¹ *
        inner ℝ (dirichletLaplacianHilbertBasis q i)
          (H1ComplDirichletToLp q v) := by
  rw [dirichletH1HilbertBasis_apply, real_inner_smul_left,
    inner_dirichletLaplacianEigenvector,
    real_inner_comm (H1ComplDirichletToLp q v)]
  have hμ : 0 ≤ i.1.1 :=
    (resolvent_eigenvalue_pos q i.1.property).le
  have hsqrt : Real.sqrt i.1.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr
      (resolvent_eigenvalue_pos q i.1.property))
  have hcoef : Real.sqrt i.1.1 * i.1.1⁻¹ =
      (Real.sqrt i.1.1)⁻¹ := by
    calc
      Real.sqrt i.1.1 * i.1.1⁻¹ =
          Real.sqrt i.1.1 * (Real.sqrt i.1.1 ^ 2)⁻¹ := by
        rw [Real.sq_sqrt hμ]
      _ = (Real.sqrt i.1.1)⁻¹ := by field_simp
  rw [← mul_assoc, hcoef]

private theorem inner_dirichletL2PartialSum_massPartialSum
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (u v : H1ComplDirichlet q) :
    inner ℝ
        (dirichletL2PartialSum q s (H1ComplDirichletToLp q u))
        (dirichletMassPartialSum q s v) =
      inner ℝ (dirichletH1PartialSum q s u) v := by
  classical
  rw [dirichletL2PartialSum_apply, dirichletMassPartialSum_apply,
    dirichletH1PartialSum_apply]
  simp only [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left, real_inner_smul_left,
    (dirichletLaplacianHilbertBasis q).orthonormal.inner_right_sum
      (fun j => (Real.sqrt j.1.1)⁻¹ *
        inner ℝ (dirichletH1HilbertBasis q j) v) hi,
    inner_dirichletH1HilbertBasis_eq q i u]
  ring

private theorem dirichletMassPartialSum_resolventDirichlet
    (q : SmoothRiemannianMetric (I_half n) M)
    (s : Finset (DirichletLaplacianEigenIndex q))
    (f : DirichletL2 q) :
    dirichletMassPartialSum q s (resolventDirichlet q f) =
      dirichletL2PartialSum q s f := by
  classical
  rw [dirichletMassPartialSum_apply, dirichletL2PartialSum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show inner ℝ (dirichletH1HilbertBasis q i)
      (resolventDirichlet q f) =
        inner ℝ (resolventDirichlet q f)
          (dirichletH1HilbertBasis q i) from real_inner_comm _ _,
    resolventDirichlet_inner_eq_lpFunctional,
    dirichletH1HilbertBasis_apply,
    (H1ComplDirichletToLp q).map_smul,
    H1ComplDirichletToLp_dirichletLaplacianEigenvector,
    real_inner_smul_left]
  congr 1
  have hsqrt : Real.sqrt i.1.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr
      (resolvent_eigenvalue_pos q i.1.property))
  rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]

private theorem intervalIntegral_congr_ae_timeMeasure
    {T a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T)
    {f g : ℝ → ℝ} (hfg : f =ᵐ[timeMeasure T] g) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have htime : f =ᵐ[volume.restrict (Icc (0 : ℝ) T)] g := by
    simpa only [timeMeasure] using hfg
  have hinterval : f =ᵐ[volume.restrict (uIoc a b)] g :=
    htime.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact intervalIntegral.integral_congr_ae
    (ae_imp_of_ae_restrict hinterval)

private noncomputable def dirichletMassPartialTimeCurve
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (w : timeH1 (H1ComplDirichlet q) T) :
    timeH1 (DirichletL2 q) T :=
  timeH1.mk (dirichletMassPartialSum q s w.init)
    ((dirichletMassPartialSum q s).compLpL 2 (timeMeasure T) w.deriv)

private theorem dirichletMassPartialTimeCurve_toFun
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (w : timeH1 (H1ComplDirichlet q) T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (dirichletMassPartialTimeCurve q s w).toFun t =
      dirichletMassPartialSum q s (w.toFun t) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
    ⟨le_rfl, ht.1.trans ht.2⟩
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hzero ht)
  have hcoe := (dirichletMassPartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) w.deriv
  have hcoeTime :
      ((dirichletMassPartialSum q s).compLpL 2
        (timeMeasure T) w.deriv : ℝ → DirichletL2 q) =ᵐ[timeMeasure T]
      fun r => dirichletMassPartialSum q s (w.deriv r) := by
    simpa only [Function.comp_apply] using hcoe
  have hcoeVolume :
      ((dirichletMassPartialSum q s).compLpL 2
        (timeMeasure T) w.deriv : ℝ → DirichletL2 q) =ᵐ[
          volume.restrict (Icc (0 : ℝ) T)]
      fun r => dirichletMassPartialSum q s (w.deriv r) := by
    simpa only [timeMeasure] using hcoeTime
  have hcoeInterval := hcoeVolume.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hintegral :
      (∫ r in (0 : ℝ)..t,
          ((dirichletMassPartialSum q s).compLpL 2
            (timeMeasure T) w.deriv) r) =
        ∫ r in (0 : ℝ)..t,
          dirichletMassPartialSum q s (w.deriv r) :=
    intervalIntegral.integral_congr_ae
      (ae_imp_of_ae_restrict hcoeInterval)
  have hmap := (dirichletMassPartialSum q s).intervalIntegral_comp_comm
    (w.intervalIntegrable_deriv hzero ht)
  rw [timeH1.toFun_apply, dirichletMassPartialTimeCurve,
    timeH1.init_mk, timeH1.deriv_mk,
    hintegral, timeH1.toFun_apply, map_add, ← hmap]

private theorem dirichletMassPartialTimeCurve_union_sub
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} [DecidableEq (DirichletLaplacianEigenIndex q)]
    (s r : Finset (DirichletLaplacianEigenIndex q))
    (w : timeH1 (H1ComplDirichlet q) T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (dirichletMassPartialTimeCurve q (s ∪ r) w).toFun t -
        (dirichletMassPartialTimeCurve q s w).toFun t =
      (dirichletMassPartialTimeCurve q (r \ s) w).toFun t := by
  rw [dirichletMassPartialTimeCurve_toFun q (s ∪ r) w ht,
    dirichletMassPartialTimeCurve_toFun q s w ht,
    dirichletMassPartialTimeCurve_toFun q (r \ s) w ht,
    dirichletMassPartialSum_union_sub]

private theorem dirichletMassPartialTimeCurve_init
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (w : timeH1 (H1ComplDirichlet q) T) (f₀ : DirichletL2 q)
    (hinit : w.init = resolventDirichlet q f₀) :
    (dirichletMassPartialTimeCurve q s w).init =
      dirichletL2PartialSum q s f₀ := by
  rw [dirichletMassPartialTimeCurve, timeH1.init_mk, hinit,
    dirichletMassPartialSum_resolventDirichlet]

private theorem dirichletMassPartialTimeCurve_ae_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun) :
    (dirichletMassPartialTimeCurve q s w).toFun =ᵐ[timeMeasure T]
      fun t => dirichletL2PartialSum q s
        (H1ComplDirichletToLp q (u t)) := by
  filter_upwards [hmass, ae_restrict_mem measurableSet_Icc] with t ht htIcc
  rw [dirichletMassPartialTimeCurve_toFun q s w htIcc, ← ht,
    dirichletMassPartialSum_resolventDirichlet]

private theorem dirichletMassPartialTimeCurve_energy
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ‖(dirichletMassPartialTimeCurve q s w).toFun b‖ ^ 2 -
        ‖(dirichletMassPartialTimeCurve q s w).toFun a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (dirichletH1PartialSum q s (u t))
        (w.deriv t) := by
  rw [timeH1.norm_sq_sub_norm_sq_eq_two_intervalIntegral
    (dirichletMassPartialTimeCurve q s w) ha hb]
  apply intervalIntegral_congr_ae_timeMeasure ha hb
  have hcurve := dirichletMassPartialTimeCurve_ae_eq q s u w hmass
  have hderiv := (dirichletMassPartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) w.deriv
  filter_upwards [hcurve, hderiv] with t htcurve htderiv
  rw [htcurve]
  change 2 * inner ℝ
      (dirichletL2PartialSum q s (H1ComplDirichletToLp q (u t)))
      (((dirichletMassPartialSum q s).compLpL 2
        (timeMeasure T) w.deriv) t) = _
  rw [htderiv,
    inner_dirichletL2PartialSum_massPartialSum]

private theorem norm_sq_dirichletMassPartialTimeCurve_le
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : DirichletL2 q)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (htrace : w.toFun τ = resolventDirichlet q f₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖(dirichletMassPartialTimeCurve q s w).toFun t‖ ^ 2 ≤
      ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
        2 * ‖(dirichletH1PartialSum q s).compLpL 2
          (timeMeasure T) u‖ * ‖w.deriv‖ := by
  have henergy := dirichletMassPartialTimeCurve_energy
    q s u w hmass hτ ht
  rw [dirichletMassPartialTimeCurve_toFun q s w hτ, htrace,
    dirichletMassPartialSum_resolventDirichlet] at henergy
  have hproj := (dirichletH1PartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) u
  have hintegral :
      (∫ r in τ..t,
          inner ℝ (dirichletH1PartialSum q s (u r)) (w.deriv r)) =
        ∫ r in τ..t,
          inner ℝ
            (((dirichletH1PartialSum q s).compLpL 2
              (timeMeasure T) u) r) (w.deriv r) := by
    apply intervalIntegral_congr_ae_timeMeasure hτ ht
    filter_upwards [hproj] with r hr
    rw [hr]
  calc
    ‖(dirichletMassPartialTimeCurve q s w).toFun t‖ ^ 2 =
        ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
          ∫ r in τ..t,
            2 * inner ℝ (dirichletH1PartialSum q s (u r))
              (w.deriv r) := by linarith
    _ = ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
        2 * ∫ r in τ..t,
          inner ℝ (dirichletH1PartialSum q s (u r))
            (w.deriv r) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
        2 * ∫ r in τ..t,
          inner ℝ
            (((dirichletH1PartialSum q s).compLpL 2
              (timeMeasure T) u) r) (w.deriv r) := by rw [hintegral]
    _ ≤ ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
        2 * |∫ r in τ..t,
          inner ℝ
            (((dirichletH1PartialSum q s).compLpL 2
              (timeMeasure T) u) r) (w.deriv r)| := by
      gcongr
      exact le_abs_self _
    _ ≤ ‖dirichletL2PartialSum q s f₀‖ ^ 2 +
        2 * ‖(dirichletH1PartialSum q s).compLpL 2
          (timeMeasure T) u‖ * ‖w.deriv‖ := by
      have hpair := abs_intervalIntegral_inner_le_norm
        ((dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u)
          w.deriv hτ ht
      nlinarith

private theorem norm_sq_dirichletMassPartialTimeCurve_le_tails
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (s d : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : DirichletL2 q)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (htrace : w.toFun τ = resolventDirichlet q f₀)
    (hd : ∀ i ∈ d, i ∉ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖(dirichletMassPartialTimeCurve q d w).toFun t‖ ^ 2 ≤
      (∑' i : {x // x ∉ s},
        (inner ℝ (dirichletLaplacianHilbertBasis q i) f₀) ^ 2) +
        2 * Real.sqrt (∑' i : {x // x ∉ s},
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2) *
          ‖w.deriv‖ := by
  classical
  have hfSummable : Summable fun i : DirichletLaplacianEigenIndex q =>
      (inner ℝ (dirichletLaplacianHilbertBasis q i) f₀) ^ 2 := by
    refine ((dirichletLaplacianHilbertBasis q).orthonormal.inner_products_summable
      f₀).congr fun i => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have huSummable := summable_norm_hilbertBasisTimeCoeff_sq
    (dirichletH1HilbertBasis q) u
  have hfTail :
      ‖dirichletL2PartialSum q d f₀‖ ^ 2 ≤
        ∑' i : {x // x ∉ s},
          (inner ℝ (dirichletLaplacianHilbertBasis q i) f₀) ^ 2 := by
    rw [norm_sq_dirichletL2PartialSum]
    exact finset_sum_le_tsum_compl _ hfSummable
      (fun i => sq_nonneg _) s d hd
  have huTailSq :
      ‖(dirichletH1PartialSum q d).compLpL 2
          (timeMeasure T) u‖ ^ 2 ≤
        ∑' i : {x // x ∉ s},
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2 := by
    rw [norm_sq_dirichletH1PartialSum_compLpL]
    exact finset_sum_le_tsum_compl _ huSummable
      (fun i => sq_nonneg _) s d hd
  have huTail :
      ‖(dirichletH1PartialSum q d).compLpL 2
          (timeMeasure T) u‖ ≤
        Real.sqrt (∑' i : {x // x ∉ s},
          ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt huTailSq
  exact (norm_sq_dirichletMassPartialTimeCurve_le
    q d u w f₀ τ hτ hmass htrace ht).trans
      (add_le_add hfTail
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huTail (by positivity))
          (norm_nonneg _)))

private theorem exists_dirichletMassTrace_uniformLimit
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : DirichletL2 q)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (htrace : w.toFun τ = resolventDirichlet q f₀) :
    ∃ U : ℝ → DirichletL2 q,
      TendstoUniformlyOn
        (fun s : Finset (DirichletLaplacianEigenIndex q) =>
          (dirichletMassPartialTimeCurve q s w).toFun)
        U atTop (Icc (0 : ℝ) T) := by
  classical
  apply exists_tendstoUniformlyOn_of_uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let initialCoeff : DirichletLaplacianEigenIndex q → ℝ := fun i =>
    (inner ℝ (dirichletLaplacianHilbertBasis q i) f₀) ^ 2
  let timeCoeff : DirichletLaplacianEigenIndex q → ℝ := fun i =>
    ‖hilbertBasisTimeCoeff (dirichletH1HilbertBasis q) u i‖ ^ 2
  let initialTail : Finset (DirichletLaplacianEigenIndex q) → ℝ := fun s =>
    ∑' i : {x // x ∉ s}, initialCoeff i
  let timeTail : Finset (DirichletLaplacianEigenIndex q) → ℝ := fun s =>
    ∑' i : {x // x ∉ s}, timeCoeff i
  have hinitialTail : Tendsto initialTail atTop (𝓝 0) := by
    simpa only [initialTail] using
      (tendsto_tsum_compl_atTop_zero initialCoeff)
  have htimeTail : Tendsto timeTail atTop (𝓝 0) := by
    simpa only [timeTail] using
      (tendsto_tsum_compl_atTop_zero timeCoeff)
  have hboundTail : Tendsto
      (fun s => initialTail s +
        2 * Real.sqrt (timeTail s) * ‖w.deriv‖)
      atTop (𝓝 0) := by
    simpa using hinitialTail.add
      ((htimeTail.sqrt.const_mul 2).mul_const ‖w.deriv‖)
  have hsmall : ∀ᶠ s in atTop,
      initialTail s + 2 * Real.sqrt (timeTail s) * ‖w.deriv‖ <
        (ε / 2) ^ 2 :=
    (tendsto_order.1 hboundTail).2 _ (sq_pos_of_pos (half_pos hε))
  rw [eventually_atTop] at hsmall
  obtain ⟨s, hs⟩ := hsmall
  have hssmall := hs s le_rfl
  refine ⟨s, ?_⟩
  intro m hm r hr t ht
  have htailNorm (d : Finset (DirichletLaplacianEigenIndex q))
      (hd : ∀ i ∈ d, i ∉ s) :
      ‖(dirichletMassPartialTimeCurve q d w).toFun t‖ < ε / 2 := by
    have hsqTail := norm_sq_dirichletMassPartialTimeCurve_le_tails
      q s d u w f₀ τ hτ hmass htrace hd ht
    change ‖(dirichletMassPartialTimeCurve q d w).toFun t‖ ^ 2 ≤
      initialTail s + 2 * Real.sqrt (timeTail s) * ‖w.deriv‖ at hsqTail
    exact (sq_lt_sq₀ (norm_nonneg _)
      (half_pos hε).le).mp (hsqTail.trans_lt hssmall)
  have hmr :
      (dirichletMassPartialTimeCurve q (m ∪ r) w).toFun t -
          (dirichletMassPartialTimeCurve q m w).toFun t =
        (dirichletMassPartialTimeCurve q (r \ m) w).toFun t :=
    dirichletMassPartialTimeCurve_union_sub q m r w ht
  have hrm :
      (dirichletMassPartialTimeCurve q (m ∪ r) w).toFun t -
          (dirichletMassPartialTimeCurve q r w).toFun t =
        (dirichletMassPartialTimeCurve q (m \ r) w).toFun t := by
    simpa only [Finset.union_comm] using
      (dirichletMassPartialTimeCurve_union_sub q r m w ht)
  have hright :
      ‖(dirichletMassPartialTimeCurve q (r \ m) w).toFun t‖ < ε / 2 :=
    htailNorm (r \ m) fun i hi hiS =>
      (Finset.mem_sdiff.mp hi).2 (hm hiS)
  have hleft :
      ‖(dirichletMassPartialTimeCurve q (m \ r) w).toFun t‖ < ε / 2 :=
    htailNorm (m \ r) fun i hi hiS =>
      (Finset.mem_sdiff.mp hi).2 (hr hiS)
  calc
    dist ((dirichletMassPartialTimeCurve q m w).toFun t)
        ((dirichletMassPartialTimeCurve q r w).toFun t) =
      ‖((dirichletMassPartialTimeCurve q (m ∪ r) w).toFun t -
          (dirichletMassPartialTimeCurve q r w).toFun t) -
        ((dirichletMassPartialTimeCurve q (m ∪ r) w).toFun t -
          (dirichletMassPartialTimeCurve q m w).toFun t)‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖(dirichletMassPartialTimeCurve q (m \ r) w).toFun t‖ +
        ‖(dirichletMassPartialTimeCurve q (r \ m) w).toFun t‖ := by
      rw [hrm, hmr]
      exact norm_sub_le _ _
    _ < ε := by linarith

private theorem dirichletMassPartialTimeCurve_energy_compLpL
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (s : Finset (DirichletLaplacianEigenIndex q))
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ‖(dirichletMassPartialTimeCurve q s w).toFun b‖ ^ 2 -
        ‖(dirichletMassPartialTimeCurve q s w).toFun a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ
        (((dirichletH1PartialSum q s).compLpL 2
          (timeMeasure T) u) t) (w.deriv t) := by
  rw [dirichletMassPartialTimeCurve_energy q s u w hmass ha hb]
  apply intervalIntegral_congr_ae_timeMeasure ha hb
  have hproj := (dirichletH1PartialSum q s).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) u
  filter_upwards [hproj] with t ht
  rw [ht]

private theorem tendsto_dirichletMassPartialTimeCurve_energy_left
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (w : timeH1 (H1ComplDirichlet q) T)
    (U : ℝ → DirichletL2 q)
    (hU : TendstoUniformlyOn
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        (dirichletMassPartialTimeCurve q s w).toFun)
      U atTop (Icc (0 : ℝ) T))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    Tendsto
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        ‖(dirichletMassPartialTimeCurve q s w).toFun b‖ ^ 2 -
          ‖(dirichletMassPartialTimeCurve q s w).toFun a‖ ^ 2)
      atTop (𝓝 (‖U b‖ ^ 2 - ‖U a‖ ^ 2)) :=
  ((hU.tendsto_at hb).norm.pow 2).sub ((hU.tendsto_at ha).norm.pow 2)

private theorem tendsto_dirichletMassPartialTimeCurve_energy_right
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    Tendsto
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        ∫ t in a..b, 2 * inner ℝ
          (((dirichletH1PartialSum q s).compLpL 2
            (timeMeasure T) u) t) (w.deriv t))
      atTop (𝓝 (∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t))) := by
  let v : Finset (DirichletLaplacianEigenIndex q) →
      timeL2 (H1ComplDirichlet q) T := fun s =>
    (dirichletH1PartialSum q s).compLpL 2 (timeMeasure T) u
  have hv : Tendsto v atTop (𝓝 u) :=
    tendsto_dirichletH1PartialSum_compLpL q u
  change Tendsto
    (fun s : Finset (DirichletLaplacianEigenIndex q) =>
      ∫ t in a..b, 2 * inner ℝ (v s t) (w.deriv t))
    atTop (𝓝 (∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t)))
  rw [tendsto_iff_dist_tendsto_zero]
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.1 hv
  have hbound : Tendsto (fun s => 2 * ‖v s - u‖ * ‖w.deriv‖)
      atTop (𝓝 0) := by
    simpa using (hnorm.const_mul 2).mul_const ‖w.deriv‖
  exact squeeze_zero'
    (Eventually.of_forall fun s => dist_nonneg)
    (Eventually.of_forall fun s =>
      dist_two_intervalIntegral_inner_le (v s) u w.deriv ha hb)
    hbound

private theorem dirichletMassTrace_energy
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (U : ℝ → DirichletL2 q)
    (hU : TendstoUniformlyOn
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        (dirichletMassPartialTimeCurve q s w).toFun)
      U atTop (Icc (0 : ℝ) T))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t) := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_dirichletMassPartialTimeCurve_energy_left q w U hU ha hb)
    (tendsto_dirichletMassPartialTimeCurve_energy_right q u w ha hb)
    (Eventually.of_forall fun s =>
      dirichletMassPartialTimeCurve_energy_compLpL
        q s u w hmass ha hb)

private theorem dirichletMassTrace_ae_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (U : ℝ → DirichletL2 q)
    (hU : TendstoUniformlyOn
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        (dirichletMassPartialTimeCurve q s w).toFun)
      U atTop (Icc (0 : ℝ) T)) :
    U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t) := by
  have hcurves : ∀ᵐ t ∂(timeMeasure T),
      ∀ s : Finset (DirichletLaplacianEigenIndex q),
        (dirichletMassPartialTimeCurve q s w).toFun t =
          dirichletL2PartialSum q s
            (H1ComplDirichletToLp q (u t)) :=
    ae_all_iff.2 fun s =>
      dirichletMassPartialTimeCurve_ae_eq q s u w hmass
  filter_upwards [hcurves, ae_restrict_mem measurableSet_Icc] with t htcurves ht
  exact tendsto_nhds_unique_of_eventuallyEq
    (hU.tendsto_at ht)
    (tendsto_dirichletL2PartialSum q
      (H1ComplDirichletToLp q (u t)))
    (Eventually.of_forall (htcurves ·))

private theorem dirichletMassTrace_zero
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 ≤ T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : DirichletL2 q)
    (hinit : w.init = resolventDirichlet q f₀)
    (U : ℝ → DirichletL2 q)
    (hU : TendstoUniformlyOn
      (fun s : Finset (DirichletLaplacianEigenIndex q) =>
        (dirichletMassPartialTimeCurve q s w).toFun)
      U atTop (Icc (0 : ℝ) T)) :
    U 0 = f₀ := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (hU.tendsto_at hzero)
    (tendsto_dirichletL2PartialSum q f₀)
    (Eventually.of_forall fun s => by
      change (dirichletMassPartialTimeCurve q s w).toFun 0 =
        dirichletL2PartialSum q s f₀
      rw [timeH1.toFun_zero,
        dirichletMassPartialTimeCurve_init q s w f₀ hinit])

private theorem exists_continuous_l2_representative_of_mass_timeH1_of_pos
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun) :
    ∃ U : ℝ → DirichletL2 q,
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
      ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
        ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
          ∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t) := by
  have : (ae (timeMeasure T)).NeBot := ae_neBot.mpr (timeMeasure_ne_zero hT)
  have hex : ∀ᵐ τ ∂(timeMeasure T), τ ∈ Icc (0 : ℝ) T ∧
      w.toFun τ = resolventDirichlet q (H1ComplDirichletToLp q (u τ)) := by
    filter_upwards [hmass, ae_restrict_mem measurableSet_Icc] with τ hτ hmem
    exact ⟨hmem, hτ.symm⟩
  obtain ⟨τ, hτ, htrace⟩ := hex.exists
  obtain ⟨U, hU⟩ := exists_dirichletMassTrace_uniformLimit
    q u w (H1ComplDirichletToLp q (u τ)) τ hτ hmass htrace
  have hcontinuous : ContinuousOn U (Icc (0 : ℝ) T) :=
    hU.continuousOn ((Eventually.of_forall fun s =>
      (dirichletMassPartialTimeCurve q s w).continuousOn_toFun).frequently)
  have hae : U =ᵐ[timeMeasure T]
      fun t => H1ComplDirichletToLp q (u t) :=
    dirichletMassTrace_ae_eq q u w hmass U hU
  exact ⟨U, hcontinuous, hae, fun a b ha hb =>
    dirichletMassTrace_energy q u w hmass U hU ha hb⟩

theorem exists_continuous_l2_representative_of_resolvent_timeH1
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ}
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun) :
    ∃ U : ℝ → DirichletL2 q,
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
      ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
        ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
          ∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t) := by
  by_cases hT : 0 < T
  · exact exists_continuous_l2_representative_of_mass_timeH1_of_pos q hT u w hmass
  · have hT' : T ≤ 0 := le_of_not_gt hT
    refine ⟨fun _ => 0, continuousOn_const, ?_, ?_⟩
    · have hbot : ae (timeMeasure T) = ⊥ :=
        MeasureTheory.ae_eq_bot.mpr (timeMeasure_eq_zero_of_nonpos hT')
      change ∀ᶠ t in ae (timeMeasure T),
        (0 : DirichletL2 q) = H1ComplDirichletToLp q (u t)
      rw [hbot]
      exact Filter.mem_bot
    · intro a b ha hb
      have hab : a = b := by
        rcases ha with ⟨ha, haT⟩
        rcases hb with ⟨hb, hbT⟩
        linarith
      subst b
      simp only [sub_self, intervalIntegral.integral_same]

theorem exists_continuous_l2_representative_of_mass_timeH1
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 ≤ T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (w : timeH1 (H1ComplDirichlet q) T)
    (f₀ : DirichletL2 q)
    (hmass : (fun t => resolventDirichlet q
      (H1ComplDirichletToLp q (u t))) =ᵐ[timeMeasure T] w.toFun)
    (hinit : w.init = resolventDirichlet q f₀) :
    ∃ U : ℝ → DirichletL2 q,
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
      U 0 = f₀ ∧
      ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
        ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
          ∫ t in a..b, 2 * inner ℝ (u t) (w.deriv t) := by
  obtain ⟨U, hU⟩ := exists_dirichletMassTrace_uniformLimit
    q u w f₀ 0 ⟨le_rfl, hT⟩ hmass (by simpa only [timeH1.toFun_zero] using hinit)
  have hcontinuous : ContinuousOn U (Icc (0 : ℝ) T) :=
    hU.continuousOn ((Eventually.of_forall fun s =>
      (dirichletMassPartialTimeCurve q s w).continuousOn_toFun).frequently)
  have hae : U =ᵐ[timeMeasure T]
      fun t => H1ComplDirichletToLp q (u t) :=
    dirichletMassTrace_ae_eq q u w hmass U hU
  have hinitU : U 0 = f₀ :=
    dirichletMassTrace_zero q hT w f₀ hinit U hU
  exact ⟨U, hcontinuous, hae, hinitU, fun a b ha hb =>
    dirichletMassTrace_energy q u w hmass U hU ha hb⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
