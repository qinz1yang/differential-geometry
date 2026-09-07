import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.H1Energy

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

section

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)

private local instance : MeasurableSpace EuN := borel _
private local instance : BorelSpace EuN := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem norm_sq_smoothScalarDirichlet_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M} (α : M) (v : SmoothScalarDirichlet q)
    (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    ‖v‖ ^ 2 = ∫ y in interior (extChartAt I_hs α).target,
      chartDensityOnE (I := I_hs) q α y *
        ((scalarOnE (I := I_hs) α v.toFun y) ^ 2 +
          ∑ i, ∑ j, chartInvGramOnE (I := I_hs) q α i j y *
            partialDeriv (E := EuN) j (scalarOnE (I := I_hs) α v.toFun) y *
            partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y)
        ∂modelHaar := by
  let F : M → ℝ := fun x => (v.toFun x) ^ 2 +
    q.inner x (gradFun q v.toFun x) (gradFun q v.toFun x)
  have hF : Continuous F :=
    (v.smooth.continuous.pow 2).add (continuous_g_inner_gradFun_gradFun q v.smooth v.smooth)
  have hFzero (x : M) (hx : x ∉ tsupport v.toFun) : F x = 0 := by
    have hgrad : gradFun q v.toFun x = 0 :=
      Function.notMem_support.mp (fun h => hx (support_gradFun_subset q v.toFun h))
    simp only [F, image_eq_zero_of_notMem_tsupport hx, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, hgrad, map_zero, add_zero]
  calc
    ‖v‖ ^ 2 = ∫ x, F x ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
      rw [v.norm_sq_eq_inner_self, interiorSmoothScalarH1Inner_def,
        ← integral_add (v.integrable_mul v) (v.integrable_inner_grad v)]
      apply integral_congr_ae
      filter_upwards with x
      change v.toFun x * v.toFun x + q.inner x (gradFun q v.toFun x)
        (gradFun q v.toFun x) = F x
      simp only [F, pow_two]
    _ = ∫ y in (extChartAt I_hs α).target,
        chartDensity q α ((extChartAt I_hs α).symm y) * F ((extChartAt I_hs α).symm y)
          ∂modelHaar :=
      Sobolev.Chart.integral_eq_integral_chartDensity_of_support_in_chart q α hF.measurable
        (fun x hx => hFzero x (fun h => hx (hv h)))
    _ = ∫ y in interior (extChartAt I_hs α).target,
        chartDensity q α ((extChartAt I_hs α).symm y) * F ((extChartAt I_hs α).symm y)
          ∂modelHaar := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_extChartAt_target (I := I_hs) α) interior_subset
      intro y hy
      have hnot : (extChartAt I_hs α).symm y ∉ tsupport v.toFun := by
        intro hys
        have hsrc := (extChartAt I_hs α).map_target hy.1
        rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
        have hi := extChartAt_mem_interior_target_of_isInteriorPoint (I := I_hs) α hsrc
          (v.interior_support hys)
        rw [(extChartAt I_hs α).right_inv hy.1] at hi
        exact hy.2 hi
      rw [hFzero _ hnot, mul_zero]
    _ = _ := by
      apply setIntegral_congr_fun isOpen_interior.measurableSet
      intro y hy
      have hsrc := (extChartAt I_hs α).map_target (interior_subset hy)
      rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
      have hxint : extChartAt I_hs α ((extChartAt I_hs α).symm y) ∈
          interior (extChartAt I_hs α).target := by
        rwa [(extChartAt I_hs α).right_inv (interior_subset hy)]
      dsimp only [F]
      rw [grad_norm_sq_chart_of_mem_interior q α (v.smooth.mdifferentiable (by simp) _) hsrc hxint,
        (extChartAt I_hs α).right_inv (interior_subset hy)]
      rfl

theorem exists_norm_sq_smoothScalarDirichlet_le_integral_chart
    (q : SmoothRiemannianMetric I_hs M) (α : M) {K : Set EuN}
    (hK : IsCompact K) (hKs : K ⊆ interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothScalarDirichlet q,
      tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source →
      (∀ x ∈ tsupport v.toFun, extChartAt I_hs α x ∈ K) →
      ‖v‖ ^ 2 ≤ C * ∫ y in K,
        (scalarOnE (I := I_hs) α v.toFun y) ^ 2 +
          ∑ k, (partialDeriv (E := EuN) k (scalarOnE (I := I_hs) α v.toFun) y) ^ 2
        ∂modelHaar := by
  classical
  let ρ : EuN → ℝ := chartDensityOnE (I := I_hs) q α
  let A : EuN → ℝ := fun y => chartInvGramMatrixL1Sum (I := I_hs) (M := M) q α
    ((extChartAt I_hs α).symm y)
  have hρ : ContinuousOn ρ K := (chartDensityOnE_contDiffOn q α).continuousOn.mono
    (hKs.trans interior_subset)
  have hA : ContinuousOn A K := by
    unfold A chartInvGramMatrixL1Sum
    apply continuousOn_finsetSum
    intro ij _
    exact ((chartInvGramOnE_contDiffOn q α ij.1 ij.2).continuousOn.abs).mono
      (hKs.trans interior_subset)
  obtain ⟨c, hc⟩ := (hK.image_of_continuousOn (hρ.mul (continuousOn_const.add hA))).bddAbove
  refine ⟨max 0 c, le_max_left _ _, ?_⟩
  intro v hv hvK
  let s : EuN → ℝ := scalarOnE (I := I_hs) α v.toFun
  let P : EuN → ℝ := fun y => ∑ k, (partialDeriv (E := EuN) k s y) ^ 2
  let Q : EuN → ℝ := fun y => (s y) ^ 2 + P y
  let F : EuN → ℝ := fun y => ρ y * ((s y) ^ 2 +
    q.inner ((extChartAt I_hs α).symm y)
      (gradFun q v.toFun ((extChartAt I_hs α).symm y))
      (gradFun q v.toFun ((extChartAt I_hs α).symm y)))
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) s (interior (extChartAt I_hs α).target) :=
    (scalarOnE_contDiffOn α v.smooth).mono interior_subset
  have hP : ContinuousOn P K := by
    apply continuousOn_finsetSum
    intro k _
    exact (((hs.continuousOn_fderiv_of_isOpen isOpen_interior (by simp)).clm_apply
      continuousOn_const).pow 2).mono hKs
  have hQ : ContinuousOn Q K := (hs.continuousOn.mono hKs |>.pow 2).add hP
  have hF : ContinuousOn F K := by
    apply hρ.mul
    apply (hs.continuousOn.mono hKs |>.pow 2).add
    exact (continuous_g_inner_gradFun_gradFun q v.smooth v.smooth).continuousOn.comp
      ((continuousOn_extChartAt_symm α).mono (hKs.trans interior_subset)) (mapsTo_univ _ _)
  have hchart : ‖v‖ ^ 2 = ∫ y in K, F y ∂modelHaar := by
    rw [norm_sq_smoothScalarDirichlet_eq_integral_chart α v hv]
    have heq : (∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) q α y *
          ((scalarOnE (I := I_hs) α v.toFun y) ^ 2 +
            ∑ i, ∑ j, chartInvGramOnE (I := I_hs) q α i j y *
              partialDeriv (E := EuN) j (scalarOnE (I := I_hs) α v.toFun) y *
              partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y) ∂modelHaar) =
        ∫ y in interior (extChartAt I_hs α).target, F y ∂modelHaar := by
      apply setIntegral_congr_fun isOpen_interior.measurableSet
      intro y hy
      have hsrc := (extChartAt I_hs α).map_target (interior_subset hy)
      rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
      have hxint : extChartAt I_hs α ((extChartAt I_hs α).symm y) ∈
          interior (extChartAt I_hs α).target := by
        rwa [(extChartAt I_hs α).right_inv (interior_subset hy)]
      dsimp only [F, ρ, s]
      rw [grad_norm_sq_chart_of_mem_interior q α (v.smooth.mdifferentiable (by simp) _) hsrc hxint,
        (extChartAt I_hs α).right_inv (interior_subset hy)]
      rfl
    rw [heq]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_interior.measurableSet hKs
    intro y hy
    have hnot : (extChartAt I_hs α).symm y ∉ tsupport v.toFun := by
      intro hsupp
      apply hy.2
      have h := hvK _ hsupp
      rwa [(extChartAt I_hs α).right_inv (interior_subset hy.1)] at h
    have hgrad : gradFun q v.toFun ((extChartAt I_hs α).symm y) = 0 :=
      Function.notMem_support.mp (fun h => hnot (support_gradFun_subset q v.toFun h))
    simp only [F, s, scalarOnE, image_eq_zero_of_notMem_tsupport hnot, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, hgrad, map_zero, add_zero, mul_zero]
  rw [hchart, ← integral_const_mul]
  apply setIntegral_mono_on (hF.integrableOn_compact hK) (hQ.integrableOn_compact hK |>.const_mul _)
    hK.measurableSet
  intro y hy
  have hyint := hKs hy
  have hsrc := (extChartAt I_hs α).map_target (interior_subset hyint)
  rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
  have hxint : extChartAt I_hs α ((extChartAt I_hs α).symm y) ∈
      interior (extChartAt I_hs α).target := by
    rwa [(extChartAt I_hs α).right_inv (interior_subset hyint)]
  have hg := g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials_of_mem_interior
    q α (v.smooth.mdifferentiable (by simp) _) hsrc hxint
  rw [(extChartAt I_hs α).right_inv (interior_subset hyint)] at hg
  have hρnonneg : 0 ≤ ρ y := by
    apply le_of_lt
    apply chartDensity_pos q α
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hAnonneg : 0 ≤ A y := Finset.sum_nonneg (fun ij _ => abs_nonneg _)
  have hPnonneg : 0 ≤ P y := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hQnonneg : 0 ≤ Q y := add_nonneg (sq_nonneg _) hPnonneg
  have hC : ρ y * (1 + A y) ≤ max 0 c :=
    (hc ⟨y, hy, rfl⟩).trans (le_max_right _ _)
  calc
    F y ≤ ρ y * ((s y) ^ 2 + A y * P y) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right hg _) hρnonneg
    _ ≤ ρ y * ((1 + A y) * Q y) := by
      apply mul_le_mul_of_nonneg_left _ hρnonneg
      dsimp only [Q]
      nlinarith [mul_nonneg hAnonneg (sq_nonneg (s y))]
    _ = (ρ y * (1 + A y)) * Q y := by ring
    _ ≤ max 0 c * Q y := mul_le_mul_of_nonneg_right hC hQnonneg

end

section

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuN := borel _
private local instance : BorelSpace EuN := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

def smoothScalarDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    SmoothScalarDirichlet q :=
  ⟨chartPullback I_hs α ψ,
    chartPullback_contMDiff α hψ hψc (hψs.trans (image_mono interior_subset)),
    tsupport_chartPullback_subset_interior α hψc hψs⟩

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem scalarOnE_chartPullback_eq
    (α : M) (ψ : EuStd → ℝ) {y : EuN} (hy : y ∈ (extChartAt I_hs α).target) :
    scalarOnE (I := I_hs) α (chartPullback I_hs α ψ) y = ψ (toEuclidean (E := EuN) y) := by
  have hsrc := (extChartAt I_hs α).map_target hy
  rw [extChartAt_source] at hsrc
  rw [scalarOnE, chartPullback_apply_of_mem α ψ hsrc, (extChartAt I_hs α).right_inv hy]

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem partialDeriv_scalarOnE_chartPullback
    (α : M) (ψ : EuStd → ℝ) {y : EuN} (hy : y ∈ interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α (chartPullback I_hs α ψ)) y =
      fderiv ℝ ψ (toEuclidean (E := EuN) y) (EuclideanSpace.single i 1) := by
  have heq : scalarOnE (I := I_hs) α (chartPullback I_hs α ψ) =ᶠ[𝓝 y]
      ψ ∘ toEuclidean (E := EuN) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact scalarOnE_chartPullback_eq α ψ (interior_subset hz)
  rw [partialDeriv, heq.fderiv_eq, (toEuclidean (E := EuN)).comp_right_fderiv,
    ContinuousLinearMap.comp_apply, chartModelBasis_apply]
  simp

theorem exists_norm_sq_smoothScalarDirichletChartPullback_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {K : Set EuStd}
    (hK : IsCompact K)
    (hKs : K ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : EuStd → ℝ)
      (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
      (hψK : tsupport ψ ⊆ K),
      ‖smoothScalarDirichletChartPullback q α hψ hψc (hψK.trans hKs)‖ ^ 2 ≤
        C * ∫ z in K, (ψ z) ^ 2 +
          ∑ k, (fderiv ℝ ψ z (EuclideanSpace.single k 1)) ^ 2 := by
  classical
  let e := toEuclidean (E := EuN)
  let L := e.symm '' K
  have hL : IsCompact L := hK.image e.symm.continuous
  have hLs : L ⊆ interior (extChartAt I_hs α).target := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hKs hz
    simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy
  obtain ⟨C, hC, hbound⟩ := exists_norm_sq_smoothScalarDirichlet_le_integral_chart q α hL hLs
  refine ⟨C, hC, ?_⟩
  intro ψ hψ hψc hψK
  let v := smoothScalarDirichletChartPullback q α hψ hψc (hψK.trans hKs)
  have hs := (hψK.trans hKs).trans (image_mono interior_subset)
  have hvs : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source := by
    intro x hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hψc hs hx
    have hy : e.symm z ∈ (extChartAt I_hs α).target :=
      interior_subset (hLs ⟨z, hψK hz, rfl⟩)
    simpa only [extChartAt_source] using (extChartAt I_hs α).map_target hy
  have hvL : ∀ x ∈ tsupport v.toFun, extChartAt I_hs α x ∈ L := by
    intro x hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hψc hs hx
    have hy : e.symm z ∈ (extChartAt I_hs α).target :=
      interior_subset (hLs ⟨z, hψK hz, rfl⟩)
    rw [(extChartAt I_hs α).right_inv hy]
    exact ⟨z, hψK hz, rfl⟩
  have hi := hbound v hvs hvL
  have he : MeasurePreserving e (modelHaar (E := EuN)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := EuN)⟩
  have himage : e '' L = K := by
    ext z
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    · intro hz
      exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩
  have heq : (∫ y in L, (scalarOnE (I := I_hs) α v.toFun y) ^ 2 +
      ∑ k, (partialDeriv (E := EuN) k (scalarOnE (I := I_hs) α v.toFun) y) ^ 2 ∂modelHaar) =
      ∫ z in K, (ψ z) ^ 2 + ∑ k, (fderiv ℝ ψ z (EuclideanSpace.single k 1)) ^ 2 := by
    rw [← himage, he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding]
    apply setIntegral_congr_fun hL.measurableSet
    intro y hy
    change (scalarOnE (I := I_hs) α (chartPullback I_hs α ψ) y) ^ 2 +
        ∑ k, (partialDeriv (E := EuN) k (scalarOnE (I := I_hs) α (chartPullback I_hs α ψ)) y) ^ 2 = _
    rw [scalarOnE_chartPullback_eq α ψ (interior_subset (hLs hy))]
    simp only [partialDeriv_scalarOnE_chartPullback α ψ (hLs hy)]
    rfl
  exact heq ▸ hi

end

section

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

omit [CompactSpace M] in
theorem smoothScalarDirichletChartPullback_add
    (q : SmoothRiemannianMetric I_hs M) (α : M) {f g : EuStd → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    smoothScalarDirichletChartPullback q α (hf.add hg) (hfc.add hgc)
      ((tsupport_add f g).trans (union_subset hfs hgs)) =
      smoothScalarDirichletChartPullback q α hf hfc hfs +
        smoothScalarDirichletChartPullback q α hg hgc hgs := by
  apply InteriorSmoothScalar.ext
  exact chartPullback_add α f g

omit [CompactSpace M] in
theorem smoothScalarDirichletChartPullback_smul
    (q : SmoothRiemannianMetric I_hs M) (α : M) (c : ℝ) {f : EuStd → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    smoothScalarDirichletChartPullback q α (contDiff_const.mul hf) hfc.mul_left
      ((tsupport_mul_subset_right (f := fun _ => c) (g := f)).trans hfs) =
      c • smoothScalarDirichletChartPullback q α hf hfc hfs := by
  apply InteriorSmoothScalar.ext
  exact chartPullback_const_smul α c f

theorem exists_norm_smoothScalarDirichletChartPullback_le_wkpNorm
    (q : SmoothRiemannianMetric I_hs M) (α : M) {K : Set EuStd}
    (hK : IsCompact K)
    (hKs : K ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Set EuStd}, IsOpen Ω → ∀ (f : EuStd → ℝ)
      (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
      (hfK : tsupport f ⊆ K), tsupport f ⊆ Ω →
      ‖smoothScalarDirichletChartPullback q α hf hfc (hfK.trans hKs)‖ ≤
        C * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_sq_smoothScalarDirichletChartPullback_le q α hK hKs
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro Ω hΩ f hf hfc hfK hfs
  have hI := integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset hΩ K hf hfc hfs
  have h := (hbound f hf hfc hfK).trans (mul_le_mul_of_nonneg_left hI hC)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) ENNReal.toReal_nonneg)).mp
  simpa only [mul_pow, Real.sq_sqrt hC] using h

end

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
