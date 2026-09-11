import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCompactness
import DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Tensor.Coordinates

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

omit [T2Space M] [CompactSpace M] in
private theorem fderiv_chartInverse_eq_inner_grad
    (g : SmoothRiemannianMetric I_hs M) (α : M) {f : M → ℝ}
    (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) {z : EuStd}
    (hz : z ∈ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    fderiv ℝ (fun y => f ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm y))) z (EuclideanSpace.single i 1) =
      g.inner ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (gradFun g f ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
        (chartBasisVecFiber (I := I_hs) α i
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) := by
  obtain ⟨y, hy, rfl⟩ := hz
  have hyt := interior_subset hy
  have hxs := (extChartAt I_hs α).map_target hyt
  rw [inner_gradFun]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt α (hf.mdifferentiable (by simp)).mdifferentiableAt]
  · change fderiv ℝ ((scalarOnE (I := I_hs) α f) ∘
        (toEuclidean (E := EuN)).symm) _ _ = _
    rw [(toEuclidean (E := EuN)).symm.comp_right_fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply,
      (extChartAt I_hs α).right_inv hyt]
    exact congrArg _ (chartModelBasis_apply i).symm
  · simpa only [ContinuousLinearEquiv.symm_apply_apply,
      extChartAt_source_eq_chartAt_source] using hxs
  · simpa only [ContinuousLinearEquiv.symm_apply_apply,
      (extChartAt I_hs α).right_inv hyt] using hy

omit [T2Space M] [CompactSpace M] in
private theorem contDiffOn_chartInverse
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    {Ω : Set EuStd}
    (hΩs : Ω ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target) :
    ContDiffOn ℝ ∞ (fun z => f ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm z))) Ω := by
  apply (scalarOnE_contDiffOn α hf).comp
    (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hΩs hz
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy

omit [T2Space M] [CompactSpace M] in
private theorem exists_chartBasis_norm_bound
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Ω,
      Real.sqrt (g.inner ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (chartBasisVecFiber (I := I_hs) α i
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
        (chartBasisVecFiber (I := I_hs) α i
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) ≤ C := by
  let e := toEuclidean (E := EuN)
  let D : Set EuN := e.symm '' closure Ω
  have hD : IsCompact D := hΩc.image e.symm.continuous
  have hDs : D ⊆ (extChartAt I_hs α).target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hΩs hz
    simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy
  have hsrc {y : EuN} (hy : y ∈ (extChartAt I_hs α).target) :
      (extChartAt I_hs α).symm y ∈
        (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have h := (extChartAt I_hs α).map_target hy
    rwa [extChartAt_source] at h
  have hc : ContinuousOn (fun y => Real.sqrt
      (chartGramMatrix g α ((extChartAt I_hs α).symm y) i i)) D :=
    Real.continuous_sqrt.comp_continuousOn
      ((chartGramMatrix_entry_contMDiffOn g α i i).continuousOn.comp
        ((continuousOn_extChartAt_symm (I := I_hs) α).mono hDs)
        (fun y hy => hsrc (hDs hy)))
  obtain ⟨B, hB⟩ := hD.bddAbove_image hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hB ⟨e.symm z, ⟨z, subset_closure hz, rfl⟩, rfl⟩).trans (le_max_left _ _)

private def smoothLocalPartial
    {g : SmoothRiemannianMetric I_hs M} (α : M)
    (i : Fin (Module.finrank ℝ EuN)) (s : SmoothScalarDirichlet g) : EuStd → ℝ :=
  fun z => fderiv ℝ (fun y => s.toFun ((extChartAt I_hs α).symm
    ((toEuclidean (E := EuN)).symm y))) z (EuclideanSpace.single i 1)

private theorem exists_smoothLocalPartial_memLp_bound
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalarDirichlet g,
      MemLp (smoothLocalPartial α i s) 2 (volume.restrict Ω) ∧
      eLpNorm (smoothLocalPartial α i s) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal (C * ‖s‖) := by
  have hΩt := hΩs.trans (image_mono interior_subset)
  let R := chartRestrictionLp g α hΩ.measurableSet hΩc hΩt 2
  obtain ⟨C, hC, hbound⟩ := exists_chartBasis_norm_bound g α hΩc hΩt i
  refine ⟨C * ‖R‖, mul_nonneg hC (norm_nonneg R), ?_⟩
  intro s
  let F : M → ℝ := fun x => Real.sqrt (g.inner x (gradFun g s.toFun x) (gradFun g s.toFun x))
  have hF : MemLp F 2 (riemannianVolumeMeasure I_hs M g) :=
    sqrt_g_inner_grad_smoothScalarDirichlet_memLp_two s
  let U := R (hF.toLp F)
  have hU : (U : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => F ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) :=
    (chartRestrictionLp_coeFn g α hΩ.measurableSet hΩc hΩt 2 (hF.toLp F)).trans
      (ae_chartInverse_of_ae g α hΩ.measurableSet hΩc hΩt (MemLp.coeFn_toLp hF))
  have hUnorm : ‖U‖ ≤ ‖R‖ * ‖s‖ := by
    apply (R.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg R)
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg s)
      (eLpNorm_sqrt_g_inner_grad_smoothScalarDirichlet_le_norm s)
  have hpart : ∀ z ∈ Ω, ‖smoothLocalPartial α i s z‖ ≤
      C * F ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    intro z hz
    rw [smoothLocalPartial, Real.norm_eq_abs,
      fderiv_chartInverse_eq_inner_grad g α s.smooth (hΩs (subset_closure hz)) i]
    apply (DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt
      g _ _ _).trans
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound z hz) (Real.sqrt_nonneg _)
  have hc : ContinuousOn (smoothLocalPartial α i s) Ω :=
    ((contDiffOn_chartInverse α s.smooth (subset_closure.trans hΩt)).continuousOn_fderiv_of_isOpen
      hΩ (by simp)).clm_apply continuousOn_const
  have hae : ∀ᵐ z ∂(volume.restrict Ω), ‖smoothLocalPartial α i s z‖ ≤ ‖C * U z‖ := by
    filter_upwards [hU, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    rw [hz]
    exact (hpart z hzΩ).trans (le_abs_self _)
  have hm : MemLp (smoothLocalPartial α i s) 2 (volume.restrict Ω) :=
    ((Lp.memLp U).const_mul C).of_le (hc.aestronglyMeasurable hΩ.measurableSet) hae
  refine ⟨hm, ?_⟩
  have hn : ‖hm.toLp (smoothLocalPartial α i s)‖ ≤ ‖C • U‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [MemLp.coeFn_toLp hm, Lp.coeFn_smul C U, hae] with z hz₁ hz₂ hz₃
    simpa only [hz₁, hz₂, Pi.smul_apply, smul_eq_mul] using hz₃
  have hn' : ‖hm.toLp (smoothLocalPartial α i s)‖ ≤ C * ‖R‖ * ‖s‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at hn
    exact hn.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hUnorm hC)
  rw [← Lp.enorm_toLp hm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn'

private def smoothLocalPartialLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) (s : SmoothScalarDirichlet g) :
    Lp ℝ 2 (volume.restrict Ω) :=
  ((exists_smoothLocalPartial_memLp_bound g α hΩ hΩc hΩs i).choose_spec.2 s).1.toLp _

private theorem smoothLocalPartialLp_coeFn
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) (s : SmoothScalarDirichlet g) :
    (smoothLocalPartialLp g α hΩ hΩc hΩs i s : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      smoothLocalPartial α i s :=
  MemLp.coeFn_toLp _

private def smoothLocalPartialLinear
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    SmoothScalarDirichlet g →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun := smoothLocalPartialLp g α hΩ hΩc hΩs i
  map_add' s t := by
    apply Lp.ext
    filter_upwards [smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i (s + t),
      smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i s,
      smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i t,
      Lp.coeFn_add (smoothLocalPartialLp g α hΩ hΩc hΩs i s)
        (smoothLocalPartialLp g α hΩ hΩc hΩs i t),
      ae_restrict_mem hΩ.measurableSet] with z hz₁ hz₂ hz₃ hz₄ hz
    simp only [hz₁, hz₄, Pi.add_apply, hz₂, hz₃]
    have hd (v : SmoothScalarDirichlet g) :=
      ((contDiffOn_chartInverse α v.smooth
        (subset_closure.trans (hΩs.trans (image_mono interior_subset)))) z hz).contDiffAt
          (hΩ.mem_nhds hz)
    change fderiv ℝ ((fun y => s.toFun ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm y))) +
      (fun y => t.toFun ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm y)))) z _ = _
    rw [fderiv_add ((hd s).differentiableAt (by simp)) ((hd t).differentiableAt (by simp))]
    rfl
  map_smul' c s := by
    apply Lp.ext
    filter_upwards [smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i (c • s),
      smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i s,
      Lp.coeFn_smul c (smoothLocalPartialLp g α hΩ hΩc hΩs i s),
      ae_restrict_mem hΩ.measurableSet] with z hz₁ hz₂ hz₃ hz
    simp only [hz₁, hz₃, Pi.smul_apply, hz₂, RingHom.id_apply]
    have hd := ((contDiffOn_chartInverse α s.smooth
      (subset_closure.trans (hΩs.trans (image_mono interior_subset)))) z hz).contDiffAt
        (hΩ.mem_nhds hz)
    change fderiv ℝ (c • (fun y => s.toFun ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm y)))) z _ = _
    rw [fderiv_const_smul ((hd).differentiableAt (by simp))]
    rfl

private def smoothLocalPartialCLM
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    SmoothScalarDirichlet g →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (smoothLocalPartialLinear g α hΩ hΩc hΩs i).mkContinuous
    (exists_smoothLocalPartial_memLp_bound g α hΩ hΩc hΩs i).choose (fun s => by
      change ‖smoothLocalPartialLp g α hΩ hΩc hΩs i s‖ ≤ _
      rw [smoothLocalPartialLp, Lp.norm_toLp]
      exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (exists_smoothLocalPartial_memLp_bound g α hΩ hΩc hΩs i).choose_spec.1
          (norm_nonneg s))
        ((exists_smoothLocalPartial_memLp_bound g α hΩ hΩc hΩs i).choose_spec.2 s).2)

def dirichletLocalWeakPartialLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    H1ComplDirichlet g →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (smoothLocalPartialCLM g α hΩ hΩc hΩs i).extend
    (smoothToH1ComplDirichlet g)

theorem dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) (s : SmoothScalarDirichlet g) :
    (dirichletLocalWeakPartialLp g α hΩ hΩc hΩs i (smoothToH1ComplDirichlet g s) : EuStd → ℝ)
      =ᵐ[volume.restrict Ω] fun z => fderiv ℝ (fun y => s.toFun ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm y))) z (EuclideanSpace.single i 1) := by
  have hu : IsUniformInducing (smoothToH1ComplDirichlet g) := by
    change IsUniformInducing ((↑) : SmoothScalarDirichlet g →
      UniformSpace.Completion (SmoothScalarDirichlet g))
    exact UniformSpace.Completion.isUniformInducing_coe _
  rw [dirichletLocalWeakPartialLp, ContinuousLinearMap.extend_eq _
    (denseRange_smoothToH1ComplDirichlet g) hu]
  exact smoothLocalPartialLp_coeFn g α hΩ hΩc hΩs i s

theorem hasWeakPartialDeriv_dirichletLocalWeakPartialLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) (u : H1ComplDirichlet g) :
    DeGiorgi.HasWeakPartialDeriv i (dirichletLocalWeakPartialLp g α hΩ hΩc hΩs i u)
      (fun z => H1ComplDirichletToLp g u
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω := by
  classical
  have hΩt := hΩs.trans (image_mono interior_subset)
  let R := chartRestrictionLp g α hΩ.measurableSet hΩc hΩt 2
  let T := dirichletLocalWeakPartialLp g α hΩ hΩc hΩs i
  let F : (M → ℝ) → EuStd → ℝ := fun f z =>
    f ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    ((denseRange_smoothToH1ComplDirichlet g) u)
  choose s hs using hv
  have hslim : Tendsto (fun k => smoothToH1ComplDirichlet g (s k)) atTop (𝓝 u) := by
    simpa only [hs] using hvlim
  have hvs (v : SmoothScalarDirichlet g) :
      (R (smoothToLpDirichlet g v) : EuStd → ℝ) =ᵐ[volume.restrict Ω] F v.toFun :=
    (chartRestrictionLp_coeFn g α hΩ.measurableSet hΩc hΩt 2 (smoothToLpDirichlet g v)).trans
      (ae_chartInverse_of_ae g α hΩ.measurableSet hΩc hΩt
        (MemLp.coeFn_toLp v.memLp_two))
  have hvu : (R (H1ComplDirichletToLp g u) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      F (H1ComplDirichletToLp g u) :=
    chartRestrictionLp_coeFn g α hΩ.measurableSet hΩc hΩt 2 (H1ComplDirichletToLp g u)
  have hvlim : Tendsto (fun k => R (smoothToLpDirichlet g (s k))) atTop
      (𝓝 (R (H1ComplDirichletToLp g u))) := by
    simpa only [ContinuousLinearMap.comp_apply, Function.comp_def,
      H1ComplDirichletToLp_smoothToH1ComplDirichlet] using
      (R.comp (H1ComplDirichletToLp g)).continuous.continuousAt.tendsto.comp hslim
  have htlim : Tendsto (fun k => T (smoothToH1ComplDirichlet g (s k))) atTop (𝓝 (T u)) :=
    T.continuous.continuousAt.tendsto.comp hslim
  apply DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_eLpNorm
    (p := 2) (by norm_num) i
    (u_n := fun k => F (s k).toFun)
    (g_n := fun k => T (smoothToH1ComplDirichlet g (s k)))
  · exact fun k => (Lp.memLp (R (smoothToLpDirichlet g (s k)))).ae_eq (hvs (s k))
  · exact fun k => Lp.memLp _
  · exact (Lp.memLp (R (H1ComplDirichletToLp g u))).ae_eq hvu
  · exact Lp.memLp _
  · intro k φ hφ hφc hφs
    have hweak := DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn
      hΩ ((contDiffOn_chartInverse α (s k).smooth (subset_closure.trans hΩt)).of_le
        (by simp)) i
    rw [hweak φ hφ hφc hφs]
    congr 1
    apply integral_congr_ae
    filter_upwards [dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn
      g α hΩ hΩc hΩs i (s k)] with z hz
    rw [hz]
  · have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun k => R (smoothToLpDirichlet g (s k))) (R (H1ComplDirichletToLp g u))).mp hvlim
    convert h using 1
    funext k
    apply eLpNorm_congr_ae
    filter_upwards [hvs (s k), hvu] with z hz₁ hz₂
    simp only [Pi.sub_apply, hz₁, hz₂, F]
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun k => T (smoothToH1ComplDirichlet g (s k))) (T u)).mp htlim

theorem memWkp_chartInverse_H1ComplDirichletToLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp 1 2
      (fun z => H1ComplDirichletToLp g u
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω := by
  apply DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mpr
  constructor
  · have hΩt := hΩs.trans (image_mono interior_subset)
    exact (Lp.memLp (chartRestrictionLp g α hΩ.measurableSet hΩc hΩt 2
      (H1ComplDirichletToLp g u))).ae_eq
      (chartRestrictionLp_coeFn g α hΩ.measurableSet hΩc hΩt 2 (H1ComplDirichletToLp g u))
  · intro i
    exact ⟨dirichletLocalWeakPartialLp g α hΩ hΩc hΩs i u, Lp.memLp _,
      hasWeakPartialDeriv_dirichletLocalWeakPartialLp g α hΩ hΩc hΩs i u⟩

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
