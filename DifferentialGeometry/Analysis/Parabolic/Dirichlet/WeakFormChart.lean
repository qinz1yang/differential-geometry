import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakFormIntegration
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalWeakForm
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDivergence
import DifferentialGeometry.Analysis.Integration.Lp.Pairing
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Geometry.Operator.WithBoundary.VossWeyl
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

section

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

private theorem continuous_setIntegral_weight_mul_lp (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ContinuousOn c (closure Ω)) (f : Lp ℝ 2 (volume.restrict Ω)) :
    Continuous (fun g : Lp ℝ 2 (volume.restrict Ω) => ∫ z in Ω, f z * c z * g z) :=
  continuous_integral_weight_mul_lp c
    (hc.memLp_top_of_subset_isCompact hΩc hΩ subset_closure) f

private theorem integrableOn_weight_mul_lp (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ContinuousOn c (closure Ω)) (f g : Lp ℝ 2 (volume.restrict Ω)) :
    IntegrableOn (fun z => f z * c z * g z) Ω volume :=
  integrable_weight_mul_lp c (hc.memLp_top_of_subset_isCompact hΩc hΩ subset_closure) f g

end

private theorem integral_mul_sum_sub_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {d : ℕ}
    (U ρ B ψ W : α → ℝ) (A V p : Fin d → α → ℝ)
    (hV : ∀ j, V j =ᵐ[μ] p j) (hW : W =ᵐ[μ] ψ)
    (hint : ∀ j, Integrable (fun z => U z * (ρ z * A j z) * V j z) μ)
    (hbint : Integrable (fun z => U z * (B z * ρ z) * W z) μ) :
    (∫ z, U z * ((∑ j, A j z * p j z) * ρ z - B z * ρ z * ψ z) ∂μ) =
      (∑ j, ∫ z, U z * (ρ z * A j z) * V j z ∂μ) -
        ∫ z, U z * (B z * ρ z) * W z ∂μ := by
  calc
    _ = ∫ z, (∑ j, U z * (ρ z * A j z) * V j z) - U z * (B z * ρ z) * W z ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hV, hW] with z hz hzW
      simp only [hz, hzW, mul_sub, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · ring
    _ = _ := by
      rw [integral_sub (integrable_finsetSum _ (fun j _ => hint j)) hbint,
        integral_finsetSum _ (fun j _ => hint j)]

private theorem integral_bilinear_eq_of_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {d : ℕ}
    (ρ U W R S : α → ℝ) (a : ℝ) (D V p B : Fin d → α → ℝ)
    (A : Fin d → Fin d → α → ℝ)
    (hV : ∀ j, V j =ᵐ[μ] p j) (hS : S =ᵐ[μ] W) (hR : R =ᵐ[μ] U)
    (hint : ∀ i j, Integrable (fun z => D i z * (ρ z * A i j z) * V j z) μ)
    (hbint : ∀ i, Integrable (fun z => D i z * (B i z * ρ z) * S z) μ) :
    -(∑ i, ∑ j, ∫ z, D i z * (ρ z * A i j z) * V j z ∂μ) +
      (∑ i, ∫ z, D i z * (B i z * ρ z) * S z ∂μ) -
      (∫ z, R z * (ρ z * a) * S z ∂μ) =
    -(∑ i, ∫ z, D i z * ((∑ j, A i j z * p j z) * ρ z - B i z * ρ z * W z) ∂μ) -
      (∫ z, ρ z * U z * (a * W z) ∂μ) := by
  have hsplit (i) := integral_mul_sum_sub_eq μ (D i) ρ (B i) W S (A i) V p hV hS
    (hint i) (hbint i)
  have hmass : (∫ z, R z * (ρ z * a) * S z ∂μ) = (∫ z, ρ z * U z * (a * W z) ∂μ) := by
    apply integral_congr_ae
    filter_upwards [hR, hS] with z hzu hzt
    rw [hzu, hzt]
    ring
  rw [hmass]
  congr 1
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hsplit i)
  rw [Finset.sum_sub_distrib] at hsum
  rw [hsum]
  ring

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

omit [T2Space M] [CompactSpace M] in
private theorem adjoint_test_eq_zero_of_notMem_tsupport
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a : ℝ) (v : SmoothScalarDirichlet q) {x : M} (hx : x ∉ tsupport v.toFun) :
    ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
      tangentSectionAction (I := I_hs) X v.toFun x -
      divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
      a * v.toFun x = 0 := by
  have hv := image_eq_zero_of_notMem_tsupport hx
  have hΔ := image_eq_zero_of_notMem_tsupport
    (fun hxΔ => hx (tsupport_Δ_g_with_boundary_subset h v.smooth v.interior_support hxΔ))
  have hgrad : (gradGWithBoundarySection (I := I_hs) q v.smooth v.interior_support) x = 0 :=
    Function.notMem_support.mp
      (fun hxg => hx (support_grad_g_with_boundary_section_subset q v.smooth v.interior_support hxg))
  have ha : tangentSectionAction (I := I_hs) X v.toFun x = 0 := by
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_hs) q X]
    change q.inner x (X x)
      ((gradGWithBoundarySection (I := I_hs) q v.smooth v.interior_support) x) = 0
    rw [hgrad]
    exact (q.inner x (X x)).map_zero
  rw [hv, hΔ, ha]
  ring

omit [T2Space M] [CompactSpace M] in
private theorem notMem_tsupport_of_mem_chart_target_sdiff_interior
    {q : SmoothRiemannianMetric I_hs M} (α : M) (v : SmoothScalarDirichlet q)
    {y : EuN} (hy : y ∈ (extChartAt I_hs α).target \ interior (extChartAt I_hs α).target) :
    (extChartAt I_hs α).symm y ∉ tsupport v.toFun := by
  intro hys
  have hsrc := (extChartAt I_hs α).map_target hy.1
  rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
  have hi := extChartAt_mem_interior_target_of_isInteriorPoint (I := I_hs) α hsrc
    (v.interior_support hys)
  rw [(extChartAt I_hs α).right_inv hy.1] at hi
  exact hy.2 hi

theorem integral_adjoint_test_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a : ℝ) (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    (∫ x, u x *
      (ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
        tangentSectionAction (I := I_hs) X v.toFun x -
        divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
        a * v.toFun x) ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) h α y * u ((extChartAt I_hs α).symm y) *
          (chartVossWeylLaplacian (I := I_hs) h α v.toFun ((extChartAt I_hs α).symm y) -
            (∑ i : Fin (Module.finrank ℝ EuN), chartCoeffOnE (I := I_hs) α X i y *
              partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α v.toFun) y) -
            localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm y) *
              scalarOnE (I := I_hs) α v.toFun y - a * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) := by
  let b : M → ℝ := fun x => ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
    tangentSectionAction (I := I_hs) X v.toFun x -
    divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
    a * v.toFun x
  have hb : Continuous b :=
    (((Δ_g_with_boundary_continuous (I := I_hs) h v.smooth v.interior_support).sub
      (tangentSectionAction_continuous_of_interior_support X v.smooth v.interior_support)).sub
        ((leviCivita_divergence_contMDiff h X).continuous.mul v.smooth.continuous)).sub
          (v.smooth.continuous.const_mul a)
  change (∫ x, u x * b x ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) = _
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.integral_eq_integral_chartDensity_of_support_in_chart
    h α (f := fun x => u x * b x) ((Lp.stronglyMeasurable u).measurable.mul hb.measurable) (fun x hx => by
      rw [show b x = 0 from adjoint_test_eq_zero_of_notMem_tsupport h X a v
        (fun hxs => hx (hv hxs)), mul_zero])]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I_hs) α) interior_subset
      (fun y hy => by
        rw [show b ((extChartAt I_hs α).symm y) = 0 from
          adjoint_test_eq_zero_of_notMem_tsupport h X a v
            (notMem_tsupport_of_mem_chart_target_sdiff_interior α v hy), mul_zero, mul_zero])]
  apply setIntegral_congr_fun isOpen_interior.measurableSet
  intro y hy
  have hsrc := (extChartAt I_hs α).map_target (interior_subset hy)
  rw [extChartAt_source_eq_chartAt_source (I := I_hs)] at hsrc
  have hright := (extChartAt I_hs α).right_inv (interior_subset hy)
  have hi : (extChartAt I_hs α).symm y ∈ (I_hs).interior M := by
    apply ((I_hs).isInteriorPoint_iff_of_mem_atlas (M := M) (n := ∞)
      (by simp) (chart_mem_atlas (EuclideanHalfSpace n) α) hsrc).2
    change extChartAt I_hs α ((extChartAt I_hs α).symm y) ∈
      interior (extChartAt I_hs α).target
    rwa [hright]
  have hdiv : divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X
        ((extChartAt I_hs α).symm y) =
      localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm y) := by
    rw [← divergence_g_eq_leviCivita_divergence_of_isInteriorPoint (I := I_hs) h X hi,
      ← divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint h X hi,
      voss_weyl_divergence_with_boundary_formula h α X hsrc,
      localDivergenceWithin_eq_localDivergence_of_isInteriorPoint h α X hsrc hi]
  dsimp only [b]
  rw [voss_weyl_laplacian_with_boundary_formula h α v.smooth v.interior_support hsrc hi,
    tangentSectionAction_chartLocal α X v.smooth hsrc (hright.symm ▸ hy), hdiv, hright]
  simp only [chartDensityOnE, scalarOnE, chartCoeffOnE]
  ring

theorem integral_mul_smooth_test_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    {c : M → ℝ} (hc : Measurable c) :
    (∫ x, c x * (u x * v.toFun x)
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) h α y *
          (c ((extChartAt I_hs α).symm y) *
            (u ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y))
        ∂(modelHaar (E := EuN)) := by
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.integral_eq_integral_chartDensity_of_support_in_chart
    h α (f := fun x => c x * (u x * v.toFun x)) (hc.mul ((Lp.stronglyMeasurable u).measurable.mul v.smooth.continuous.measurable))
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hxs => hx (hv hxs)), mul_zero, mul_zero])]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I_hs) α) interior_subset
      (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport
          (notMem_tsupport_of_mem_chart_target_sdiff_interior α v hy), mul_zero, mul_zero, mul_zero])

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem scalarOnE_chartPullback_eq
    (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) y =
      ψ (toEuclidean (E := EuN) y) := by
  have hsrc := (extChartAt I_hs α).map_target hy
  rw [extChartAt_source] at hsrc
  rw [scalarOnE, DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_apply_of_mem α ψ hsrc,
    (extChartAt I_hs α).right_inv hy]

omit [T2Space M] [CompactSpace M] [IsManifold I_hs ∞ M] in
private theorem partialDeriv_scalarOnE_chartPullback
    (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ interior (extChartAt I_hs α).target)
    (i : Fin (Module.finrank ℝ EuN)) :
    partialDeriv (E := EuN) i (scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ)) y =
      fderiv ℝ ψ (toEuclidean (E := EuN) y) (EuclideanSpace.single i 1) := by
  have heq : scalarOnE (I := I_hs) α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) =ᶠ[𝓝 y]
        ψ ∘ (toEuclidean (E := EuN)) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact scalarOnE_chartPullback_eq α ψ (interior_subset hz)
  rw [partialDeriv, heq.fderiv_eq, (toEuclidean (E := EuN)).comp_right_fderiv,
    ContinuousLinearMap.comp_apply, chartModelBasis_apply]
  simp

omit [T2Space M] [CompactSpace M] in
private theorem chartVossWeylLaplacian_chartPullback
    (h : SmoothRiemannianMetric I_hs M) (α : M) (ψ : EuStd → ℝ) {y : EuN}
    (hy : y ∈ interior (extChartAt I_hs α).target) :
    chartVossWeylLaplacian (I := I_hs) h α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ)
        ((extChartAt I_hs α).symm y) =
      (∑ i : Fin (Module.finrank ℝ EuN),
        fderiv ℝ (fun z : EuStd =>
          (∑ j : Fin (Module.finrank ℝ EuN),
            chartInvGramOnE (I := I_hs) h α i j ((toEuclidean (E := EuN)).symm z) *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) *
            chartDensityOnE (I := I_hs) h α ((toEuclidean (E := EuN)).symm z))
          (toEuclidean (E := EuN) y) (EuclideanSpace.single i 1)) /
        chartDensityOnE (I := I_hs) h α y := by
  rw [chartVossWeylLaplacian, (extChartAt I_hs α).right_inv (interior_subset hy)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let F : EuStd → ℝ := fun z =>
    (∑ j : Fin (Module.finrank ℝ EuN),
      chartInvGramOnE (I := I_hs) h α i j ((toEuclidean (E := EuN)).symm z) *
        fderiv ℝ ψ z (EuclideanSpace.single j 1)) *
      chartDensityOnE (I := I_hs) h α ((toEuclidean (E := EuN)).symm z)
  have heq : chartVossWeylIntegrand (I := I_hs) h α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) i =ᶠ[𝓝 y]
        F ∘ (toEuclidean (E := EuN)) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    simp only [chartVossWeylIntegrand, gradChartCoeffOnE, Function.comp_apply, F,
      ContinuousLinearEquiv.symm_apply_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [partialDeriv_scalarOnE_chartPullback α ψ hz j]
  rw [partialDeriv, heq.fderiv_eq, (toEuclidean (E := EuN)).comp_right_fderiv,
    ContinuousLinearMap.comp_apply, chartModelBasis_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rfl

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem integral_mul_chartPullback_eq_integral_euclidean
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (U : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (ψ : EuStd → ℝ)
    (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hveq : v.toFun = DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ)
    {c : M → ℝ} (hc : Measurable c) :
    (∫ x, c x * (U x * v.toFun x)
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ z in toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) h α ((toEuclidean (E := EuN)).symm z) *
          (c ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
            (U ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * ψ z)) := by
  let e := toEuclidean (E := EuN)
  have he : MeasurePreserving e (modelHaar (E := EuN)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := EuN)⟩
  rw [integral_mul_smooth_test_eq_integral_chart h α U v hv hc]
  rw [he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding
    (fun z => chartDensityOnE (I := I_hs) h α (e.symm z) *
      (c ((extChartAt I_hs α).symm (e.symm z)) *
        (U ((extChartAt I_hs α).symm (e.symm z)) * ψ z)))
    (interior (extChartAt I_hs α).target)]
  apply setIntegral_congr_fun isOpen_interior.measurableSet
  intro y hy
  dsimp only
  rw [hveq, scalarOnE_chartPullback_eq α ψ (interior_subset hy)]
  simp only [e, ContinuousLinearEquiv.symm_apply_apply]

theorem integral_adjoint_chartPullback_eq_integral_euclidean
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) (a : ℝ)
    (U : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : SmoothScalarDirichlet q) (ψ : EuStd → ℝ)
    (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hveq : v.toFun = DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    (∫ x, U x *
      (ΔGWithBoundary (I := I_hs) h v.smooth v.interior_support x -
        tangentSectionAction (I := I_hs) X v.toFun x -
        divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) h) X x * v.toFun x -
        a * v.toFun x) ∂(riemannianVolumeMeasure (I := I_hs) (M := M) h)) =
      ∫ z in e '' interior (extChartAt I_hs α).target,
        ρ z * U (x z) *
          ((∑ i : Fin (Module.finrank ℝ EuN),
            fderiv ℝ (fun z' : EuStd =>
              (∑ j : Fin (Module.finrank ℝ EuN),
                A i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ z') z
                (EuclideanSpace.single i 1)) / ρ z -
            (∑ i : Fin (Module.finrank ℝ EuN), B i z *
              fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
            localDivergence (I := I_hs) h α X (x z) * ψ z - a * ψ z) := by
  intro e x ρ A B
  have he : MeasurePreserving e (modelHaar (E := EuN)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := EuN)⟩
  rw [integral_adjoint_test_eq_integral_chart h α X a U v hv]
  rw [he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding
    (fun z => ρ z * U (x z) *
      ((∑ i : Fin (Module.finrank ℝ EuN),
        fderiv ℝ (fun z' : EuStd =>
          (∑ j : Fin (Module.finrank ℝ EuN),
            A i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ z') z
            (EuclideanSpace.single i 1)) / ρ z -
        (∑ i : Fin (Module.finrank ℝ EuN), B i z *
          fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
        localDivergence (I := I_hs) h α X (x z) * ψ z - a * ψ z))
    (interior (extChartAt I_hs α).target)]
  apply setIntegral_congr_fun isOpen_interior.measurableSet
  intro y hy
  dsimp only
  rw [hveq, chartVossWeylLaplacian_chartPullback h α ψ hy,
    scalarOnE_chartPullback_eq α ψ (interior_subset hy)]
  simp_rw [partialDeriv_scalarOnE_chartPullback α ψ hy]
  simp only [e, x, ρ, A, B, ContinuousLinearEquiv.symm_apply_apply]

open DifferentialGeometry.Analysis.Sobolev.Chart

theorem dirichletWeakFormCompl_apply_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let v := fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hψ hψc
        (hψs.trans (subset_closure.trans hΩs)))) =
      -(∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ((∑ j, A i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ z -
          B i z * ρ z * ψ z)) - ∫ z in Ω, ρ z * v z * (a * ψ z) := by
  intro e ρ A B v
  let test := smoothScalarDirichletChartPullback q α hψ hψc
    (hψs.trans (subset_closure.trans hΩs))
  have hsrc : tsupport test.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source := by
    intro x hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hψc
      ((hψs.trans (subset_closure.trans hΩs)).trans (image_mono interior_subset)) hx
    have hz' := (hψs.trans (subset_closure.trans hΩs)) hz
    obtain ⟨z', hz', heq⟩ := hz'
    subst z
    have hm := (extChartAt I_hs α).map_target (interior_subset hz')
    simpa only [ContinuousLinearEquiv.symm_apply_apply, extChartAt_source] using hm
  rw [dirichletWeakFormCompl_apply_eq_integral_adjoint,
    integral_adjoint_chartPullback_eq_integral_euclidean h α X a
      (H1ComplDirichletToLp q u) test ψ hsrc rfl]
  refine (Sobolev.Euclidean.integral_adjoint_eq_integral_of_tsupport_subset
    ((toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior).measurableSet
      (subset_closure.trans hΩs) hψs v ρ
      (fun z => localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm (e.symm z)))
      (fun _ => a) A B).trans ?_
  exact integral_chart_adjoint_sub_potential_eq_neg_sum_integral q h α hΩ hΩc hΩs X u
    (b := fun _ => a) continuousOn_const hψ hψc hψs


private theorem dirichletLocalWeakPartialLp_smooth_chartPullback_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {ψ : EuStd → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω)
    (i : Fin (Module.finrank ℝ EuN)) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
      (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hψ hψc
        (hψs.trans (subset_closure.trans hΩs)))) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
  rw [← h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet q α hΩ hΩc hΩs hψ hψc hψs]
  apply dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae
  · exact ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable
  · exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn
      hΩ (hψ.of_le (by simp)).contDiffOn i

private theorem chartRestrictionLp_smooth_chartPullback_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {ψ : EuStd → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q
        (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hψ hψc
          (hψs.trans (subset_closure.trans hΩs))))) : EuStd → ℝ) =ᵐ[volume.restrict Ω] ψ := by
  rw [← h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet q α hΩ hΩc hΩs hψ hψc hψs]
  exact (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2 _).trans
      (chartInverse_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs _ hψs)


omit [T2Space M] [CompactSpace M] in
private theorem chart_coefficients_continuousOn
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    ContinuousOn ρ (closure Ω) ∧
      (∀ i j, ContinuousOn (fun z => ρ z * A i j z) (closure Ω)) ∧
      (∀ i, ContinuousOn (fun z => B i z * ρ z) (closure Ω)) := by
  intro e ρ A B
  have hy {z : EuStd} (hz : z ∈ closure Ω) : e.symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs hz
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hρ : ContinuousOn ρ (closure Ω) :=
    ((chartDensityOnE_contDiffOn (I := I_hs) h α).comp
      e.symm.contDiff.contDiffOn (fun _ hz => hy hz)).continuousOn
  refine ⟨hρ, ?_, ?_⟩
  · intro i j
    exact hρ.mul (((chartInvGramOnE_contDiffOn (I := I_hs) h α i j).comp
      e.symm.contDiff.contDiffOn (fun _ hz => hy hz)).continuousOn)
  · intro i
    exact (((chartCoeffOnE_contDiffOn (I := I_hs) α X i).comp
      e.symm.contDiff.contDiffOn (fun _ hz => hy hz)).continuousOn).mul hρ


private def dirichletChartWeakForm
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) (a : ℝ)
    (u v : H1ComplDirichlet q) : ℝ :=
  let e := toEuclidean (E := EuN)
  let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
  let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
  let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  let R := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  show ℝ from
    -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) * D j v z) +
    (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * R v z) -
      (∫ z in Ω, R u z * (ρ z * a) * R v z)


private theorem continuous_dirichletChartWeakForm
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) (a : ℝ)
    (u : H1ComplDirichlet q) : Continuous (dirichletChartWeakForm q h α hΩ hΩc hΩs X a u) := by
  obtain ⟨hρ, hA, hB⟩ := chart_coefficients_continuousOn h α hΩs X
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  let R := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  unfold dirichletChartWeakForm
  apply Continuous.sub
  · apply Continuous.add
    · apply Continuous.neg
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact (continuous_setIntegral_weight_mul_lp hΩ.measurableSet hΩc (hA i j) (D i u)).comp
        (D j).continuous
    · apply continuous_finsetSum
      intro i _
      exact (continuous_setIntegral_weight_mul_lp hΩ.measurableSet hΩc (hB i) (D i u)).comp
        R.continuous
  · exact (continuous_setIntegral_weight_mul_lp hΩ.measurableSet hΩc (hρ.mul continuousOn_const)
      (R u)).comp R.continuous


private theorem dirichletChartWeakForm_smooth_chartPullback
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) (a : ℝ)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let v := fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    dirichletChartWeakForm q h α hΩ hΩc hΩs X a u
      (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hψ hψc
        (hψs.trans (subset_closure.trans hΩs)))) =
      -(∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ((∑ j, A i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ z -
          B i z * ρ z * ψ z)) - ∫ z in Ω, ρ z * v z * (a * ψ z) := by
  intro e ρ A B v
  let test := smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hψ hψc
    (hψs.trans (subset_closure.trans hΩs)))
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  let R := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  have hD (j) : (D j test : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1) :=
    dirichletLocalWeakPartialLp_smooth_chartPullback_coeFn q α hΩ hΩc hΩs hψ hψc hψs j
  have hR : (R test : EuStd → ℝ) =ᵐ[volume.restrict Ω] ψ :=
    chartRestrictionLp_smooth_chartPullback_coeFn q α hΩ hΩc hΩs hψ hψc hψs
  have hRu : (R u : EuStd → ℝ) =ᵐ[volume.restrict Ω] v :=
    chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) 2 _
  obtain ⟨hρ, hA, hB⟩ := chart_coefficients_continuousOn h α hΩs X
  exact integral_bilinear_eq_of_ae (volume.restrict Ω) ρ v ψ (R u) (R test) a
    (fun i => D i u) (fun j => D j test)
    (fun j z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) B A hD hR hRu
    (fun i j => integrableOn_weight_mul_lp hΩ.measurableSet hΩc (hA i j) _ _)
    (fun i => integrableOn_weight_mul_lp hΩ.measurableSet hΩc (hB i) _ _)


private theorem dirichletWeakFormCompl_chartPullback_eq_dirichletChartWeakForm
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : Sobolev.Euclidean.MemWkp 1 2 ψ Ω) (hψs : tsupport ψ ⊆ Ω) :
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs) =
    dirichletChartWeakForm q h α hΩ hΩc hΩs X a u
      (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs) := by
  obtain ⟨φ, hφ, hφc, hφs, _, ht⟩ :=
    exists_smooth_tendsto_h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs
  have hseq (j : ℕ) :
      dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
        (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α (hφ j) (hφc j)
          ((hφs j).trans (subset_closure.trans hΩs)))) =
      dirichletChartWeakForm q h α hΩ hΩc hΩs X a u
        (smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α (hφ j) (hφc j)
          ((hφs j).trans (subset_closure.trans hΩs)))) :=
    (dirichletWeakFormCompl_apply_eq_integral_chart h α hΩ hΩc hΩs X a Bx hX hCg hequiv
      Cv hCv0 hCvtop hvol u (hφ j) (hφc j) (hφs j)).trans
      (dirichletChartWeakForm_smooth_chartPullback q h α hΩ hΩc hΩs X a u
        (hφ j) (hφc j) (hφs j)).symm
  apply tendsto_nhds_unique
    (((dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u).continuous.tendsto _).comp ht)
  convert ((continuous_dirichletChartWeakForm q h α hΩ hΩc hΩs X a u).tendsto _).comp ht using 1
  funext j
  exact hseq j


theorem dirichletWeakFormCompl_apply_h1ComplDirichletChartPullback_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : Sobolev.Euclidean.MemWkp 1 2 ψ Ω) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u w =
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) * D j w z) +
        (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * ψ z) -
          (∫ z in Ω, ρ z * U z * (a * ψ z)) := by
  intro e ρ A B U D w
  rw [dirichletWeakFormCompl_chartPullback_eq_dirichletChartWeakForm]
  let R := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  have hRu : (R u : EuStd → ℝ) =ᵐ[volume.restrict Ω] U :=
    chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) 2 _
  have hRw : (R w : EuStd → ℝ) =ᵐ[volume.restrict Ω] ψ :=
    (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 _).trans
      (chartInverse_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hψ hψs)
  change -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) * D j w z) +
    (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * R w z) -
      (∫ z in Ω, R u z * (ρ z * a) * R w z) = _
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hRw] with z hz
    rw [hz]
  · apply integral_congr_ae
    filter_upwards [hRu, hRw] with z hzu hzw
    rw [hzu, hzw]
    ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
