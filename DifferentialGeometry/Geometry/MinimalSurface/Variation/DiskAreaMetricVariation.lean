import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricIntegral
import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Topology.StandardModel

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [hBoundary : I.Boundaryless]

omit [T2Space Q] hBoundary in
theorem riemannianAreaDensity_pullbackMetricCross
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (U : ℂ → A) (z : ℂ) :
    riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z =
        (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [riemannianAreaDensity, tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] hBoundary in
private theorem diskMapPartial_comp_diffeomorphCross
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
    (φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (U : ℂ → Q) (z v : ℂ)
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) I U z) :
    diskMapPartial (E := E) (M := A) (fun w => φ (U w)) z v =
      mfderiv I 𝓘(ℝ, E) (φ : Q → A) (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) := by
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => φ (U w)) z v =
    (mfderiv I 𝓘(ℝ, E) (φ : Q → A) (U z)) ((mfderiv 𝓘(ℝ, ℂ) I U z) v)
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, E) (φ (U z)) => L v)
    (mfderiv_comp z (φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU)

omit [T2Space Q] hBoundary in
private theorem inner_pullbackMetricCross_comp_diffeomorphCross
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q) (x : Q)
    (a b : TangentSpace 𝓘(ℝ, E) (φ x)) :
    (Diffeomorph.pullbackMetricCross g φ.symm).inner (φ x) a b =
      g.inner x (mfderiv 𝓘(ℝ, E) I (φ.symm : A → Q) (φ x) a)
        (mfderiv 𝓘(ℝ, E) I (φ.symm : A → Q) (φ x) b) := by
  rw [Diffeomorph.pullbackMetricCross_inner, φ.symm_apply_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] hBoundary in
private theorem mfderiv_symm_apply_mfderiv_apply
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
    (φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (p : Q) (X : TangentSpace I p) :
    mfderiv 𝓘(ℝ, E) I (φ.symm : A → Q) (φ p) (mfderiv I 𝓘(ℝ, E) (φ : Q → A) p X) = X := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, E) (φ : Q → A) p :=
    φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, E) I (φ.symm : A → Q) (φ p) :=
    φ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hid : (fun y => φ.symm (φ y)) = id := funext fun y => φ.symm_apply_apply y
  have hcomp := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := (φ : Q → A)) (g := (φ.symm : A → Q)) p h2 h1
  simp only [Function.comp_def] at hcomp
  rw [hid, mfderiv_id] at hcomp
  exact (congrArg (fun (L : TangentSpace I p →L[ℝ] TangentSpace I p) => L X) hcomp).symm

variable {D : RealTimeInterval} {t₀ : ℝ}

omit [T2Space Q] hBoundary in
theorem hasDerivAt_integral_riemannianAreaDensity_metricFamily
    [SigmaCompactSpace Q]
    (c : Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {g : ℝ → SmoothRiemannianMetric I Q} {hG : MetricFamilySmoothOn D g}
    (ht₀ : D.regular ∈ 𝓝 t₀)
    {U : ℂ → Q} {s : Set ℂ} (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U s)
    (hDs : Metric.closedBall (0 : ℂ) 1 ⊆ s) :
    let K : ℂ → ℝ := fun z =>
      ((deriv (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))) t₀) +
        (deriv (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
          (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)) t₀)) / 2
    (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0 ∧
        (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
          (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
            (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)) →
    IntegrableOn K (Metric.closedBall (0 : ℂ) 1) ∧
      HasDerivAt (fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) 1,
          riemannianAreaDensity (g t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1, K z) t₀ := by
  intro K hconf
  let φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let g' : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) c.Q :=
    fun t => Diffeomorph.pullbackMetricCross (g t) φ.symm
  let U' : ℂ → c.Q := fun z => φ (U z)
  have hg' : MetricFamilySmoothOn D g' :=
    MetricFamilySmoothOn.of_pullback hG g' (fun x => φ.symm x) φ.symm.contMDiff
      (fun t x v w => Diffeomorph.pullbackMetricCross_inner (g t) φ.symm x v w)
  have hU'sm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U' s :=
    φ.contMDiff.comp_contMDiffOn hU
  let u' : C(Metric.closedBall (0 : ℂ) 1, c.Q) :=
    ⟨fun z => U' (z : ℂ), (hU'sm.mono hDs).continuousOn.domRestrict⟩
  have hExt : SmoothDiskExtension (u := u') U' := ⟨fun _ => rfl, s, hs, hDs, hU'sm⟩
  have hconf' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (g' t₀) U' z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hconf z hz
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℂ) I U z :=
      ((hU z (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp)
    have hpair (v w : ℂ) : (g' t₀).inner (U' z) (diskMapPartial U' z v) (diskMapPartial U' z w) =
        (g t₀).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) (mfderiv 𝓘(ℝ, ℂ) I U z w) := by
      have hv : diskMapPartial U' z v =
          mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) :=
        diskMapPartial_comp_diffeomorphCross φ U z v hdiff
      have hw : diskMapPartial U' z w =
          mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) (U z) (mfderiv 𝓘(ℝ, ℂ) I U z w) :=
        diskMapPartial_comp_diffeomorphCross φ U z w hdiff
      rw [hv, hw, inner_pullbackMetricCross_comp_diffeomorphCross φ (g t₀) (U z)]
      rw [mfderiv_symm_apply_mfderiv_apply φ (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v),
        mfderiv_symm_apply_mfderiv_apply φ (U z) (mfderiv 𝓘(ℝ, ℂ) I U z w)]
    have h1' := hpair 1 Complex.I
    have h2' := hpair 1 1
    have h3' := hpair Complex.I Complex.I
    rw [diskMapPartial, diskMapPartial] at h1'
    exact ⟨h1'.trans h1, (h2'.trans h2).trans h3'.symm⟩
  obtain ⟨hint', hderiv'⟩ :=
    SmoothDiskExtension.hasDerivAt_area_metric (u := u') (U := U') hExt hg' ht₀ hconf'
  have hpoint : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      diskMapMetricVariationDensity g' t₀ U' z = K z := by
    intro z hz
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℂ) I U z :=
      ((hU z (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp)
    have hpair (r : ℝ) (v w : ℂ) : (g' r).inner (U' z) (diskMapPartial U' z v)
        (diskMapPartial U' z w) =
        (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) (mfderiv 𝓘(ℝ, ℂ) I U z w) := by
      have hv : diskMapPartial U' z v =
          mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v) :=
        diskMapPartial_comp_diffeomorphCross φ U z v hdiff
      have hw : diskMapPartial U' z w =
          mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) (U z) (mfderiv 𝓘(ℝ, ℂ) I U z w) :=
        diskMapPartial_comp_diffeomorphCross φ U z w hdiff
      rw [hv, hw, inner_pullbackMetricCross_comp_diffeomorphCross φ (g r) (U z)]
      rw [mfderiv_symm_apply_mfderiv_apply φ (U z) (mfderiv 𝓘(ℝ, ℂ) I U z v),
        mfderiv_symm_apply_mfderiv_apply φ (U z) (mfderiv 𝓘(ℝ, ℂ) I U z w)]
    have h1 : (fun r : ℝ => (g' r).inner (U' z) (diskMapPartial U' z 1) (diskMapPartial U' z 1)) =
        (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))) := funext fun r => hpair r 1 1
    have h2 : (fun r : ℝ => (g' r).inner (U' z) (diskMapPartial U' z Complex.I)
        (diskMapPartial U' z Complex.I)) =
        (fun r : ℝ => (g r).inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
          (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)) := funext fun r => hpair r Complex.I Complex.I
    rw [diskMapMetricVariationDensity, h1, h2]
  have hInt : IntegrableOn K (Metric.closedBall (0 : ℂ) 1) := by
    refine hint'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hpoint z hz
  refine ⟨hInt, ?_⟩
  have hfun : (fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) 1,
      riemannianAreaDensity (g t) U z) =
      (fun t : ℝ => riemannianDiskArea (g' t) u') := by
    funext t
    rw [riemannianDiskArea_eq_of_extension (g' t) u' U' hExt.1, riemannianArea]
    refine setIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
    rw [riemannianAreaDensity_pullbackMetricCross (g t) φ.symm U' z]
    congr 1
    funext w
    simp only [U']
    exact (φ.symm_apply_apply (U w)).symm
  have hIntEq : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity g' t₀ U' z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, K z := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hpoint z hz
  rw [hIntEq, ← hfun] at hderiv'
  exact hderiv'


end DifferentialGeometry.Geometry
