import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Isometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.HarmonicGradient
import DifferentialGeometry.Geometry.Operator.Laplacian.Isometry
import DifferentialGeometry.Geometry.Metric.CylinderAxial

noncomputable section

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem laplacian_height_eq_zero_of_initial_cylinder
    {D : RealTimeInterval} (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S) {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a₀))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ x (v : TangentSpace (I.prod 𝓘(ℝ)) x),
      0 ≤ ricciTensor (S.base.metric a) x v v)
    (g : SmoothRiemannianMetric I M) (hinitial : S.base.metric a = cylinderMetric g) :
    ∀ t ∈ Icc a b, ∀ x,
      laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) Prod.snd x = 0 := by
  let _ : NeZero (Module.finrank ℝ (E × ℝ)) := ⟨by
    rw [Module.finrank_prod, Module.finrank_self]; omega⟩
  intro t ht x
  let Phi := cylinderAxialDiffeomorph (I := I) (M := M) (2 * x.2) (-1) (by norm_num)
  have hinit : Diffeomorph.pullbackMetricCross (S.base.metric a) Phi = S.base.metric a := by
    rw [hinitial, Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact pullback_cylinderMetric_cylinderAxialDiffeomorph g _ _ _
  have hpull := ricci_flow_pullback_eq_on_slab_of_initial_isometry S hS hbuffer hab
    hslab hreg hcomplete hcurv
    (fun y v => by simpa only [zero_mul] using hRic y v)
    Phi hinit t ht
  apply laplacian_eq_zero_of_isometry_antisymmetry (S.base.metric t) Phi hpull
    contMDiff_snd (c := 2 * x.2)
  · funext y
    simp only [Function.comp_apply, Phi, cylinderAxialDiffeomorph_apply, neg_mul, one_mul]
    rfl
  · apply Prod.ext
    · rfl
    · change 2 * x.2 + (-1) * x.2 = x.2
      ring

theorem normGradSqFun_height_eq_one_of_initial_cylinder
    {D : RealTimeInterval} (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S) {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a₀))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ Icc a b, ∀ x (v : TangentSpace (I.prod 𝓘(ℝ)) x),
      0 ≤ ricciTensor (S.base.metric t) x v v)
    (g : SmoothRiemannianMetric I M) (hinitial : S.base.metric a = cylinderMetric g) :
    ∀ t ∈ Icc a b, ∀ x, normGradSqFun (S.base.metric t) Prod.snd x = 1 := by
  let _ : NeZero (Module.finrank ℝ (E × ℝ)) := ⟨by
    rw [Module.finrank_prod, Module.finrank_self]; omega⟩
  let _ : CompleteSpace (E × ℝ) := FiniteDimensional.complete ℝ (E × ℝ)
  have hharmonic := laplacian_height_eq_zero_of_initial_cylinder S hS hbuffer hab hslab hreg hcomplete hcurv
    (hRic a ⟨le_rfl, hab.le⟩) g hinitial
  obtain ⟨K, hK, hcurv⟩ := hcurv
  have hsub : Icc a b ⊆ Icc a₀ b := fun t ht => ⟨hbuffer.le.trans ht.1, ht.2⟩
  have hcompleteA : RiemannianMetricComplete (S.base.metric a) :=
    complete_of_ricBound S hS hslab hreg
      (K := (Module.finrank ℝ (E × ℝ) : ℝ) ^ 2 * Real.sqrt K) (by positivity)
      (fun t ht x v => ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hcurv t ht x))
      hcomplete ⟨hbuffer.le, hab.le⟩
  apply normGradSqFun_eq_on_slab_of_harmonic_of_ricci_nonnegative S hS hab.le
    (fun t ht => hreg ⟨hbuffer.trans_le ht.1, ht.2⟩) hcompleteA
    ⟨K, hK, fun t ht => hcurv t (hsub ht)⟩
    (fun t ht x v => by simpa only [zero_mul] using hRic t ht x v)
    contMDiff_snd hharmonic
  intro x
  rw [hinitial, normGradSqFun_def, gradFun_height_eq_cylinderAxis, cylinderMetric_axis_unit]

theorem covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder
    {D : RealTimeInterval} (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S) {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a₀))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ Icc a b, ∀ x (v : TangentSpace (I.prod 𝓘(ℝ)) x),
      0 ≤ ricciTensor (S.base.metric t) x v v)
    (g : SmoothRiemannianMetric I M) (hinitial : S.base.metric a = cylinderMetric g) :
    ∀ t ∈ Icc a b, ∀ x,
      (LeviCivita (S.base.metric t)).toFun
        (fun y => gradFun (S.base.metric t) Prod.snd y) x = 0 := by
  have hharmonic := laplacian_height_eq_zero_of_initial_cylinder S hS hbuffer hab hslab hreg
    hcomplete hcurv (hRic a ⟨le_rfl, hab.le⟩) g hinitial
  have hnorm := normGradSqFun_height_eq_one_of_initial_cylinder S hS hbuffer hab hslab hreg
    hcomplete hcurv hRic g hinitial
  intro t ht x
  apply covariantDerivative_gradFun_eq_zero_of_harmonic_of_locally_constant_norm
    (S.base.metric t) contMDiff_snd x (Filter.Eventually.of_forall (hnorm t ht))
  · apply Filter.Eventually.of_forall
    intro y
    rw [← laplacian_levi_eq]
    exact hharmonic t ht y
  · exact hRic t ht x _

end DifferentialGeometry.PDE.RicciFlow
