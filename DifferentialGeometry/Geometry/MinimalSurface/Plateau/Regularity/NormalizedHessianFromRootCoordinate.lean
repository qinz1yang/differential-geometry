import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.NormalizedHessian
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.RootCoordinateSecondDerivative
import DifferentialGeometry.Analysis.Calculus.Inverse.PuncturedHessian

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- The same literal root coordinate of the original Morrey leading projection
carries its normal height to a `C²` height at the branch center. The actual
leading-projection ROOT2 producer supplies the forward Hessian bound, and the
inverse adaptation supplies the inverse bound. Neither bound is an input.
The supplied disk, gradient coefficient, normal direction and coordinate remain
unchanged throughout the composition. -/
theorem DiskRegularity.ConsumerAudit.morrey_normalized_height_hessian_bound_of_root_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    {m : ℕ} (hm : 1 ≤ m) {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient (diskExtension u a) (diskExtension u) i z) =
        (z - a) ^ m • B z)
    {N : E}
    (hN : chartLeadingPlaneProjection g (diskExtension u a) (diskExtension u a)
      (B a) N = 0)
    (e : OpenPartialHomeomorph ℂ ℂ) (hae : a ∈ e.source) (hea : e a = 0)
    (he1 : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei1 : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (he2 : ContDiffOn ℝ 2 (e : ℂ → ℂ) (e.source \ {a}))
    (hei2 : ContDiffOn ℝ 2 (e.symm : ℂ → ℂ) (e.target \ {(0 : ℂ)}))
    (heliteral :
      let p := diskExtension u a
      let proj := chartLeadingPlaneProjection g p p (B a)
      let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
      (e : ℂ → ℂ) = (fun z : ℂ => if z = a then 0 else
        (z - a) * Complex.exp
          (Complex.log (((m + 1 : ℕ) : ℂ) * (F z - F a) / (z - a) ^ (m + 1)) /
            ((m + 1 : ℕ) : ℂ))))
    (hepower :
      let p := diskExtension u a
      let proj := chartLeadingPlaneProjection g p p (B a)
      let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
      ∀ z ∈ e.source, F z = F a + (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) :
    let p := diskExtension u a
    let Q := chartGramBilin g p p
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
    let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p p (B a) (X z)
    let H : ℂ → ℝ := fun w => Q N (X (e.symm w) - X a)
    (∀ w ∈ e.target, F (e.symm w) = F a + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) ∧
      ContDiffAt ℝ 2 H 0 ∧ fderiv ℝ H 0 = 0 ∧
      fderiv ℝ (fderiv ℝ H) 0 = 0 ∧
      ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
        ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m := by
  obtain ⟨r, C, hr, hC, _, hbound⟩ :=
    DiskRegularity.ConsumerAudit.morrey_root_coordinate_second_derivative_bound
      hu ha hB hBne hfactor e hae heliteral
  have hforward : ∃ C > 0, ∀ᶠ z in 𝓝[≠] a,
      ‖fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) z‖ ≤ C := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)),
      (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] a, z ≠ a)] with z hz hza
    exact (hbound z hz hza).2
  have hinverse := DifferentialGeometry.Analysis.exists_eventually_norm_second_fderiv_symm_le
    e hae hea he1 hei1 he2 hei2 hforward
  exact DiskRegularity.ConsumerAudit.morrey_normalized_height_hessian_bound
    hu ha hm hB hBne hfactor hN e hae hea hei1 hei2 hinverse hepower
