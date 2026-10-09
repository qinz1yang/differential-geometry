import DifferentialGeometry.Analysis.Complex.BranchedCoordinate
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientBranchExpansion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

/-- The supplied literal coordinate of the original Morrey leading projection has
bounded second derivative off the center. The original disk, gradient order,
coefficient and coordinate are inputs throughout; no new coordinate is chosen. -/
theorem DiskRegularity.ConsumerAudit.morrey_root_coordinate_second_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun k => chartComplexGradient (E := E)
        (diskExtension u a) (diskExtension u) k z) = (z - a) ^ m • B z) :
    let p := diskExtension u a
    let proj := chartLeadingPlaneProjection g p p (B a)
    let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
    ∀ e : OpenPartialHomeomorph ℂ ℂ, a ∈ e.source →
      (e : ℂ → ℂ) = (fun z : ℂ => if z = a then 0 else
        (z - a) * Complex.exp
          (Complex.log (((m + 1 : ℕ) : ℂ) * (F z - F a) / (z - a) ^ (m + 1)) /
            ((m + 1 : ℕ) : ℂ))) →
      ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ball a r ⊆ e.source ∧
        ∀ z ∈ ball a r, z ≠ a →
          DifferentiableAt ℝ (fderiv ℝ (e : ℂ → ℂ)) z ∧
            ‖fderiv ℝ (fderiv ℝ (e : ℂ → ℂ)) z‖ ≤ C := by
  dsimp only
  let p := diskExtension u a
  let proj := chartLeadingPlaneProjection g p p (B a)
  let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
  intro e hsource he
  have hsrc : diskExtension u a ∈ (chartAt E p).source := mem_chart_source E p
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u)
      (ball (0 : ℂ) 1) := hu.smoothInterior.of_le (by norm_num)
  obtain ⟨T, _, hTa, rT, hrT, _, _, hT, hF, hDF⟩ :=
    chartComplexGradient_leading_projection_c1_factor (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc hB hBne hfactor
  obtain ⟨Cv, rv, hCv, hrv, _, _, hvalue⟩ :=
    chartComplexGradient_leading_projection_expansion (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc hB hBne hfactor
  obtain ⟨Cd, rd, hCd, hrd, _, _, hderiv⟩ :=
    chartComplexGradient_leading_projection_fderiv_error (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc hB hBne hfactor
  let R := min rT (min rv rd)
  have hR : 0 < R := lt_min hrT (lt_min hrv hrd)
  have hRT : ball a R ⊆ ball a rT := ball_subset_ball (min_le_left _ _)
  have hRv : ball a R ⊆ ball a rv :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hRd : ball a R ⊆ ball a rd :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hDFR : ∀ z ∈ ball a R, z ≠ a →
      fderiv ℝ F z = (T z).comp
        ((z - a) ^ ((m + 1) - 1) • ContinuousLinearMap.id ℝ ℂ) := by
    intro z hz _
    simpa only [Nat.add_sub_cancel] using hDF z (hRT hz)
  have hvalueR : ∀ z ∈ ball a R,
      ‖F z - F a - (z - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ ≤
        Cv * ‖z - a‖ ^ ((m + 1) + 1) := by
    intro z hz
    simpa only [Nat.add_assoc] using hvalue z (hRv hz)
  have hderivR : ∀ z ∈ ball a R, ∀ v : ℂ,
      ‖fderiv ℝ F z v - (z - a) ^ ((m + 1) - 1) * v‖ ≤
        Cd * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
    intro z hz v
    simpa only [Nat.add_sub_cancel] using hderiv z (hRd hz) v
  obtain ⟨ρ, C, hρ, _, hC, hbound⟩ :=
    DifferentialGeometry.Analysis.exists_bounded_second_fderiv_complex_power_root_coordinate
      (F := F) (T := T) (Nat.succ_pos m) hR hCv.le hCd.le
      (hF.mono hRT) (hT.mono hRT) hTa hDFR hvalueR hderivR
  obtain ⟨s, hs, hse⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hsource)
  refine ⟨min ρ s, C, lt_min hρ hs, hC,
    (ball_subset_ball (min_le_right _ _)).trans hse, ?_⟩
  intro z hz hza
  rw [he]
  exact hbound z ((ball_subset_ball (min_le_left _ _)) hz) hza
