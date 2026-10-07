import DifferentialGeometry.Geometry.HarmonicMap.TwoMapMinimalGraphDifference
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original and alternative Morrey disks supply the full one-sided
elliptic equation for their literal common graph heights. The receiving
sections are the fixed original/alternative source parameters composed with
the fixed graph inverses. All chart and source memberships are retained;
no scalar PDE or conformality of these sections is an input. -/
theorem IMS03Embeddedness.actual_two_morrey_graph_height_difference_on
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ γAlt : freeLoop M}
    {u qAlt : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hqAlt : IsMorreyDisk g γAlt qAlt)
    (QOriginal QAlt : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) u QOriginal)
    (hQAlt : SmoothDiskExtension (E := E) qAlt QAlt)
    (aOriginal aAlt : ℂ) (hbase : QAlt aAlt = QOriginal aOriginal)
    (p : M) (b : Fin (Module.finrank ℝ E) → ℂ) (N : E)
    (hunit : chartGramBilin g p (QOriginal aOriginal) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (QOriginal aOriginal) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
        (fun i => (2 : ℝ) *
          (chartLeadingPlaneProjection g p (QOriginal aOriginal) b v * b i).re) +
        (chartGramBilin g p (QOriginal aOriginal) N v) • N)
    {O S : Set ℂ} (hO : IsOpen O) (hS : IsOpen S) (hSO : S ⊆ O)
    (hSnonempty : S.Nonempty)
    (rOuter rInner : ℂ → ℂ)
    (hrOuter : ContDiffOn ℝ ∞ rOuter S) (hrInner : ContDiffOn ℝ ∞ rInner S)
    (hmapsOuter : MapsTo rOuter S (Metric.ball (0 : ℂ) 1))
    (hmapsInner : MapsTo rInner S (Metric.ball (0 : ℂ) 1))
    (hchartOuter : ∀ y ∈ S, QOriginal (rOuter y) ∈ (chartAt E p).source)
    (hchartInner : ∀ y ∈ S, QAlt (rInner y) ∈ (chartAt E p).source)
    (hrightOuter : ∀ y ∈ S, chartLeadingPlaneProjection g p (QOriginal aOriginal) b
      (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y))) = y)
    (hrightInner : ∀ y ∈ S, chartLeadingPlaneProjection g p (QOriginal aOriginal) b
      (extChartAt 𝓘(ℝ, E) p (QAlt (rInner y))) = y) :
    let xa := extChartAt 𝓘(ℝ, E) p (QOriginal aOriginal)
    let proj := chartLeadingPlaneProjection g p (QOriginal aOriginal) b
    let eta := chartGramBilin g p (QOriginal aOriginal) N
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    let hOuter : ℂ → ℝ := fun y => eta (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) - xa)
    let hInner : ℂ → ℝ := fun y => eta (extChartAt 𝓘(ℝ, E) p (QAlt (rInner y)) - xa)
    ContDiffOn ℝ ∞ hOuter O → ContDiffOn ℝ ∞ hInner O →
    (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (xa + lift (y - proj xa) + hInner y • N) +
        t • (xa + lift (y - proj xa) + hOuter y • N) ∈
          (extChartAt 𝓘(ℝ, E) p).target) →
    ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) O) ∧
      (∀ y ∈ O, (A y).PosDef) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧ ContDiffOn ℝ ∞ c O ∧
      ∀ y ∈ S,
        (∑ i : Fin 2, ∑ j : Fin 2,
          A y i j * fderiv ℝ (fderiv ℝ (hOuter - hInner)) y
            (![1, Complex.I] i) (![1, Complex.I] j)) +
          (∑ i : Fin 2, beta y i * fderiv ℝ (hOuter - hInner) y (![1, Complex.I] i)) +
            c y * (hOuter - hInner) y = 0 := by
  intro xa proj eta lift hOuter hInner hhOuter hhInner hsegment
  obtain ⟨V₁, _, hV₁, hQV₁⟩ := hQOriginal.2
  obtain ⟨V₂, _, hV₂, hQV₂⟩ := hQAlt.2
  have hQB₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ QOriginal (Metric.ball (0 : ℂ) 1) :=
    hQV₁.mono (Metric.ball_subset_closedBall.trans hV₁)
  have hQB₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ QAlt (Metric.ball (0 : ℂ) 1) :=
    hQV₂.mono (Metric.ball_subset_closedBall.trans hV₂)
  let s₁ := Metric.ball (0 : ℂ) 1 ∩ QOriginal ⁻¹' (chartAt E p).source
  let s₂ := Metric.ball (0 : ℂ) 1 ∩ QAlt ⁻¹' (chartAt E p).source
  have hs₁ : IsOpen s₁ :=
    hQB₁.continuousOn.isOpen_inter_preimage Metric.isOpen_ball (chartAt E p).open_source
  have hs₂ : IsOpen s₂ :=
    hQB₂.continuousOn.isOpen_inter_preimage Metric.isOpen_ball (chartAt E p).open_source
  exact two_original_maps_graph_height_difference_on g p (QOriginal aOriginal) b N
    hunit hprojN hsplit (a₁ := aOriginal) (a₂ := aAlt) rfl hbase hs₁ hs₂
    (hQB₁.mono inter_subset_left) (hQB₂.mono inter_subset_left)
    (fun z hz => hu.conformal_of_extension hQOriginal z hz.1)
    (fun z hz => hqAlt.conformal_of_extension hQAlt z hz.1)
    (fun z hz => hu.tension_eq_zero_of_extension hQOriginal z hz.1)
    (fun z hz => hqAlt.tension_eq_zero_of_extension hQAlt z hz.1)
    (fun _ hz => hz.2) (fun _ hz => hz.2) hO hS hSO hSnonempty
    hOuter hInner hhOuter hhInner rOuter rInner hrOuter hrInner
    (fun y hy => ⟨hmapsOuter hy, hchartOuter y hy⟩)
    (fun y hy => ⟨hmapsInner hy, hchartInner y hy⟩)
    hrightOuter hrightInner (fun _ _ => rfl) (fun _ _ => rfl) hsegment
