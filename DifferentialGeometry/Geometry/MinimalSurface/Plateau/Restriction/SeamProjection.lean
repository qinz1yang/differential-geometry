import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Geometry.HarmonicMap.RegularLeadingPlane
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold ComplexConjugate

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original Morrey disk supplies a normalized original-metric projection
and graph splitting for the actual reflected seam chart. Conformality is used
only for the original smooth extension inside the disk. The derivative of the
arbitrary seam chart is handled by the chain rule, not by a conformality claim. -/
theorem IMS03Embeddedness.actual_morrey_seam_projection_and_split
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (QOriginal : ℂ → M) (hQ : SmoothDiskExtension (E := E) u QOriginal)
    (hd3 : Module.finrank ℝ E = 3)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχzero : (0 : ℂ) ∈ χ.source) (hχinside : χ 0 ∈ Metric.ball (0 : ℂ) 1)
    (hrank : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (χ 0)))
    (p : M) (hp : QOriginal (χ 0) ∈ (chartAt E p).source) :
    let b : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p QOriginal i (χ 0)
    let Q := chartGramBilin g p (QOriginal (χ 0))
    let proj := chartLeadingPlaneProjection g p (QOriginal (χ 0)) b
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    (proj.comp (fderiv ℝ
      (fun z => extChartAt 𝓘(ℝ, E) p (QOriginal (χ (conj z)))) 0)).IsInvertible ∧
    ∃ N : E, Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) := by
  intro b Q proj lift
  obtain ⟨N₀, _, hDN₀, hQN₀⟩ := hQ.2
  have hQball : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ QOriginal
      (Metric.ball (0 : ℂ) 1) :=
    hQN₀.mono (fun _ hz => hDN₀ (Metric.ball_subset_closedBall hz))
  let s : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ QOriginal ⁻¹' (chartAt E p).source
  have hs : IsOpen s :=
    hQball.continuousOn.isOpen_inter_preimage Metric.isOpen_ball (chartAt E p).open_source
  have ha : χ 0 ∈ s := ⟨hχinside, hp⟩
  have hder : (show ℂ →L[ℝ] E from
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) QOriginal (χ 0)) =
      (show ℂ →L[ℝ] E from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (χ 0)) := by
    ext v
    exact congrArg (fun L => L v)
      ((hQ.eventuallyEq_diskExtension hχinside).mfderiv_eq
        (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
  have hiQ : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) QOriginal (χ 0)) := by
    have hpoint (v : ℂ) := congrArg (fun L : ℂ →L[ℝ] E => L v) hder
    intro v w hvw
    apply hrank
    exact (hpoint v).symm.trans (hvw.trans (hpoint w))
  obtain ⟨hnorm, N, hNN, hPN, hsplit⟩ :=
    chartLeadingPlaneProjection_regular_normalization_and_split g hd3 hs
      (hQball.mono inter_subset_left)
      (fun z hz => hu.conformal_of_extension hQ z hz.1) ha
      (fun _ hz => hz.2) hiQ
  refine ⟨?_, N, hNN, hPN, hsplit⟩
  let ψ := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  have hψzero : (0 : ℂ) ∈ ψ.source := by
    refine ⟨mem_univ _, ?_⟩
    change conj (0 : ℂ) ∈ χ.source
    simpa only [map_zero] using hχzero
  have hcenter : ψ 0 = χ 0 := by
    change χ (conj (0 : ℂ)) = χ 0
    rw [map_zero]
  have hψd : DifferentiableAt ℝ ψ 0 :=
    ((ψ.contMDiffOn.contDiffOn.contDiffAt
      (ψ.open_source.mem_nhds hψzero)).differentiableAt (by simp))
  have hψbij := Analysis.bijective_fderiv_of_partialDiffeomorph ψ hψzero
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ ψ 0).toLinearMap hψbij).toContinuousLinearEquiv
  have hψinv : (fderiv ℝ ψ 0).IsInvertible := by
    refine ⟨L, ?_⟩
    ext v
    rfl
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (QOriginal z)
  have hXd : DifferentiableAt ℝ X (χ 0) :=
    (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hp).comp (χ 0)
      (hQball.contMDiffAt (Metric.isOpen_ball.mem_nhds hχinside))).contDiffAt).differentiableAt
      (by simp)
  have hXd' : DifferentiableAt ℝ X (ψ 0) := by rw [hcenter]; exact hXd
  have hchain : fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (QOriginal (χ (conj z)))) 0 =
      (fderiv ℝ X (χ 0)).comp (fderiv ℝ ψ 0) := by
    have hd := (hXd'.hasFDerivAt.comp 0 hψd.hasFDerivAt).fderiv
    rw [hcenter] at hd
    exact hd
  rw [hchain, ← ContinuousLinearMap.comp_assoc, hnorm, ContinuousLinearMap.id_comp]
  exact hψinv
