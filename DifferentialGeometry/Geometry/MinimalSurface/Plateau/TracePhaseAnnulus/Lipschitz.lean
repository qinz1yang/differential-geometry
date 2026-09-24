import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus
import Mathlib.Analysis.Calculus.Rademacher

section

noncomputable section

open Set Filter Function MeasureTheory Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem cylinderArea_tracePhaseAnnulus_eq_zero_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) :
    cylinderArea g (tracePhaseAnnulus γ δ) = 0 := by
  have hf := (hψ.comp Complex.imCLM.lipschitz).ae_differentiableAt (μ := volume)
  have ha : ∀ᵐ z ∂volume.restrict unitSquare,
      riemannianAreaDensity g (cylinderLift (tracePhaseAnnulus γ δ)) z = 0 := by
    filter_upwards [ae_restrict_of_ae hf] with z hz
    have hphase : DifferentiableAt ℝ
        (fun w : ℂ => (1 - w.re) * ψ w.im + w.re * w.im) z :=
      (((differentiableAt_const (c := (1 : ℝ))).sub Complex.reCLM.differentiableAt).mul hz).add
        (Complex.reCLM.differentiableAt.mul Complex.imCLM.differentiableAt)
    have heq : cylinderLift (tracePhaseAnnulus γ δ) =
        (fun t : ℝ => γ (t : loopCircle)) ∘
          (fun w : ℂ => (1 - w.re) * ψ w.im + w.re * w.im) :=
      funext (cylinderLift_tracePhaseAnnulus hδ)
    rw [heq]
    exact riemannianAreaDensity_comp_curve_eq_zero g
      (hγ.mdifferentiableAt (by simp)) hphase.mdifferentiableAt
  change (∫ z in unitSquare, riemannianAreaDensity g
    (cylinderLift (tracePhaseAnnulus γ δ)) z) = 0
  rw [integral_congr_ae ha, integral_zero]

omit [FiniteDimensional ℝ E] in
theorem cylinderArea_tracePhaseAnnulusStrip_eq_zero_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t) :
    cylinderArea g (tracePhaseAnnulusStrip γ δ) = 0 := by
  have heq : ∀ᵐ z ∂volume.restrict unitSquare,
      riemannianAreaDensity g (cylinderLift (tracePhaseAnnulusStrip γ δ)) z =
        riemannianAreaDensity g (cylinderLift (tracePhaseAnnulus γ δ)) z := by
    have hmem : ∀ᵐ z ∂volume.restrict unitSquare, z.re ∈ Ioo (0 : ℝ) 1 := by
      filter_upwards [ae_restrict_mem isCompact_unitSquare.measurableSet,
        ae_restrict_of_ae (ae_complex_re_ne 0), ae_restrict_of_ae (ae_complex_re_ne 1)]
        with z hz h0 h1
      exact ⟨lt_of_le_of_ne hz.1.1 h0.symm, lt_of_le_of_ne hz.1.2 h1⟩
    filter_upwards [hmem] with z hz
    exact riemannianAreaDensity_congr g (by
      filter_upwards [(isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz] with w hw
      simp only [cylinderLift, tracePhaseAnnulusStrip,
        projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hw)])
  exact (integral_congr_ae heq).trans
    (cylinderArea_tracePhaseAnnulus_eq_zero_of_lipschitz g hγ hψ hδ)

variable [T3Space M]

theorem exists_spanning_disk_area_eq_of_lipschitz_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {Lγ : ℝ≥0} (hγL : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤
      (Lγ : ℝ≥0∞) * edist s t)
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ)
    (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    {u : C(closedDisk, M)} {L : ℝ≥0}
    (htr : ∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ (ψ t : loopCircle))
    (hL : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  have hper : Periodic (fun t => ψ t - t) 1 := by
    intro t
    change ψ (t + 1) - (t + 1) = ψ t - t
    rw [hp]
    ring
  let δ : loopCircle → ℝ := hper.lift
  have hδ (t : ℝ) : δ (t : loopCircle) = ψ t - t := hper.lift_coe t
  have hδL : LipschitzWith (C + 1) δ := by
    apply loop_lipschitz_of_lift
    exact hψ.sub (LipschitzWith.id)
  obtain ⟨B, hB⟩ := tracePhaseAnnulus_lipschitzOn_strip g hγL hδL
  obtain ⟨A, hA⟩ := tracePhaseAnnulusStrip_lipschitz_of_strip g hB
  let H := tracePhaseAnnulusStrip γ δ
  have hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (A : ℝ≥0∞) * edist p q := hA
  have hU := diskExtension_riemannian_lipschitz g hL
  have hglue (θ : loopCircle) : diskExtension u (AddCircle.toCircle θ : ℂ) = H (0, θ) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change diskExtension u (diskBoundary (t : loopCircle)) =
      tracePhaseAnnulusStrip γ δ (0, (t : loopCircle))
    rw [diskExtension_coe, htr]
    exact (tracePhaseAnnulusStrip_zero hδ
      (σ := affineCircleMap ψ hψ.continuous hp) (fun _ => rfl) (t : loopCircle)).symm
  obtain ⟨Kv, hKv⟩ := attachDiskAnnulus_riemannian_lipschitz g hU hH hglue
  let v : C(closedDisk, M) := ⟨fun z => attachDiskAnnulus (diskExtension u) H z,
    (continuous_of_riemannian_lipschitz g hKv).comp continuous_subtype_val⟩
  refine ⟨v, ⟨?_, Kv, fun z w => hKv z w⟩, ?_⟩
  · ext θ
    change attachDiskAnnulus (diskExtension u) H (AddCircle.toCircle θ : ℂ) = γ θ
    rw [attachDiskAnnulus_boundary]
    exact tracePhaseAnnulusStrip_one θ
  · rw [riemannianDiskArea_eq_of_extension g v
      (attachDiskAnnulus (diskExtension u) H) (fun _ => rfl),
      attachDiskAnnulus_area g hU hH hglue,
      cylinderArea_tracePhaseAnnulusStrip_eq_zero_of_lipschitz g hγ hψ hδ, add_zero]
    rfl

end DifferentialGeometry.Geometry

end

end
