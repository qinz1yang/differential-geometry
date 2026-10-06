import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus
import DifferentialGeometry.Topology.LoopSpace.RadialProfile

set_option autoImplicit false
noncomputable section

open Set Filter Function MeasureTheory Manifold Metric
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- The original-metric area of the relative phase pasting is the area of the same disk.
The radial change is only Lipschitz, including at zero. The annular contribution is
computed from the actual smooth curve and phase, not supplied as an assumption. -/
theorem riemannianArea_relative_tracePhase_pasting
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u F : ℂ → M} {Cu CF : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (Cu : ℝ≥0∞) * edist z w)
    (hF : ∀ z w, riemannianEDistOf g (F z) (F w) ≤ (CF : ℝ≥0∞) * edist z w)
    {R : loopCircle → ℝ} {CR : ℝ≥0} (hR : LipschitzWith CR R)
    (hRlo : ∀ θ, 1 / 2 ≤ R θ) (hRhi : ∀ θ, R θ ≤ 1)
    {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ψ t - t)
    (htrace : ∀ t : ℝ, u (AddCircle.toCircle (t : loopCircle) : ℂ) =
      γ (ψ t : loopCircle))
    {CH : ℝ≥0}
    (hH : ∀ p q : ℝ × loopCircle,
      riemannianEDistOf g (tracePhaseAnnulusStrip γ δ p) (tracePhaseAnnulusStrip γ δ q) ≤
        (CH : ℝ≥0∞) * edist p q)
    (hinner : ∀ z : ℂ, ‖z‖ ≤ R (polarAnnulusCoordinates z).2 →
      F z = u (radialProfileInv R z))
    (houter : ∀ z : ℂ, ¬ ‖z‖ ≤ R (polarAnnulusCoordinates z).2 →
      F z = tracePhaseAnnulusStrip γ δ (polarAnnulusCoordinates z)) :
    riemannianArea g F (closedBall (0 : ℂ) 1) =
      riemannianArea g u (closedBall (0 : ℂ) 1) := by
  let S : Set ℂ := {z | ‖z‖ ≤ R (polarAnnulusCoordinates z).2}
  let H : ℝ × loopCircle → M := tracePhaseAnnulusStrip γ δ
  let A : ℂ → M := attachDiskAnnulus u H
  have hpos (θ : loopCircle) : 0 < R θ := lt_of_lt_of_le (by norm_num) (hRlo θ)
  have hSc : IsClosed S := isClosed_radialProfile_star hR hRlo
  have hSD : S ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr (hz.trans (hRhi _))
  have hhalfS : closedBall (0 : ℂ) (1 / 2) ⊆ S := by
    intro z hz
    exact (mem_closedBall_zero_iff.mp hz).trans (hRlo _)
  have hinnerArea : riemannianArea g F S =
      riemannianArea g u (closedBall (0 : ℂ) 1) := by
    have hcv := riemannianArea_precomp g (s := closedBall (0 : ℂ) 1) hF
      (radialProfile_lipschitz hR hRlo hRhi) (radialProfileInv_lipschitz hR hRlo)
      measurableSet_closedBall (fun z _ => radialProfileInv_radialProfile hpos z)
    rw [radialProfile_image_closedBall hpos] at hcv
    refine hcv.symm.trans (riemannianArea_congr_on_closedBall g ?_)
    intro z hz
    change F (radialProfile R z) = u z
    have hmem : radialProfile R z ∈ S := by
      change radialProfile R z ∈ {w : ℂ | ‖w‖ ≤ R (polarAnnulusCoordinates w).2}
      rw [← radialProfile_image_closedBall hpos]
      exact mem_image_of_mem _ hz
    rw [hinner _ hmem, radialProfileInv_radialProfile hpos]
  have hglue (θ : loopCircle) : u (AddCircle.toCircle θ : ℂ) = H (0, θ) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [htrace]
    change γ (ψ t : loopCircle) = tracePhaseAnnulusStrip γ δ (0, (t : loopCircle))
    rw [tracePhaseAnnulusStrip_eq_of_mem (left_mem_Icc.mpr zero_le_one)]
    simp only [tracePhaseAnnulus, sub_zero, one_mul, hδ]
    rw [← AddCircle.coe_add]
    congr 2
    ring
  have hzero : cylinderArea g H = 0 :=
    cylinderArea_tracePhaseAnnulusStrip_eq_zero g hγ hψ hδ
  obtain ⟨CA, hA⟩ := attachDiskAnnulus_riemannian_lipschitz g hu hH hglue
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hAi : IntegrableOn (riemannianAreaDensity g A) (closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g hA _
  have hFi : IntegrableOn (riemannianAreaDensity g F) (closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g hF _
  have hhalfD : closedBall (0 : ℂ) (1 / 2) ⊆ closedBall (0 : ℂ) 1 :=
    closedBall_subset_closedBall (by norm_num)
  have hshell : riemannianArea g A
      (closedBall (0 : ℂ) 1 \ closedBall (0 : ℂ) (1 / 2)) = 0 := by
    change (∫ z in closedBall (0 : ℂ) 1 \ closedBall (0 : ℂ) (1 / 2),
      riemannianAreaDensity g A z) = 0
    rw [setIntegral_sdiff measurableSet_closedBall hAi hhalfD]
    change riemannianArea g (attachDiskAnnulus u H) (closedBall (0 : ℂ) 1) -
      riemannianArea g (attachDiskAnnulus u H) (closedBall (0 : ℂ) (1 / 2)) = 0
    rw [attachDiskAnnulus_area g hu hH hglue, attachDiskAnnulus_inner_area g hu H,
      hzero, add_zero, sub_self]
  have hFA : EqOn F A Sᶜ := by
    intro z hz
    have hout : ¬ ‖z‖ ≤ R (polarAnnulusCoordinates z).2 := hz
    rw [houter z hout]
    change H (polarAnnulusCoordinates z) = attachDiskAnnulus u H z
    exact (attachDiskAnnulus_outer u H hglue
      ((hRlo _).trans (lt_of_not_ge hout).le)).symm
  have houterArea : riemannianArea g F (closedBall (0 : ℂ) 1 \ S) = 0 := by
    have heq : riemannianArea g F (closedBall (0 : ℂ) 1 \ S) =
        riemannianArea g A (closedBall (0 : ℂ) 1 \ S) := by
      apply setIntegral_congr_fun (measurableSet_closedBall.diff hSc.measurableSet)
      intro z hz
      exact riemannianAreaDensity_congr g
        (hFA.eventuallyEq_of_mem (hSc.isOpen_compl.mem_nhds hz.2))
    rw [heq]
    apply le_antisymm
    · have hsub : closedBall (0 : ℂ) 1 \ S ⊆
          closedBall (0 : ℂ) 1 \ closedBall (0 : ℂ) (1 / 2) := by
        intro z hz
        exact ⟨hz.1, fun h => hz.2 (hhalfS h)⟩
      exact (setIntegral_mono_set (hAi.mono_set sdiff_subset)
        (Eventually.of_forall (riemannianAreaDensity_nonneg g A))
        (Eventually.of_forall hsub)).trans_eq hshell
    · exact integral_nonneg (riemannianAreaDensity_nonneg g A)
  have hsplit := setIntegral_sdiff hSc.measurableSet hFi hSD
  change riemannianArea g F (closedBall (0 : ℂ) 1 \ S) =
    riemannianArea g F (closedBall (0 : ℂ) 1) - riemannianArea g F S at hsplit
  rw [houterArea, hinnerArea] at hsplit
  linarith

end DifferentialGeometry.Geometry
