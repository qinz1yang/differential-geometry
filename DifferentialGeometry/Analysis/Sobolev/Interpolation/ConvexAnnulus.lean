import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusComparison
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy

section

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Metric
open DifferentialGeometry.Topology
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℝ F]

theorem attachThinAnnulus_mapsTo_closedBall_of_convex
    {K : Set F} (hK : Convex ℝ K) {u v : ℂ → F} {R h : ℝ}
    (hh : 0 < h) (hhR : h < R)
    (hu : MapsTo u (sphere (0 : ℂ) R) K)
    (hv : MapsTo v (closedBall (0 : ℂ) R) K) :
    MapsTo (attachThinAnnulus u v id R h) (closedBall (0 : ℂ) R) K := by
  intro z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  by_cases hi : ‖z‖ ≤ R - h
  · rw [attachThinAnnulus_inner u v id R h hi]
    apply hv
    have ha := sub_pos.mpr hhR
    have hR := hh.trans hhR
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR ha)]
    exact (mul_le_mul_of_nonneg_left hi (div_nonneg hR.le ha.le)).trans_eq
      (div_mul_cancel₀ R ha.ne')
  · have hshell : R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R := ⟨(lt_of_not_ge hi).le, hzR⟩
    rw [attachThinAnnulus_shell u v id hh hhR (fun _ _ => rfl) (fun _ _ => rfl) hshell]
    have hp : thinAnnulusProjection R z ∈ sphere (0 : ℂ) R := by
      simpa only [mem_sphere, dist_zero_right] using
        thinAnnulusProjection_norm (hh.trans hhR).le z
    have hθ := thinAnnulusParameter_mem_Icc hh hshell
    exact hK (hv (sphere_subset_closedBall hp)) (hu hp)
      (sub_nonneg.mpr hθ.2) hθ.1 (sub_add_cancel 1 _)

theorem integrableOn_quadratic_fderiv_of_lipschitz [FiniteDimensional ℝ F]
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f)
    {S : Set ℂ} (hS : IsCompact S) {K : Set F} (hK : IsCompact K)
    (hfK : MapsTo f S K) (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    IntegrableOn (fun z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) S := by
  borelize F
  let μ : Measure ℂ := volume.restrict S
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  have hm (w : ℂ) : MemLp (fun z => fderiv ℝ f z w) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f w).aestronglyMeasurable
      ((L : ℝ) * ‖w‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ f z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg w))
  have hAc : ContinuousOn (fun z => A (f z)) S := hA.comp hf.continuous.continuousOn hfK
  have hAm (v w : F) : AEStronglyMeasurable (fun z => A (f z) v w) μ :=
    ((hAc.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hS.measurableSet
  have hnorm : ContinuousOn (fun x => ‖A x‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  have hAb : ∀ᵐ z ∂μ, ‖A (f z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact hC (mem_image_of_mem (fun x => ‖A x‖) (hfK hz))
  exact ((integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
    hAm hAb (hm 1) (hm 1)).add
    (integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
      hAm hAb (hm Complex.I) (hm Complex.I))).div_const 2

end Normed

variable [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_convex_thin_annulus_tendsto_quadratic_energy
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {R : ℝ} (hR : 0 < R)
    (hgap : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 R (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 R (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0))
    {D : ℝ} (hder : ∀ n, (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D)
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (huK : ∀ᶠ n in atTop, MapsTo (u n) (sphere (0 : ℂ) R) K)
    (hvK : ∀ n, MapsTo (v n) (closedBall (0 : ℂ) R) K) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, h n < R / 2 ∧
        (∃ C : ℝ≥0, LipschitzWith C (attachThinAnnulus (u n) (v n) id R (h n))) ∧
        MapsTo (attachThinAnnulus (u n) (v n) id R (h n)) (closedBall (0 : ℂ) R) K) ∧
      (∀ n z, R ≤ ‖z‖ → attachThinAnnulus (u n) (v n) id R (h n) z = u n z) ∧
      ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
        Tendsto (fun n =>
          (∫ z in closedBall (0 : ℂ) R,
            (A (attachThinAnnulus (u n) (v n) id R (h n) z)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z 1)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z 1) +
              A (attachThinAnnulus (u n) (v n) id R (h n) z)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z Complex.I)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z Complex.I)) / 2) -
          (∫ z in closedBall (0 : ℂ) R,
            (A (v n z) (fderiv ℝ (v n) z 1) (fderiv ℝ (v n) z 1) +
              A (v n z) (fderiv ℝ (v n) z Complex.I) (fderiv ℝ (v n) z Complex.I)) / 2))
          atTop (𝓝 0) := by
  obtain ⟨h, hh, hh0, hgood, houter, hnorm⟩ :=
    exists_width_tendsto_annulus_energy_attachThinAnnulus_zero u v Ku Kv hu hv
      (fun _ => R) hR (fun _ => ⟨le_rfl, le_rfl⟩) hgap hder id differentiable_id
      (L := 1) (by
        intro x
        rw [fderiv_id]
        exact ContinuousLinearMap.norm_id_le) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hmaps : ∀ᶠ n in atTop,
      MapsTo (attachThinAnnulus (u n) (v n) id R (h n)) (closedBall (0 : ℂ) R) K := by
    filter_upwards [hgood, huK] with n hn huKn
    exact attachThinAnnulus_mapsTo_closedBall_of_convex hKconv (hh n)
      (by linarith [hn.1]) huKn (hvK n)
  refine ⟨h, hh, hh0, hgood.and hmaps |>.mono (fun n hn =>
    ⟨hn.1.1, hn.1.2, hn.2⟩), houter, ?_⟩
  intro A hA
  let f (n : ℕ) := attachThinAnnulus (u n) (v n) id R (h n)
  let S (n : ℕ) := {z : ℂ | ‖z‖ ∈ Icc (R - h n) R}
  let energy (w : ℂ → F) (z : ℂ) :=
    (A (w z) (fderiv ℝ w z 1) (fderiv ℝ w z 1) +
      A (w z) (fderiv ℝ w z Complex.I) (fderiv ℝ w z Complex.I)) / 2
  have hsub (n : ℕ) : S n ⊆ closedBall (0 : ℂ) R := fun z hz =>
    mem_closedBall_zero_iff.mpr hz.2
  have hcompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      (isClosed_Icc.preimage continuous_norm) (hsub n)
  have hquad : Tendsto (fun n => ∫ z in S n, energy (f n) z) atTop (𝓝 0) :=
    tendsto_integral_quadratic_fderiv_of_eventually_lipschitz f S hcompact hK A hA
      (by
        filter_upwards [hgood, hmaps] with n hn hnK
        exact ⟨hn.2, hnK.mono_left (hsub n)⟩) hnorm
  apply hquad.congr'
  filter_upwards [hgood, hmaps] with n hn hnK
  obtain ⟨C, hC⟩ := hn.2
  have hhR : h n < R := by linarith [hn.1]
  have hint := integrableOn_quadratic_fderiv_of_lipschitz hC
    (isCompact_closedBall (0 : ℂ) R) hK hnK A hA
  have heq := integral_quadratic_fderiv_attachThinAnnulus_closedBall
    A (u n) (v n) id (hh n) hhR (le_refl R) hint
  change (∫ z in closedBall (0 : ℂ) R, energy (f n) z) =
    (∫ z in closedBall (0 : ℂ) R, energy (v n) z) +
      (∫ z in closedBall (0 : ℂ) R \ closedBall (0 : ℂ) (R - h n), energy (f n) z) +
      ∫ z in closedBall (0 : ℂ) R \ closedBall (0 : ℂ) R, energy (u n) z at heq
  simp only [Set.sdiff_self, setIntegral_empty, add_zero] at heq
  have hsets : closedBall (0 : ℂ) R \ closedBall (0 : ℂ) (R - h n) =ᵐ[volume] S n := by
    have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (0 : ℂ) (R - h n) := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using
        Measure.addHaar_sphere volume (0 : ℂ) (R - h n)
    filter_upwards [hnull] with z hz
    apply propext
    have hne : ‖z‖ ≠ R - h n := by simpa only [mem_sphere, dist_zero_right] using hz
    change (z ∈ closedBall (0 : ℂ) R ∧ z ∉ closedBall (0 : ℂ) (R - h n)) ↔
      (R - h n ≤ ‖z‖ ∧ ‖z‖ ≤ R)
    simp only [mem_closedBall, dist_zero_right, not_le]
    exact ⟨fun hz => ⟨hz.2.le, hz.1⟩,
      fun hz => ⟨hz.2, lt_of_le_of_ne hz.1 hne.symm⟩⟩
  have hshell : (∫ z in closedBall (0 : ℂ) R \ closedBall (0 : ℂ) (R - h n),
      energy (f n) z) = ∫ z in S n, energy (f n) z := setIntegral_congr_set hsets
  change (∫ z in S n, energy (f n) z) =
    (∫ z in closedBall (0 : ℂ) R, energy (f n) z) -
      ∫ z in closedBall (0 : ℂ) R, energy (v n) z
  rw [heq, hshell]
  ring

end DifferentialGeometry.Analysis

end

end
