import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ScalarHeat.MildSolution
import DifferentialGeometry.Analysis.Heat.Semigroup.Duhamel
import DifferentialGeometry.Analysis.Heat.Smoothing.MildSolution
import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupHs
import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupHsExt
import DifferentialGeometry.Analysis.Sobolev.Hs.Inclusion
import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupContinuity

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.HeatEquation

theorem scalarQuasilinearMildSolution_eq_mildSolution
    (g : SmoothRiemannianMetric I M)
    (u₀ : scalarHs (I := I) (M := M) g 0)
    {N : scalarHs (I := I) (M := M) g 0 → scalarHs (I := I) (M := M) g 0}
    {L : NNReal} (hN : LipschitzWith L N)
    {T : ℝ}
    {u : ℝ → scalarHs (I := I) (M := M) g 0}
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g 0 t u₀ +
        ∫ τ in (0 : ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      scalarHsZeroEquivL2 (I := I) (M := M) g (u t) =
        mildSolution (I := I) (M := M) g
          (scalarHsZeroEquivL2 (I := I) (M := M) g u₀)
          (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) t := by
  classical
  let e : scalarHs (I := I) (M := M) g 0 →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure I M g) :=
    (scalarHsZeroEquivL2 (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap
  intro t ht
  have hsem_apply : ∀ {τ : ℝ} (hτ : 0 < τ)
      (v : scalarHs (I := I) (M := M) g 0),
      e (heatSemigroupHsExt (I := I) (M := M) g 0 τ v) =
        heatSemigroup (I := I) (M := M) g τ (e v) := by
    intro τ hτ v
    rw [heatSemigroupHsExt_of_pos (I := I) (M := M) hτ]
    exact heatSemigroupHs_zeroEquivL2_apply (I := I) (M := M) hτ v
  have hsem_zero : ∀ v : scalarHs (I := I) (M := M) g 0,
      e (heatSemigroupHsExt (I := I) (M := M) g 0 0 v) =
        heatSemigroup (I := I) (M := M) g 0 (e v) := by
    intro v
    rw [heatSemigroupHsExt_zero (I := I) (M := M) g 0]
    simp [heatSemigroup_zero]
  have hpoint : Set.EqOn
      (fun τ : ℝ => e (heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))))
      (fun τ : ℝ => heatSemigroup (I := I) (M := M) g (t - τ) (e (N (u τ))))
      (Set.uIcc 0 t) := by
    intro τ hτ
    by_cases hτt : τ = t
    · subst τ
      change e (heatSemigroupHsExt (I := I) (M := M) g 0 (t - t) (N (u t))) =
        heatSemigroup (I := I) (M := M) g (t - t) (e (N (u t)))
      rw [sub_self, hsem_zero]
    · have hpos : 0 < t - τ := by
        rw [sub_pos]
        exact lt_of_le_of_ne (by
          have hτle : τ ≤ t := by
            rw [Set.uIcc_of_le ht.1] at hτ
            exact hτ.2
          exact hτle) hτt
      change e (heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))) =
        heatSemigroup (I := I) (M := M) g (t - τ) (e (N (u τ)))
      exact hsem_apply hpos (N (u τ))
  have hφ2 : ContinuousOn (fun τ : ℝ => N (u τ)) (Set.Icc 0 t) := by
    exact (hN.continuous.comp_continuousOn hu_cont).mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hφ : ContinuousOn (fun τ : ℝ => (t - τ, N (u τ))) (Set.Icc 0 t) := by
    exact ((continuous_const.sub continuous_id).continuousOn).prodMk hφ2
  have hS : ContinuousOn
      (fun p : ℝ × scalarHs (I := I) (M := M) g 0 =>
        scalarHsBoundedC0Semigroup (I := I) (M := M) g 0 p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) :=
    (scalarHsBoundedC0Semigroup (I := I) (M := M) g 0).continuousOn_uncurry
  have hφdom : ∀ τ ∈ Set.Icc 0 t, (t - τ, N (u τ)) ∈ Set.Ici 0 ×ˢ Set.univ := by
    intro τ hτ
    exact ⟨by rw [Set.mem_Ici]; exact sub_nonneg.mpr hτ.2, Set.mem_univ _⟩
  have hcont : ContinuousOn
      (fun τ : ℝ => heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ)))
      (Set.Icc 0 t) := by
    simpa [scalarHsBoundedC0Semigroup_apply] using (hS.comp hφ hφdom)
  have hf : IntervalIntegrable
      (fun τ : ℝ => heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ)))
      MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable_of_Icc ht.1
  have hint_comm : e (∫ τ in (0 : ℝ)..t,
        heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))) =
      ∫ τ in (0 : ℝ)..t,
        e (heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))) :=
    (ContinuousLinearMap.intervalIntegral_comp_comm e hf).symm
  unfold mildSolution
  change e (u t) = heatSemigroup (I := I) (M := M) g t (e u₀) +
    ∫ s in (0 : ℝ)..t, heatSemigroup (I := I) (M := M) g (t - s) (e (N (u s)))
  have hu' := hu_eq t ht
  have heval : e (u t) = e (heatSemigroupHsExt (I := I) (M := M) g 0 t u₀) +
      e (∫ τ in (0 : ℝ)..t,
        heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ))) := by
    rw [hu', map_add]
  rw [heval, hint_comm]
  congr 1
  · by_cases ht0 : t = 0
    · subst t
      exact hsem_zero u₀
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact hsem_apply htpos u₀
  · exact intervalIntegral.integral_congr hpoint

theorem scalarQuasilinear_smooth_representative_of_forcingSpectralMass
    (g : SmoothRiemannianMetric I M)
    (u₀ : scalarHs (I := I) (M := M) g 0)
    {N : scalarHs (I := I) (M := M) g 0 → scalarHs (I := I) (M := M) g 0}
    {L : NNReal} (hN : LipschitzWith L N)
    {T : ℝ} {u : ℝ → scalarHs (I := I) (M := M) g 0}
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g 0 t u₀ +
        ∫ τ in (0 : ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ)))
    (hf_cont : Continuous (fun s : ℝ =>
      scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g
        (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) t k)) :
    ∃ u_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
        scalarHsZeroEquivL2 (I := I) (M := M) g (u t) := by
  classical
  let f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure I M g) := fun s : ℝ =>
    scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))
  obtain ⟨u_smooth, hu_smooth⟩ :=
    mildSolution_smooth_representative_of_forcingSpectralMass
      (I := I) (M := M) g
      (scalarHsZeroEquivL2 (I := I) (M := M) g u₀) hf_cont ht (by simpa [f] using hmass)
  have hw := scalarQuasilinearMildSolution_eq_mildSolution
    (I := I) (M := M) g u₀ hN hu_cont hu_eq t ⟨le_of_lt ht, htT⟩
  refine ⟨u_smooth, ?_⟩
  rw [hu_smooth]
  simpa [f] using hw.symm

theorem scalarQuasilinear_satisfies_heat_equation_of_forcingSpectralMass
    (g : SmoothRiemannianMetric I M)
    (u₀ : scalarHs (I := I) (M := M) g 0)
    {N : scalarHs (I := I) (M := M) g 0 → scalarHs (I := I) (M := M) g 0}
    {L : NNReal} (hN : LipschitzWith L N)
    {T : ℝ} {u : ℝ → scalarHs (I := I) (M := M) g 0}
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g 0 t u₀ +
        ∫ τ in (0 : ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ)))
    (hf : ContDiff ℝ 1 (fun s : ℝ =>
      scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g
        (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) t k))
    (hmass_deriv : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g
        (deriv (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))) t k))
    (f_smooth : SmoothScalar g)
    (hf_smooth : smoothToLp (I := I) (M := M) g f_smooth =
      scalarHsZeroEquivL2 (I := I) (M := M) g (N (u t))) :
    ∃ u_smooth du_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
          scalarHsZeroEquivL2 (I := I) (M := M) g (u t) ∧
        smoothToLp (I := I) (M := M) g du_smooth =
          -(heatPower (I := I) (M := M) g 1 t
              (scalarHsZeroEquivL2 (I := I) (M := M) g u₀)) +
            mildSolution (I := I) (M := M) g
              ((fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) 0)
              (deriv (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))) t ∧
        du_smooth = u_smooth.laplacian + f_smooth := by
  classical
  let f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure I M g) := fun s : ℝ =>
    scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))
  obtain ⟨u_smooth, du_smooth, hu, hdu, hdeq⟩ :=
    mildSolution_has_classical_representatives_of_forcingSpectralMass
      (I := I) (M := M) g
      (scalarHsZeroEquivL2 (I := I) (M := M) g u₀) hf ht
      (by simpa [f] using hmass) (by simpa [f] using hmass_deriv)
      f_smooth (by simpa [f] using hf_smooth)
  have hw := scalarQuasilinearMildSolution_eq_mildSolution
    (I := I) (M := M) g u₀ hN hu_cont hu_eq t ⟨le_of_lt ht, htT⟩
  refine ⟨u_smooth, du_smooth, ?_, ?_, ?_⟩
  · rw [hu]
    simpa [f] using hw.symm
  · simpa [f] using hdu
  · exact hdeq

theorem scalar_quasilinear_classical_solution_of_smooth_forcing
    (g : SmoothRiemannianMetric I M)
    (u₀ : scalarHs (I := I) (M := M) g 0)
    {N : scalarHs (I := I) (M := M) g 0 → scalarHs (I := I) (M := M) g 0}
    {L : NNReal} (hN : LipschitzWith L N)
    {T : ℝ} {u : ℝ → scalarHs (I := I) (M := M) g 0}
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g 0 t u₀ +
        ∫ τ in (0 : ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g 0 (t - τ) (N (u τ)))
    (hN_smooth : ∀ s : ℝ, ∃ f_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g f_smooth =
        scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))
    (hf : ContDiff ℝ 1 (fun s : ℝ =>
      scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g
        (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) t k))
    (hmass_deriv : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g
        (deriv (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))) t k)) :
    ∃ u_smooth du_smooth f_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
          scalarHsZeroEquivL2 (I := I) (M := M) g (u t) ∧
        smoothToLp (I := I) (M := M) g f_smooth =
          scalarHsZeroEquivL2 (I := I) (M := M) g (N (u t)) ∧
        du_smooth = u_smooth.laplacian + f_smooth ∧
        smoothToLp (I := I) (M := M) g du_smooth =
          -(heatPower (I := I) (M := M) g 1 t
              (scalarHsZeroEquivL2 (I := I) (M := M) g u₀)) +
            mildSolution (I := I) (M := M) g
              ((fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) 0)
              (deriv (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))) t := by
  classical
  obtain ⟨f_smooth, hf_smooth⟩ := hN_smooth t
  obtain ⟨u_smooth, du_smooth, hu, hdu, hdeq⟩ :=
    scalarQuasilinear_satisfies_heat_equation_of_forcingSpectralMass
      (I := I) (M := M) g u₀ hN hu_cont hu_eq hf ht htT hmass hmass_deriv
      f_smooth hf_smooth
  exact ⟨u_smooth, du_smooth, f_smooth, hu, hf_smooth, hdeq, hdu⟩

theorem scalar_quasilinear_local_classical_solution_of_smooth_forcing
    (g : SmoothRiemannianMetric I M)
    (u₀ : scalarHs (I := I) (M := M) g 0)
    {N : scalarHs (I := I) (M := M) g 0 → scalarHs (I := I) (M := M) g 0}
    {L : NNReal} (hN : LipschitzWith L N)
    (hN_smooth : ∀ (u : ℝ → scalarHs (I := I) (M := M) g 0) (s : ℝ),
      ∃ f_smooth : SmoothScalar g,
        smoothToLp (I := I) (M := M) g f_smooth =
          scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))
    (hf : ∀ u : ℝ → scalarHs (I := I) (M := M) g 0,
      ContDiff ℝ 1 (fun s : ℝ =>
        scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))))
    (hmass : ∀ (u : ℝ → scalarHs (I := I) (M := M) g 0) (t : ℝ) (k : ℕ),
      Summable (forcingSpectralMass (I := I) (M := M) g
        (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s))) t k))
    (hmass_deriv : ∀ (u : ℝ → scalarHs (I := I) (M := M) g 0) (t : ℝ) (k : ℕ),
      Summable (forcingSpectralMass (I := I) (M := M) g
        (deriv (fun s : ℝ => scalarHsZeroEquivL2 (I := I) (M := M) g (N (u s)))) t k)) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → scalarHs (I := I) (M := M) g 0,
      ContinuousOn u (Set.Icc 0 T) ∧ u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < t →
        ∃ u_smooth du_smooth f_smooth : SmoothScalar g,
          smoothToLp (I := I) (M := M) g u_smooth =
              scalarHsZeroEquivL2 (I := I) (M := M) g (u t) ∧
            smoothToLp (I := I) (M := M) g f_smooth =
              scalarHsZeroEquivL2 (I := I) (M := M) g (N (u t)) ∧
            du_smooth = u_smooth.laplacian + f_smooth := by
  classical
  obtain ⟨T, hT, u, hu_cont, hu_zero, hu_eq⟩ :=
    scalar_quasilinear_local_existence (I := I) (M := M) g 0 u₀ hN
  refine ⟨T, hT, u, hu_cont, hu_zero, ?_⟩
  intro t ht htpos
  obtain ⟨u_smooth, du_smooth, f_smooth, hu, hf_smooth, hdeq, _⟩ :=
    scalar_quasilinear_classical_solution_of_smooth_forcing
      (I := I) (M := M) g u₀ hN hu_cont hu_eq
      (hN_smooth u) (hf u) htpos ht.2 (hmass u t) (hmass_deriv u t)
  exact ⟨u_smooth, du_smooth, f_smooth, hu, hf_smooth, hdeq⟩

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
