import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem timeDependentFlow_apply_eq_of_isIntegralCurveOn (V : ℝ × E → E)
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V) {γ : ℝ → E} {s t : ℝ} (hst : s ≤ t)
    (hγ : IsIntegralCurveOn γ (fun u x => V (u, x)) (Set.Icc s t)) :
    timeDependentFlow V hV hs s t (γ s) = γ t := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hV (by simp)
  have hslice (u : ℝ) : LipschitzWith K (fun x : E => V (u, x)) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
      hK.dist_le_mul (u, x) (u, y)
  have hflow := isIntegralCurve_timeDependentFlow V hV hs s (γ s)
  have hleft : ContinuousOn (fun u => timeDependentFlow V hV hs s u (γ s)) (Set.Icc s t) :=
    (continuous_iff_continuousAt.mpr (fun u => (hflow u).continuousAt)).continuousOn
  have hmem (u : ℝ) (hu : u ∈ Set.Ico s t) : Set.Icc s t ∈ 𝓝[Set.Ici u] u := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio t, isOpen_Iio.mem_nhds hu.2, ?_⟩
    rintro v ⟨hv1, hv2⟩
    exact ⟨le_trans hu.1 hv2, hv1.le⟩
  have hright : ∀ u ∈ Set.Ico s t, HasDerivWithinAt γ (V (u, γ u)) (Set.Ici u) u := by
    intro u hu
    exact (hγ u ⟨hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin (hmem u hu)
  have heq : EqOn (fun u => timeDependentFlow V hV hs s u (γ s)) γ (Set.Icc s t) :=
    ODE_solution_unique (v := fun u x => V (u, x)) (K := K)
      (fun u => hslice u) hleft
      (fun u _ => (hflow u).hasDerivWithinAt) hγ.continuousOn hright
      (by simp only [timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq])
  exact heq (x := t) ⟨hst, le_rfl⟩

theorem exists_isCompact_isotopy_eqOn_linearPath
    (L : ℝ → E ≃L[ℝ] E) (D : ℝ → E →L[ℝ] E) (hL0 : ∀ x, L 0 x = x)
    (hLc : ContDiff ℝ ∞ (fun p : ℝ × E => L p.1 p.2))
    (hLsc : ContDiff ℝ ∞ (fun p : ℝ × E => (L p.1).symm p.2))
    (hDc : ContDiff ℝ ∞ D)
    (hDdef : ∀ t x, HasDerivAt (fun s => L s x) (D t x) t) (ε : ℝ) :
    ∃ (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (Ks : Set E),
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      IsCompact Ks ∧
      (∀ t x, x ∉ Ks → Φ t x = x ∧ (Φ t).symm x = x) ∧
      ∀ x, ‖x‖ ≤ ε → Φ 1 x = L 1 x := by
  obtain ⟨ρ, hρ⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : E) ε)).exists_bound_of_continuousOn
    hLc.continuous.continuousOn
  let η : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : ContDiffBump (0 : E) :=
    ⟨max ρ 0 + 1, max ρ 0 + 2, by positivity, by linarith⟩
  let V : ℝ × E → E := fun p => (η p.1 * χ p.2) • (D p.1) ((L p.1).symm p.2)
  have hVsmooth : ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1) ((L p.1).symm p.2)) :=
    (hDc.comp contDiff_fst).clm_apply hLsc
  have hV : ContDiff ℝ ∞ V :=
    (((η.contDiff).comp contDiff_fst).mul ((χ.contDiff).comp contDiff_snd)).smul hVsmooth
  have hVsub : tsupport V ⊆ tsupport η ×ˢ tsupport χ := by
    refine closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
    rintro p hp
    have hp0 : V p ≠ 0 := hp
    refine ⟨subset_tsupport _ (fun h => hp0 ?_), subset_tsupport _ (fun h => hp0 ?_)⟩
    · show V p = 0
      dsimp only [V]
      rw [h, zero_mul, zero_smul]
    · show V p = 0
      dsimp only [V]
      rw [h, mul_zero, zero_smul]
  have hsupp : HasCompactSupport V :=
    (η.hasCompactSupport.prod χ.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport V) hVsub
  refine ⟨fun t => timeDependentFlow V hV hsupp 0 t, Prod.snd '' tsupport V,
    timeDependentFlow_refl V hV hsupp 0, ?_, ?_, hsupp.image continuous_snd,
    fun t x hx =>
      ⟨(timeDependentFlow_eqOn_compl_image_tsupport V hV hsupp 0 t).1 (x := x) hx,
        (timeDependentFlow_eqOn_compl_image_tsupport V hV hsupp 0 t).2 (x := x) hx⟩, ?_⟩
  · exact (contDiff_timeDependentFlow V hV hsupp).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  · exact (contDiff_timeDependentFlow_symm V hV hsupp).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  · intro x hx
    have hγ : IsIntegralCurveOn (fun t => L t x) (fun u y => V (u, y)) (Set.Icc 0 1) := by
      intro u hu
      have hη : η u = 1 := η.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff]
        exact abs_le.2 ⟨by linarith [hu.1], hu.2⟩)
      have hχ : χ (L u x) = 1 := χ.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff]
        exact (hρ (u, x) ⟨hu, by rwa [mem_closedBall_zero_iff]⟩).trans (by linarith [le_max_left ρ 0]))
      have hval : V (u, L u x) = D u x := by
        simp only [V, hη, hχ, one_mul, one_smul]
        rw [ContinuousLinearEquiv.symm_apply_apply]
      have hderiv := (hDdef u x).hasDerivWithinAt (s := Set.Icc 0 1)
      rw [← hval] at hderiv
      exact hderiv
    have hflow := timeDependentFlow_apply_eq_of_isIntegralCurveOn V hV hsupp
      (γ := fun t => L t x) (s := 0) (t := 1) zero_le_one hγ
    change (timeDependentFlow V hV hsupp 0 1) x = (L 1) x
    rw [hL0 x] at hflow
    exact hflow

end Diffeomorph
