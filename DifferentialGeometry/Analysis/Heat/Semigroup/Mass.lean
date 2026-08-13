import DifferentialGeometry.Analysis.Heat.Semigroup.Duhamel
import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

abbrev heatMassSpace (g : SmoothRiemannianMetric I M) :=
  Lp ℝ 2 (riemannianVolumeMeasure I M g)

noncomputable def heatMassOne (g : SmoothRiemannianMetric I M) : heatMassSpace g := by
  classical
  letI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact indicatorConstLp 2 (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
    (measure_ne_top (riemannianVolumeMeasure I M g) Set.univ) (1 : ℝ)

noncomputable def heatMass (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) (t : ℝ) : ℝ :=
  ⟪heatMassOne (I := I) (M := M) g, heatSemigroup (I := I) (M := M) g t u₀⟫_ℝ

theorem heatMass_eq_integral
    (g : SmoothRiemannianMetric I M) (v : heatMassSpace g)
    (s : ℝ) :
    heatMass (I := I) (M := M) g v s =
      ∫ x, ((heatSemigroup (I := I) (M := M) g s v : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g) := by
  classical
  set μ := riemannianVolumeMeasure I M g with hμ
  letI : IsFiniteMeasure μ := by
    rw [hμ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  unfold heatMass
  calc
    ⟪heatMassOne (I := I) (M := M) g, heatSemigroup (I := I) (M := M) g s v⟫_ℝ =
        ∫ x in Set.univ, ((heatSemigroup (I := I) (M := M) g s v :
            heatMassSpace g) : M → ℝ) x ∂μ := by
      exact MeasureTheory.L2.inner_indicatorConstLp_one
        (μ := μ) (𝕜 := ℝ)
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
        (measure_ne_top μ Set.univ) (heatSemigroup (I := I) (M := M) g s v)
    _ = ∫ x, ((heatSemigroup (I := I) (M := M) g s v : heatMassSpace g) : M → ℝ) x ∂μ :=
      setIntegral_univ

theorem heatMass_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
      ⟪heatMassOne (I := I) (M := M) g, -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ t := by
  obtain ⟨u_smooth, du_smooth, hu, hdu, hderiv, hlap⟩ :=
    heatSemigroup_has_smooth_generator_representative_of_closed (I := I) (M := M) g ht u₀
  let L : heatMassSpace g →L[ℝ] ℝ :=
    innerSL (𝕜 := ℝ) (E := heatMassSpace g)
      (heatMassOne (I := I) (M := M) g)
  have hcomp : HasDerivAt (fun s : ℝ =>
      L (heatSemigroup (I := I) (M := M) g s u₀))
      (L (smoothToLp (I := I) (M := M) g du_smooth)) t := by
    exact HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt hderiv
  have hmass_eq : (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) =
      fun s : ℝ => L (heatSemigroup (I := I) (M := M) g s u₀) := by
    funext s
    rfl
  have hval_eq : ⟪heatMassOne (I := I) (M := M) g, -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ =
      L (smoothToLp (I := I) (M := M) g du_smooth) := by
    rw [hdu]
    rfl
  simpa [hmass_eq, hval_eq] using hcomp

theorem heatMass_deriv_zero
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) 0 t := by
  have hderiv := heatMass_hasDerivAt (I := I) (M := M) g u₀ ht
  have hval : ⟪heatMassOne (I := I) (M := M) g,
      -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ = 0 := by
    obtain ⟨u_smooth, du_smooth, hu, hdu, hderiv', hlap⟩ :=
      heatSemigroup_has_smooth_generator_representative_of_closed (I := I) (M := M) g ht u₀
    rw [← hdu]
    classical
    set μ := riemannianVolumeMeasure I M g with hμ
    letI : IsFiniteMeasure μ := by
      rw [hμ]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    have hinner :
        ⟪heatMassOne (I := I) (M := M) g, smoothToLp (I := I) (M := M) g du_smooth⟫_ℝ =
          ∫ x in Set.univ, ((smoothToLp (I := I) (M := M) g du_smooth :
            heatMassSpace g) : M → ℝ) x ∂μ := by
      exact MeasureTheory.L2.inner_indicatorConstLp_one
        (μ := μ) (𝕜 := ℝ)
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
        (measure_ne_top μ Set.univ) (smoothToLp (I := I) (M := M) g du_smooth)
    rw [hinner]
    rw [setIntegral_univ]
    have hae := MemLp.coeFn_toLp (f := du_smooth.toFun) (p := (2 : ℝ≥0∞))
      (μ := μ) du_smooth.memLp_two
    have hint_congr : (∫ x, ((smoothToLp (I := I) (M := M) g du_smooth :
        heatMassSpace g) : M → ℝ) x ∂μ) =
        ∫ x, du_smooth.toFun x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact hae
    rw [hint_congr]
    have htoFun : du_smooth.toFun = Δ_g (I := I) g u_smooth.toContMDiffMap := by
      rw [← congrArg SmoothScalar.toFun hlap]
      exact SmoothScalar.laplacian_toFun u_smooth
    rw [htoFun]
    exact laplacian_integral_eq_zero (I := I) (M := M) g u_smooth.smooth
  simpa [hval] using hderiv

theorem heatSemigroup_mass_invariant
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, ((heatSemigroup (I := I) (M := M) g t u₀ : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g)) =
      ∫ x, ((u₀ : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g) := by
  classical
  set μ := riemannianVolumeMeasure I M g with hμ
  letI : IsFiniteMeasure μ := by
    rw [hμ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let L : heatMassSpace g →L[ℝ] ℝ :=
    innerSL (𝕜 := ℝ) (E := heatMassSpace g)
      (heatMassOne (I := I) (M := M) g)
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    simp [heatSemigroup_zero]
  · have hcont : ContinuousOn (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
        (Icc 0 t) := by
      have hcontIci := heatSemigroup_continuous_on_nonneg (I := I) (M := M) g u₀
      have hcomp : ContinuousOn (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (Ici 0) :=
        L.continuous.comp_continuousOn hcontIci
      exact hcomp.mono (by intro p hp; exact hp.1)
    have hconst_on : ∀ ε ∈ Ioo 0 t,
        heatMass (I := I) (M := M) g u₀ ε = heatMass (I := I) (M := M) g u₀ t := by
      intro ε hε
      have hderiv : ∀ x ∈ Ico ε t,
          HasDerivWithinAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) 0 (Ici x) x := by
        intro x hx
        exact (heatMass_deriv_zero (I := I) (M := M) g u₀
          (lt_of_lt_of_le hε.1 hx.1)).hasDerivWithinAt
      have hconst_ε := constant_of_has_deriv_right_zero
        (f := fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
        (hcont.mono (Set.Icc_subset_Icc (le_of_lt hε.1) le_rfl)) hderiv t
        ⟨le_of_lt hε.2, le_rfl⟩
      exact hconst_ε.symm
    have h_ev : (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε) =ᶠ[𝓝[>] (0 : ℝ)]
        fun _ : ℝ => heatMass (I := I) (M := M) g u₀ t := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{x : ℝ | 0 < x} ∩ Set.Iio t, ?_, ?_⟩
      · exact inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htpos))
      intro ε hε
      exact hconst_on ε hε
    have h_tend : Tendsto (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (heatMass (I := I) (M := M) g u₀ t)) := by
      exact Filter.Tendsto.congr' h_ev.symm
        (tendsto_const_nhds (x := heatMass (I := I) (M := M) g u₀ t))
    have h_tend0 : Tendsto (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (heatMass (I := I) (M := M) g u₀ 0)) := by
      have hcontLp0 := heatSemigroup_continuous_at_zero (I := I) (M := M) g u₀
      have hL : Tendsto (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (𝓝[≥] (0 : ℝ)) (𝓝 (L u₀)) :=
        (L.continuous.continuousAt (x := u₀)).tendsto.comp hcontLp0
      have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) := by
        exact nhdsWithin_mono (x := (0 : ℝ))
          (s := {x : ℝ | 0 < x}) (t := {x : ℝ | 0 ≤ x})
          (by intro x hx; dsimp at hx ⊢; exact le_of_lt hx)
      have hL' : Tendsto (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (𝓝[>] (0 : ℝ)) (𝓝 (L u₀)) :=
        hL.mono_left hmono
      simpa [heatMass, heatSemigroup_zero] using hL'
    have hconst := tendsto_nhds_unique h_tend h_tend0
    calc
      (∫ x, ((heatSemigroup (I := I) (M := M) g t u₀ : heatMassSpace g) : M → ℝ) x
          ∂(riemannianVolumeMeasure I M g)) =
          heatMass (I := I) (M := M) g u₀ t :=
        (heatMass_eq_integral (I := I) (M := M) g u₀ t).symm
      _ = heatMass (I := I) (M := M) g u₀ 0 := hconst
      _ = ∫ x, ((u₀ : heatMassSpace g) : M → ℝ) x
          ∂(riemannianVolumeMeasure I M g) := by
        rw [heatMass_eq_integral (I := I) (M := M) g u₀ 0]
        simp [heatSemigroup_zero]

end HeatEquation
end Analysis
end DifferentialGeometry

end
