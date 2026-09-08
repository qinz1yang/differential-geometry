import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.SolutionSpace

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
variable {g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M}
variable {a b T : ℝ}

theorem timeModeCoeff_compLpL_dirichletHsInclusion (hab : a ≤ b)
    (f : timeL2 (DirichletHs g b) T) (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f) i =
      timeModeCoeff f i := by
  apply Lp.ext
  filter_upwards [timeModeCoeff_coeFn
    ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f) i,
    (dirichletHsInclusion hab).coeFn_compLpL (p := 2) (μ := timeMeasure T) f,
    timeModeCoeff_coeFn f i] with t h₁ h₂ h₃
  rw [h₁, h₂, DirichletHs.dirichletHsInclusion_coeff, h₃]

theorem maximalRegularitySolField_compLpL_dirichletHsInclusion
    (hab : a ≤ b) (hT : 0 ≤ T) (f : timeL2 (DirichletHs g b) T) :
    (dirichletHsInclusion (show a + 2 ≤ b + 2 by linarith)).compLpL 2 (timeMeasure T)
        (maximalRegularitySolField b hT f) =
      maximalRegularitySolField a hT
        ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f) := by
  apply timeModeCoeff_injective
  intro i
  rw [timeModeCoeff_compLpL_dirichletHsInclusion,
    maximalRegularitySolField_timeModeCoeff,
    maximalRegularitySolField_timeModeCoeff]
  unfold solModeCoeff
  rw [timeModeCoeff_compLpL_dirichletHsInclusion]

theorem maximalRegularityDuhamelSolField_compLpL_dirichletHsInclusion
    (hab : a ≤ b) (hT : 0 < T) (u₀ : DirichletHs g (b + 1))
    (f : timeL2 (DirichletHs g b) T) :
    (dirichletHsInclusion (show a + 2 ≤ b + 2 by linarith)).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelSolField b hT u₀ f) =
      maximalRegularityDuhamelSolField a hT
        (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)
        ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f) := by
  apply timeModeCoeff_injective
  intro i
  rw [timeModeCoeff_compLpL_dirichletHsInclusion,
    maximalRegularityDuhamelSolField, maximalRegularityDuhamelSolField,
    timeModeCoeff_add, timeModeCoeff_add,
    maximalRegularityHomogeneousSolField_timeModeCoeff hT.le,
    maximalRegularityHomogeneousSolField_timeModeCoeff hT.le,
    maximalRegularitySolField_timeModeCoeff,
    maximalRegularitySolField_timeModeCoeff]
  unfold solModeCoeff
  rw [timeModeCoeff_compLpL_dirichletHsInclusion]
  rfl

theorem maximalRegularityDuhamelSolFieldHa1_compLpL_dirichletHsInclusion
    (hab : a ≤ b) (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (b + 1)) (f : timeL2 (DirichletHs g b) T) :
    (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith)).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelSolFieldHa1 b hT u₀ f) =
      maximalRegularityDuhamelSolFieldHa1 a hT
        (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)
        ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f) := by
  apply timeModeCoeff_injective
  intro i
  rw [timeModeCoeff_compLpL_dirichletHsInclusion,
    maximalRegularityDuhamelSolFieldHa1, maximalRegularityDuhamelSolFieldHa1,
    timeModeCoeff_add, timeModeCoeff_add,
    maximalRegularityHomogeneousSolFieldHa1_timeModeCoeff hT.le,
    maximalRegularityHomogeneousSolFieldHa1_timeModeCoeff hT.le,
    maximalRegularitySolFieldHa1_timeModeCoeff hT hT1,
    maximalRegularitySolFieldHa1_timeModeCoeff hT hT1]
  unfold solModeCoeff
  rw [timeModeCoeff_compLpL_dirichletHsInclusion]
  rfl

theorem maximalRegularityDuhamelMap_deriv_compLpL_dirichletHsInclusion
    (hab : a ≤ b) (hT : 0 < T) (u₀ : DirichletHs g (b + 1))
    (f : timeL2 (DirichletHs g b) T) :
    (dirichletHsInclusion hab).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelMap b hT u₀ f).deriv =
      (maximalRegularityDuhamelMap a hT
        (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)
        ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f)).deriv := by
  apply timeModeCoeff_injective
  intro i
  rw [timeModeCoeff_compLpL_dirichletHsInclusion,
    maximalRegularityDuhamelMap_deriv, maximalRegularityDuhamelMap_deriv,
    timeModeCoeff_add, timeModeCoeff_add,
    maximalRegularityHomogeneousDerivField_timeModeCoeff hT.le,
    maximalRegularityHomogeneousDerivField_timeModeCoeff hT.le,
    maximalRegularityDerivField_timeModeCoeff,
    maximalRegularityDerivField_timeModeCoeff]
  unfold derivModeCoeff
  rw [timeModeCoeff_compLpL_dirichletHsInclusion]
  rfl


theorem maximalRegularityDuhamelMap_toFun_dirichletHsInclusion
    (hab : a ≤ b) (hT : 0 < T) (u₀ : DirichletHs g (b + 1))
    (f : timeL2 (DirichletHs g b) T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    dirichletHsInclusion hab ((maximalRegularityDuhamelMap b hT u₀ f).toFun t) =
      (maximalRegularityDuhamelMap a hT
        (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)
        ((dirichletHsInclusion hab).compLpL 2 (timeMeasure T) f)).toFun t := by
  let J := dirichletHsInclusion (g := g) hab
  let u := maximalRegularityDuhamelMap b hT u₀ f
  let v := maximalRegularityDuhamelMap a hT
    (dirichletHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)
    (J.compLpL 2 (timeMeasure T) f)
  change J (u.toFun t) = v.toFun t
  have hder : (fun s => J (u.deriv s)) =ᵐ[timeMeasure T] v.deriv := by
    have h := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) u.deriv
    rw [show J.compLpL 2 (timeMeasure T) u.deriv = v.deriv from
      maximalRegularityDuhamelMap_deriv_compLpL_dirichletHsInclusion hab hT u₀ f] at h
    exact h.symm
  have hint : (∫ s in (0 : ℝ)..t, J (u.deriv s)) = ∫ s in (0 : ℝ)..t, v.deriv s := by
    apply intervalIntegral.integral_congr_ae
    apply ae_imp_of_ae_restrict
    exact hder.filter_mono (ae_mono (Measure.restrict_mono
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, hT.le⟩ ht)) le_rfl))
  have hinit : J u.init = v.init := by
    dsimp only [u, v]
    rw [maximalRegularityDuhamelMap_init, maximalRegularityDuhamelMap_init]
    apply DirichletHs.ext
    rfl
  rw [timeH1.toFun_apply, timeH1.toFun_apply, map_add, hinit,
    ← J.intervalIntegral_comp_comm (u.intervalIntegrable_deriv ⟨le_rfl, hT.le⟩ ht), hint]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity
