import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FixedMassTrace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.EnergyDuality

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_continuous_dirichletHs_zero_representative
    (q : SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 < T)
    (u : timeH1 (DirichletHs q (-1)) T)
    (U₁ : timeL2 (DirichletHs q 1) T)
    (hfield : (fun t => dirichletHsInclusion (show (-1 : ℝ) ≤ 1 by norm_num) (U₁ t))
      =ᵐ[timeMeasure T] u.toFun) :
    ∃ U : ℝ → DirichletHs q 0,
      ContinuousOn U (Icc (0 : ℝ) T) ∧
      (U =ᵐ[timeMeasure T] fun t =>
        dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₁ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U t) = u.toFun t) ∧
      ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
        ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
          ∫ t in a..b, 2 * dirichletHsNegOneEquivH1Dual q (u.deriv t)
            (dirichletHsOneEquivH1Compl q (U₁ t)) := by
  let L := (dirichletHsOneEquivH1Compl q).toContinuousLinearEquiv.toContinuousLinearMap
  let R := (dirichletHsNegOneRieszEquivH1Compl q).toContinuousLinearEquiv.toContinuousLinearMap
  let v := L.compLpL 2 (timeMeasure T) U₁
  have hv : v =ᵐ[timeMeasure T] fun t => L (U₁ t) := L.coeFn_compLpL U₁
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_comp_clm R u
  have hmass : (fun t => resolventDirichlet q (H1ComplDirichletToLp q (v t)))
      =ᵐ[timeMeasure T] w.toFun := by
    filter_upwards [hv, hfield, ae_restrict_mem measurableSet_Icc] with t hvt ht htmem
    rw [hvt, hw t htmem]
    change resolventDirichlet q
      (H1ComplDirichletToLp q (dirichletHsOneEquivH1Compl q (U₁ t))) = R (u.toFun t)
    rw [H1ComplDirichletToLp_dirichletHsOneEquivH1Compl,
      ← dirichletHsNegOneRieszEquivH1Compl_inclusion_zero,
      ← DirichletHs.dirichletHsInclusion_trans_apply, ht]
    rfl
  obtain ⟨V, hVcont, hVae, hVenergy⟩ :=
    exists_continuous_l2_representative_of_resolvent_timeH1 q v w hmass
  let U := fun t => (dirichletHsZeroEquivL2 q).symm (V t)
  have hUcont : ContinuousOn U (Icc (0 : ℝ) T) :=
    (dirichletHsZeroEquivL2 q).symm.continuous.comp_continuousOn hVcont
  have hUae : U =ᵐ[timeMeasure T] fun t =>
      dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₁ t) := by
    filter_upwards [hVae, hv] with t ht hvt
    change (dirichletHsZeroEquivL2 q).symm (V t) = _
    rw [ht, hvt]
    change (dirichletHsZeroEquivL2 q).symm
      (H1ComplDirichletToLp q (dirichletHsOneEquivH1Compl q (U₁ t))) = _
    rw [H1ComplDirichletToLp_dirichletHsOneEquivH1Compl,
      LinearIsometryEquiv.symm_apply_apply]
  have heq : (fun t => dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U t))
      =ᵐ[timeMeasure T] u.toFun := by
    filter_upwards [hUae, hfield] with t ht hf
    rw [ht, ← DirichletHs.dirichletHsInclusion_trans_apply]
    exact hf
  refine ⟨U, hUcont, hUae, ?_, ?_⟩
  · exact Measure.eqOn_Icc_of_ae_eq (μ := volume) hT.ne heq
      ((dirichletHsInclusion (g := q) (show (-1 : ℝ) ≤ 0 by norm_num)).continuous.comp_continuousOn
        hUcont) u.continuousOn_toFun
  · intro a b ha hb
    change ‖(dirichletHsZeroEquivL2 q).symm (V b)‖ ^ 2 -
      ‖(dirichletHsZeroEquivL2 q).symm (V a)‖ ^ 2 = _
    rw [(dirichletHsZeroEquivL2 q).symm.norm_map,
      (dirichletHsZeroEquivL2 q).symm.norm_map, hVenergy a b ha hb]
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hv,
      ae_mono (Measure.restrict_mono hsub le_rfl) hwd] with t hvt hwt
    rw [hvt, hwt, dirichletHsNegOneEquivH1Dual_apply, real_inner_comm]
    rfl

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
