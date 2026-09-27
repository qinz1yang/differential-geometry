import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankContinuity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientNullPlane
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private theorem curvature_rank_le_one_at_negative_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hcarrier : D.carrier = Iic 0) (hregular : D.regular = Iio 0)
    (hR : ∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hzero : leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x) = 0)
    {t : ℝ} (ht : t < 0) (y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) y
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) y)) ≤ 1 := by
  have hreg : Icc (t - 1) t ⊆ D.regular := by
    intro r hr
    rw [hregular]
    exact hr.2.trans_lt ht
  have hcone : ∀ r ∈ Icc (t - 1) t, ∀ z : M,
      (⟨metricRm04At (S.family.metric r) z,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) z⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) z) ∈
            algebraicCurvatureOperatorNonnegativeCone := by
    intro r hr z
    exact hR r (hr.2.trans ht.le) z
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time
    S hS hdim (s := t - 1) (t := t) (by linarith) hreg hcone x
  have hconstant := curvatureOperatorImageAt_finrank_eq_at_later_time
    S hS hdim (s := t - 1) (t := t) (by linarith) hreg hcone y x
  have hnull :=
    Perelman.KappaSolutions.leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero
      S hS hdim hcarrier hregular hR x hzero ht
  have hne : Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≠ 3 := by
    intro hthree
    have hpos := leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
      (S.base.metric t) x hdim (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)
      (hR t ht.le x) hthree
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  change Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
    (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 0 ∨
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 1 ∨
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 3 at htri
  change Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) y
    (metricAlgebraicCurvatureTensorAt (S.base.metric t) y)) =
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) at hconstant
  omega


theorem curvatureOperatorImageAt_finrank_le_one_of_terminal_least_eigenvalue_eq_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hcarrier : D.carrier = Iic 0) (hregular : D.regular = Iio 0)
    (hR : ∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hzero : leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x) = 0)
    {t : ℝ} (ht : t ≤ 0) (y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) y
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) y)) ≤ 1 := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact curvature_rank_le_one_at_negative_time S hS hdim hcarrier hregular hR x hzero hlt y
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U := (S.timeShift (-1)).timeRestrict (RealTimeInterval.closed 0 1 (by norm_num))
  have hcar : (RealTimeInterval.closed 0 1 (by norm_num)).carrier ⊆
      (D.timeShift (-1)).carrier := by
    intro r hr
    change r + -1 ∈ D.carrier
    rw [hcarrier]
    change r ∈ Icc 0 1 at hr
    exact sub_nonpos.mpr hr.2
  have hreg : (RealTimeInterval.closed 0 1 (by norm_num)).regular ⊆
      (D.timeShift (-1)).regular := by
    intro r hr
    change r + -1 ∈ D.regular
    rw [hregular]
    change r ∈ Ioo 0 1 at hr
    exact sub_neg.mpr hr.2
  have hU : IsSolutionOn U :=
    isSolutionOn_timeRestrict (isSolutionOn_timeShift hS (-1)) hcar hreg
  have hbound : ∀ r ∈ Ioo 0 1,
      Module.finrank ℝ (curvatureOperatorImageAt (U.base.metric r) y
        (metricAlgebraicCurvatureTensorAt (U.base.metric r) y)) ≤ 1 := by
    intro r hr
    exact curvature_rank_le_one_at_negative_time S hS hdim hcarrier hregular hR x hzero
      (show r + -1 < 0 from sub_neg.mpr hr.2) y
  have hend := curvatureOperatorImageAt_finrank_le_at_terminal (by norm_num : (0 : ℝ) < 1)
    U hU (fun _ => hdim) y hbound
  have hmetric : U.base.metric 1 = S.base.metric 0 := by
    change S.base.metric ((1 : ℝ) + -1) = S.base.metric 0
    rw [add_neg_cancel]
  rw [hmetric] at hend
  exact hend

open scoped _root_.Topology in
open Filter in
theorem exists_curvatureOperatorImageAt_finrank_eq_one_on_terminal_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hcarrier : D.carrier = Iic 0) (hregular : D.regular = Iio 0)
    (hR : ∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hnotflat : ∃ t ≤ 0, ∃ y : M, metricRm04At (S.base.metric t) y ≠ 0)
    (x : M)
    (hzero : leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x) = 0) :
    ∃ s < 0, ∀ t ∈ Ioo s 0, ∀ y : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) y
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) y)) = 1 := by
  let rank (t : ℝ) (y : M) := Module.finrank ℝ
    (curvatureOperatorImageAt (S.base.metric t) y
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) y))
  obtain ⟨s, hs, z, hpositive⟩ : ∃ s < 0, ∃ y : M, 0 < rank s y := by
    obtain ⟨t, ht, y, hnonzero⟩ := hnotflat
    have hpositive : 0 < rank t y := by
      apply Nat.pos_of_ne_zero
      intro hrank
      let _ : FiniteDimensional ℝ (TangentSpace I y [⋀^Fin 2]→L[ℝ] ℝ) :=
        (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
          (Module.finBasis ℝ (TangentSpace I y))).finiteDimensional_of_finite
      have hbot : curvatureOperatorImageAt (S.base.metric t) y
          (metricAlgebraicCurvatureTensorAt (S.base.metric t) y) = ⊥ :=
        Submodule.finrank_eq_zero.mp hrank
      apply hnonzero
      apply metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
        (S.base.metric t) y hdim
      apply ContinuousLinearMap.ext
      intro a
      have ha : curvatureOperatorEndomorphismAt (S.base.metric t) y
          (metricAlgebraicCurvatureTensorAt (S.base.metric t) y) a ∈
          curvatureOperatorImageAt (S.base.metric t) y
            (metricAlgebraicCurvatureTensorAt (S.base.metric t) y) := ⟨a, rfl⟩
      rw [hbot] at ha
      simpa [metricAlgebraicCurvatureTensorAt] using ha
    rcases lt_or_eq_of_le ht with htneg | rfl
    · exact ⟨t, htneg, y, hpositive⟩
    · have hlow : ∀ᶠ r in 𝓝[D.carrier] (0 : ℝ), rank 0 y ≤ rank r y :=
        curvatureOperatorImageAt_finrank_eventually_ge S hS hdim y
          (by simp only [hcarrier, mem_Iic, le_refl])
      rw [hcarrier] at hlow
      have hleft : ∀ᶠ r in 𝓝[<] (0 : ℝ), rank 0 y ≤ rank r y :=
        hlow.filter_mono (nhdsWithin_mono 0 Iio_subset_Iic_self)
      obtain ⟨s, hsrank, hs⟩ := (hleft.and self_mem_nhdsWithin).exists
      exact ⟨s, hs, y, hpositive.trans_le hsrank⟩
  refine ⟨s, hs, ?_⟩
  intro t ht y
  change rank t y = 1
  have hle : rank s z ≤ rank t y :=
    curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim ht.1
      (by intro r hr; rw [hregular]; exact hr.2.trans_lt ht.2)
      (fun r hr => hR r (hr.2.trans ht.2.le)) z y
  have hupper : rank t y ≤ 1 :=
    curvatureOperatorImageAt_finrank_le_one_of_terminal_least_eigenvalue_eq_zero
      S hS hdim hcarrier hregular hR x hzero ht.2.le y
  exact Nat.le_antisymm hupper (Nat.succ_le_iff.mpr (hpositive.trans_le hle))

end DifferentialGeometry.PDE.RicciFlow
