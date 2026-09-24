import DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartGramOp_unit {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target)
    (p : Real × E) (hp : p ∈ J ×ˢ K) :
    IsUnit (chartGramOp (I := I) G alpha p) := by
  obtain ⟨c, hc, hlower⟩ := chartGramOp_lower (I := I) hG
    (show ({p.1} : Set Real) ⊆ D.regular from fun t ht => by
      rcases Set.mem_singleton_iff.mp ht with rfl
      exact hJ hp.1)
    isCompact_singleton alpha
    (show ({p.2} : Set E) ⊆ interior (extChartAt I alpha).target from fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hK hp.2)
    isCompact_singleton
  let B : E →L[Real] E →L[Real] Real :=
    chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
      ((extChartAt I alpha).symm p.2)
  have hco : IsCoercive B := by
    refine ⟨c, hc, ?_⟩
    intro v
    have hv := hlower p (by simp) v
    have heq : B v v =
        inner Real (chartGramOp (I := I) G alpha p v) v := by
      dsimp only [B]
      rw [chartGramBilin_eq_innerJinv]
      exact (chartGramOp_inner (I := I) G alpha p v v).symm
    rw [heq]
    simpa only [pow_two, mul_assoc] using hv
  change IsUnit (IsCoercive.gramCLM B)
  exact IsCoercive.gramCLM_isUnit hco

theorem chartGramInv_smooth {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target) :
    ContDiffOn Real ∞
      (fun p => Ring.inverse (chartGramOp (I := I) G alpha p))
      (J ×ˢ K) := by
  have hGram : ContDiffOn Real ∞ (chartGramOp (I := I) G alpha)
      (J ×ˢ K) :=
    (chartGramOp_smooth (I := I) hG alpha hK).mono
      (prod_mono hJ Subset.rfl)
  intro p hp
  have hunit := chartGramOp_unit (I := I) hG hJ alpha hK p hp
  exact (contDiffAt_ringInverse Real (IsUnit.unit hunit)).comp_contDiffWithinAt
    p (hGram p hp)

theorem chartGramInv_cont {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target) :
    ContinuousOn (fun p => Ring.inverse (chartGramOp (I := I) G alpha p))
      (J ×ˢ K) := by
  intro p hp
  obtain ⟨u, hu⟩ := chartGramOp_unit (I := I) hG hJ alpha hK p hp
  have hinv : ContinuousAt (fun A : E →L[Real] E => Ring.inverse A)
      (chartGramOp (I := I) G alpha p) := by
    rw [show chartGramOp (I := I) G alpha p = (u : E →L[Real] E) from hu.symm]
    exact NormedRing.inverse_continuousAt u
  simpa only [Function.comp_def] using hinv.continuousWithinAt.comp
    (chartGramOp_cont (I := I) hG hJ alpha hK p hp) (mapsTo_univ _ _)

end DifferentialGeometry.Geometry.Curvature

end

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartGramOp_unit_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.carrier) (alpha : M) {K : Set E}
    (hK : K ⊆ (extChartAt I alpha).target)
    (p : Real × E) (hp : p ∈ J ×ˢ K) :
    IsUnit (chartGramOp (I := I) G alpha p) := by
  obtain ⟨c, hc, hlower⟩ := chartGramOp_lower_of_carrier (I := I) hG
    (show ({p.1} : Set Real) ⊆ D.carrier from fun t ht => by
      rcases Set.mem_singleton_iff.mp ht with rfl
      exact hJ hp.1)
    isCompact_singleton alpha
    (show ({p.2} : Set E) ⊆ (extChartAt I alpha).target from fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hK hp.2)
    isCompact_singleton
  let B : E →L[Real] E →L[Real] Real :=
    chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
      ((extChartAt I alpha).symm p.2)
  have hco : IsCoercive B := by
    refine ⟨c, hc, ?_⟩
    intro v
    have hv := hlower p (by simp) v
    have heq : B v v =
        inner Real (chartGramOp (I := I) G alpha p v) v := by
      dsimp only [B]
      rw [chartGramBilin_eq_innerJinv]
      exact (chartGramOp_inner (I := I) G alpha p v v).symm
    rw [heq]
    simpa only [pow_two, mul_assoc] using hv
  change IsUnit (IsCoercive.gramCLM B)
  exact IsCoercive.gramCLM_isUnit hco

theorem chartGramInv_continuousOn_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.carrier) (alpha : M) {K : Set E}
    (hK : K ⊆ (extChartAt I alpha).target) :
    ContinuousOn (fun p => Ring.inverse (chartGramOp (I := I) G alpha p))
      (J ×ˢ K) := by
  intro p hp
  obtain ⟨u, hu⟩ := chartGramOp_unit_of_carrier (I := I) hG hJ alpha hK p hp
  have hinv : ContinuousAt (fun A : E →L[Real] E => Ring.inverse A)
      (chartGramOp (I := I) G alpha p) := by
    rw [show chartGramOp (I := I) G alpha p = (u : E →L[Real] E) from hu.symm]
    exact NormedRing.inverse_continuousAt u
  simpa only [Function.comp_def] using hinv.continuousWithinAt.comp
    (chartGramOp_continuousOn_of_carrier (I := I) hG hJ alpha hK p hp) (mapsTo_univ _ _)

end DifferentialGeometry.Geometry.Curvature

end
section

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem contDiffOn_chart_velocity_of_momentum {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) (tau : Real → Real) (u q P : Real → E) {U : Set Real}
    {n : ℕ∞} (htau : ContDiffOn Real n tau U)
    (hu : ContDiffOn Real n u U) (hP : ContDiffOn Real n P U)
    (htime : MapsTo tau U D.regular)
    (hchart : MapsTo u U (interior (extChartAt I alpha).target))
    (hPeq : EqOn P (fun s => (2 : Real) •
      chartGramOp (I := I) G alpha (tau s, u s) (q s)) U) :
    ContDiffOn Real n q U := by
  have hinv : ContDiffOn Real n
      (fun s => Ring.inverse (chartGramOp (I := I) G alpha (tau s, u s))) U :=
    ((chartGramInv_smooth (I := I) hG Subset.rfl alpha Subset.rfl).of_le
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
      (htau.prodMk hu) (fun s hs => ⟨htime hs, hchart hs⟩)
  refine ((hinv.clm_apply hP).const_smul (1 / 2 : Real)).congr ?_
  intro s hs
  rw [hPeq hs, ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit (I := I) hG Subset.rfl alpha Subset.rfl
    (tau s, u s) ⟨htime hs, hchart hs⟩
  have hmul := congrArg (fun A : E →L[Real] E => A (q s))
    (Ring.inverse_mul_cancel _ hunit)
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : Real) ≠ 0), one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using hmul.symm

end DifferentialGeometry.Geometry.Curvature

end

end
