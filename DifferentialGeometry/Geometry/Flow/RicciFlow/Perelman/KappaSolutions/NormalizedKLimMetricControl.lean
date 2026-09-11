import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMetricLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance normalizedMetricControlTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance normalizedMetricControlCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance normalizedMetricControlSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance normalizedMetricControlC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedMetricControlT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance normalizedMetricControlSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance normalizedMetricControlTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

private theorem terminal_scalar_ricci_bound
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}
    {kappa C s : ℝ} (hK : KLim kappa F) (hs : s ≤ 0)
    (x : F.M) (hC : F.S.scalar 0 x ≤ C) (v : TangentSpace I x) :
    0 ≤ F.S.ricciAt s x (vec2 v v) ∧
      F.S.ricciAt s x (vec2 v v) ≤ (C / 2) * (F.S.base.metric s).inner x v v := by
  have hscar : s ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using hs
  have hcone : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric s) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric s) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hK.nonnegativeCurvatureOperator s hscar x n c a b
  have hv : 0 ≤ (F.S.base.metric s).inner x v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact ((F.S.base.metric s).pos x v hz).le
  change 0 ≤ metricRicciAt (I := I) (F.S.base.metric s) x (vec2 v v) ∧ _
  refine ⟨metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    (F.S.base.metric s) x hcone v, ?_⟩
  have hR : metricScalarAt (I := I) (F.S.base.metric s) x ≤ C :=
    (hK.scalar_le_terminal hs x).trans hC
  exact (metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
    (F.S.base.metric s) x hcone v).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR (by norm_num)) hv)

theorem KLim.metric_inner_le_exp_terminal_bound
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}
    {kappa C s : ℝ} (hK : KLim kappa F) (hs : s ≤ 0)
    (x : F.M) (hC : F.S.scalar 0 x ≤ C) (v : TangentSpace I x) :
    (F.S.base.metric s).inner x v v ≤
      Real.exp (C * (-s)) * (F.S.base.metric 0).inner x v v := by
  have hslab : Icc s 0 ⊆ D.carrier := by
    intro q hq
    simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2
  have hreg : Ioo s 0 ⊆ D.regular := by
    intro q hq
    simpa only [hK.regular_eq, Set.mem_Iio] using hq.2
  have hRic : ∀ q ∈ Ioo s 0, ∀ y ∈ ({x} : Set F.M), ∀ w : TangentSpace I y,
      F.S.ricciAt q y (vec2 w w) ≤ (C / 2) * (F.S.base.metric q).inner y w w := by
    intro q hq y hy w
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact (terminal_scalar_ricci_bound hK hq.2.le x hC w).2
  have hraw := metric_inner_lower_bound_of_ricci_upper_interior F.S F.isSolution
    hs hslab hreg hRic (Set.mem_singleton x) v
  have heq : 2 * (C / 2) * (0 - s) = C * (-s) := by ring
  rw [heq] at hraw
  calc
    (F.S.base.metric s).inner x v v =
        Real.exp (C * (-s)) *
          (Real.exp (-(C * (-s))) * (F.S.base.metric s).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C * (-s)) * (F.S.base.metric 0).inner x v v :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le

theorem KLim.ricci_le_exp_terminal_bound
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}
    {kappa C s : ℝ} (hK : KLim kappa F) (hs : s ≤ 0)
    (x : F.M) (hC : F.S.scalar 0 x ≤ C) (v : TangentSpace I x) :
    0 ≤ F.S.ricciAt s x (vec2 v v) ∧
      F.S.ricciAt s x (vec2 v v) ≤
        ((C / 2) * Real.exp (C * (-s))) * (F.S.base.metric 0).inner x v v := by
  have hC0 : 0 ≤ C := (hK.scalar_nonneg le_rfl x).trans hC
  have hRic := terminal_scalar_ricci_bound hK hs x hC v
  refine ⟨hRic.1, hRic.2.trans ?_⟩
  calc
    (C / 2) * (F.S.base.metric s).inner x v v ≤
        (C / 2) * (Real.exp (C * (-s)) * (F.S.base.metric 0).inner x v v) :=
      mul_le_mul_of_nonneg_left
        (hK.metric_inner_le_exp_terminal_bound hs x hC v) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

theorem KLim.ricci_energy_bound_on_backward_slab
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}
    {kappa C B a s : ℝ} (hK : KLim kappa F) (hs : s ∈ Icc a 0)
    (x : F.M) (hC : F.S.scalar 0 x ≤ C) (v : TangentSpace I x)
    (hB : (F.S.base.metric 0).inner x v v ≤ B) :
    ‖F.S.ricciAt s x (vec2 v v)‖ ≤ ((C / 2) * Real.exp (C * (-a))) * B := by
  have hC0 : 0 ≤ C := (hK.scalar_nonneg le_rfl x).trans hC
  have hv : 0 ≤ (F.S.base.metric 0).inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg
      (F.S.base.metric 0) x v
  have hRic := hK.ricci_le_exp_terminal_bound hs.2 x hC v
  rw [Real.norm_eq_abs, abs_of_nonneg hRic.1]
  apply hRic.2.trans
  have hexp : Real.exp (C * (-s)) ≤ Real.exp (C * (-a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (neg_le_neg hs.1) hC0)
  calc
    ((C / 2) * Real.exp (C * (-s))) * (F.S.base.metric 0).inner x v v ≤
        ((C / 2) * Real.exp (C * (-a))) * (F.S.base.metric 0).inner x v v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by positivity)) hv
    _ ≤ ((C / 2) * Real.exp (C * (-a))) * B :=
      mul_le_mul_of_nonneg_left hB (by positivity)

theorem exists_normalized_klim_backward_metric_constants [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A s : ℝ, s ≤ 0 → ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A → ∀ v : TangentSpace I y,
          ((F.S.base.metric 0).inner y v v ≤ (F.S.base.metric s).inner y v v ∧
            (F.S.base.metric s).inner y v v ≤
              Real.exp (C A * (-s)) * (F.S.base.metric 0).inner y v v) ∧
          (0 ≤ F.S.ricciAt s y (vec2 v v) ∧
            F.S.ricciAt s y (vec2 v v) ≤
              ((C A / 2) * Real.exp (C A * (-s))) * (F.S.base.metric 0).inner y v v) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants (I := I) hdim kappa
  refine ⟨C, hC, ?_⟩
  intro D F hK hbase A s hs y hy v
  have hscalar := (hbound D F hK hbase A y hy 0 le_rfl).1.2
  exact ⟨⟨hK.metric_inner_le hs le_rfl y v,
    hK.metric_inner_le_exp_terminal_bound hs y hscalar v⟩,
    hK.ricci_le_exp_terminal_bound hs y hscalar v⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
