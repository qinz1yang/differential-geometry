import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Curvature.DimensionThree
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- The quantitative logarithmic step used in KL (86.7): a bounded scalar
at a sufficiently small time-normalized scale forces a sectional lower bound. -/
theorem fixedHI_negative_bound_CX12 {a R ν K D : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (hlarge : Real.exp (K + 4) * D ≤ a)
    (hreg : (R, ν) ∈ fixedHamiltonIveyRegion a) (hR : R ≤ K / D) :
    -ν ≤ D⁻¹ := by
  by_contra hn
  have hn : D⁻¹ < -ν := lt_of_not_ge hn
  have hν : 0 < -ν := (inv_pos.mpr hD).trans hn
  have ha : 0 < a := (mul_pos (Real.exp_pos _) hD).trans_le hlarge
  have harg : Real.exp (K + 4) ≤ a * (-ν) := by
    have he : Real.exp (K + 4) ≤ a / D := (le_div_iff₀ hD).mpr hlarge
    calc Real.exp (K + 4) ≤ a / D := he
      _ = a * D⁻¹ := div_eq_mul_inv _ _
      _ ≤ a * (-ν) := mul_le_mul_of_nonneg_left hn.le ha.le
  have hlog : K + 4 ≤ Real.log (a * (-ν)) :=
    (Real.le_log_iff_exp_le (mul_pos ha hν)).mpr harg
  have hb : (-ν) * (Real.log (a * (-ν)) - 3) ≤ R := by
    rcases hreg with h | h
    · linarith
    · exact h
  have hprod : D⁻¹ * (K + 1) ≤ (-ν) * (Real.log (a * (-ν)) - 3) :=
    mul_le_mul hn.le (by linarith) (by linarith) hν.le
  have hlt : K / D < D⁻¹ * (K + 1) := by
    have := (div_lt_div_iff_of_pos_right hD).mpr (lt_add_one K)
    simpa only [div_eq_mul_inv, mul_comm] using this
  exact (not_lt_of_ge (hprod.trans (hb.trans hR))) hlt

/-- Small normalized radius turns the preceding numerical estimate into
the exact `-r⁻²` sectional lower bound, on any three-manifold. -/
theorem sectional_of_fixedHI_small_scale_CX12
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (gm : SmoothRiemannianMetric ThreeModel M) (x : M)
    {a K r : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hlarge : Real.exp (K + 4) * r ^ 2 ≤ a)
    (hreg : InFixedHamiltonIveyRegion gm a x)
    (hR : metricScalarAt gm x ≤ K / r ^ 2) :
    SectionalBoundedBelowAt gm x (-(r ^ 2)⁻¹) := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt gm x hdim
  have hneg := fixedHI_negative_bound_CX12 (by positivity : 0 < r ^ 2) hK hlarge
    ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion gm a x).mp hreg) hR
  rw [sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt hdim,
    curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le basis horth]
  have hinv : 0 ≤ (r ^ 2)⁻¹ := by positivity
  linarith

/-- A positive scale depending only on the desired scalar bound. -/
theorem exists_HI_scale_CX12 (K : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ t r : ℝ, 0 ≤ t → 0 ≤ r → r ≤ b * Real.sqrt t →
      Real.exp (K + 4) * r ^ 2 ≤ t := by
  let b := Real.sqrt (Real.exp (-(K + 4)))
  have hb : 0 < b := Real.sqrt_pos.mpr (Real.exp_pos _)
  refine ⟨b, hb, ?_⟩
  intro t r ht hr hsize
  have hs := pow_le_pow_left₀ hr hsize 2
  have hb2 : b ^ 2 = Real.exp (-(K + 4)) := Real.sq_sqrt (Real.exp_pos _).le
  rw [mul_pow, hb2, Real.sq_sqrt ht] at hs
  calc Real.exp (K + 4) * r ^ 2
      ≤ Real.exp (K + 4) * (Real.exp (-(K + 4)) * t) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = t := by rw [← mul_assoc, ← Real.exp_add]; simp

/-- Transport of the profile's fixed Hamilton--Ivey region to every time
of a slice history. This includes the post-surgery metric at event times.
The transport follows the independently frozen O16 pinching adapter. -/
theorem slice_history_fixedHI_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (v : Icc (0 : ℝ) s.history.horizon) :
    ∀ x, InFixedHamiltonIveyRegion (s.history.stageMetric (s.history.activeStage v) v)
      (Hp.pinchingShift + v) x := by
  have hv0 : (0 : ℝ) ≤ v := v.2.1
  have hvs : (v : ℝ) ≤ s.time := v.2.2
  let t : Icc (0 : ℝ) (v : ℝ) := ⟨v, hv0, le_rfl⟩
  have hst := F.observation.observe_slice_stage v s.time hv0 s.positive.le hvs t
  have hmet := F.observation.observe_slice_metric v s.time hv0 s.positive.le hvs t
  obtain ⟨hs0, hm0⟩ := postData_observe_O3 F.observation v hv0
  have hlast : (F.observation.observe v hv0).activeStage t =
      Fin.last (F.observation.observe v hv0).eventCount :=
    (F.observation.observe v hv0).activeStage_at_horizon
  have hst' : postStage F.observation v = s.history.stageAt v := by
    refine hs0.trans ?_
    have h1 : (F.observation.observe v hv0).stageAt t =
        (F.observation.observe v hv0).stage (Fin.last _) := by
      change (F.observation.observe v hv0).stage ((F.observation.observe v hv0).activeStage t) = _
      rw [hlast]
    exact h1.symm.trans hst
  have hm' : HEq (postMetric F.observation v)
      (s.history.stageMetric (s.history.activeStage v) v) := by
    refine hm0.trans ?_
    refine (stageMetric_heq_of_index_eq_O3 _ hlast.symm (v : ℝ)).trans ?_
    exact hmet
  exact stageMetric_transport_O3 hst' hm'
    (fun Q m => ∀ x : Q.Carrier, InFixedHamiltonIveyRegion m (Hp.pinchingShift + v) x)
    (Hp.pinching v hv0)

/-- The scalar-to-sectional conversion is uniform over all slice histories,
including their nonregular observation times. -/
theorem slice_history_sectional_of_scalar_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) s.history.horizon) (x : (s.history.stageAt v).Carrier) (r : ℝ),
      0 < r → r ≤ b * Real.sqrt v →
      metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x ≤ K / r ^ 2 →
      SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage v) v) x (-(r ^ 2)⁻¹) := by
  obtain ⟨b, hb, hscale⟩ := exists_HI_scale_CX12 K
  refine ⟨b, hb, fun s v x r hr hsize hR => ?_⟩
  exact sectional_of_fixedHI_small_scale_CX12 _ x hr hK
    ((hscale v r v.2.1 hr.le hsize).trans
      (le_add_of_nonneg_left Hp.pinchingShift_pos.le))
    (slice_history_fixedHI_CX12 Hp s v x) hR

end GC.LongTime.Ch12
