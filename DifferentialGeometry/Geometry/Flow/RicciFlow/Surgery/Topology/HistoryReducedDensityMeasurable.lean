import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.EndpointContinuity
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem regularizedDensity_eq_zero_iff
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedDensity first last hle T B v p q = 0 ↔
      H.regularizedCost first last hle T B 0 v p q = ⊤ := by
  rw [H.regularizedCost_eq_top_iff]
  constructor
  · intro hzero A hA
    by_contra hne
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
    have hle : ENNReal.ofReal (Real.exp (-a / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        H.regularizedDensity first last hle T B v p q :=
      le_iSup_of_le a (le_iSup_of_le hA le_rfl)
    rw [hzero] at hle
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).not_ge hle
  · intro htop
    apply le_antisymm ?_ zero_le
    apply iSup_le
    intro A
    apply iSup_le
    intro hA
    exact (WithTop.coe_ne_top (htop A hA)).elim

theorem regularizedDensity_pos_iff
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    0 < H.regularizedDensity first last hle T B v p q ↔
      H.regularizedCost first last hle T B 0 v p q ≠ ⊤ := by
  rw [pos_iff_ne_zero]
  exact not_congr (H.regularizedDensity_eq_zero_iff first last hle T B v p q)

private local instance (j : Fin (H.eventCount + 1)) :
    MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) :
    BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem measurable_regularizedDensity
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) :
    Measurable (H.regularizedDensity first last hle T B v p) := by
  classical
  have hmeas : Measurable (H.regularizedCost first last hle T B 0 v p) :=
    (H.lowerSemicontinuous_regularizedCost first last hle T B 0 v
      (by simpa only [zero_pow two_ne_zero, sub_zero] using hupper) hscalar p).measurable
  let f : WithTop ℝ → ℝ≥0∞ := fun C =>
    if C = ⊤ then 0 else ENNReal.ofReal (Real.exp (-C.untopD 0 / (2 * v) -
      (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hf : Measurable f := by
    apply WithTop.measurable_of_measurable_comp_coe
    have hcont : Continuous (fun C : ℝ => ENNReal.ofReal (Real.exp (-C / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (((continuous_id.neg.div_const _).sub continuous_const).sub continuous_const))
    simpa only [f, WithTop.coe_ne_top, ↓reduceIte, WithTop.untopD_coe] using hcont.measurable
  have heq : H.regularizedDensity first last hle T B v p =
      f ∘ (fun q => H.regularizedCost first last hle T B 0 v p q) := by
    funext q
    by_cases htop : H.regularizedCost first last hle T B 0 v p q = ⊤
    · simp only [Function.comp_apply, f, htop, ↓reduceIte]
      exact (H.regularizedDensity_eq_zero_iff first last hle T B v p q).mpr htop
    · obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp htop
      have hd := H.regularizedDensity_eq_exp_of_cost_eq first last hle T B hv hupper hscalar p q hA.symm
      simpa only [Function.comp_apply, f, ← hA, WithTop.coe_ne_top, ↓reduceIte,
        WithTop.untopD_coe] using hd
  rw [heq]
  exact hf.comp hmeas

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
