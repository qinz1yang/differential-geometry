import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



noncomputable section

open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis


def unitStrip : Set ℂ := {z | z.re ∈ Icc (0 : ℝ) 1}


def unitSquare : Set ℂ := {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1}


def stripClamp (z : ℂ) : ℂ :=
  Complex.equivRealProdCLM.symm (projIcc 0 1 zero_le_one z.re, z.im)

theorem stripClamp_mem (z : ℂ) : stripClamp z ∈ unitStrip := by
  exact (projIcc 0 1 zero_le_one z.re).property

theorem stripClamp_eq_self {z : ℂ} (hz : z ∈ unitStrip) : stripClamp z = z := by
  change Complex.equivRealProdCLM.symm ((projIcc 0 1 zero_le_one z.re : ℝ), z.im) = z
  rw [projIcc_of_mem zero_le_one hz]
  exact Complex.equivRealProdCLM.symm_apply_apply z

theorem stripClamp_eventually_eq_id {z : ℂ} (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    stripClamp =ᶠ[𝓝 z] id := by
  filter_upwards [(isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz] with w hw
  exact stripClamp_eq_self (Ioo_subset_Icc_self hw)

theorem exists_lipschitz_stripClamp : ∃ C : ℝ≥0, LipschitzWith C stripClamp := by
  have ht := ((LipschitzWith.subtype_val (Icc (0 : ℝ) 1)).comp
    (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))).comp
    Complex.reCLM.lipschitz
  exact ⟨_, Complex.equivRealProdCLM.symm.lipschitz.comp (ht.prodMk Complex.imCLM.lipschitz)⟩

theorem isCompact_unitSquare : IsCompact unitSquare :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

end DifferentialGeometry.Analysis
