import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem GeometricCutoffRecord.nominalRadius_lt_mul_of_accuracy_bound
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (hranti : AntitoneOn p.neckRadius (Ici 0))
    (haccuracy : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (u + 1))
    {ε t : ℝ} (hε : 0 < ε) (ht : 2 / ε ≤ t)
    (hhalf : t / 2 ≤ H.time i.succ)
    (h : Nonempty (H.event i).transition.trace.tubes.Index) :
    R.nominalRadius h < ε * p.neckRadius t := by
  let u : ℝ := H.time i.succ
  have htpos : 0 < t := (div_pos (by norm_num : (0 : ℝ) < 2) hε).trans_le ht
  have ht2u : t ≤ 2 * u := by
    change t / 2 ≤ u at hhalf
    linarith
  have hu : 0 ≤ u := by linarith
  have hu1 : 0 < u + 1 := by linarith
  have hrt : 0 < p.neckRadius t := p.neckRadius_pos t htpos.le
  have hr : p.neckRadius (2 * u) ≤ p.neckRadius t :=
    hranti htpos.le (by linarith : 0 ≤ 2 * u) ht2u
  have hεt : 2 ≤ t * ε := (div_le_iff₀ hε).mp ht
  have hεtu : ε * t ≤ ε * (2 * u) := mul_le_mul_of_nonneg_left ht2u hε.le
  have hεden : 1 < ε * (u + 1) := by nlinarith
  have hlast : p.neckRadius t / (u + 1) < ε * p.neckRadius t := by
    apply (div_lt_iff₀ hu1).mpr
    nlinarith [mul_lt_mul_of_pos_left hεden hrt]
  calc
    R.nominalRadius h < p.delta u ^ 2 * p.neckRadius u := R.nominal_small h
    _ < p.neckRadius (2 * u) / (u + 1) := haccuracy u hu
    _ ≤ p.neckRadius t / (u + 1) := div_le_div_of_nonneg_right hr hu1.le
    _ < ε * p.neckRadius t := hlast

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
