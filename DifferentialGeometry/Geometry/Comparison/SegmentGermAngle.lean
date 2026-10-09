import DifferentialGeometry.Topology.MetricSpace.SegmentExtension
import DifferentialGeometry.Geometry.Comparison.CanonicalLocalAngle
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem germComparisonAngle_IccExtend_adjacent_sum_le_pi
    {X : Type*} [MetricSpace X] {κ a b h S : ℝ} (hκ : 0 ≤ κ)
    (hah : a < h) (hhb : h < b) (hS : 0 < S)
    {σ : Icc a b → X} (hσ : Isometry σ) {β : ℝ → X}
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω)
    (hp : σ ⟨h, ⟨hah.le, hhb.le⟩⟩ ∈ Ω)
    (hβrad : ∀ s ∈ Ioc (0 : ℝ) S, dist (σ ⟨h, ⟨hah.le, hhb.le⟩⟩) (β s) = s)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|) :
    germComparisonAngle κ β (fun t => IccExtend (hah.le.trans hhb.le) σ (h - t)) +
      germComparisonAngle κ β (fun t => IccExtend (hah.le.trans hhb.le) σ (h + t)) ≤ Real.pi := by
  let L : Fin 3 → ℝ := ![h - a, S, b - h]
  let γ : Fin 3 → ℝ → X := ![fun t => IccExtend (hah.le.trans hhb.le) σ (h - t),
    β, fun t => IccExtend (hah.le.trans hhb.le) σ (h + t)]
  have hL : ∀ i, 0 < L i := by
    intro i
    fin_cases i
    · exact sub_pos.mpr hah
    · exact hS
    · exact sub_pos.mpr hhb
  have hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i),
      dist (σ ⟨h, ⟨hah.le, hhb.le⟩⟩) (γ i s) = s := by
    intro i s hs
    fin_cases i
    · exact hσ.IccExtend_backward_radial ⟨hah.le, hhb.le⟩ ⟨hs.1.le, hs.2⟩
    · exact hβrad s hs
    · exact hσ.IccExtend_forward_radial ⟨hah.le, hhb.le⟩ ⟨hs.1.le, hs.2⟩
  have hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t| := by
    intro i s hs t ht
    fin_cases i
    · exact hσ.IccExtend_backward_dist ⟨hah.le, hhb.le⟩ ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩
    · exact hβmin s hs t ht
    · exact hσ.IccExtend_forward_dist ⟨hah.le, hhb.le⟩ ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩
  have hopp : ∀ s ∈ Ioc (0 : ℝ) (L 2), ∀ t ∈ Ioc (0 : ℝ) (L 0),
      dist (γ 2 s) (γ 0 t) = s + t := by
    intro s hs t ht
    exact hσ.IccExtend_opposite_dist ⟨hah.le, hhb.le⟩ ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩
  have hadj := germComparisonAngle_adjacent_sum_le_pi_of_local_fourPointComparison
    hκ hL hΩ hcomp hp hrad hmin 0 1 2 hopp
  change germComparisonAngle κ (fun t => IccExtend (hah.le.trans hhb.le) σ (h - t)) β +
    germComparisonAngle κ β (fun t => IccExtend (hah.le.trans hhb.le) σ (h + t)) ≤ Real.pi at hadj
  rwa [germComparisonAngle_comm κ _ β] at hadj

end DifferentialGeometry.Geometry.Comparison.Toponogov
