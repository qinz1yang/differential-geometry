import DifferentialGeometry.Geometry.Comparison.Volume.ConvexBoundaryPolarComparison

/-!
# Consumers of the BSA02 kernel

* `bsa02_stopped_model_cross`: an inhabitant of the BSA02 polar data with a genuine exit: one
  direction (Dirac measure), the model Jacobian `s_κ²` stopped at an exit time `c` (alive set
  `(0, c)`, zero afterwards). `bsa02_modelVolume_cross` gives the relative comparison against
  `V_κ = modelVolume (−κ²) 3` for the truncated volume `t ↦ ∫_{(0,t]} 1_{(0,c)} s_κ²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

/-- The stopped model satisfies BSA02: for `0 < a ≤ b < L`,
`vol(b) · V_κ(a) ≤ vol(a) · V_κ(b)` with `vol(t) = ∫_{(0,t]} 1_{(0,c)} s_κ²`. -/
theorem bsa02_stopped_model_cross (κ c : ℝ) {L a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < L) :
    (∫⁻ s in Ioc 0 b, ENNReal.ofReal
        ((Ioo 0 c).indicator (fun t => modelRadius (-(κ ^ 2)) t ^ 2) s)) *
        ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 a) ≤
      (∫⁻ s in Ioc 0 a, ENNReal.ofReal
        ((Ioo 0 c).indicator (fun t => modelRadius (-(κ ^ 2)) t ^ 2) s)) *
        ENNReal.ofReal (modelVolume (-(κ ^ 2)) 3 b) := by
  have hs : ∀ t, 0 < t → modelRadius (-(κ ^ 2)) t ≠ 0 := fun t ht =>
    (modelRadius_pos ⟨ht, fun h => absurd h (not_lt.mpr (neg_nonpos.mpr (sq_nonneg κ)))⟩).ne'
  have hratio : AntitoneOn
      (fun t => (fun t => modelRadius (-(κ ^ 2)) t ^ 2) t / modelRadius (-(κ ^ 2)) t ^ 2)
      (Ioo 0 c ∩ Ioo 0 L) := by
    intro x hx y hy _
    simp only
    rw [div_self (pow_ne_zero 2 (hs x hx.2.1)), div_self (pow_ne_zero 2 (hs y hy.2.1))]
  have hmeas : Measurable ((Ioo 0 c).indicator (fun t => modelRadius (-(κ ^ 2)) t ^ 2)) :=
    ((modelRadius_continuous _).pow 2).measurable.indicator measurableSet_Ioo
  exact bsa02_modelVolume_cross (Measure.dirac ()) (fun _ t => modelRadius (-(κ ^ 2)) t ^ 2)
    (fun _ => Ioo 0 c) κ
    (fun t => ∫⁻ s in Ioc 0 t, ENNReal.ofReal
      ((Ioo 0 c).indicator (fun t => modelRadius (-(κ ^ 2)) t ^ 2) s))
    (fun _ t => sq_nonneg _) (fun _ a' b' ha' hab' hb' => ⟨ha', hab'.trans_lt hb'.2⟩)
    (fun _ => hratio) (fun _ => hmeas) (fun t _ => by rw [lintegral_dirac]) ha hab hb

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
