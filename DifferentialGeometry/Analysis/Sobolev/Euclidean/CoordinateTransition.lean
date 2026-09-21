import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Locality

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

theorem weakGrad_ae_coordinate_transition_on_preimage
    {X : Type*} {Ω : Set E} (hΩ : IsOpen Ω)
    {P : X → F} {Q : X → H} {v : E → X} {s : Set X}
    (hP : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => P (v x) i) Ω)
    (hQ : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => Q (v x) k) Ω)
    (R : F → H) (hR : ContDiff ℝ 1 R) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ R y‖ ≤ C)
    (htrans : ∀ p ∈ s, R (P p) = Q p)
    {c : E} {a : ℝ} (hball : closedBall c a ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict (ball c a)).restrict (v ⁻¹' s), ∀ j : Fin d,
      WithLp.toLp 2 (fun k => (hQ k).weakGrad x j) =
        fderiv ℝ R (P (v x)) (WithLp.toLp 2 (fun i => (hP i).weakGrad x j)) := by
  obtain ⟨hw, hrep⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball
    hΩ hP R hR hC hball
  have hBΩ : ball c a ⊆ Ω := ball_subset_closedBall.trans hball
  have hlocal (k : κ) : (hw k).weakGrad =ᵐ[(volume.restrict (ball c a)).restrict (v ⁻¹' s)]
      (hQ k).weakGrad := by
    apply DeGiorgi.MemW1pWitness.weakGrad_ae_eq_restrict_of_eqOn isOpen_ball
      (hw k) (DeGiorgi.MemW1pWitness.restrict isOpen_ball hBΩ (hQ k))
    intro x hx
    exact congrArg (fun y : H => y k) (htrans (v x) hx)
  filter_upwards [ae_all_iff.mpr hlocal] with x hx j
  apply PiLp.ext
  intro k
  change (hQ k).weakGrad x j = _
  rw [← hx k, hrep k x j]

theorem gradient_quadratic_ae_coordinate_transition_on_preimage
    {X : Type*} [MeasurableSpace X] {Ω : Set E} (hΩ : IsOpen Ω)
    {P : X → F} {Q : X → H} {v : E → X} {s : Set X}
    (hv : AEMeasurable v (volume.restrict Ω)) (hs : MeasurableSet s)
    (hP : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => P (v x) i) Ω)
    (hQ : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => Q (v x) k) Ω)
    (R : F → H) (hR : ContDiff ℝ 1 R) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ R y‖ ≤ C)
    (htrans : ∀ p ∈ s, R (P p) = Q p)
    (B : X → F →L[ℝ] F →L[ℝ] ℝ) (D : X → H →L[ℝ] H →L[ℝ] ℝ)
    (hmetric : ∀ p ∈ s, ∀ z : F,
      D p (fderiv ℝ R (P p) z) (fderiv ℝ R (P p) z) = B p z z)
    {c : E} {a : ℝ} (hball : closedBall c a ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict (ball c a)).restrict (v ⁻¹' s), ∀ j : Fin d,
      D (v x) (WithLp.toLp 2 (fun k => (hQ k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hQ k).weakGrad x j)) =
      B (v x) (WithLp.toLp 2 (fun i => (hP i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hP i).weakGrad x j)) := by
  have hgrad := weakGrad_ae_coordinate_transition_on_preimage
    hΩ hP hQ R hR hC htrans hball
  have hvm : AEMeasurable v (volume.restrict (ball c a)) :=
    hv.mono_measure (Measure.restrict_mono_set volume (ball_subset_closedBall.trans hball))
  filter_upwards [hgrad, ae_restrict_mem₀ (hvm.nullMeasurableSet_preimage hs)] with x hx hxs j
  rw [hx j]
  exact hmetric (v x) hxs _

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
