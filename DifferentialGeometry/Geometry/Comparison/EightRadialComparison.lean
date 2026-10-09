import DifferentialGeometry.Geometry.Comparison.IntrinsicEightRadialComparison
import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry

set_option autoImplicit false


open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngleNegCurvature_le_of_radial_isometries_in_eight_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {κ L r A B : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hbuffer : 8 * r < L)
    {n : ℕ} (hdim : dimH (ball p L) ≤ n)
    (hlocal : ∀ z ∈ ball p L,
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (hrA : r ≤ A) (hrB : r ≤ B)
    (γ : Icc (0 : ℝ) A → X) (β : Icc (0 : ℝ) B → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, hr.le.trans hrA⟩⟩ = p)
    (hβ0 : β ⟨0, ⟨le_rfl, hr.le.trans hrB⟩⟩ = p)
    {s t : ℝ} (hs : s ∈ Ioc (0 : ℝ) r) (ht : t ∈ Ioc (0 : ℝ) r) :
    comparisonAngleNegCurvature κ r r
        (dist (γ ⟨r, ⟨hr.le, hrA⟩⟩) (β ⟨r, ⟨hr.le, hrB⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
        (dist (γ ⟨s, ⟨hs.1.le, hs.2.trans hrA⟩⟩)
          (β ⟨t, ⟨ht.1.le, ht.2.trans hrB⟩⟩)) := by
  have hsub : ball p (8 * r) ⊆ ball p L := ball_subset_ball hbuffer.le
  let : LocallyCompactSpace (ball p (8 * r)) :=
    locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
      hcurves hκ.le isOpen_ball ((dimH_mono hsub).trans hdim)
      (fun z hz => hlocal z (hsub hz))
  have hlocal' : ∀ z : ball p (8 * r), ∃ Ω : Set (ball p (8 * r)),
      @IsOpen (ball p (8 * r))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * r)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * r))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * r)) κ Ω ∧ z ∈ Ω := by
    intro z
    exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
      (by positivity : 0 < 8 * r) z).mpr (hlocal z (hsub z.property))
  let γ' : Icc (0 : ℝ) r → X := fun u => γ ⟨u.val, ⟨u.property.1, u.property.2.trans hrA⟩⟩
  let β' : Icc (0 : ℝ) r → X := fun u => β ⟨u.val, ⟨u.property.1, u.property.2.trans hrB⟩⟩
  have hγ' : Isometry γ' := hγ.comp (Isometry.of_dist_eq fun _ _ => rfl)
  have hβ' : Isometry β' := hβ.comp (Isometry.of_dist_eq fun _ _ => rfl)
  exact comparisonAngleNegCurvature_le_of_radial_isometries_intrinsic_8_buffer
    hcurves p hκ hr hlocal' γ' β' hγ' hβ' hγ0 hβ0 hs ht

end DifferentialGeometry.Geometry.Comparison.Toponogov
