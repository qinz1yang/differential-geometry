import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- Uniform linear energy decay and cubic gradient-excess decay give a `C¹`
representative of the original Sobolev function. Both almost-everywhere identities
hold on the original ball, and the returned Sobolev witness retains the supplied
weak gradient literally. No continuous representative is assumed in the input. -/
theorem exists_contDiffOn_one_representative_of_linear_energy_cubic_excess
    {u : V → ℝ} {a : V} {R E K : ℝ} (hR : 0 < R)
    (hu : DeGiorgi.MemW1pWitness 2 u (ball a R)) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (henergy : ∀ b : DeGiorgi.CampanatoBall a R,
      (∫ x in ball b.center b.radius, ‖hu.weakGrad x‖ ^ 2) ≤ E * b.radius)
    (hexcess : ∀ b : DeGiorgi.CampanatoBall a R,
      (∫ x in ball b.center b.radius,
        ‖hu.weakGrad x - ⨍ y in ball b.center b.radius, hu.weakGrad y‖ ^ 2) ≤
          K * b.radius ^ 3) :
    ∃ (v : V → ℝ) (G : V → V) (C : ℝ)
      (hv : DeGiorgi.MemW1pWitness 2 v (ball a R)),
      0 ≤ C ∧ v =ᵐ[volume.restrict (ball a R)] u ∧
      hv.weakGrad = hu.weakGrad ∧
      G =ᵐ[volume.restrict (ball a R)] hu.weakGrad ∧
      ContDiffOn ℝ 1 v (ball a (R / 2)) ∧ ContinuousOn G (ball a (R / 2)) ∧
      (∀ x ∈ ball a (R / 2), HasFDerivAt v (innerSL ℝ (G x)) x) ∧
      ∀ x ∈ ball a (R / 2), ∀ y ∈ ball a (R / 2),
        ‖G x - G y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cu, _, hcamp⟩ :=
    Sobolev.Euclidean.exists_campanato_bound_of_weak_gradient_energy
      (α := (1 / 2 : ℝ)) hu Subset.rfl hE (by
        intro b
        simpa using henergy b)
  obtain ⟨v, hvae, hholderv⟩ := DeGiorgi.campanato_implies_holder
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hR hcamp
  let Cv := max (DeGiorgi.CCampanatoHolder 2 (1 / 2) * Cu) 0
  have hvc : ContinuousOn v (ball a (R / 2)) := by
    apply continuousOn_of_norm_sub_le_rpow (C := Cv) (le_max_right _ _)
      (by norm_num : (0 : ℝ) < 1 / 2)
    intro x hx y hy
    rw [Real.norm_eq_abs]
    exact (hholderv x hx y hy).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  obtain ⟨Gs, Cs, hCs, hGs, hGsc, hGsh⟩ :=
    Sobolev.Euclidean.exists_holder_representative_of_gradient_excess_bound
      (G := fun _ : Fin 1 => hu.weakGrad) (α := (1 / 2 : ℝ)) hR
      (by norm_num) (by norm_num) hK (fun _ => hu.weakGrad_memLp) (by
        intro b
        simpa only [Fin.sum_univ_one,
          show (2 : ℝ) + 2 * (1 / 2) = 3 by norm_num, Real.rpow_ofNat] using hexcess b)
  let hv : DeGiorgi.MemW1pWitness 2 v (ball a R) :=
    { memLp := hu.memLp.ae_eq (Filter.EventuallyEq.symm hvae)
      weakGrad := hu.weakGrad
      weakGrad_component_memLp := hu.weakGrad_component_memLp
      isWeakGrad := fun i => (hu.isWeakGrad i).congr_ae (Filter.EventuallyEq.symm hvae) EventuallyEq.rfl }
  have hhalf : ball a (R / 2) ⊆ ball a R := ball_subset_ball (by linarith)
  let hvh := hv.restrict isOpen_ball hhalf
  have hGh : Gs 0 =ᵐ[volume.restrict (ball a (R / 2))] hvh.weakGrad :=
    ae_restrict_of_ae_restrict_of_subset hhalf (hGs 0)
  have hdiff : ContDiffOn ℝ 1 v (ball a (R / 2)) :=
    hvh.contDiffOn_one_of_continuousOn_weakGrad isOpen_ball hvc (hGsc 0) hGh
  refine ⟨v, Gs 0, Cs 0, hv, hCs 0, hvae, rfl, hGs 0, hdiff, hGsc 0, ?_, hGsh 0⟩
  intro x hx
  exact hvh.hasFDerivAt_of_continuousOn_weakGrad isOpen_ball hvc (hGsc 0) hGh hx

end DifferentialGeometry.Analysis
