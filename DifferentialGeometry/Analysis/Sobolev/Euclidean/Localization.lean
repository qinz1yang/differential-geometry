import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def MemW1pWitness.extendOfCompactSupport
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness p u Omega)
    (hu_cpt : HasCompactSupport u) (hu_sub : tsupport u ⊆ Omega) :
    MemW1pWitness p u Set.univ where
  memLp := by
    have hind : Omega.indicator u = u :=
      Set.indicator_eq_self.mpr ((subset_tsupport u).trans hu_sub)
    have hglobal : MemLp (Omega.indicator u) p (volume : Measure E) :=
      (memLp_indicator_iff_restrict hOmega.measurableSet).mpr hu.memLp
    simpa only [hind, Measure.restrict_univ] using hglobal
  weakGrad := Omega.indicator hu.weakGrad
  weakGrad_component_memLp := by
    intro i
    have hglobal : MemLp (Omega.indicator (fun x => hu.weakGrad x i)) p
        (volume : Measure E) :=
      (memLp_indicator_iff_restrict hOmega.measurableSet).mpr
        (hu.weakGrad_component_memLp i)
    have heq : (fun x => (Omega.indicator hu.weakGrad x) i) =
        Omega.indicator (fun x => hu.weakGrad x i) := by
      funext x
      by_cases hx : x ∈ Omega <;> simp [hx]
    simpa only [heq, Measure.restrict_univ] using hglobal
  isWeakGrad := by
    intro i
    have hae : chosenWeakPartialOrZero p i u Omega =ᵐ[volume.restrict Omega]
        (fun x => hu.weakGrad x i) :=
      HasWeakPartialDeriv.ae_eq hOmega
        (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i) (hu.isWeakGrad i)
        ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p i).locallyIntegrable hp)
        ((hu.weakGrad_component_memLp i).locallyIntegrable hp)
    have hext : Omega.indicator (chosenWeakPartialOrZero p i u Omega) =ᵐ[
        volume.restrict Set.univ] (fun x => (Omega.indicator hu.weakGrad x) i) := by
      rw [Measure.restrict_univ]
      filter_upwards [(ae_restrict_iff' hOmega.measurableSet).mp hae] with x hx
      by_cases hxOmega : x ∈ Omega
      · simpa [hxOmega] using hx hxOmega
      · simp [hxOmega]
    exact (hasWeakPartialDeriv_indicator_chosenWeakPartial_univ hp hOmega
      hu.memW1p hu_cpt hu_sub i).congr_ae Filter.EventuallyEq.rfl hext

@[simp] theorem MemW1pWitness.extendOfCompactSupport_weakGrad
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness p u Omega)
    (hu_cpt : HasCompactSupport u) (hu_sub : tsupport u ⊆ Omega) :
    (hu.extendOfCompactSupport hp hOmega hu_cpt hu_sub).weakGrad =
      Omega.indicator hu.weakGrad := rfl

theorem MemW1pWitness.exists_compactly_supported_extension
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness p u Omega)
    {K : Set E} (hK : IsCompact K) (hsub : K ⊆ Omega) :
    ∃ (U : E → ℝ) (hU : MemW1pWitness p U Set.univ),
      HasCompactSupport U ∧ tsupport U ⊆ Omega ∧
      EqOn U u K ∧ EqOn hU.weakGrad hu.weakGrad K := by
  obtain ⟨delta, chi, hdelta, _, hchi, hchi_cpt, hchi_range, hchi_one, hchi_sub⟩ :=
    exists_smooth_cutoff_with_neighborhood hK hOmega hsub
  obtain ⟨C, hC⟩ := (hchi.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hchi_cpt.fderiv (𝕜 := ℝ))
  have hC_nonneg : 0 ≤ C := (norm_nonneg (fderiv ℝ chi (0 : E))).trans (hC 0)
  have hchi_bound : ∀ x, |chi x| ≤ 1 := by
    intro x
    have hx := hchi_range (mem_range_self x)
    simpa only [abs_of_nonneg hx.1] using hx.2
  let hv := hu.mulSmoothBoundedP hp hOmega hchi zero_le_one hC_nonneg hchi_bound hC
  have hv_cpt : HasCompactSupport (fun x => chi x * u x) := hchi_cpt.mul_right
  have hv_sub : tsupport (fun x => chi x * u x) ⊆ Omega :=
    (tsupport_smul_subset_left chi u).trans hchi_sub
  refine ⟨fun x => chi x * u x, hv.extendOfCompactSupport hp hOmega hv_cpt hv_sub,
    hv_cpt, hv_sub, ?_, ?_⟩
  · intro x hx
    simp only [hchi_one x (Metric.self_subset_cthickening K hx), one_mul]
  · intro x hx
    rw [MemW1pWitness.extendOfCompactSupport_weakGrad, Set.indicator_of_mem (hsub hx)]
    have hchix : chi x = 1 := hchi_one x (Metric.self_subset_cthickening K hx)
    ext i
    have hderiv : (fderiv ℝ chi x) (EuclideanSpace.single i 1) = 0 :=
      fderiv_cutoff_apply_zero_on_cthickening hdelta hchi_one hx i
    simp [hv, MemW1pWitness.mulSmoothBoundedP, hchix, hderiv]

end DeGiorgi
