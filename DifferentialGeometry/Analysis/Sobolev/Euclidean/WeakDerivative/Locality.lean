import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.MeasureTheory.Integral.Bochner.Set
import DifferentialGeometry.External.DeGiorgi.PositivePart

section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DeGiorgi.MemW1pWitness

variable {d : ℕ} {Ω U : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakGrad_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → ℝ} (hf : MemW1pWitness p f Ω) (hg : MemW1pWitness p g Ω)
    (hfg : f =ᵐ[volume.restrict U] g) :
    hf.weakGrad =ᵐ[volume.restrict U] hg.weakGrad := by
  have hcoord (i : Fin d) : (fun x => hf.weakGrad x i) =ᵐ[volume.restrict U]
      (fun x => hg.weakGrad x i) := by
    have hwf : HasWeakPartialDeriv i (fun x => hf.weakGrad x i) f U :=
      HasWeakPartialDeriv.restrict hU hsub (hf.isWeakGrad i)
    have hwg : HasWeakPartialDeriv i (fun x => hg.weakGrad x i) f U := by
      intro φ hφ hφc hφs
      have hleft : (∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in U, g x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [hfg] with x hx
        rw [hx]
      rw [hleft]
      exact HasWeakPartialDeriv.restrict hU hsub (hg.isWeakGrad i) φ hφ hφc hφs
    exact HasWeakPartialDeriv.ae_eq hU hwf hwg
      (((hf.weakGrad_component_memLp i).mono_measure
        (Measure.restrict_mono_set volume hsub)).locallyIntegrable hp)
      (((hg.weakGrad_component_memLp i).mono_measure
        (Measure.restrict_mono_set volume hsub)).locallyIntegrable hp)
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  exact PiLp.ext hx

end DeGiorgi.MemW1pWitness

end

end

section

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set

namespace DeGiorgi

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.weakGrad_ae_eq_on_eqSet
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    ∀ᵐ x ∂volume.restrict Ω, u x = v x → hu.weakGrad x = hv.weakGrad x := by
  have hcoord (i : Fin d) : ∀ᵐ x ∂volume.restrict Ω,
      u x = v x → hu.weakGrad x i = hv.weakGrad x i := by
    let : NeZero d := ⟨fun hd => by simpa [hd] using i.isLt⟩
    let hw := hu.add (hv.smul (-1))
    filter_upwards [hw.weakGrad_ae_eq_zero_on_zeroSet hΩ i] with x hx hux
    have hz : u x + -1 * v x = 0 := by rw [hux]; ring
    have hgrad := hx hz
    change hu.weakGrad x i + -1 * hv.weakGrad x i = 0 at hgrad
    linarith
  filter_upwards [ae_all_iff.mpr hcoord] with x hx heq
  exact PiLp.ext fun i => hx i heq

theorem MemW1pWitness.weakGrad_ae_eq_restrict_of_eqOn
    {Ω s : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) (heq : EqOn u v s) :
    hu.weakGrad =ᵐ[(volume.restrict Ω).restrict s] hv.weakGrad := by
  apply (ae_restrict_iff₀ (nullMeasurableSet_eq_fun
    hu.weakGrad_memLp.aemeasurable.restrict hv.weakGrad_memLp.aemeasurable.restrict)).mpr
  filter_upwards [hu.weakGrad_ae_eq_on_eqSet hΩ hv] with x hx hxs
  exact hx (heq hxs)

theorem MemW1pWitness.weakGrad_ae_eq_restrict_preimage_of_eqOn
    {X : Type*} {Ω : Set E} (hΩ : IsOpen Ω)
    {f g : X → ℝ} {v : E → X} {s : Set X}
    (hf : MemW1pWitness 2 (f ∘ v) Ω) (hg : MemW1pWitness 2 (g ∘ v) Ω)
    (heq : EqOn f g s) :
    hf.weakGrad =ᵐ[(volume.restrict Ω).restrict (v ⁻¹' s)] hg.weakGrad := by
  apply hf.weakGrad_ae_eq_restrict_of_eqOn hΩ hg
  intro x hx
  exact heq hx

theorem MemW1pWitness.weakGrad_ae_eq_restrict_preimage_of_cutoffs
    {X : Type*} {Ω : Set E} (hΩ : IsOpen Ω)
    {χ χ' ψ : X → ℝ} {v : E → X} {s : Set X}
    (hχ : ∀ p ∈ s, χ p = 1) (hχ' : ∀ p ∈ s, χ' p = 1)
    (hf : MemW1pWitness 2 (fun x => χ (v x) * ψ (v x)) Ω)
    (hg : MemW1pWitness 2 (fun x => χ' (v x) * ψ (v x)) Ω) :
    hf.weakGrad =ᵐ[(volume.restrict Ω).restrict (v ⁻¹' s)] hg.weakGrad := by
  apply MemW1pWitness.weakGrad_ae_eq_restrict_preimage_of_eqOn
    (f := fun p => χ p * ψ p) (g := fun p => χ' p * ψ p) hΩ hf hg
  intro p hp
  change χ p * ψ p = χ' p * ψ p
  rw [hχ p hp, hχ' p hp]

end DeGiorgi

end

end
