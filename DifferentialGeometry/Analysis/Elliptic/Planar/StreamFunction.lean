import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.MeanValue

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

def planarFluxForm (F : V → V) (x : V) : V →L[ℝ] ℝ :=
  -(F x 1) • EuclideanSpace.proj 0 + F x 0 • EuclideanSpace.proj 1

theorem exists_stream_function_of_hasWeakDiv_zero
    {Ω : Set V} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {F : V → V}
    (hF : ContDiffOn ℝ ∞ F Ω) (hdiv : DeGiorgi.HasWeakDiv 0 F Ω) :
    ∃ s : V → ℝ, ContDiffOn ℝ ∞ s Ω ∧
      ∀ x ∈ Ω, HasFDerivAt s (planarFluxForm F x) x := by
  have hFc (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => F x i) Ω :=
    (contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hF
  have hω : ContDiffOn ℝ ∞ (planarFluxForm F) Ω :=
    ((hFc 1).neg.smul_const (EuclideanSpace.proj 0 : V →L[ℝ] ℝ)).add
      ((hFc 0).smul_const (EuclideanSpace.proj 1 : V →L[ℝ] ℝ))
  have hD := hdiv.sum_fderiv_eq_zero hΩ (hF.of_le (by norm_cast))
  have hsymmetric : ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (planarFluxForm F) a x y = fderiv ℝ (planarFluxForm F) a y x := by
    intro a ha x y
    have h0 := ((hFc 0).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds ha)
    have h1 := ((hFc 1).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds ha)
    have hd := (h1.hasFDerivAt.neg.smul_const (EuclideanSpace.proj 0 : V →L[ℝ] ℝ)).add
      (h0.hasFDerivAt.smul_const (EuclideanSpace.proj 1 : V →L[ℝ] ℝ))
    have hdd := hd.fderiv
    change fderiv ℝ (planarFluxForm F) a = _ at hdd
    rw [hdd]
    have hex (v : V) : v = v 0 • EuclideanSpace.single 0 1 +
        v 1 • EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp
    have hde := hD a ha
    simp only [Fin.sum_univ_two] at hde
    change -(fderiv ℝ (fun z => F z 1) a x) * y 0 +
      (fderiv ℝ (fun z => F z 0) a x) * y 1 =
      -(fderiv ℝ (fun z => F z 1) a y) * x 0 +
      (fderiv ℝ (fun z => F z 0) a y) * x 1
    have hlin (L : V →L[ℝ] ℝ) (v : V) :
        L v = v 0 * L (EuclideanSpace.single 0 1) +
          v 1 * L (EuclideanSpace.single 1 1) := by
      conv_lhs => rw [hex v]
      simp only [map_add, map_smul, smul_eq_mul]
    rw [hlin (fderiv ℝ (fun z => F z 1) a) x,
      hlin (fderiv ℝ (fun z => F z 0) a) x,
      hlin (fderiv ℝ (fun z => F z 1) a) y,
      hlin (fderiv ℝ (fun z => F z 0) a) y]
    have he : fderiv ℝ (fun z => F z 1) a (EuclideanSpace.single 1 1) =
        -(fderiv ℝ (fun z => F z 0) a (EuclideanSpace.single 0 1)) := by linarith
    rw [he]
    ring
  obtain ⟨s, hs⟩ := hc.exists_forall_hasFDerivAt_of_fderiv_symmetric hΩ
    (hω.differentiableOn (by simp)) hsymmetric
  refine ⟨s, (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mpr ⟨?_, ?_⟩, hs⟩
  · exact fun x hx => (hs x hx).differentiableAt.differentiableWithinAt
  · exact hω.congr (fun x hx => (hs x hx).fderiv)

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_stream_function_extension_of_hasWeakDiv_zero
    {Ω S : Set V} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (hS : IsOpen S) (hcS : IsPreconnected S) (hSΩ : S ⊆ Ω)
    {a : V} (ha : a ∈ S) {F : V → V} (hF : ContDiffOn ℝ ∞ F Ω)
    (hdiv : DeGiorgi.HasWeakDiv 0 F Ω) {s₀ : V → ℝ}
    (hs₀ : ∀ x ∈ S, HasFDerivAt s₀ (planarFluxForm F x) x) :
    ∃ s : V → ℝ, ContDiffOn ℝ ∞ s Ω ∧ EqOn s s₀ S ∧
      ∀ x ∈ Ω, HasFDerivAt s (planarFluxForm F x) x := by
  obtain ⟨s, hs, hds⟩ := exists_stream_function_of_hasWeakDiv_zero hΩ hc hF hdiv
  let t := fun x => s x + (s₀ a - s a)
  have ht : ContDiffOn ℝ ∞ t Ω := hs.add contDiffOn_const
  have hdt : ∀ x ∈ Ω, HasFDerivAt t (planarFluxForm F x) x :=
    fun x hx => (hds x hx).add_const _
  refine ⟨t, ht, ?_, hdt⟩
  apply hS.eqOn_of_fderiv_eq hcS
    ((ht.differentiableOn (by simp)).mono hSΩ)
    (fun x hx => (hs₀ x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hdt x (hSΩ hx)).fderiv.trans (hs₀ x hx).fderiv.symm) ha
  dsimp only [t]
  ring

end DifferentialGeometry.Analysis

end

end
