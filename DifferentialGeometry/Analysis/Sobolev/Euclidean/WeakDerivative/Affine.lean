import DifferentialGeometry.Analysis.Calculus.AffineComposition
import DifferentialGeometry.Analysis.Integration.Measure.Affine
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.Tactic.Ring
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.External.DeGiorgi.PositivePart
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeAffine
import Mathlib.Analysis.InnerProductSpace.Adjoint

section

section

section

noncomputable section

open MeasureTheory Set

namespace DeGiorgi

open DifferentialGeometry.Analysis.Calculus

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_comp_add_smul (F : E → ℝ) (b : E)
    {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    (∫ x in (fun y => b + r • y) ⁻¹' Ω, F (b + r • x)) =
      |(r ^ Module.finrank ℝ E)⁻¹| * ∫ x in Ω, F x := by
  let e : E ≃ᵐ E :=
    (MeasurableEquiv.smul₀ r hr).trans (MeasurableEquiv.addLeft b)
  have hmap : ((volume : Measure E).restrict (e ⁻¹' Ω)).map e =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • volume.restrict Ω :=
    Measure.map_add_smul_restrict_addHaar volume b hr Ω
  change (∫ x in e ⁻¹' Ω, F (e x)) = _
  rw [← integral_map_equiv e, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem HasWeakPartialDeriv.comp_add_smul {j : Fin d} {g f : E → ℝ} {Ω : Set E}
    (h : HasWeakPartialDeriv j g f Ω) (b : E) {r : ℝ} (hr : r ≠ 0) :
    HasWeakPartialDeriv j (fun x => r * g (b + r • x))
      (fun x => f (b + r • x)) ((fun x => b + r • x) ⁻¹' Ω) := by
  intro φ hφ hφc hφs
  let S : E → E := fun x => b + r • x
  let Ω' := S ⁻¹' Ω
  let ψ : E → ℝ := fun z => φ (r⁻¹ • (z - b))
  let v : E := EuclideanSpace.single j 1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_comp_affine_inverse b r hφ
  have hψc : HasCompactSupport ψ := hasCompactSupport_comp_affine_inverse b hr hφc
  have hψs : tsupport ψ ⊆ Ω :=
    tsupport_comp_affine_inverse_subset_of_preimage b hr hφs
  have hψS (x : E) : ψ (S x) = φ x := by
    simp [ψ, S, smul_smul, hr, sub_eq_add_neg, add_comm, add_assoc]
  have hD (x : E) : fderiv ℝ ψ (S x) v = r⁻¹ * fderiv ℝ φ x v := by
    simpa only [ψ, S, smul_eq_mul] using
      fderiv_comp_affine_inverse_at_image b hr ((hφ.differentiable (by simp)) x) v
  have hsource := h ψ hψ hψc hψs
  change (∫ x in Ω, f x * fderiv ℝ ψ x v) = -∫ x in Ω, g x * ψ x at hsource
  have htransport : (∫ x in Ω', f (S x) * fderiv ℝ ψ (S x) v) =
      -∫ x in Ω', g (S x) * ψ (S x) := by
    change (∫ x in (fun y => b + r • y) ⁻¹' Ω,
        f (b + r • x) * fderiv ℝ ψ (b + r • x) v) =
      -∫ x in (fun y => b + r • y) ⁻¹' Ω, g (b + r • x) * ψ (b + r • x)
    rw [integral_comp_add_smul (fun z => f z * fderiv ℝ ψ z v) b hr Ω,
      integral_comp_add_smul (fun z => g z * ψ z) b hr Ω, hsource, mul_neg]
  have hleft : (∫ x in Ω', f (S x) * fderiv ℝ ψ (S x) v) =
      r⁻¹ * ∫ x in Ω', f (S x) * fderiv ℝ φ x v := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp only; rw [hD x]; ring
  have hright : (∫ x in Ω', g (S x) * ψ (S x)) =
      ∫ x in Ω', g (S x) * φ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp only; rw [hψS x]
  rw [hleft, hright] at htransport
  have hscaled := congrArg (fun z : ℝ => r * z) htransport
  have hfactor : (∫ x in Ω', (r * g (S x)) * φ x) =
      r * ∫ x in Ω', g (S x) * φ x := by
    simp_rw [mul_assoc]
    exact integral_const_mul r _
  change (∫ x in Ω', f (S x) * fderiv ℝ φ x v) =
    -∫ x in Ω', (r * g (S x)) * φ x
  rw [hfactor]
  simpa only [← mul_assoc, mul_inv_cancel₀ hr, one_mul, mul_neg] using hscaled

end DeGiorgi

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal
namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def MemW1pWitness.compAddSmul
    {p : ℝ≥0∞} {f : E → ℝ} {Ω : Set E}
    (hf : MemW1pWitness p f Ω) (b : E) {r : ℝ} (hr : r ≠ 0) :
    MemW1pWitness p (fun x => f (b + r • x))
      ((fun x => b + r • x) ⁻¹' Ω) where
  memLp := hf.memLp.comp_add_smul b hr
  weakGrad := fun x => r • hf.weakGrad (b + r • x)
  weakGrad_component_memLp := by
    intro j
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      ((hf.weakGrad_component_memLp j).comp_add_smul b hr).const_mul r
  isWeakGrad := by
    intro j
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      (hf.isWeakGrad j).comp_add_smul b hr

theorem MemW1pWitness.compAddSmul_weakGrad
    {p : ℝ≥0∞} {f : E → ℝ} {Ω : Set E}
    (hf : MemW1pWitness p f Ω) (b : E) {r : ℝ} (hr : r ≠ 0) (x : E) :
    (hf.compAddSmul b hr).weakGrad x = r • hf.weakGrad (b + r • x) := rfl

theorem weakGrad_column_compAddSmul
    {ι : Type*} {p : ℝ≥0∞} {u : E → EuclideanSpace ℝ ι} {Ω : Set E}
    (hu : ∀ i : ι, MemW1pWitness p (fun x => u x i) Ω)
    (b : E) {r : ℝ} (hr : r ≠ 0) (x : E) (j : Fin d) :
    (WithLp.toLp 2 (fun i => ((hu i).compAddSmul b hr).weakGrad x j) :
      EuclideanSpace ℝ ι) =
      r • WithLp.toLp 2 (fun i => (hu i).weakGrad (b + r • x) j) := by
  ext i
  simp only [MemW1pWitness.compAddSmul, PiLp.smul_apply]

end DeGiorgi

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_translated_memW1pWitness_of_eqOn
    {p : ℝ≥0∞} {Ω : Set E} {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    {b : E} {R : ℝ} (hball : ball b R ⊆ Ω) (hfg : EqOn f g (ball b R)) :
    ∃ hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g (b + x) i) (ball (0 : E) R),
      ∀ i x, (hg i).weakGrad x = (hf i).weakGrad (b + x) := by
  have hmaps : ball (0 : E) R ⊆ (fun x => b + (1 : ℝ) • x) ⁻¹' Ω := by
    intro x hx
    apply hball
    simpa only [one_smul, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
  have heq (i : ι) : (fun x => f (b + (1 : ℝ) • x) i) =ᵐ[volume.restrict (ball (0 : E) R)]
      (fun x => g (b + x) i) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxB : b + x ∈ ball b R := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
    simpa only [one_smul] using congrArg (fun y : F => y i) (hfg hxB)
  let hg := fun i =>
    (((hf i).compAddSmul b (one_ne_zero : (1 : ℝ) ≠ 0)).restrict isOpen_ball hmaps).congr (heq i)
  refine ⟨hg, ?_⟩
  intro i x
  change (1 : ℝ) • (hf i).weakGrad (b + (1 : ℝ) • x) = (hf i).weakGrad (b + x)
  rw [one_smul, one_smul]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

end

section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem exists_memW1pWitness_add_const
    {Ω : Set V} [IsFiniteMeasure (volume.restrict Ω)] (hΩ : IsOpen Ω) {z : V → F}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω) (y₀ : F) :
    ∃ hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => (z x + y₀) i) Ω,
      ∀ i, (hw i).weakGrad = (hz i).weakGrad := by
  let hw (i : Fin m) : DeGiorgi.MemW1pWitness 2 (fun x => (z x + y₀) i) Ω :=
    ((hz i).subConst hΩ (-y₀ i)).congr
    (Eventually.of_forall fun x => by simp only [PiLp.add_apply, sub_neg_eq_add])
  exact ⟨hw, fun _ => rfl⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

end

section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DeGiorgi

open scoped InnerProductSpace

theorem HasWeakGrad.integral_mul_fderiv
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {U : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : HasWeakGrad G U Ω) (hU : LocallyIntegrableOn U Ω volume)
    (hG : LocallyIntegrableOn G Ω volume) (v : EuclideanSpace ℝ (Fin d))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, U x * fderiv ℝ φ x v) = -∫ x in Ω, ⟪G x, v⟫_ℝ * φ x := by
  have hint {W ψ : EuclideanSpace ℝ (Fin d) → ℝ}
      (hW : LocallyIntegrableOn W Ω volume) (hψ : Continuous ψ)
      (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
      Integrable (fun x => W x * ψ x) (volume.restrict Ω) := by
    apply Integrable.mono_measure _ Measure.restrict_le_self
    apply (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport (fun x => W x * ψ x)).trans tsupport_mul_subset_right)).mp
    exact (hW.integrableOn_compact_subset hψs hψc).mul_continuousOn hψ.continuousOn hψc
  have hUi (i : Fin d) := hint hU
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hφs)
  have hGi (i : Fin d) : Integrable (fun x => G x i * φ x) (volume.restrict Ω) :=
    hint ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).locallyIntegrableOn_comp hG) hφ.continuous hφc hφs
  have hv : (∑ i, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hd (x) : fderiv ℝ φ x v = ∑ i, v i * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hg (x) : ⟪G x, v⟫_ℝ = ∑ i, v i * G x i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  simp only [hd, hg, Finset.mul_sum, Finset.sum_mul]
  have hl (i x) : U x * (v i * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      v i * (U x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by ring
  simp_rw [hl, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hUi i).const_mul (v i)),
    integral_finsetSum _ (fun i _ => (hGi i).const_mul (v i))]
  simp only [integral_const_mul, h _ φ hφ hφc hφs, mul_neg, Finset.sum_neg_distrib]

theorem HasWeakGrad.comp_affineEquiv
    {d m : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {U : EuclideanSpace ℝ (Fin m) → ℝ}
    {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (h : HasWeakGrad G U Ω) (hU : LocallyIntegrableOn U Ω volume)
    (hG : LocallyIntegrableOn G Ω volume) :
    HasWeakGrad (fun x => e.toContinuousAffineMap.contLinear.adjoint (G (e x)))
      (U ∘ e) (e ⁻¹' Ω) := by
  intro i
  have hw := DifferentialGeometry.Analysis.Sobolev.weak_deriv_comp_affineEquiv e
    (μ := volume) (ν := volume) (EuclideanSpace.single i 1)
    (fun φ hφ hφc hφs => h.integral_mul_fderiv hU hG
      (e.toAffineEquiv.linear (EuclideanSpace.single i 1)) hφ hφc hφs)
  have he (y : EuclideanSpace ℝ (Fin m)) :
      ⟪G y, e.toAffineEquiv.linear (EuclideanSpace.single i 1)⟫_ℝ =
        (e.toContinuousAffineMap.contLinear.adjoint (G y)) i := by
    rw [← EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  simpa only [HasWeakPartialDeriv, he, Function.comp_apply] using hw

end DeGiorgi

end

end
