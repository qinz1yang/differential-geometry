import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Analysis.Integration.LpNorm

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memW1pWitness_fderiv_of_lipschitz
    {Ω : Set E} {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hfm : MemLp f 2 (volume.restrict Ω))
    (hdfm : MemLp (fderiv ℝ f) 2 (volume.restrict Ω)) :
    ∃ hw : DeGiorgi.MemW1pWitness 2 f Ω,
      (∀ x i, hw.weakGrad x i = fderiv ℝ f x (EuclideanSpace.single i 1)) ∧
      eLpNorm hw.weakGrad 2 (volume.restrict Ω) =
        eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω) := by
  let G : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hGm : MemLp G 2 (volume.restrict Ω) :=
    hdfm.continuousLinearMap_comp (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  have hG (x : E) (i : Fin d) :
      G x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
    have hi : G x i = inner ℝ (G x) (EuclideanSpace.single i 1) := by
      simpa using (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (G x)).symm
    rw [hi]
    exact InnerProductSpace.toDual_symm_apply
  have hweak (i : Fin d) : DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) f Ω := by
    apply (hasWeakPart_of_lip hf i).congr_ae Filter.EventuallyEq.rfl
    filter_upwards [ae_restrict_of_ae (s := Ω) hf.ae_differentiableAt] with x hx
    rw [hG x i]
    exact hx.lineDeriv_eq_fderiv
  let hw : DeGiorgi.MemW1pWitness 2 f Ω := {
    memLp := hfm
    weakGrad := G
    weakGrad_component_memLp := fun i => hGm.eval_piLp i
    isWeakGrad := hweak }
  refine ⟨hw, hG, eLpNorm_congr_norm_ae hGm.aestronglyMeasurable hdfm.aestronglyMeasurable ?_⟩
  exact Filter.Eventually.of_forall fun x =>
    (InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ f x)

theorem exists_memW1pWitness_fderiv_of_lipschitz_of_integrable_sq
    {Ω : Set E} {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hfm : MemLp f 2 (volume.restrict Ω))
    (hdf : IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2) Ω) {B : ℝ}
    (hB : (∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2) ≤ B) :
    ∃ hw : DeGiorgi.MemW1pWitness 2 f Ω,
      (∀ x i, hw.weakGrad x i = fderiv ℝ f x (EuclideanSpace.single i 1)) ∧
      eLpNorm hw.weakGrad 2 (volume.restrict Ω) ≤ ENNReal.ofReal (Real.sqrt B) := by
  have hm : MemLp (fderiv ℝ f) 2 (volume.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm (measurable_fderiv ℝ f).aestronglyMeasurable).mpr hdf
  obtain ⟨hw, hrep, hnorm⟩ := exists_memW1pWitness_fderiv_of_lipschitz hf hfm hm
  refine ⟨hw, hrep, ?_⟩
  rw [hnorm]
  exact Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le hm hB

private theorem norm_fderiv_coordinate_le_ae_of_lipschitz
    {ι : Type*} [Fintype ι] {Ω : Set E} {f : E → EuclideanSpace ℝ ι} {K : ℝ≥0}
    (hf : LipschitzWith K f) (i : ι) : ∀ᵐ x ∂volume.restrict Ω,
      ‖fderiv ℝ (fun y => f y i) x‖ ≤ ‖fderiv ℝ f x‖ := by
  filter_upwards [ae_restrict_of_ae (s := Ω) hf.ae_differentiableAt] with x hx
  have hchain : fderiv ℝ (fun y => f y i) x =
      (EuclideanSpace.proj i).comp (fderiv ℝ f x) := by
    exact (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj i)).comp x
      hx.hasFDerivAt |>.fderiv
  rw [hchain]
  refine ((EuclideanSpace.proj i).comp (fderiv ℝ f x)).opNorm_le_bound
    (norm_nonneg (fderiv ℝ f x)) fun v => ?_
  exact (PiLp.norm_apply_le (fderiv ℝ f x v) i).trans ((fderiv ℝ f x).le_opNorm v)

theorem exists_coordinate_memW1pWitness_fderiv_of_lipschitz
    {ι : Type*} [Fintype ι] {Ω : Set E} {f : E → EuclideanSpace ℝ ι} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hfm : MemLp f 2 (volume.restrict Ω))
    (hdfm : MemLp (fderiv ℝ f) 2 (volume.restrict Ω)) :
    ∃ hw : ∀ i : ι, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω,
      (∀ i x j, (hw i).weakGrad x j =
        fderiv ℝ (fun y => f y i) x (EuclideanSpace.single j 1)) ∧
      (∀ i, eLpNorm (hw i).weakGrad 2 (volume.restrict Ω) ≤
        eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω)) := by
  have hmi (i : ι) : MemLp (fderiv ℝ (fun y => f y i)) 2 (volume.restrict Ω) :=
    hdfm.of_le (measurable_fderiv ℝ _).aestronglyMeasurable
      (norm_fderiv_coordinate_le_ae_of_lipschitz hf i)
  have hfi (i : ι) : LipschitzWith K (fun x => f x i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (f x i) (f y i) = ‖(f x - f y) i‖ := by rw [dist_eq_norm]; rfl
      _ ≤ ‖f x - f y‖ := PiLp.norm_apply_le _ i
      _ ≤ (K : ℝ) * dist x y := by
        rw [← dist_eq_norm]
        exact hf.dist_le_mul x y
  choose hw hrep hnorm using fun i =>
    exists_memW1pWitness_fderiv_of_lipschitz (hfi i) (hfm.eval_piLp i) (hmi i)
  exact ⟨hw, hrep, fun i => (hnorm i).trans_le
    (eLpNorm_mono_ae (hmi i).aestronglyMeasurable
      (norm_fderiv_coordinate_le_ae_of_lipschitz hf i))⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_uniform_coordinate_memW1pWitness_of_lipschitz
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (f : ℕ → E → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    {D B : ℝ} (hD : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖f n x‖ ≤ D)
    (hB : ∀ n, (∫ x in Ω, ‖fderiv ℝ (f n) x‖ ^ 2) ≤ B) :
    ∃ (R : ℝ) (hw : ∀ n (i : ι), DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω),
      (∀ n i x j, (hw n i).weakGrad x j =
        fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)) ∧
      (∀ n i, eLpNorm (fun x => f n x i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R) ∧
      (∀ n i, eLpNorm (hw n i).weakGrad 2 (volume.restrict Ω) ≤ ENNReal.ofReal R) := by
  have hfm (n : ℕ) : MemLp (f n) 2 (volume.restrict Ω) :=
    MemLp.of_bound (hf n).continuous.aestronglyMeasurable D
      (hD n)
  have hdfm (n : ℕ) : MemLp (fderiv ℝ (f n)) 2 (volume.restrict Ω) :=
    MemLp.of_bound (measurable_fderiv ℝ (f n)).aestronglyMeasurable (K n)
      (Filter.Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ (hf n))
  choose hw hrep hgrad using fun n =>
    exists_coordinate_memW1pWitness_fderiv_of_lipschitz (hf n) (hfm n) (hdfm n)
  let A : ℝ≥0∞ := (volume.restrict Ω) univ ^ (1 / 2 : ℝ) * ENNReal.ofReal D
  have hAtop : A ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
      ENNReal.ofReal_ne_top
  have hfun (n : ℕ) : eLpNorm (f n) 2 (volume.restrict Ω) ≤ A := by
    simpa only [A, ENNReal.toReal_ofNat, one_div] using
      eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (hfm n).aestronglyMeasurable (hD n)
  let R : ℝ := A.toReal + Real.sqrt B
  refine ⟨R, hw, hrep, ?_, ?_⟩
  · intro n i
    apply ((eLpNorm_mono_ae ((hfm n).eval_piLp i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le (f n x) i)).trans
      (hfun n)).trans
    rw [← ENNReal.ofReal_toReal hAtop]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Real.sqrt_nonneg B))
  · intro n i
    apply (hgrad n i).trans
      ((Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le (hdfm n) (hB n)).trans ?_)
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left ENNReal.toReal_nonneg)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
