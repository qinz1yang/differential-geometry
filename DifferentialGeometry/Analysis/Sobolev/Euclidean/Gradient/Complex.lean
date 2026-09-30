import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Columns
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSpace.Complete

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)


section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def complexColumnRestriction {Ω : Set V} {b : ℝ}
    (hball : Metric.closedBall (0 : V) b ⊆ Ω) :
    Lp F 2 (volume.restrict Ω) →L[ℝ]
      Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Complex.orthonormalBasisOneI.repr
    (measurePreserving_complex_plane_repr_closedBall b)).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (E := F) (p := 2)
      (by simp : (1 : ℝ≥0∞) ≠ ∞)
      (by simpa only [one_smul] using Measure.restrict_mono_set volume hball))

private theorem complexColumnRestriction_coeFn {Ω : Set V} {b : ℝ}
    (hball : Metric.closedBall (0 : V) b ⊆ Ω) (A : Lp F 2 (volume.restrict Ω)) :
    (complexColumnRestriction hball A : ℂ → F) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) b)]
      (fun z => A (Complex.orthonormalBasisOneI.repr z)) := by
  let hle : volume.restrict (Metric.closedBall (0 : V) b) ≤ (1 : ℝ≥0∞) • volume.restrict Ω :=
    by simpa only [one_smul] using Measure.restrict_mono_set volume hball
  let R : Lp F 2 (volume.restrict Ω) →L[ℝ]
      Lp F 2 (volume.restrict (Metric.closedBall (0 : V) b)) :=
    Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ∞) hle
  have hR : (R A : V → F) =ᵐ[volume.restrict (Metric.closedBall (0 : V) b)] A :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ∞) hle A
  have hcomp := Lp.coeFn_compMeasurePreserving (R A)
    (measurePreserving_complex_plane_repr_closedBall b)
  have hrep := (measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae hR
  exact hcomp.trans hrep

private theorem fderiv_comp_plane_repr_symm
    (U : ℂ → F) (z : ℂ) (j : Fin 2) :
    fderiv ℝ (U ∘ Complex.orthonormalBasisOneI.repr.symm)
      (Complex.orthonormalBasisOneI.repr z) (EuclideanSpace.single j 1) =
      fderiv ℝ U z (Complex.orthonormalBasisOneI j) := by
  erw [Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    OrthonormalBasis.repr_symm_single]
  change fderiv ℝ U (Complex.orthonormalBasisOneI.repr.symm
    (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI j) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem exists_complex_lp_columns_of_tendsto_dual
    {Ω : Set V} {b : ℝ} (hball : Metric.closedBall (0 : V) b ⊆ Ω)
    (U : ℕ → ℂ → F) (G : Fin 2 → V → F)
    (A : Fin 2 → ℕ → Lp F 2 (volume.restrict Ω))
    (A₀ : Fin 2 → Lp F 2 (volume.restrict Ω))
    (hA : ∀ j n, (A j n : V → F) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (U n ∘ Complex.orthonormalBasisOneI.repr.symm) x
        (EuclideanSpace.single j 1)))
    (hA₀ : ∀ j, (A₀ j : V → F) =ᵐ[volume.restrict Ω] G j)
    (hweak : ∀ j (L : Lp F 2 (volume.restrict Ω) →L[ℝ] ℝ),
      Tendsto (fun n => L (A j n)) atTop (𝓝 (L (A₀ j)))) :
    ∃ (B : Fin 2 → ℕ → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
      (B₀ : Fin 2 → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b))),
      (∀ j n, (B j n : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
        (fun z => fderiv ℝ (U n) z (Complex.orthonormalBasisOneI j))) ∧
      (∀ j, (B₀ j : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
        (fun z => G j (Complex.orthonormalBasisOneI.repr z))) ∧
      ∀ j (L : Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) →L[ℝ] ℝ),
        Tendsto (fun n => L (B j n)) atTop (𝓝 (L (B₀ j))) := by
  let T := complexColumnRestriction (F := F) hball
  refine ⟨fun j n => T (A j n), fun j => T (A₀ j), ?_, ?_, ?_⟩
  · intro j n
    have hsource := ae_mono (Measure.restrict_mono_set volume hball) (hA j n)
    have hpull :=
      (measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae hsource
    filter_upwards [complexColumnRestriction_coeFn hball (A j n), hpull] with z hz hs
    exact hz.trans (hs.trans (fderiv_comp_plane_repr_symm (U n) z j))
  · intro j
    have hsource := ae_mono (Measure.restrict_mono_set volume hball) (hA₀ j)
    exact (complexColumnRestriction_coeFn hball (A₀ j)).trans
      ((measurePreserving_complex_plane_repr_closedBall b).quasiMeasurePreserving.ae hsource)
  · intro j L
    exact hweak j (L.comp T)

end Normed

variable {ι : Type*} [Fintype ι]
local notation "F" => EuclideanSpace ℝ ι

theorem exists_complex_lp_gradient_columns_of_tendsto_inner
    {Ω : Set V} {b : ℝ} (hball : Metric.closedBall (0 : V) b ⊆ Ω)
    (U : ℕ → ℂ → F) (v : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => U n (Complex.orthonormalBasisOneI.repr.symm x) i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hU : ∀ n, LipschitzWith (K n) (U n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => U n (Complex.orthonormalBasisOneI.repr.symm y) i)
        x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z))) :
    ∃ (B : Fin 2 → ℕ → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
      (B₀ : Fin 2 → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b))),
      (∀ j n, (B j n : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
        (fun z => fderiv ℝ (U n) z (Complex.orthonormalBasisOneI j))) ∧
      (∀ j, (B₀ j : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
        (fun z => WithLp.toLp 2
          (fun i => (hv i).weakGrad (Complex.orthonormalBasisOneI.repr z) j))) ∧
      ∀ j (L : Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) →L[ℝ] ℝ),
        Tendsto (fun n => L (B j n)) atTop (𝓝 (L (B₀ j))) := by
  have hf (n : ℕ) : LipschitzWith (K n)
      (U n ∘ Complex.orthonormalBasisOneI.repr.symm) := by
    simpa only [mul_one] using
      (hU n).comp Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitzWith
  obtain ⟨A, A₀, hA, hA₀, hAw⟩ := exists_lp_gradient_columns_of_tendsto_inner
    (fun n => U n ∘ Complex.orthonormalBasisOneI.repr.symm) v hs hv K hf hrep hweak
  exact exists_complex_lp_columns_of_tendsto_dual hball U
    (fun j x => WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) A A₀ hA hA₀ hAw

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology F]

theorem exists_complex_lp_columns_tendsto_of_tendsto_eLpNorm
    (U : ℕ → ℂ → F) (G : Fin 2 → ℂ → F) (K : ℕ → ℝ≥0)
    (hU : ∀ n, LipschitzWith (K n) (U n)) (b : ℝ)
    (B₀ : Fin 2 → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
    (hB₀ : ∀ j, (B₀ j : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)] G j)
    (hstrong : ∀ j, Tendsto (fun n => eLpNorm
      (fun z => fderiv ℝ (U n) z (Complex.orthonormalBasisOneI j) - G j z)
      2 (volume.restrict (Metric.ball (0 : ℂ) b))) atTop (𝓝 0)) :
    ∃ B : Fin 2 → ℕ → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)),
      (∀ j n, (B j n : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
        (fun z => fderiv ℝ (U n) z (Complex.orthonormalBasisOneI j))) ∧
      ∀ j, Tendsto (B j) atTop (𝓝 (B₀ j)) := by
  borelize F
  let μ : Measure ℂ := volume.restrict (Metric.closedBall (0 : ℂ) b)
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) b).measure_lt_top.ne
  let D (j : Fin 2) (n : ℕ) (z : ℂ) :=
    fderiv ℝ (U n) z (Complex.orthonormalBasisOneI j)
  have hD (j : Fin 2) (n : ℕ) : MemLp (D j n) 2 μ := by
    apply MemLp.of_bound
      (measurable_fderiv_apply_const ℝ (U n) (Complex.orthonormalBasisOneI j)).aestronglyMeasurable
      ((K n : ℝ) * ‖Complex.orthonormalBasisOneI j‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ (U n) z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hU n)) (norm_nonneg _))
  let B (j : Fin 2) (n : ℕ) : Lp F 2 μ := (hD j n).toLp (D j n)
  have hB (j : Fin 2) (n : ℕ) : (B j n : ℂ → F) =ᵐ[μ] D j n := (hD j n).coeFn_toLp
  refine ⟨B, hB, fun j => ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (B j) (B₀ j)).mpr
  have h := hstrong j
  rw [restrict_ball_eq_restrict_closedBall_complex b] at h
  have heq (n : ℕ) : eLpNorm (⇑(B j n) - ⇑(B₀ j)) 2 μ =
      eLpNorm (fun z => D j n z - G j z) 2 μ :=
    eLpNorm_congr_ae ((hB j n).sub (hB₀ j))
  simpa only [heq] using h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
