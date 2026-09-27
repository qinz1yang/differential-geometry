import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import DifferentialGeometry.Analysis.Integration.Lp.Cutoff

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_second_mul_cutoff_univ
    {Ω : Set E} (hΩ : IsOpen Ω) {u gj gk gjk η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hgj : MemLp gj 2 (volume.restrict Ω))
    (hgk : MemLp gk 2 (volume.restrict Ω))
    (hgjk : MemLp gjk 2 (volume.restrict Ω))
    (j k : Fin d)
    (hfirst_j : DeGiorgi.HasWeakPartialDeriv j gj u Ω)
    (hfirst_k : DeGiorgi.HasWeakPartialDeriv k gk u Ω)
    (hsecond : DeGiorgi.HasWeakPartialDeriv j gjk gk Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    DeGiorgi.HasWeakPartialDeriv k
      (fun x => η x * gk x + fderiv ℝ η x (EuclideanSpace.single k 1) * u x)
      (fun x => η x * u x) univ ∧
    DeGiorgi.HasWeakPartialDeriv j
      (fun x => η x * gjk x + fderiv ℝ η x (EuclideanSpace.single j 1) * gk x +
        fderiv ℝ η x (EuclideanSpace.single k 1) * gj x +
        fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single k 1)) x
          (EuclideanSpace.single j 1) * u x)
      (fun x => η x * gk x + fderiv ℝ η x (EuclideanSpace.single k 1) * u x)
      univ := by
  refine ⟨hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hgk k hfirst_k hη hηc hηs, ?_⟩
  let Dη : Fin d → E → ℝ := fun i x => fderiv ℝ η x (EuclideanSpace.single i 1)
  have hDη (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (Dη i) :=
    (hη.fderiv_right (by simp)).clm_apply contDiff_const
  have hDηc (i : Fin d) : HasCompactSupport (Dη i) :=
    hηc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hDηs (i : Fin d) : tsupport (Dη i) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hηs
  have hDDη : Continuous
      (fun x => fderiv ℝ (Dη k) x (EuclideanSpace.single j 1)) :=
    ((hDη k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDDηc : HasCompactSupport
      (fun x => fderiv ℝ (Dη k) x (EuclideanSpace.single j 1)) :=
    (hDηc k).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  have hDDηs : tsupport
      (fun x => fderiv ℝ (Dη k) x (EuclideanSpace.single j 1)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans (hDηs k)
  have hlocal {v ξ : E → ℝ} (hv : MemLp v 2 (volume.restrict Ω))
      (hξ : Continuous ξ) (hξc : HasCompactSupport ξ) (hξs : tsupport ξ ⊆ Ω) :
      LocallyIntegrable (fun x => ξ x * v x) (volume.restrict univ) := by
    simpa only [Measure.restrict_univ, smul_eq_mul] using
      (hv.continuous_smul_of_tsupport_subset hΩ.measurableSet hξ hξc hξs).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hleft := hasWeakPartialDeriv_mul_cutoff_univ hΩ hgk hgjk j hsecond hη hηc hηs
  have hright := hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hgj j hfirst_j
    (hDη k) (hDηc k) (hDηs k)
  have hsum := hleft.add hright
    (hlocal hgk hη.continuous hηc hηs)
    (hlocal hu (hDη k).continuous (hDηc k) (hDηs k))
    ((hlocal hgjk hη.continuous hηc hηs).add
      (hlocal hgk (hDη j).continuous (hDηc j) (hDηs j)))
    ((hlocal hgj (hDη k).continuous (hDηc k) (hDηs k)).add
      (hlocal hu hDDη hDDηc hDDηs))
  convert hsum using 1 <;> (ext x; simp only [Pi.add_apply, Dη] <;> ring)

end DifferentialGeometry.Analysis.Sobolev
