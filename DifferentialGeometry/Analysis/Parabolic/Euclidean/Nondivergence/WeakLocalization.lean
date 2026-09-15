import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Cutoff

noncomputable section
open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_nondivergence_cutoff
    {Ω : Set E} (hΩ : IsOpen Ω) {u dtU du d2u a f η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hdtU : MemLp dtU 2 (volume.restrict Ω))
    (hdu : MemLp du 2 (volume.restrict Ω))
    (hd2u : MemLp d2u 2 (volume.restrict Ω))
    (it ix : Fin d)
    (htime : DeGiorgi.HasWeakPartialDeriv it dtU u Ω)
    (hspace : DeGiorgi.HasWeakPartialDeriv ix du u Ω)
    (hsecond : DeGiorgi.HasWeakPartialDeriv ix d2u du Ω)
    (heq : dtU =ᵐ[volume.restrict Ω] fun x => a x * d2u x + f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    let v := fun x => η x * u x
    let vt := fun x => η x * dtU x + fderiv ℝ η x (EuclideanSpace.single it 1) * u x
    let vx := fun x => η x * du x + fderiv ℝ η x (EuclideanSpace.single ix 1) * u x
    let vxx := fun x => η x * d2u x +
      2 * fderiv ℝ η x (EuclideanSpace.single ix 1) * du x +
      fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) x
        (EuclideanSpace.single ix 1) * u x
    let residual := fun x => η x * f x +
      fderiv ℝ η x (EuclideanSpace.single it 1) * u x -
      a x * (2 * fderiv ℝ η x (EuclideanSpace.single ix 1) * du x +
        fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) x
          (EuclideanSpace.single ix 1) * u x)
    DeGiorgi.HasWeakPartialDeriv it vt v univ ∧
      DeGiorgi.HasWeakPartialDeriv ix vx v univ ∧
      DeGiorgi.HasWeakPartialDeriv ix vxx vx univ ∧
      vt =ᵐ[volume] fun x => a x * vxx x + residual x := by
  dsimp only
  have ht := hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hdtU it htime hη hηc hηs
  have hs := hasWeakPartialDeriv_second_mul_cutoff_univ hΩ hu hdu hdu hd2u
    ix ix hspace hspace hsecond hη hηc hηs
  refine ⟨ht, hs.1, ?_, ?_⟩
  · convert hs.2 using 1
    ext x
    ring
  · have heq' := ae_imp_of_ae_restrict heq
    filter_upwards [heq'] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hx hxΩ]
      ring
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxΩ (hηs h))
      have htηs : tsupport (fun y => fderiv ℝ η y (EuclideanSpace.single it 1)) ⊆ Ω :=
        (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single it 1)).trans hηs
      have hxηs : tsupport (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) ⊆ Ω :=
        (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single ix 1)).trans hηs
      have hxxηs : tsupport (fun z =>
          fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) z
            (EuclideanSpace.single ix 1)) ⊆ Ω :=
        (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single ix 1)).trans hxηs
      have htηx : (fun y => fderiv ℝ η y (EuclideanSpace.single it 1)) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ η y (EuclideanSpace.single it 1))
          (x := x) (fun h => hxΩ (htηs h))
      have hxηx : (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ η y (EuclideanSpace.single ix 1))
          (x := x) (fun h => hxΩ (hxηs h))
      have hxxηx : (fun z =>
          fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) z
            (EuclideanSpace.single ix 1)) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun z => fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single ix 1)) z
            (EuclideanSpace.single ix 1)) (x := x) (fun h => hxΩ (hxxηs h))
      simp only [hηx, htηx, hxηx, hxxηx, zero_mul, add_zero, sub_zero, mul_zero]

end DifferentialGeometry.Analysis.Parabolic.Euclidean
