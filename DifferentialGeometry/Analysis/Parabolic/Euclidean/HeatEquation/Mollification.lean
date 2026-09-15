import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Local

noncomputable section

open MeasureTheory Set Metric
open scoped Convolution

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem mollifyEps_heat_equation_on
    {ε : ℝ} (hε : 0 < ε) {u dtU du d2u : E → ℝ}
    {it ix : Fin d} {c : ℝ} {Ω Ω' : Set E}
    (hu : LocallyIntegrable u volume) (hdu : LocallyIntegrable du volume)
    (htime : DeGiorgi.HasWeakPartialDeriv it dtU u Ω)
    (hspace : DeGiorgi.HasWeakPartialDeriv ix du u Ω)
    (hsecond : DeGiorgi.HasWeakPartialDeriv ix d2u du Ω)
    (hequation : dtU =ᵐ[volume.restrict Ω] fun y => c * d2u y)
    (hΩ : MeasurableSet Ω) (hΩ' : IsOpen Ω')
    (hball : ∀ x ∈ Ω', closedBall x ε ⊆ Ω)
    {x : E} (hx : x ∈ Ω') :
    fderiv ℝ (mollifyEps hε u) x (EuclideanSpace.single it 1) =
      c * fderiv ℝ (fun y => fderiv ℝ (mollifyEps hε u) y
        (EuclideanSpace.single ix 1)) x (EuclideanSpace.single ix 1) := by
  rw [mollifyEps_partial_eq_mollifyEps_weakPartial_of_closedBall_subset
      hε hu htime x (hball x hx),
    mollifyEps_second_partial_eq_mollifyEps_weakPartial_on
      hε hu hdu hspace hsecond hΩ' hball hx,
    mollifyEps_eq_of_ae_eq_on hε hΩ hequation x (hball x hx)]
  rw [mollifyEps_eq_convolution_swap, mollifyEps_eq_convolution_swap,
    convolution_lsmul, convolution_lsmul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  ring

end DifferentialGeometry.Analysis.Parabolic.Euclidean
