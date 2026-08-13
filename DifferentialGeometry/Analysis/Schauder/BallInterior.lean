import DifferentialGeometry.Analysis.Schauder.BallCutoff
import DifferentialGeometry.Analysis.Schauder.Interior

noncomputable section

open Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def ballInteriorLaplacianSchauderConst
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (alpha Ku Kdu Kf : NNReal)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) : NNReal :=
  interiorLaplacianSchauderConst alpha
    (ballCutoffHolderConst r R)
    (ballCutoffFDerivHolderConst r R)
    (ballCutoffLaplacianHolderConst (V := V) r R)
    Ku Kdu Kf
    (ballCutoffBcf center hr hrR)
    (ballCutoffFDerivBcf center hr hrR)
    (ballCutoffFDeriv2Bcf center hr hrR)
    u du d2u

theorem ball_interior_laplacian_schauder_estimate
    {center : V} {rho r R : Real}
    (hrho : 0 ≤ rho) (hrhor : rho < r) (hrR : r < R)
    {alpha Ku Kdu Kf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (huHolder : HolderWith Ku alpha (u : V → F))
    (hduHolder : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hfHolder : HolderWith Kf alpha (coreLap d2u : V → F)) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho) (u : V → F) ≤
      ballInteriorLaplacianSchauderConst center (hrho.trans hrhor.le) hrR
        alpha Ku Kdu Kf u du d2u := by
  let chi := ballCutoffBcf center (hrho.trans hrhor.le) hrR
  let dchi := ballCutoffFDerivBcf center (hrho.trans hrhor.le) hrR
  let d2chi := ballCutoffFDeriv2Bcf center (hrho.trans hrhor.le) hrR
  have hsU : Metric.closedBall center rho ⊆ Metric.ball center r := by
    intro x hx
    exact Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hx).trans_lt hrhor)
  have hchiOne : ∀ x ∈ Metric.ball center r, chi x = 1 := by
    intro x hx
    exact ballCutoff_eq_one_of_mem_closedBall
      (hrho.trans hrhor.le) hrR (Metric.ball_subset_closedBall hx)
  have hchi : ∀ x, HasFDerivAt (chi : V → Real) (dchi x) x := by
    intro x
    exact hasFDerivAt_ballCutoff center r R x
  have hdchi : ∀ x,
      HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x := by
    intro x
    exact hasFDerivAt_ballCutoffFDeriv center r R x
  have hchiHolder :
      HolderWith (ballCutoffHolderConst r R) alpha (chi : V → Real) :=
    ballCutoff_holderWith (hrho.trans hrhor.le) hrR halpha0.le halpha1.le
  have hdchiHolder :
      HolderWith (ballCutoffFDerivHolderConst r R) alpha
        (dchi : V → V →L[Real] Real) :=
    ballCutoffFDeriv_holderWith
      (hrho.trans hrhor.le) hrR halpha0.le halpha1.le
  have hlapchiHolder :
      HolderWith (ballCutoffLaplacianHolderConst (V := V) r R) alpha
        (coreLap d2chi : V → Real) := by
    have heq : (coreLap d2chi : V → Real) =
        ballCutoffLaplacian center r R := by
      funext x
      exact coreLap_ballCutoffFDeriv2Bcf center
        (hrho.trans hrhor.le) hrR x
    rw [heq]
    exact ballCutoffLaplacian_holderWith (V := V) (center := center)
      (hrho.trans hrhor.le) hrR halpha0.le halpha1.le
  exact interior_laplacian_schauder_estimate_of_cutoff
    (s := Metric.closedBall center rho) (U := Metric.ball center r)
    Metric.isOpen_ball hsU halpha0 halpha1 chi dchi d2chi u du d2u
    hchiOne hchi hdchi hu hdu hchiHolder hdchiHolder hlapchiHolder
    huHolder hduHolder hfHolder

theorem ball_interior_laplacian_schauder_estimate_midpoint
    {center : V} {rho R : Real} (hrho : 0 ≤ rho) (hrhoR : rho < R)
    {alpha Ku Kdu Kf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (huHolder : HolderWith Ku alpha (u : V → F))
    (hduHolder : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hfHolder : HolderWith Kf alpha (coreLap d2u : V → F)) :
    eContDiffHolderGaugeOn 2 alpha (Metric.closedBall center rho) (u : V → F) ≤
      ballInteriorLaplacianSchauderConst center
        (show 0 ≤ (rho + R) / 2 by nlinarith)
        (show (rho + R) / 2 < R by nlinarith)
        alpha Ku Kdu Kf u du d2u := by
  exact ball_interior_laplacian_schauder_estimate hrho
    (show rho < (rho + R) / 2 by nlinarith)
    (show (rho + R) / 2 < R by nlinarith)
    halpha0 halpha1 u du d2u hu hdu huHolder hduHolder hfHolder

end DifferentialGeometry.Analysis.Schauder

end
