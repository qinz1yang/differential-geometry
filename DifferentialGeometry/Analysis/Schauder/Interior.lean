import DifferentialGeometry.Analysis.Schauder.ConstantCoefficientElliptic
import DifferentialGeometry.Analysis.Schauder.CutoffExistence
import DifferentialGeometry.Analysis.Schauder.CutoffLaplacian

noncomputable section

open Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def interiorLaplacianSchauderConst
    (alpha Kchi Kdchi Klapchi Ku Kdu Kf : NNReal)
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) : NNReal :=
  laplacianSchauderConst alpha
    (cutoffLaplacianHolderConst Kchi Kdchi Klapchi Ku Kdu Kf
      chi dchi d2chi u du d2u)
    (cutoffLaplacianSupConst chi dchi d2chi u du d2u)
    (cutoffValue chi u)

theorem interior_laplacian_schauder_estimate_of_cutoff
    {s U : Set V} (hU : IsOpen U) (hsU : s ⊆ U)
    {alpha Kchi Kdchi Klapchi Ku Kdu Kf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hchi_one : ∀ x ∈ U, chi x = 1)
    (hchi : ∀ x, HasFDerivAt (chi : V → Real) (dchi x) x)
    (hdchi : ∀ x,
      HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x)
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (hchiHolder : HolderWith Kchi alpha (chi : V → Real))
    (hdchiHolder : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hlapchiHolder : HolderWith Klapchi alpha (coreLap d2chi : V → Real))
    (huHolder : HolderWith Ku alpha (u : V → F))
    (hduHolder : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hfHolder : HolderWith Kf alpha (coreLap d2u : V → F)) :
    eContDiffHolderGaugeOn 2 alpha s (u : V → F) ≤
      interiorLaplacianSchauderConst alpha Kchi Kdchi Klapchi Ku Kdu Kf
        chi dchi d2chi u du d2u := by
  have hw : ∀ x,
      HasFDerivAt (cutoffValue chi u : V → F)
        (cutoffJet1 chi dchi u du x) x :=
    cutoffValue_hasFDerivAt chi dchi u du hchi hu
  have hdw : ∀ x,
      HasFDerivAt (cutoffJet1 chi dchi u du : V → V →L[Real] F)
        (cutoffJet2 chi dchi d2chi u du d2u x) x :=
    cutoffJet1_hasFDerivAt chi dchi d2chi u du d2u hchi hdchi hu hdu
  have hbound :
      ‖cutoffLaplacian chi dchi d2chi u du d2u‖ ≤
        cutoffLaplacianSupConst chi dchi d2chi u du d2u := by
    exact_mod_cast nnnorm_cutoffLaplacian_le chi dchi d2chi u du d2u
  have hholder := cutoffLaplacian_holderWith chi dchi d2chi u du d2u
    hchiHolder hdchiHolder hlapchiHolder huHolder hduHolder hfHolder
  have hglobal := laplacian_schauder_estimate halpha0 halpha1
    (cutoffValue chi u) (cutoffJet1 chi dchi u du)
    (cutoffJet2 chi dchi d2chi u du d2u) hw hdw hbound (by
      simpa only [cutoffLaplacian] using hholder)
  have heq : Set.EqOn (u : V → F) (cutoffValue chi u : V → F) U := by
    intro x hx
    rw [cutoffValue_apply, hchi_one x hx, one_smul]
  rw [eContDiffHolderGaugeOn_congr_of_eqOn_open hU hsU heq 2 alpha]
  exact (eContDiffHolderGaugeOn_mono (Set.subset_univ s)
    2 alpha (cutoffValue chi u : V → F)).trans hglobal

theorem exists_interior_laplacian_schauder_bound
    {K Omega : Set V} (hK : IsCompact K) (hOmega : IsOpen Omega)
    (hKOmega : K ⊆ Omega) {alpha Kf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (hfHolder : HolderWith Kf alpha (coreLap d2u : V → F)) :
    ∃ C : NNReal, eContDiffHolderGaugeOn 2 alpha K (u : V → F) ≤ C := by
  let Ku := max (2 * ‖u‖₊) ‖du‖₊
  have huHolder : HolderWith Ku alpha (u : V → F) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖u‖₊) (N := ‖du‖₊) halpha0.le halpha1.le hu
    · exact fun x ↦ by simpa using u.norm_coe_le_norm x
    · exact fun x ↦ by simpa using du.norm_coe_le_norm x
  let Kdu := max (2 * ‖du‖₊) ‖d2u‖₊
  have hduHolder : HolderWith Kdu alpha (du : V → V →L[Real] F) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖du‖₊) (N := ‖d2u‖₊) halpha0.le halpha1.le hdu
    · exact fun x ↦ by simpa using du.norm_coe_le_norm x
    · exact fun x ↦ by simpa using d2u.norm_coe_le_norm x
  obtain ⟨U, chi, dchi, d2chi, Kchi, Kdchi, Klapchi,
    hU, hKU, hchiOne, hchiSupp, hchiRange,
    hchi, hdchi, hchiHolder, hdchiHolder, hlapchiHolder⟩ :=
      exists_schauder_cutoff hK hOmega hKOmega halpha0.le halpha1.le
  let C := interiorLaplacianSchauderConst
    alpha Kchi Kdchi Klapchi Ku Kdu Kf chi dchi d2chi u du d2u
  refine ⟨C, ?_⟩
  exact interior_laplacian_schauder_estimate_of_cutoff hU hKU
    halpha0 halpha1 chi dchi d2chi u du d2u hchiOne
    hchi hdchi hu hdu hchiHolder hdchiHolder hlapchiHolder
    huHolder hduHolder hfHolder

end DifferentialGeometry.Analysis.Schauder

end
