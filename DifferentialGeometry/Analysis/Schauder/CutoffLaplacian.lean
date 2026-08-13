import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamel
import DifferentialGeometry.Analysis.Schauder.CutoffProduct

noncomputable section

open Real
open scoped BoundedContinuousFunction RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def cutoffGradientPair
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F)) :
    BoundedContinuousFunction V F :=
  ∑ i : Fin (Module.finrank Real V),
    ((ContinuousLinearMap.apply Real Real
      ((stdOrthonormalBasis Real V) i)).compLeftContinuousBounded V dchi) •
    ((ContinuousLinearMap.apply Real F
      ((stdOrthonormalBasis Real V) i)).compLeftContinuousBounded V du)

@[simp]
theorem cutoffGradientPair_apply
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F)) (x : V) :
    cutoffGradientPair dchi du x =
      ∑ i : Fin (Module.finrank Real V),
        dchi x ((stdOrthonormalBasis Real V) i) •
          du x ((stdOrthonormalBasis Real V) i) := by
  unfold cutoffGradientPair
  rw [BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

def cutoffLaplacian
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) :
    BoundedContinuousFunction V F :=
  coreLap (cutoffJet2 chi dchi d2chi u du d2u)

@[simp]
theorem cutoffLaplacian_apply
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (x : V) :
    cutoffLaplacian chi dchi d2chi u du d2u x =
      chi x • coreLap d2u x +
        2 • cutoffGradientPair dchi du x +
        coreLap d2chi x • u x := by
  simp only [cutoffLaplacian, coreLap_apply, cutoffJet2_apply,
    cutoffGradientPair_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  simp only [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [Finset.smul_sum, Finset.sum_smul, two_nsmul]
  abel_nf

theorem cutoffLaplacian_eq
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) :
    cutoffLaplacian chi dchi d2chi u du d2u =
      cutoffValue chi (coreLap d2u) +
        2 • cutoffGradientPair dchi du +
        cutoffValue (coreLap d2chi) u := by
  ext x
  simp only [cutoffLaplacian_apply, cutoffValue_apply,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.nsmul_apply]

theorem norm_cutoffGradientPair_le
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F)) :
    ‖cutoffGradientPair dchi du‖ ≤
      Module.finrank Real V * ‖dchi‖ * ‖du‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [cutoffGradientPair_apply]
  calc
    ‖∑ i : Fin (Module.finrank Real V),
        dchi x ((stdOrthonormalBasis Real V) i) •
          du x ((stdOrthonormalBasis Real V) i)‖ ≤
        ∑ _i : Fin (Module.finrank Real V), ‖dchi‖ * ‖du‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [norm_smul, Real.norm_eq_abs]
      have hdchi :
          |dchi x ((stdOrthonormalBasis Real V) i)| ≤ ‖dchi‖ := by
        calc
          |dchi x ((stdOrthonormalBasis Real V) i)| =
              ‖dchi x ((stdOrthonormalBasis Real V) i)‖ := by
            rw [Real.norm_eq_abs]
          _ ≤ ‖dchi x‖ * ‖(stdOrthonormalBasis Real V) i‖ :=
            (dchi x).le_opNorm _
          _ ≤ ‖dchi‖ := by
            rw [(stdOrthonormalBasis Real V).orthonormal.norm_eq_one i, mul_one]
            exact dchi.norm_coe_le_norm x
      have hdu :
          ‖du x ((stdOrthonormalBasis Real V) i)‖ ≤ ‖du‖ := by
        calc
          ‖du x ((stdOrthonormalBasis Real V) i)‖ ≤
              ‖du x‖ * ‖(stdOrthonormalBasis Real V) i‖ :=
            (du x).le_opNorm _
          _ ≤ ‖du‖ := by
            rw [(stdOrthonormalBasis Real V).orthonormal.norm_eq_one i, mul_one]
            exact du.norm_coe_le_norm x
      exact mul_le_mul hdchi hdu (norm_nonneg _) (norm_nonneg _)
    _ = Module.finrank Real V * ‖dchi‖ * ‖du‖ := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

theorem norm_cutoffLaplacian_le
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) :
    ‖cutoffLaplacian chi dchi d2chi u du d2u‖ ≤
      ‖chi‖ * ‖coreLap d2u‖ +
        2 * (Module.finrank Real V * ‖dchi‖ * ‖du‖) +
        ‖coreLap d2chi‖ * ‖u‖ := by
  rw [cutoffLaplacian_eq]
  calc
    ‖cutoffValue chi (coreLap d2u) +
        2 • cutoffGradientPair dchi du +
        cutoffValue (coreLap d2chi) u‖ ≤
      ‖cutoffValue chi (coreLap d2u)‖ +
        ‖2 • cutoffGradientPair dchi du‖ +
      ‖cutoffValue (coreLap d2chi) u‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖chi‖ * ‖coreLap d2u‖ +
        2 * (Module.finrank Real V * ‖dchi‖ * ‖du‖) +
        ‖coreLap d2chi‖ * ‖u‖ := by
      gcongr
      · exact norm_smul_le chi (coreLap d2u)
      · rw [RCLike.norm_nsmul (K := Real), nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left (norm_cutoffGradientPair_le dchi du)
          (by norm_num : (0 : Real) ≤ 2)
      · exact norm_smul_le (coreLap d2chi) u

private theorem norm_apply_stdOrthonormalBasis_le_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
    (i : Fin (Module.finrank Real V)) :
    ‖ContinuousLinearMap.apply Real G ((stdOrthonormalBasis Real V) i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (ContinuousLinearMap.apply Real G ((stdOrthonormalBasis Real V) i))
    zero_le_one ?_
  intro A
  change ‖A ((stdOrthonormalBasis Real V) i)‖ ≤ 1 * ‖A‖
  simpa only [(stdOrthonormalBasis Real V).orthonormal.norm_eq_one i, mul_one, one_mul] using
    A.le_opNorm ((stdOrthonormalBasis Real V) i)

theorem cutoffGradientPair_holderWith
    {alpha Kdchi Kdu : NNReal}
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (hdchi : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hdu : HolderWith Kdu alpha (du : V → V →L[Real] F)) :
    HolderWith
      ((Module.finrank Real V : NNReal) *
        (‖dchi‖₊ * Kdu + ‖du‖₊ * Kdchi)) alpha
      (cutoffGradientPair dchi du : V → F) := by
  let e := stdOrthonormalBasis Real V
  let K := ‖dchi‖₊ * Kdu + ‖du‖₊ * Kdchi
  have hcomponent : ∀ i : Fin (Module.finrank Real V),
      HolderWith K alpha
        (fun x ↦ dchi x (e i) • du x (e i)) := by
    intro i
    have hdchi_i : HolderWith Kdchi alpha (fun x ↦ dchi x (e i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real (e i))
        (norm_apply_stdOrthonormalBasis_le_one (V := V) (G := Real) i) hdchi
    have hdu_i : HolderWith Kdu alpha (fun x ↦ du x (e i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F (e i))
        (norm_apply_stdOrthonormalBasis_le_one (V := V) (G := F) i) hdu
    apply holderWith_smul_of_norm_le hdchi_i hdu_i
    · intro x
      calc
        ‖dchi x (e i)‖ ≤ ‖dchi x‖ * ‖e i‖ := (dchi x).le_opNorm _
        _ ≤ ‖dchi‖ := by
          rw [show ‖e i‖ = 1 from
            (stdOrthonormalBasis Real V).orthonormal.norm_eq_one i, mul_one]
          exact dchi.norm_coe_le_norm x
        _ = (‖dchi‖₊ : Real) := rfl
    · intro x
      calc
        ‖du x (e i)‖ ≤ ‖du x‖ * ‖e i‖ := (du x).le_opNorm _
        _ ≤ ‖du‖ := by
          rw [show ‖e i‖ = 1 from
            (stdOrthonormalBasis Real V).orthonormal.norm_eq_one i, mul_one]
          exact du.norm_coe_le_norm x
        _ = (‖du‖₊ : Real) := rfl
  have hsum := holderWith_finset_sum
    (Finset.univ : Finset (Fin (Module.finrank Real V)))
    (K := fun _ ↦ K) (f := fun i x ↦ dchi x (e i) • du x (e i))
    (fun i _ ↦ hcomponent i)
  rw [show (cutoffGradientPair dchi du : V → F) =
      fun x ↦ ∑ i : Fin (Module.finrank Real V), dchi x (e i) • du x (e i) from
    funext fun x ↦ cutoffGradientPair_apply dchi du x]
  simpa only [K, e, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hsum

def cutoffLaplacianSupConst
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) : NNReal :=
  ‖chi‖₊ * ‖coreLap d2u‖₊ +
    2 * ((Module.finrank Real V : NNReal) * ‖dchi‖₊ * ‖du‖₊) +
    ‖coreLap d2chi‖₊ * ‖u‖₊

theorem nnnorm_cutoffLaplacian_le
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) :
    ‖cutoffLaplacian chi dchi d2chi u du d2u‖₊ ≤
      cutoffLaplacianSupConst chi dchi d2chi u du d2u := by
  rw [← NNReal.coe_le_coe]
  simpa only [cutoffLaplacianSupConst, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, coe_nnnorm] using
      norm_cutoffLaplacian_le chi dchi d2chi u du d2u

def cutoffLaplacianHolderConst
    (Kchi Kdchi Klapchi Ku Kdu Kf : NNReal)
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) : NNReal :=
  ‖chi‖₊ * Kf + ‖coreLap d2u‖₊ * Kchi +
    2 * ((Module.finrank Real V : NNReal) *
      (‖dchi‖₊ * Kdu + ‖du‖₊ * Kdchi)) +
    ‖coreLap d2chi‖₊ * Ku + ‖u‖₊ * Klapchi

theorem cutoffLaplacian_holderWith
    {alpha Kchi Kdchi Klapchi Ku Kdu Kf : NNReal}
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hchi : HolderWith Kchi alpha (chi : V → Real))
    (hdchi : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hlapchi : HolderWith Klapchi alpha (coreLap d2chi : V → Real))
    (hu : HolderWith Ku alpha (u : V → F))
    (hdu : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hf : HolderWith Kf alpha (coreLap d2u : V → F)) :
    HolderWith
      (cutoffLaplacianHolderConst Kchi Kdchi Klapchi Ku Kdu Kf
        chi dchi d2chi u du d2u) alpha
      (cutoffLaplacian chi dchi d2chi u du d2u : V → F) := by
  have hfirst := holderWith_smul_of_norm_le
    (M := ‖chi‖₊) (N := ‖coreLap d2u‖₊) hchi hf
    (fun x ↦ by simpa using chi.norm_coe_le_norm x)
    (fun x ↦ by simpa using (coreLap d2u).norm_coe_le_norm x)
  have hcross := cutoffGradientPair_holderWith dchi du hdchi hdu
  have hthird := holderWith_smul_of_norm_le
    (M := ‖coreLap d2chi‖₊) (N := ‖u‖₊) hlapchi hu
    (fun x ↦ by simpa using (coreLap d2chi).norm_coe_le_norm x)
    (fun x ↦ by simpa using u.norm_coe_le_norm x)
  rw [show (cutoffLaplacian chi dchi d2chi u du d2u : V → F) =
      fun x ↦ chi x • coreLap d2u x +
        2 • cutoffGradientPair dchi du x + coreLap d2chi x • u x from
    funext fun x ↦ cutoffLaplacian_apply chi dchi d2chi u du d2u x]
  have hall := (hfirst.add (hcross.add hcross)).add hthird
  simpa only [cutoffLaplacianHolderConst, Pi.add_apply, two_nsmul,
    add_assoc, two_mul] using hall

end DifferentialGeometry.Analysis.Schauder

end
