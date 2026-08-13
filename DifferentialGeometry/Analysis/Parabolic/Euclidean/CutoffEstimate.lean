import DifferentialGeometry.Analysis.Parabolic.Euclidean.Cutoff
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicMatrixCutoffCommutatorSupConst
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  (∑ i, ∑ j, 2 * (A i j * Mdchi * Mdu)) +
    ∑ i, ∑ j, A i j * Md2chi * Mu

def parabolicMatrixCutoffCommutatorHolderConst
    (A Ka : n → n → NNReal)
    (Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  ∑ i, ∑ j,
    (2 * ((A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)) +
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j))

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicMatrixCutoffCommutatorSupConst_add
    (A : n → n → NNReal) (Mdchi Md2chi Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicMatrixCutoffCommutatorSupConst A Mdchi
        (Mdu₁ + Mdu₂) Md2chi (Mu₁ + Mu₂) =
      parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu₁ Md2chi Mu₁ +
        parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu₂ Md2chi Mu₂ := by
  unfold parabolicMatrixCutoffCommutatorSupConst
  simp only [mul_add, Finset.sum_add_distrib]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicMatrixCutoffCommutatorSupConst_nnreal_mul
    (d : NNReal) (A : n → n → NNReal)
    (Mdchi Mdu Md2chi Mu : NNReal) :
    parabolicMatrixCutoffCommutatorSupConst A Mdchi
        (d * Mdu) Md2chi (d * Mu) =
      d * parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  unfold parabolicMatrixCutoffCommutatorSupConst
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicMatrixCutoffCommutatorHolderConst_add
    (A Ka : n → n → NNReal) (Kdchi Kd2chi Mdchi Md2chi : NNReal)
    (Kdu₁ Kdu₂ Ku₁ Ku₂ Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicMatrixCutoffCommutatorHolderConst A Ka Kdchi
        (Kdu₁ + Kdu₂) Kd2chi (Ku₁ + Ku₂) Mdchi
        (Mdu₁ + Mdu₂) Md2chi (Mu₁ + Mu₂) =
      parabolicMatrixCutoffCommutatorHolderConst A Ka Kdchi
          Kdu₁ Kd2chi Ku₁ Mdchi Mdu₁ Md2chi Mu₁ +
        parabolicMatrixCutoffCommutatorHolderConst A Ka Kdchi
          Kdu₂ Kd2chi Ku₂ Mdchi Mdu₂ Md2chi Mu₂ := by
  unfold parabolicMatrixCutoffCommutatorHolderConst
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicMatrixCutoffCommutatorHolderConst_nnreal_mul
    (d : NNReal) (A Ka : n → n → NNReal)
    (Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu : NNReal) :
    parabolicMatrixCutoffCommutatorHolderConst A Ka Kdchi
        (d * Kdu) Kd2chi (d * Ku) Mdchi (d * Mdu) Md2chi (d * Mu) =
      d * parabolicMatrixCutoffCommutatorHolderConst A Ka Kdchi
        Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu := by
  unfold parabolicMatrixCutoffCommutatorHolderConst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicMatrixCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicMatrixCutoffCommutator a dchi d2chi u du p‖ ≤
      parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  unfold parabolicMatrixCutoffCommutator
  refine (norm_sum_le _ _).trans ?_
  rw [parabolicMatrixCutoffCommutatorSupConst, NNReal.coe_add]
  push_cast
  calc
    ∑ i, ‖∑ j,
        ((a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
            du p (EuclideanSpace.basisFun n Real j) +
          (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
            du p (EuclideanSpace.basisFun n Real i) +
          (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u p.time p.space)‖ ≤
        ∑ i, ∑ j,
          (2 * ((A i j : Real) * Mdchi * Mdu) +
            (A i j : Real) * Md2chi * Mu) := by
      apply Finset.sum_le_sum
      intro i _hi
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _hj ↦ ?_)
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) ?_
      · have hai : |a i j p| ≤ A i j := by
          simpa only [Real.norm_eq_abs] using haNorm i j p hp
        have hdchii :
            |dchi p (EuclideanSpace.basisFun n Real i)| ≤ Mdchi := by
          rw [← Real.norm_eq_abs]
          exact (dchi p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
            simpa using hdchiNorm p hp)
        have hdchij :
            |dchi p (EuclideanSpace.basisFun n Real j)| ≤ Mdchi := by
          rw [← Real.norm_eq_abs]
          exact (dchi p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
            simpa using hdchiNorm p hp)
        have hdui :
            ‖du p (EuclideanSpace.basisFun n Real i)‖ ≤ Mdu :=
          (du p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
            simpa using hduNorm p hp)
        have hduj :
            ‖du p (EuclideanSpace.basisFun n Real j)‖ ≤ Mdu :=
          (du p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
            simpa using hduNorm p hp)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_mul, abs_mul]
        have hi : |a i j p| *
            |dchi p (EuclideanSpace.basisFun n Real i)| *
              ‖du p (EuclideanSpace.basisFun n Real j)‖ ≤
            (A i j : Real) * Mdchi * Mdu := by
          gcongr
        have hj : |a i j p| *
            |dchi p (EuclideanSpace.basisFun n Real j)| *
              ‖du p (EuclideanSpace.basisFun n Real i)‖ ≤
            (A i j : Real) * Mdchi * Mdu := by
          gcongr
        linarith
      · rw [norm_smul, Real.norm_eq_abs, abs_mul]
        have hai : |a i j p| ≤ A i j := by
          simpa only [Real.norm_eq_abs] using haNorm i j p hp
        have hd2chiij : |d2chi p
            (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)| ≤ Md2chi := by
          rw [← Real.norm_eq_abs]
          calc
            ‖d2chi p (EuclideanSpace.basisFun n Real i)
                (EuclideanSpace.basisFun n Real j)‖ ≤
                ‖d2chi p (EuclideanSpace.basisFun n Real i)‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                  mul_one] using
                (d2chi p (EuclideanSpace.basisFun n Real i)).le_opNorm
                  (EuclideanSpace.basisFun n Real j)
            _ ≤ ‖d2chi p‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                  mul_one] using
                (d2chi p).le_opNorm (EuclideanSpace.basisFun n Real i)
            _ ≤ Md2chi := hd2chiNorm p hp
        exact mul_le_mul
          (mul_le_mul hai hd2chiij (abs_nonneg _) (A i j).coe_nonneg)
          (huNorm p hp) (norm_nonneg _) (by positivity)
    _ = (∑ i, ∑ j, 2 * ((A i j : Real) * Mdchi * Mdu)) +
          ∑ i, ∑ j, (A i j : Real) * Md2chi * Mu := by
      simp only [Finset.sum_add_distrib]

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicMatrixCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicMatrixCutoffCommutator a dchi d2chi u du) ≤
      parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicMatrixCutoffCommutator_le a dchi d2chi u du
    A Mdchi Mdu Md2chi Mu haNorm hdchiNorm hduNorm hd2chiNorm huNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCutoffCommutator_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicMatrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict (parabolicMatrixCutoffCommutator a dchi d2chi u du)) := by
  classical
  let C : n → n → NNReal := fun i j ↦
    (A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)
  let D : n → n → NNReal := fun i j ↦
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j)
  have hcomponent : ∀ i j, HolderWith (C i j + C i j + D i j) alpha
      (fun p : Q ↦
        (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j) +
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i) +
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space) := by
    intro i j
    have hdchii : HolderWith Kdchi alpha
        (fun p : Q ↦ dchi p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdchi
    have hdchij : HolderWith Kdchi alpha
        (fun p : Q ↦ dchi p.1 (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdchi
    have hdui : HolderWith Kdu alpha
        (fun p : Q ↦ du p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdu
    have hduj : HolderWith Kdu alpha
        (fun p : Q ↦ du p.1 (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdu
    have hd2chii : HolderWith Kd2chi alpha
        (fun p : Q ↦ d2chi p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real (Euc n →L[Real] Real)
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hd2chi
    have hd2chiij : HolderWith Kd2chi alpha
        (fun p : Q ↦ d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hd2chii
    have hadchii : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          dchi p.1 (EuclideanSpace.basisFun n Real i)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchii
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real i)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Mdchi := hdchiNorm p.1 p.2))
    have hadchij : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          dchi p.1 (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real j)
              _ ≤ Mdchi := hdchiNorm p.1 p.2))
    have had2chi : HolderWith
        (A i j * Kd2chi + Md2chi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hd2chiij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)
                  (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (d2chi p.1 (EuclideanSpace.basisFun n Real i)).le_opNorm
                    (EuclideanSpace.basisFun n Real j)
              _ ≤ ‖d2chi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (d2chi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Md2chi := hd2chiNorm p.1 p.2))
    have hadchiNorm : ∀ k (p : Q),
        ‖a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real k)‖ ≤
          A i j * Mdchi := by
      intro k p
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p.1 p.2)
        (by rw [← Real.norm_eq_abs]
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real k)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one k,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real k)
              _ ≤ Mdchi := hdchiNorm p.1 p.2)
        (abs_nonneg _) (A i j).coe_nonneg
    have had2chiNorm : ∀ p : Q,
        ‖a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ A i j * Md2chi := by
      intro p
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p.1 p.2)
        (by rw [← Real.norm_eq_abs]
            calc
              ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)
                  (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (d2chi p.1 (EuclideanSpace.basisFun n Real i)).le_opNorm
                    (EuclideanSpace.basisFun n Real j)
              _ ≤ ‖d2chi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (d2chi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Md2chi := hd2chiNorm p.1 p.2)
        (abs_nonneg _) (A i j).coe_nonneg
    have hcrossi : HolderWith (C i j) alpha
        (fun p : Q ↦
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j)) := by
      exact holderWith_smul_of_norm_le hadchii hduj (hadchiNorm i)
        (fun p ↦ (du p.1).le_opNorm _ |>.trans (by
          simpa only
            [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one] using hduNorm p.1 p.2))
    have hcrossj : HolderWith (C i j) alpha
        (fun p : Q ↦
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i)) := by
      exact holderWith_smul_of_norm_le hadchij hdui (hadchiNorm j)
        (fun p ↦ (du p.1).le_opNorm _ |>.trans (by
          simpa only
            [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              mul_one] using hduNorm p.1 p.2))
    have hhessian : HolderWith (D i j) alpha
        (fun p : Q ↦
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space) := by
      exact holderWith_smul_of_norm_le had2chi hu had2chiNorm
        (fun p ↦ huNorm p.1 p.2)
    exact hcrossi.add hcrossj |>.add hhessian
  have hinner : ∀ i, HolderWith (∑ j, (C i j + C i j + D i j)) alpha
      (fun p : Q ↦ ∑ j,
        ((a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j) +
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i) +
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space)) := by
    intro i
    exact holderWith_finset_sum Finset.univ (fun j _hj ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, (C i j + C i j + D i j))
    (f := fun i (p : Q) ↦ ∑ j,
      ((a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
          du p.1 (EuclideanSpace.basisFun n Real j) +
        (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
          du p.1 (EuclideanSpace.basisFun n Real i) +
        (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) •
            u p.1.time p.1.space))
    (fun i _hi ↦ hinner i)
  convert hall using 1
  · simp only [parabolicMatrixCutoffCommutatorHolderConst, C, D, two_mul,
      add_assoc]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCutoffCommutator_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha ((Q ∩ U).restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0)
    (hd2chiZero : ∀ p, p ∈ Q → p ∉ U → d2chi p = 0) :
    HolderWith (parabolicMatrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict (parabolicMatrixCutoffCommutator a dchi d2chi u du)) := by
  classical
  let C : n → n → NNReal := fun i j ↦
    (A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)
  let D : n → n → NNReal := fun i j ↦
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j)
  have hcomponent : ∀ i j, HolderWith (C i j + C i j + D i j) alpha
      (Q.restrict (fun p ↦
        (a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
            du p (EuclideanSpace.basisFun n Real j) +
          (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
            du p (EuclideanSpace.basisFun n Real i) +
          (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u p.time p.space)) := by
    intro i j
    have hdchii : HolderWith Kdchi alpha
        (Q.restrict (fun p ↦ dchi p (EuclideanSpace.basisFun n Real i))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real Real
            (EuclideanSpace.basisFun n Real i))
          (norm_apply_euclideanBasis_le_one i) hdchi
    have hdchij : HolderWith Kdchi alpha
        (Q.restrict (fun p ↦ dchi p (EuclideanSpace.basisFun n Real j))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real Real
            (EuclideanSpace.basisFun n Real j))
          (norm_apply_euclideanBasis_le_one j) hdchi
    have hdui : HolderWith Kdu alpha
        ((Q ∩ U).restrict
          (fun p ↦ du p (EuclideanSpace.basisFun n Real i))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real F
            (EuclideanSpace.basisFun n Real i))
          (norm_apply_euclideanBasis_le_one i) hdu
    have hduj : HolderWith Kdu alpha
        ((Q ∩ U).restrict
          (fun p ↦ du p (EuclideanSpace.basisFun n Real j))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real F
            (EuclideanSpace.basisFun n Real j))
          (norm_apply_euclideanBasis_le_one j) hdu
    have hd2chii : HolderWith Kd2chi alpha
        (Q.restrict
          (fun p ↦ d2chi p (EuclideanSpace.basisFun n Real i))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real (Euc n →L[Real] Real)
            (EuclideanSpace.basisFun n Real i))
          (norm_apply_euclideanBasis_le_one i) hd2chi
    have hd2chiij : HolderWith Kd2chi alpha
        (Q.restrict (fun p ↦ d2chi p (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j))) := by
      simpa only [Set.restrict_apply] using
        holderWith_comp_continuousLinearMap_of_norm_le_one
          (ContinuousLinearMap.apply Real Real
            (EuclideanSpace.basisFun n Real j))
          (norm_apply_euclideanBasis_le_one j) hd2chii
    have hadchii : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (Q.restrict (fun p ↦ a i j p *
          dchi p (EuclideanSpace.basisFun n Real i))) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchii
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            exact (dchi p.1).le_opNorm _ |>.trans (by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                  mul_one] using hdchiNorm p.1 p.2)))
    have hadchij : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (Q.restrict (fun p ↦ a i j p *
          dchi p (EuclideanSpace.basisFun n Real j))) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            exact (dchi p.1).le_opNorm _ |>.trans (by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                  mul_one] using hdchiNorm p.1 p.2)))
    have had2chi : HolderWith
        (A i j * Kd2chi + Md2chi * Ka i j) alpha
        (Q.restrict (fun p ↦ a i j p *
          d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j))) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hd2chiij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)
                  (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (d2chi p.1 (EuclideanSpace.basisFun n Real i)).le_opNorm
                    (EuclideanSpace.basisFun n Real j)
              _ ≤ ‖d2chi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (d2chi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Md2chi := hd2chiNorm p.1 p.2))
    have hadchiNorm : ∀ k p, p ∈ Q → p ∈ U →
        ‖a i j p * dchi p (EuclideanSpace.basisFun n Real k)‖ ≤
          A i j * Mdchi := by
      intro k p hp _hpU
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p hp)
        ((dchi p).le_opNorm _ |>.trans (by
          simpa only
            [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one k,
              mul_one] using hdchiNorm p hp))
        (abs_nonneg _) (A i j).coe_nonneg
    have had2chiNorm : ∀ p, p ∈ Q → p ∈ U →
        ‖a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ A i j * Md2chi := by
      intro p hp _hpU
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p hp)
        (by
          calc
            ‖d2chi p (EuclideanSpace.basisFun n Real i)
                (EuclideanSpace.basisFun n Real j)‖ ≤
                ‖d2chi p (EuclideanSpace.basisFun n Real i)‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                  mul_one] using
                (d2chi p (EuclideanSpace.basisFun n Real i)).le_opNorm
                  (EuclideanSpace.basisFun n Real j)
            _ ≤ ‖d2chi p‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                  mul_one] using
                (d2chi p).le_opNorm (EuclideanSpace.basisFun n Real i)
            _ ≤ Md2chi := hd2chiNorm p hp)
        (abs_nonneg _) (A i j).coe_nonneg
    have hduNormEval : ∀ k p, p ∈ Q → p ∈ U →
        ‖du p (EuclideanSpace.basisFun n Real k)‖ ≤ Mdu := by
      intro k p hp hpU
      exact (du p).le_opNorm _ |>.trans (by
        simpa only
          [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one k,
            mul_one] using hduNorm p hp hpU)
    have hadchiZero : ∀ k p, p ∈ Q → p ∉ U →
        a i j p * dchi p (EuclideanSpace.basisFun n Real k) = 0 := by
      intro k p hp hpU
      rw [hdchiZero p hp hpU, ContinuousLinearMap.zero_apply, mul_zero]
    have had2chiZero : ∀ p, p ∈ Q → p ∉ U →
        a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) = 0 := by
      intro p hp hpU
      rw [hd2chiZero p hp hpU, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.zero_apply, mul_zero]
    have hcrossi : HolderWith (C i j) alpha
        (Q.restrict (fun p ↦
          (a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
            du p (EuclideanSpace.basisFun n Real j))) := by
      exact holderWith_smul_of_eq_zero_outside
        (fun p ↦ a i j p * dchi p (EuclideanSpace.basisFun n Real i))
        (fun p ↦ du p (EuclideanSpace.basisFun n Real j))
        hadchii hduj (hadchiNorm i) (hduNormEval j) (hadchiZero i)
    have hcrossj : HolderWith (C i j) alpha
        (Q.restrict (fun p ↦
          (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
            du p (EuclideanSpace.basisFun n Real i))) := by
      exact holderWith_smul_of_eq_zero_outside
        (fun p ↦ a i j p * dchi p (EuclideanSpace.basisFun n Real j))
        (fun p ↦ du p (EuclideanSpace.basisFun n Real i))
        hadchij hdui (hadchiNorm j) (hduNormEval i) (hadchiZero j)
    have hhessian : HolderWith (D i j) alpha
        (Q.restrict (fun p ↦
          (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u p.time p.space)) := by
      exact holderWith_smul_of_eq_zero_outside
        (fun p ↦ a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j))
        (fun p ↦ u p.time p.space) had2chi hu had2chiNorm huNorm had2chiZero
    exact hcrossi.add hcrossj |>.add hhessian
  have hinner : ∀ i, HolderWith (∑ j, (C i j + C i j + D i j)) alpha
      (Q.restrict (fun p ↦ ∑ j,
        ((a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
            du p (EuclideanSpace.basisFun n Real j) +
          (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
            du p (EuclideanSpace.basisFun n Real i) +
          (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u p.time p.space))) := by
    intro i
    exact holderWith_finset_sum Finset.univ (fun j _hj ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, (C i j + C i j + D i j))
    (f := fun i (p : Q) ↦ ∑ j,
      ((a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
          du p.1 (EuclideanSpace.basisFun n Real j) +
        (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
          du p.1 (EuclideanSpace.basisFun n Real i) +
        (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) • u p.1.time p.1.space))
    (fun i _hi ↦ hinner i)
  convert hall using 1
  · simp only [parabolicMatrixCutoffCommutatorHolderConst, C, D, two_mul,
      add_assoc]

def parabolicCutoffOperatorCommutatorSupConst
    (A : n → n → NNReal) (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal) :
    NNReal :=
  MdtimeChi * Mu +
    parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu

def parabolicCutoffOperatorCommutatorHolderConst
    (A Ka : n → n → NNReal)
    (KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu :
      NNReal) : NNReal :=
  MdtimeChi * Ku + Mu * KdtimeChi +
    parabolicMatrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicCutoffOperatorCommutatorSupConst_add
    (A : n → n → NNReal) (MdtimeChi Mdchi Md2chi : NNReal)
    (Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicCutoffOperatorCommutatorSupConst A MdtimeChi Mdchi
        (Mdu₁ + Mdu₂) Md2chi (Mu₁ + Mu₂) =
      parabolicCutoffOperatorCommutatorSupConst A MdtimeChi Mdchi
          Mdu₁ Md2chi Mu₁ +
        parabolicCutoffOperatorCommutatorSupConst A MdtimeChi Mdchi
          Mdu₂ Md2chi Mu₂ := by
  unfold parabolicCutoffOperatorCommutatorSupConst
  rw [mul_add, parabolicMatrixCutoffCommutatorSupConst_add]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicCutoffOperatorCommutatorSupConst_nnreal_mul
    (d : NNReal) (A : n → n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal) :
    parabolicCutoffOperatorCommutatorSupConst A MdtimeChi Mdchi
        (d * Mdu) Md2chi (d * Mu) =
      d * parabolicCutoffOperatorCommutatorSupConst A MdtimeChi Mdchi
        Mdu Md2chi Mu := by
  unfold parabolicCutoffOperatorCommutatorSupConst
  rw [parabolicMatrixCutoffCommutatorSupConst_nnreal_mul]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicCutoffOperatorCommutatorHolderConst_add
    (A Ka : n → n → NNReal)
    (KdtimeChi Kdchi Kd2chi MdtimeChi Mdchi Md2chi : NNReal)
    (Kdu₁ Kdu₂ Ku₁ Ku₂ Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicCutoffOperatorCommutatorHolderConst A Ka KdtimeChi Kdchi
        (Kdu₁ + Kdu₂) Kd2chi (Ku₁ + Ku₂) MdtimeChi Mdchi
        (Mdu₁ + Mdu₂) Md2chi (Mu₁ + Mu₂) =
      parabolicCutoffOperatorCommutatorHolderConst A Ka KdtimeChi Kdchi
          Kdu₁ Kd2chi Ku₁ MdtimeChi Mdchi Mdu₁ Md2chi Mu₁ +
        parabolicCutoffOperatorCommutatorHolderConst A Ka KdtimeChi Kdchi
          Kdu₂ Kd2chi Ku₂ MdtimeChi Mdchi Mdu₂ Md2chi Mu₂ := by
  unfold parabolicCutoffOperatorCommutatorHolderConst
  rw [mul_add, add_mul, parabolicMatrixCutoffCommutatorHolderConst_add]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicCutoffOperatorCommutatorHolderConst_nnreal_mul
    (d : NNReal) (A Ka : n → n → NNReal)
    (KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu : NNReal) :
    parabolicCutoffOperatorCommutatorHolderConst A Ka KdtimeChi Kdchi
        (d * Kdu) Kd2chi (d * Ku) MdtimeChi Mdchi (d * Mdu) Md2chi (d * Mu) =
      d * parabolicCutoffOperatorCommutatorHolderConst A Ka KdtimeChi Kdchi
        Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu := by
  unfold parabolicCutoffOperatorCommutatorHolderConst
  rw [parabolicMatrixCutoffCommutatorHolderConst_nnreal_mul]
  ring

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicCutoffOperatorCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicCutoffOperatorCommutator
      a dtimeChi dchi d2chi u du p‖ ≤
        parabolicCutoffOperatorCommutatorSupConst
          A MdtimeChi Mdchi Mdu Md2chi Mu := by
  unfold parabolicCutoffOperatorCommutator
  rw [parabolicCutoffOperatorCommutatorSupConst, NNReal.coe_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by
      simpa only [Real.norm_eq_abs] using hdtimeChiNorm p hp)
      (huNorm p hp) (norm_nonneg _) MdtimeChi.coe_nonneg
  · exact norm_parabolicMatrixCutoffCommutator_le a dchi d2chi u du
      A Mdchi Mdu Md2chi Mu haNorm hdchiNorm hduNorm hd2chiNorm
        huNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicCutoffOperatorCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du) ≤
      parabolicCutoffOperatorCommutatorSupConst
        A MdtimeChi Mdchi Mdu Md2chi Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicCutoffOperatorCommutator_le
    a dtimeChi dchi d2chi u du A MdtimeChi Mdchi Mdu Md2chi Mu
      haNorm hdtimeChiNorm hdchiNorm hduNorm hd2chiNorm huNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffOperatorCommutator_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha KdtimeChi Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicCutoffOperatorCommutatorHolderConst A Ka
      KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du)) := by
  have htime : HolderWith (MdtimeChi * Ku + Mu * KdtimeChi) alpha
      (fun p : Q ↦ dtimeChi p.1 • u p.1.time p.1.space) :=
    holderWith_smul_of_norm_le hdtimeChi hu
      (fun p ↦ hdtimeChiNorm p.1 p.2) (fun p ↦ huNorm p.1 p.2)
  have hmatrix := parabolicMatrixCutoffCommutator_holderWith_restrict
    a dchi d2chi u du A Ka Mdchi Mdu Md2chi Mu ha hdchi hdu hd2chi hu
      haNorm hdchiNorm hduNorm hd2chiNorm huNorm
  have hmatrixNeg : HolderWith
      (parabolicMatrixCutoffCommutatorHolderConst A Ka
        Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (fun p : Q ↦ -parabolicMatrixCutoffCommutator
        a dchi d2chi u du p.1) := by
    intro p q
    simpa only [edist_neg_neg] using hmatrix p q
  have hsum := htime.add hmatrixNeg
  change HolderWith _ alpha (fun p : Q ↦
    dtimeChi p.1 • u p.1.time p.1.space +
      -parabolicMatrixCutoffCommutator a dchi d2chi u du p.1) at hsum
  unfold parabolicCutoffOperatorCommutatorHolderConst
    parabolicCutoffOperatorCommutator
  change HolderWith _ alpha (fun p : Q ↦
    dtimeChi p.1 • u p.1.time p.1.space -
      parabolicMatrixCutoffCommutator a dchi d2chi u du p.1)
  simpa only [sub_eq_add_neg, add_assoc] using hsum

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicCutoffOperatorCommutator_le_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeChiZero : ∀ p, p ∈ Q → p ∉ U → dtimeChi p = 0)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0)
    (hd2chiZero : ∀ p, p ∈ Q → p ∉ U → d2chi p = 0)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicCutoffOperatorCommutator
      a dtimeChi dchi d2chi u du p‖ ≤
        parabolicCutoffOperatorCommutatorSupConst
          A MdtimeChi Mdchi Mdu Md2chi Mu := by
  by_cases hpU : p ∈ U
  · exact norm_parabolicCutoffOperatorCommutator_le
      (Q := Q ∩ U) a dtimeChi dchi d2chi u du
      A MdtimeChi Mdchi Mdu Md2chi Mu
      (fun i j q hq ↦ haNorm i j q hq.1)
      (fun q hq ↦ hdtimeChiNorm q hq.1)
      (fun q hq ↦ hdchiNorm q hq.1)
      (fun q hq ↦ hduNorm q hq.1 hq.2)
      (fun q hq ↦ hd2chiNorm q hq.1)
      (fun q hq ↦ huNorm q hq.1 hq.2) p ⟨hp, hpU⟩
  · unfold parabolicCutoffOperatorCommutator
    rw [hdtimeChiZero p hp hpU, zero_smul]
    have hmatrix : parabolicMatrixCutoffCommutator a dchi d2chi u du p = 0 := by
      unfold parabolicMatrixCutoffCommutator
      rw [hdchiZero p hp hpU, hd2chiZero p hp hpU]
      simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_smul,
        zero_add, Finset.sum_const_zero]
    rw [hmatrix, sub_zero, norm_zero]
    positivity

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffOperatorCommutator_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha KdtimeChi Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha ((Q ∩ U).restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeChiZero : ∀ p, p ∈ Q → p ∉ U → dtimeChi p = 0)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0)
    (hd2chiZero : ∀ p, p ∈ Q → p ∉ U → d2chi p = 0) :
    HolderWith (parabolicCutoffOperatorCommutatorHolderConst A Ka
      KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du)) := by
  have htime : HolderWith (MdtimeChi * Ku + Mu * KdtimeChi) alpha
      (Q.restrict (fun p ↦ dtimeChi p • u p.time p.space)) :=
    holderWith_smul_of_eq_zero_outside dtimeChi
      (fun p ↦ u p.time p.space) hdtimeChi hu
        (fun p hp _hpU ↦ hdtimeChiNorm p hp) huNorm hdtimeChiZero
  have hmatrix :=
    parabolicMatrixCutoffCommutator_holderWith_restrict_of_eq_zero_outside
      a dchi d2chi u du A Ka Mdchi Mdu Md2chi Mu ha hdchi hdu hd2chi hu
      haNorm hdchiNorm hduNorm hd2chiNorm huNorm hdchiZero hd2chiZero
  have hmatrixNeg : HolderWith
      (parabolicMatrixCutoffCommutatorHolderConst A Ka
        Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict (fun p ↦ -parabolicMatrixCutoffCommutator
        a dchi d2chi u du p)) := by
    intro p q
    simpa only [Set.restrict_apply, edist_neg_neg] using hmatrix p q
  have hsum := htime.add hmatrixNeg
  change HolderWith _ alpha (Q.restrict (fun p ↦
    dtimeChi p • u p.time p.space +
      -parabolicMatrixCutoffCommutator a dchi d2chi u du p)) at hsum
  unfold parabolicCutoffOperatorCommutatorHolderConst
    parabolicCutoffOperatorCommutator
  change HolderWith _ alpha (Q.restrict (fun p ↦
    dtimeChi p • u p.time p.space -
      parabolicMatrixCutoffCommutator a dchi d2chi u du p))
  simpa only [sub_eq_add_neg, add_assoc] using hsum

def parabolicDriftCutoffCommutatorSupConst
    (Bb : n → NNReal) (Mdchi Mu : NNReal) : NNReal :=
  ∑ i, Bb i * Mdchi * Mu

def parabolicDriftCutoffCommutatorHolderConst
    (Kb Bb : n → NNReal) (Kdchi Ku Mdchi Mu : NNReal) : NNReal :=
  ∑ i, ((Bb i * Mdchi) * Ku +
    Mu * (Bb i * Kdchi + Mdchi * Kb i))

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicDriftCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (Bb : n → NNReal) (Mdchi Mu : NNReal)
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicDriftCutoffCommutator b dchi u p‖ ≤
      parabolicDriftCutoffCommutatorSupConst Bb Mdchi Mu := by
  unfold parabolicDriftCutoffCommutator
  refine (norm_sum_le _ _).trans ?_
  rw [parabolicDriftCutoffCommutatorSupConst]
  push_cast
  apply Finset.sum_le_sum
  intro i _hi
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hdchii : |dchi p (EuclideanSpace.basisFun n Real i)| ≤ Mdchi := by
    rw [← Real.norm_eq_abs]
    calc
      ‖dchi p (EuclideanSpace.basisFun n Real i)‖ ≤ ‖dchi p‖ := by
        simpa only
          [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
            mul_one] using
          (dchi p).le_opNorm (EuclideanSpace.basisFun n Real i)
      _ ≤ Mdchi := hdchiNorm p hp
  exact mul_le_mul
    (mul_le_mul (by
      simpa only [Real.norm_eq_abs] using hbNorm i p hp) hdchii
      (abs_nonneg _) (Bb i).coe_nonneg)
    (huNorm p hp) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicDriftCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (Bb : n → NNReal) (Mdchi Mu : NNReal)
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicDriftCutoffCommutator b dchi u) ≤
      parabolicDriftCutoffCommutatorSupConst Bb Mdchi Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicDriftCutoffCommutator_le
    b dchi u Bb Mdchi Mu hbNorm hdchiNorm huNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftCutoffCommutator_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))} {alpha Kdchi Ku : NNReal}
    (b : n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (Kb Bb : n → NNReal) (Mdchi Mu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicDriftCutoffCommutatorHolderConst
      Kb Bb Kdchi Ku Mdchi Mu) alpha
      (Q.restrict (parabolicDriftCutoffCommutator b dchi u)) := by
  have hcomponent : ∀ i, HolderWith
      ((Bb i * Mdchi) * Ku + Mu * (Bb i * Kdchi + Mdchi * Kb i)) alpha
      (fun p : Q ↦
        (b i p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
          u p.1.time p.1.space) := by
    intro i
    have hdchii : HolderWith Kdchi alpha
        (fun p : Q ↦ dchi p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdchi
    have hbdchi : HolderWith (Bb i * Kdchi + Mdchi * Kb i) alpha
        (fun p : Q ↦ b i p.1 *
          dchi p.1 (EuclideanSpace.basisFun n Real i)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (hb i) hdchii
          (fun p ↦ hbNorm i p.1 p.2)
          (fun p ↦ (by
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real i)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Mdchi := hdchiNorm p.1 p.2))
    have hbdchiNorm : ∀ p : Q,
        ‖b i p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)‖ ≤
          Bb i * Mdchi := by
      intro p
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using hbNorm i p.1 p.2)
        (by rw [← Real.norm_eq_abs]
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real i)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Mdchi := hdchiNorm p.1 p.2)
        (abs_nonneg _) (Bb i).coe_nonneg
    exact holderWith_smul_of_norm_le hbdchi hu hbdchiNorm
      (fun p ↦ huNorm p.1 p.2)
  have hsum := holderWith_finset_sum Finset.univ
    (K := fun i ↦ (Bb i * Mdchi) * Ku +
      Mu * (Bb i * Kdchi + Mdchi * Kb i))
    (f := fun i (p : Q) ↦
      (b i p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
        u p.1.time p.1.space)
    (fun i _hi ↦ hcomponent i)
  simpa only [parabolicDriftCutoffCommutatorHolderConst,
    parabolicDriftCutoffCommutator, Set.restrict_apply] using hsum

def parabolicNondivergenceCutoffCommutatorSupConst
    (A : n → n → NNReal) (Bb : n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorSupConst
      A MdtimeChi Mdchi Mdu Md2chi Mu +
    parabolicDriftCutoffCommutatorSupConst Bb Mdchi Mu

def parabolicNondivergenceCutoffCommutatorHolderConst
    (A Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu :
      NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorHolderConst A Ka
      KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu +
    parabolicDriftCutoffCommutatorHolderConst Kb Bb Kdchi Ku Mdchi Mu

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicNondivergenceCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Bb : n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicNondivergenceCutoffCommutator
        a b dtimeChi dchi d2chi u du) ≤
      parabolicNondivergenceCutoffCommutatorSupConst
        A Bb MdtimeChi Mdchi Mdu Md2chi Mu := by
  unfold parabolicNondivergenceCutoffCommutator
  exact (eSupNormOn_sub_le Q _ _).trans (add_le_add
    (eSupNormOn_parabolicCutoffOperatorCommutator_le
      a dtimeChi dchi d2chi u du A MdtimeChi Mdchi Mdu Md2chi Mu
        haNorm hdtimeChiNorm hdchiNorm hduNorm hd2chiNorm huNorm)
    (eSupNormOn_parabolicDriftCutoffCommutator_le
      b dchi u Bb Mdchi Mu hbNorm hdchiNorm huNorm))

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceCutoffCommutator_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha KdtimeChi Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (MdtimeChi Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicNondivergenceCutoffCommutatorHolderConst A Ka Kb Bb
      KdtimeChi Kdchi Kdu Kd2chi Ku MdtimeChi Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict (parabolicNondivergenceCutoffCommutator
        a b dtimeChi dchi d2chi u du)) := by
  have hop := parabolicCutoffOperatorCommutator_holderWith_restrict
    a dtimeChi dchi d2chi u du A Ka MdtimeChi Mdchi Mdu Md2chi Mu
      ha hdtimeChi hdchi hdu hd2chi hu haNorm hdtimeChiNorm hdchiNorm
        hduNorm hd2chiNorm huNorm
  have hdrift := parabolicDriftCutoffCommutator_holderWith_restrict
    b dchi u Kb Bb Mdchi Mu hb hdchi hu hbNorm hdchiNorm huNorm
  have hdriftNeg : HolderWith
      (parabolicDriftCutoffCommutatorHolderConst
        Kb Bb Kdchi Ku Mdchi Mu) alpha
      (fun p : Q ↦ -parabolicDriftCutoffCommutator b dchi u p.1) := by
    intro p q
    simpa only [edist_neg_neg] using hdrift p q
  have hsum := hop.add hdriftNeg
  change HolderWith _ alpha (fun p : Q ↦
    parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du p.1 +
      -parabolicDriftCutoffCommutator b dchi u p.1) at hsum
  unfold parabolicNondivergenceCutoffCommutatorHolderConst
    parabolicNondivergenceCutoffCommutator
  change HolderWith _ alpha (fun p : Q ↦
    parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du p.1 -
      parabolicDriftCutoffCommutator b dchi u p.1)
  simpa only [sub_eq_add_neg] using hsum

def parabolicCutoffSourceSupConst
    (Mchi Bsource Bcomm : NNReal) : NNReal :=
  Mchi * Bsource + Bcomm

def parabolicCutoffSourceHolderConst
    (Kchi Ksource Kcomm Mchi Bsource : NNReal) : NNReal :=
  Mchi * Ksource + Bsource * Kchi + Kcomm

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem norm_parabolicCutoffSource_le
    {Q : Set (ParabolicPoint (Euc n))}
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource Bcomm : NNReal)
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → ‖source p‖ ≤ Bsource)
    (hcommNorm : ∀ p, p ∈ Q → ‖comm p‖ ≤ Bcomm)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖chi p • source p + comm p‖ ≤
      parabolicCutoffSourceSupConst Mchi Bsource Bcomm := by
  rw [parabolicCutoffSourceSupConst, NNReal.coe_add, NNReal.coe_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_smul _ _).trans_le (mul_le_mul
      (hchiNorm p hp) (hsourceNorm p hp) (norm_nonneg _) Mchi.coe_nonneg))
    (hcommNorm p hp))

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicCutoffSource_le
    {Q : Set (ParabolicPoint (Euc n))}
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource Bcomm : NNReal)
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → ‖source p‖ ≤ Bsource)
    (hcommNorm : ∀ p, p ∈ Q → ‖comm p‖ ≤ Bcomm) :
    eSupNormOn Q (fun p ↦ chi p • source p + comm p) ≤
      parabolicCutoffSourceSupConst Mchi Bsource Bcomm := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicCutoffSource_le chi source comm
    Mchi Bsource Bcomm hchiNorm hsourceNorm hcommNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffSource_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Ksource Kcomm : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource : NNReal)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hsource : HolderWith Ksource alpha (Q.restrict source))
    (hcomm : HolderWith Kcomm alpha (Q.restrict comm))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → ‖source p‖ ≤ Bsource) :
    HolderWith
      (parabolicCutoffSourceHolderConst Kchi Ksource Kcomm Mchi Bsource)
      alpha (Q.restrict (fun p ↦ chi p • source p + comm p)) := by
  have hproduct : HolderWith (Mchi * Ksource + Bsource * Kchi) alpha
      (fun p : Q ↦ chi p.1 • source p.1) :=
    holderWith_smul_of_norm_le hchi hsource
      (fun p ↦ hchiNorm p.1 p.2) (fun p ↦ hsourceNorm p.1 p.2)
  have hsum := hproduct.add hcomm
  unfold parabolicCutoffSourceHolderConst
  simpa only [Set.restrict_apply] using hsum

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffSource_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Ksource Kcomm : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource : NNReal)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hsource : HolderWith Ksource alpha ((Q ∩ U).restrict source))
    (hcomm : HolderWith Kcomm alpha (Q.restrict comm))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → p ∈ U → ‖source p‖ ≤ Bsource)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0) :
    HolderWith
      (parabolicCutoffSourceHolderConst Kchi Ksource Kcomm Mchi Bsource)
      alpha (Q.restrict (fun p ↦ chi p • source p + comm p)) := by
  have hproduct := holderWith_smul_of_eq_zero_outside
    chi source hchi hsource hchiNorm hsourceNorm hchiZero
  have hsum := hproduct.add hcomm
  unfold parabolicCutoffSourceHolderConst
  simpa only [Set.restrict_apply] using hsum

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem norm_parabolicCutoffSource_le_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource Bcomm : NNReal)
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → p ∈ U → ‖source p‖ ≤ Bsource)
    (hcommNorm : ∀ p, p ∈ Q → ‖comm p‖ ≤ Bcomm)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0) :
    ∀ p, p ∈ Q →
      ‖chi p • source p + comm p‖ ≤
        parabolicCutoffSourceSupConst Mchi Bsource Bcomm := by
  have hproduct := norm_smul_le_of_eq_zero_outside
    chi source hchiNorm hsourceNorm hchiZero
  intro p hp
  rw [parabolicCutoffSourceSupConst, NNReal.coe_add, NNReal.coe_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (hproduct p hp) (hcommNorm p hp))

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicCutoffSource_eqOn_le_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    (g : ParabolicPoint (Euc n) → F)
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource Bcomm : NNReal)
    (hg : Set.EqOn g (fun p ↦ chi p • source p + comm p) Q)
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → p ∈ U → ‖source p‖ ≤ Bsource)
    (hcommNorm : ∀ p, p ∈ Q → ‖comm p‖ ≤ Bcomm)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0) :
    eSupNormOn Q g ≤
      parabolicCutoffSourceSupConst Mchi Bsource Bcomm := by
  rw [eSupNormOn_congr hg, eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicCutoffSource_le_of_eq_zero_outside
    chi source comm Mchi Bsource Bcomm hchiNorm hsourceNorm
      hcommNorm hchiZero p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffSource_eqOn_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Ksource Kcomm : NNReal}
    (g : ParabolicPoint (Euc n) → F)
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource : NNReal)
    (hg : Set.EqOn g (fun p ↦ chi p • source p + comm p) Q)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hsource : HolderWith Ksource alpha ((Q ∩ U).restrict source))
    (hcomm : HolderWith Kcomm alpha (Q.restrict comm))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → p ∈ U → ‖source p‖ ≤ Bsource)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0) :
    HolderWith
      (parabolicCutoffSourceHolderConst Kchi Ksource Kcomm Mchi Bsource)
      alpha (Q.restrict g) := by
  have heq : Q.restrict g =
      Q.restrict (fun p ↦ chi p • source p + comm p) := by
    funext p
    exact hg p.2
  rw [heq]
  exact parabolicCutoffSource_holderWith_restrict_of_eq_zero_outside
    chi source comm Mchi Bsource hchi hsource hcomm hchiNorm
      hsourceNorm hchiZero

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicCutoffSource_eqOn_le
    {Q : Set (ParabolicPoint (Euc n))}
    (g : ParabolicPoint (Euc n) → F)
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource Bcomm : NNReal)
    (hg : Set.EqOn g (fun p ↦ chi p • source p + comm p) Q)
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → ‖source p‖ ≤ Bsource)
    (hcommNorm : ∀ p, p ∈ Q → ‖comm p‖ ≤ Bcomm) :
    eSupNormOn Q g ≤
      parabolicCutoffSourceSupConst Mchi Bsource Bcomm := by
  rw [eSupNormOn_congr hg]
  exact eSupNormOn_parabolicCutoffSource_le chi source comm
    Mchi Bsource Bcomm hchiNorm hsourceNorm hcommNorm

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffSource_eqOn_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Ksource Kcomm : NNReal}
    (g : ParabolicPoint (Euc n) → F)
    (chi : ParabolicPoint (Euc n) → Real)
    (source comm : ParabolicPoint (Euc n) → F)
    (Mchi Bsource : NNReal)
    (hg : Set.EqOn g (fun p ↦ chi p • source p + comm p) Q)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hsource : HolderWith Ksource alpha (Q.restrict source))
    (hcomm : HolderWith Kcomm alpha (Q.restrict comm))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hsourceNorm : ∀ p, p ∈ Q → ‖source p‖ ≤ Bsource) :
    HolderWith
      (parabolicCutoffSourceHolderConst Kchi Ksource Kcomm Mchi Bsource)
      alpha (Q.restrict g) := by
  have heq : Q.restrict g =
      Q.restrict (fun p ↦ chi p • source p + comm p) := by
    funext p
    exact hg p.2
  rw [heq]
  exact parabolicCutoffSource_holderWith_restrict chi source comm
    Mchi Bsource hchi hsource hcomm hchiNorm hsourceNorm

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
