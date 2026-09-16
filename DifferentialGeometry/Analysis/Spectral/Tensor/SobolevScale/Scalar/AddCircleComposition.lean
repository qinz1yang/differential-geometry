import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacianNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.ScalarComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ProductDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open scoped Manifold ContDiff BigOperators

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private theorem scalar0_ccOperatorFieldComp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
    TensorRSField.scalar0 (ccOperatorFieldComp g 0 0 0 S T).toSection x =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  let f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  rw [← hS, operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc,
    scalar0_smul_cc, scalar0_scalarCc]

private theorem scalar0_sum {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (s : Finset ι) (u : ι → SmoothCcTensor g 0 0) :
    TensorRSField.scalar0 (∑ i ∈ s, u i).toSection =
      ∑ i ∈ s, TensorRSField.scalar0 (u i).toSection := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, SmoothCcTensor.toSection_zero,
      TensorRSField.scalar0_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, SmoothCcTensor.toSection_add,
      TensorRSField.scalar0_add, ih]

open scoped Classical in
theorem parameterDerivativeCcTensor_scalarCompOn
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    parameterDerivativeCcTensor g (SmoothCcTensor.scalarCompOn u F hF hu) =
      ∑ i, ccOperatorFieldComp g 0 0 0
        (SmoothCcTensor.scalarCompOn u
          (fun z => fderiv ℝ F z (Pi.single i 1))
          ((hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const) hu)
        (parameterDerivativeCcTensor g (u i)) := by
  classical
  apply SmoothCcTensor.ext_scalar0
  funext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [scalar0_parameterDerivativeCcTensor_coe, SmoothCcTensor.scalar0_scalarCompOn,
    scalar0_sum]
  simp only [Finset.sum_apply, scalar0_ccOperatorFieldComp,
    SmoothCcTensor.scalar0_scalarCompOn, scalar0_parameterDerivativeCcTensor_coe]
  let v : ℝ → ι → ℝ := fun t i => TensorRSField.scalar0 (u i).toSection (t : AddCircle (1 : ℝ))
  have hv (i : ι) : DifferentiableAt ℝ (fun t => v t i) x :=
    (((TensorRSField.scalar0_smooth (u i).toSection).comp contMDiff_coe).contDiff).differentiable (by simp) x
  have hFx : DifferentiableAt ℝ F (v x) :=
    (hF.contDiffAt (hU.mem_nhds (hu (x : AddCircle (1 : ℝ))))).differentiableAt (by simp)
  have hchain := hFx.hasFDerivAt.comp_hasDerivAt x
    ((differentiableAt_pi.mpr hv).hasDerivAt)
  change deriv (F ∘ v) x = _
  rw [hchain.deriv, deriv_pi hv, pi_eq_sum_univ' (fun i => deriv (fun t => v t i) x), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, smul_eq_mul]
  exact mul_comm _ _

theorem parameterDerivativeCcTensor_sub
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) :
    parameterDerivativeCcTensor g (S - T) =
      parameterDerivativeCcTensor g S - parameterDerivativeCcTensor g T := by
  simp only [parameterDerivativeCcTensor, covGrad_sub, operatorFieldApplication_sub_right]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem norm_parameterDerivativeCcTensor_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 (n : ℝ) (parameterDerivativeCcTensor g S)‖ ≤
        C * ‖ccTensorToHs g 0 ((n : ℝ) + 1) S‖ := by
  refine ⟨‖parameterDerivativeHs g n‖, norm_nonneg _, ?_⟩
  intro S
  have h := (parameterDerivativeHs g n).le_opNorm
    (ccTensorToHs g 0 ((n : ℝ) + 1) S)
  rw [parameterDerivativeHs_apply_ccTensorToHs] at h
  exact h

private theorem scalar0_sub_norm_le_sum_hs {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {σ : ℝ} (hσ : 1 ≤ σ)
    (u v : ι → SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
    ‖(fun i => TensorRSField.scalar0 (u i).toSection x) -
      (fun i => TensorRSField.scalar0 (v i).toSection x)‖ ≤
      ‖scalarH1ToContinuous g‖ * ∑ i, ‖ccTensorToHs g 0 σ (u i - v i)‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have hh := ((ContinuousMap.norm_coe_le_norm
    (scalarH1ToContinuous g (ccTensorToHs g 0 1 (u i - v i))) x).trans
      ((scalarH1ToContinuous g).le_opNorm (ccTensorToHs g 0 1 (u i - v i))))
  rw [scalarH1ToContinuous_apply_ccTensorToHs, SmoothCcTensor.toSection_sub,
    TensorRSField.scalar0_sub] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    ((ccToHs_norm_mono g 0 hσ _).trans
      (Finset.single_le_sum (fun j _ => norm_nonneg (ccTensorToHs g 0 σ (u j - v j)))
        (Finset.mem_univ i))) (norm_nonneg _))

private theorem absolute_bound_of_difference {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (σ : ℝ) (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hKU : K ⊆ U) (R C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (u v : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
      (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K),
      (∑ i, ‖ccTensorToHs g 0 σ (u i)‖) ≤ R →
      (∑ i, ‖ccTensorToHs g 0 σ (v i)‖) ≤ R →
      ‖ccTensorToHs g 0 σ
        (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖ ≤
        C * ∑ i, ‖ccTensorToHs g 0 σ (u i - v i)‖) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K),
      (∑ i, ‖ccTensorToHs g 0 σ (u i)‖) ≤ R →
      ‖ccTensorToHs g 0 σ
        (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)))‖ ≤ A := by
  classical
  by_cases hex : ∃ v : ι → SmoothCcTensor g 0 0,
      (∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K) ∧
      (∑ i, ‖ccTensorToHs g 0 σ (v i)‖) ≤ R
  · obtain ⟨v, hv, hnv⟩ := hex
    let B := ‖ccTensorToHs g 0 σ
      (SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖
    have hR : 0 ≤ R := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hnv
    refine ⟨C * (2 * R) + B, by positivity, ?_⟩
    intro u hu hnu
    have hsum : ∑ i, ‖ccTensorToHs g 0 σ (u i - v i)‖ ≤ 2 * R := by
      calc
        _ ≤ ∑ i, (‖ccTensorToHs g 0 σ (u i)‖ + ‖ccTensorToHs g 0 σ (v i)‖) := by
          apply Finset.sum_le_sum
          intro i _
          rw [show ccTensorToHs g 0 σ (u i - v i) =
            ccTensorToHs g 0 σ (u i) - ccTensorToHs g 0 σ (v i) from
              (ccToHsLin g 0 σ).map_sub _ _]
          exact norm_sub_le _ _
        _ ≤ 2 * R := by rw [Finset.sum_add_distrib]; linarith
    have hd := (hbound u v hu hv hnu hnv).trans (mul_le_mul_of_nonneg_left hsum hC)
    have h := norm_le_norm_sub_add (ccTensorToHs g 0 σ
      (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x))))
      (ccTensorToHs g 0 σ (SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x))))
    have heq := (ccToHsLin g 0 σ).map_sub
      (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)))
      (SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))
    change ccTensorToHs g 0 σ _ =
      ccTensorToHs g 0 σ (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x))) -
      ccTensorToHs g 0 σ (SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x))) at heq
    rw [← heq] at h
    exact h.trans (add_le_add hd le_rfl)
  · exact ⟨0, le_rfl, fun u hu hnu => False.elim (hex ⟨u, hu, hnu⟩)⟩

theorem exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u v : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
      (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K),
      (∑ i, ‖ccTensorToHs g 0 ((n : ℝ) + 1) (u i)‖) ≤ R →
      (∑ i, ‖ccTensorToHs g 0 ((n : ℝ) + 1) (v i)‖) ≤ R →
      ‖ccTensorToHs g 0 ((n : ℝ) + 1)
        (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖ ≤
        C * ∑ i, ‖ccTensorToHs g 0 ((n : ℝ) + 1) (u i - v i)‖ := by
  classical
  by_cases hR : 0 ≤ R
  case neg =>
    refine ⟨0, le_rfl, ?_⟩
    intro u v hu hv hnu hnv
    exact False.elim (hR ((Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hnu))
  case pos =>
    have hnorm {a b : ℝ} (h : a = b) (W : SmoothCcTensor g 0 0) :
        ‖ccTensorToHs g 0 a W‖ = ‖ccTensorToHs g 0 b W‖ :=
      congrArg (fun σ : ℝ => ‖ccTensorToHs g 0 σ W‖) h
    change ∀ ⦃z⦄, z ∈ K → z ∈ U at hKU
    induction n generalizing F with
    | zero =>
        simp_rw [hnorm (show ((0 : ℕ) : ℝ) + 1 = 1 by norm_num)]
        obtain ⟨C, hC, hc⟩ :=
          DifferentialGeometry.Analysis.Spectral.exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
            g F hF hU hK hKU
        let E := ‖scalarH1ToContinuous g‖
        refine ⟨C * (1 + E * R), by positivity, ?_⟩
        intro u v hu hv _ hnv
        let d := ∑ i, ‖ccTensorToHs g 0 1 (u i - v i)‖
        have hd : 0 ≤ d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have h := hc u v hu hv (E * d) (by positivity)
          (fun x => scalar0_sub_norm_le_sum_hs g le_rfl u v x)
        calc
          _ ≤ C * (d + E * d * ∑ i, ‖ccTensorToHs g 0 1 (v i)‖) := h
          _ ≤ C * (d + E * d * R) := by gcongr
          _ = _ := by ring
    | succ n ih =>
        simp_rw [hnorm (show ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 1 + 1 by norm_num)]
        let G (i : ι) (z : ι → ℝ) := fderiv ℝ F z (Pi.single i 1)
        have hG (i : ι) : ContDiffOn ℝ ∞ (G i) U :=
          (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
        choose B hB hb using fun i => ih (G i) (hG i)
        choose A hA ha using fun i =>
          absolute_bound_of_difference g ((n : ℝ) + 1) (G i) (hG i) hKU R (B i) (hB i) (hb i)
        let A₀ := ∑ i, A i
        let B₀ := ∑ i, B i
        have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
        have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg (fun i _ => hB i)
        have hAi (i : ι) : A i ≤ A₀ := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
        have hBi (i : ι) : B i ≤ B₀ := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
        obtain ⟨V, hV, hvb⟩ := ih F hF
        obtain ⟨D, hD, hd'⟩ := norm_parameterDerivativeCcTensor_le g (n + 1)
        have hd (W : SmoothCcTensor g 0 0) :
            ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g W)‖ ≤
              D * ‖ccTensorToHs g 0 ((n : ℝ) + 1 + 1) W‖ := by
          simpa only [hnorm (show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num),
            hnorm (show ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 1 + 1 by norm_num)] using hd' W
        obtain ⟨P, hP, hp'⟩ := scalar_product_sub_hs_bound g (n + 1) (by simp)
        have hp (A B D T : SmoothCcTensor g 0 0) :
            ‖ccTensorToHs g 0 ((n : ℝ) + 1)
              (ccOperatorFieldComp g 0 0 0 A B - ccOperatorFieldComp g 0 0 0 D T)‖ ≤
              P * (‖ccTensorToHs g 0 ((n : ℝ) + 1) A‖ *
                ‖ccTensorToHs g 0 ((n : ℝ) + 1) (B - T)‖ +
                ‖ccTensorToHs g 0 ((n : ℝ) + 1) (A - D)‖ *
                ‖ccTensorToHs g 0 ((n : ℝ) + 1) T‖) := by
          simpa only [hnorm (show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num)] using hp' A B D T
        obtain ⟨H, hH, hh'⟩ := exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative g n
        have hh (W : SmoothCcTensor g 0 0) :
            ‖ccTensorToHs g 0 ((n : ℝ) + 1 + 1) W‖ ≤
              H * (‖ccTensorToHs g 0 (n : ℝ) W‖ +
                ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g W)‖) := by
          rw [hnorm (show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring)]
          exact hh' W
        let Q := P * (A₀ * D + B₀ * D * R)
        have hQ : 0 ≤ Q := by positivity
        refine ⟨H * (V + Q), by positivity, ?_⟩
        intro u v hu hv hnu hnv
        let L₁ := ccToHsLin g 0 ((n : ℝ) + 1)
        let L₂ := ccToHsLin g 0 ((n : ℝ) + 1 + 1)
        let d := ∑ i, ‖L₂ (u i - v i)‖
        have hd₀ : 0 ≤ d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have hlo (w : ι → SmoothCcTensor g 0 0) :
            (∑ i, ‖ccTensorToHs g 0 ((n : ℝ) + 1) (w i)‖) ≤
              ∑ i, ‖L₂ (w i)‖ :=
          Finset.sum_le_sum (fun _ _ => ccToHs_norm_mono g 0 (by linarith) _)
        let Pu := SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x))
        let Pv := SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x))
        let Gu (i : ι) := SmoothCcTensor.scalarCompOn u (G i) (hG i) (fun x => hKU (hu x))
        let Gv (i : ι) := SmoothCcTensor.scalarCompOn v (G i) (hG i) (fun x => hKU (hv x))
        have habs (i : ι) : ‖L₁ (Gu i)‖ ≤ A₀ :=
          (ha i u hu ((hlo u).trans hnu)).trans (hAi i)
        have hdiff (i : ι) : ‖L₁ (Gu i - Gv i)‖ ≤ B₀ * d :=
          (hb i u v hu hv ((hlo u).trans hnu) ((hlo v).trans hnv)).trans
            (mul_le_mul (hBi i) (hlo (fun j => u j - v j))
              (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hB₀)
        have hprod (i : ι) :
            ‖L₁ (ccOperatorFieldComp g 0 0 0 (Gu i) (parameterDerivativeCcTensor g (u i)) -
              ccOperatorFieldComp g 0 0 0 (Gv i) (parameterDerivativeCcTensor g (v i)))‖ ≤
              P * (A₀ * (D * ‖L₂ (u i - v i)‖) +
                (B₀ * d) * (D * ‖L₂ (v i)‖)) := by
          have h := hp (Gu i) (parameterDerivativeCcTensor g (u i))
            (Gv i) (parameterDerivativeCcTensor g (v i))
          rw [← parameterDerivativeCcTensor_sub] at h
          exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul (habs i) (hd (u i - v i)) (norm_nonneg _) hA₀)
            (mul_le_mul (hdiff i) (hd (v i)) (norm_nonneg _) (mul_nonneg hB₀ hd₀))) hP)
        have hder : ‖L₁ (parameterDerivativeCcTensor g (Pu - Pv))‖ ≤ Q * d := by
          have heq : parameterDerivativeCcTensor g (Pu - Pv) =
              ∑ i, (ccOperatorFieldComp g 0 0 0 (Gu i) (parameterDerivativeCcTensor g (u i)) -
                ccOperatorFieldComp g 0 0 0 (Gv i) (parameterDerivativeCcTensor g (v i))) := by
            rw [parameterDerivativeCcTensor_sub]
            dsimp only [Pu, Pv]
            rw [parameterDerivativeCcTensor_scalarCompOn g u F hF hU,
              parameterDerivativeCcTensor_scalarCompOn g v F hF hU]
            exact (Finset.sum_sub_distrib _ _).symm
          rw [heq, map_sum]
          calc
            _ ≤ ∑ i, ‖L₁ (ccOperatorFieldComp g 0 0 0 (Gu i) (parameterDerivativeCcTensor g (u i)) -
                ccOperatorFieldComp g 0 0 0 (Gv i) (parameterDerivativeCcTensor g (v i)))‖ :=
              norm_sum_le _ _
            _ ≤ ∑ i, P * (A₀ * (D * ‖L₂ (u i - v i)‖) +
                (B₀ * d) * (D * ‖L₂ (v i)‖)) := Finset.sum_le_sum (fun i _ => hprod i)
            _ = P * (A₀ * (D * d) + (B₀ * d) * (D * ∑ i, ‖L₂ (v i)‖)) := by
              simp only [mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
              rfl
            _ ≤ P * (A₀ * (D * d) + (B₀ * d) * (D * R)) :=
              mul_le_mul_of_nonneg_left (add_le_add le_rfl
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnv hD)
                  (mul_nonneg hB₀ hd₀))) hP
            _ = Q * d := by dsimp only [Q]; ring
        have hval : ‖ccTensorToHs g 0 (n : ℝ) (Pu - Pv)‖ ≤ V * d :=
          (ccToHs_norm_mono g 0 (by linarith) _).trans
            ((hvb u v hu hv ((hlo u).trans hnu) ((hlo v).trans hnv)).trans
              (mul_le_mul_of_nonneg_left (hlo (fun j => u j - v j)) hV))
        calc
          _ ≤ H * (‖ccTensorToHs g 0 (n : ℝ) (Pu - Pv)‖ +
              ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g (Pu - Pv))‖) := hh _
          _ ≤ H * (V * d + Q * d) := mul_le_mul_of_nonneg_left (add_le_add hval hder) hH
          _ = _ := by change H * (V * d + Q * d) = H * (V + Q) * d; ring

theorem exists_norm_ccTensorToHs_scalarCompOn_h2_sub_le_of_isCompact
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u v : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
      (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K),
      (∑ i, ‖ccTensorToHs g 0 2 (u i)‖) ≤ R →
      (∑ i, ‖ccTensorToHs g 0 2 (v i)‖) ≤ R →
      ‖ccTensorToHs g 0 2
        (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖ ≤
        C * ∑ i, ‖ccTensorToHs g 0 2 (u i - v i)‖ := by
  have hn (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 1) W‖ = ‖ccTensorToHs g 0 2 W‖ :=
    congrArg (fun σ : ℝ => ‖ccTensorToHs g 0 σ W‖) (by norm_num)
  simpa only [hn] using
    exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact g 1 F hF hU hK hKU R


theorem exists_norm_ccTensorToHs_scalarCompOn_h2_le_of_h1_bound
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K),
      (∑ i, ‖ccTensorToHs g 0 1 (u i)‖) ≤ R →
      ‖ccTensorToHs g 0 2
        (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)))‖ ≤
        C * (1 + ∑ i, ‖ccTensorToHs g 0 2 (u i)‖) := by
  classical
  have hnorm {a b : ℝ} (h : a = b) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a W‖ = ‖ccTensorToHs g 0 b W‖ :=
    congrArg (fun σ : ℝ => ‖ccTensorToHs g 0 σ W‖) h
  have habs (G : (ι → ℝ) → ℝ) (hG : ContDiffOn ℝ ∞ G U) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : ι → SmoothCcTensor g 0 0)
        (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K),
        (∑ i, ‖ccTensorToHs g 0 1 (u i)‖) ≤ R →
        ‖ccTensorToHs g 0 1
          (SmoothCcTensor.scalarCompOn u G hG (fun x => hKU (hu x)))‖ ≤ A := by
    obtain ⟨C, hC, hc⟩ := exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
      g 0 G hG hU hK hKU R
    simp_rw [hnorm (by norm_num : ((0 : ℕ) : ℝ) + 1 = 1)] at hc
    exact absolute_bound_of_difference g 1 G hG hKU R C hC hc
  obtain ⟨V, hV, hv⟩ := habs F hF
  let G (i : ι) (z : ι → ℝ) := fderiv ℝ F z (Pi.single i 1)
  have hG (i : ι) : ContDiffOn ℝ ∞ (G i) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  choose A hA ha using fun i => habs (G i) (hG i)
  let A₀ := ∑ i, A i
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
  have hAi (i : ι) : A i ≤ A₀ :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  obtain ⟨P, hP, hp⟩ := scalar_product_hs_bound g 1 (by norm_num)
  obtain ⟨D, hD, hd⟩ := norm_parameterDerivativeCcTensor_le g 1
  obtain ⟨H, hH, hh⟩ := exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative g 0
  let Q := P * A₀ * D
  have hQ : 0 ≤ Q := by positivity
  refine ⟨H * (V + Q), by positivity, ?_⟩
  intro u hu hnu
  let Pu := SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x))
  let Gu (i : ι) := SmoothCcTensor.scalarCompOn u (G i) (hG i) (fun x => hKU (hu x))
  let L₁ := ccToHsLin g 0 1
  let N := ∑ i, ‖ccTensorToHs g 0 2 (u i)‖
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hGu (i : ι) : ‖ccTensorToHs g 0 1 (Gu i)‖ ≤ A₀ :=
    (ha i u hu hnu).trans (hAi i)
  have hDu (i : ι) :
      ‖ccTensorToHs g 0 1 (parameterDerivativeCcTensor g (u i))‖ ≤
        D * ‖ccTensorToHs g 0 2 (u i)‖ := by
    simpa only [hnorm (by norm_num : ((1 : ℕ) : ℝ) = 1),
      hnorm (by norm_num : ((1 : ℕ) : ℝ) + 1 = 2)] using hd (u i)
  have hprod (i : ι) :
      ‖L₁ (ccOperatorFieldComp g 0 0 0 (Gu i) (parameterDerivativeCcTensor g (u i)))‖ ≤
        Q * ‖ccTensorToHs g 0 2 (u i)‖ := by
    have h := hp (Gu i) (parameterDerivativeCcTensor g (u i))
    simp_rw [hnorm (by norm_num : ((1 : ℕ) : ℝ) = 1)] at h
    change ‖L₁ _‖ ≤ P * ‖ccTensorToHs g 0 1 (Gu i)‖ *
      ‖ccTensorToHs g 0 1 (parameterDerivativeCcTensor g (u i))‖ at h
    calc
      _ ≤ P * ‖ccTensorToHs g 0 1 (Gu i)‖ *
          ‖ccTensorToHs g 0 1 (parameterDerivativeCcTensor g (u i))‖ := h
      _ ≤ P * A₀ * (D * ‖ccTensorToHs g 0 2 (u i)‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hGu i) hP) (hDu i)
          (norm_nonneg _) (mul_nonneg hP hA₀)
      _ = Q * ‖ccTensorToHs g 0 2 (u i)‖ := by dsimp only [Q]; ring
  have hder : ‖L₁ (parameterDerivativeCcTensor g Pu)‖ ≤ Q * N := by
    have heq : parameterDerivativeCcTensor g Pu =
        ∑ i, ccOperatorFieldComp g 0 0 0 (Gu i) (parameterDerivativeCcTensor g (u i)) :=
      parameterDerivativeCcTensor_scalarCompOn g u F hF hU (fun x => hKU (hu x))
    rw [heq, map_sum]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hprod i)).trans_eq
      (Finset.mul_sum _ _ _).symm)
  have hval : ‖ccTensorToHs g 0 0 Pu‖ ≤ V :=
    (ccToHs_norm_mono g 0 (by norm_num : (0 : ℝ) ≤ 1) Pu).trans (hv u hu hnu)
  have hgraph : ‖ccTensorToHs g 0 2 Pu‖ ≤
      H * (‖ccTensorToHs g 0 0 Pu‖ + ‖L₁ (parameterDerivativeCcTensor g Pu)‖) := by
    simpa only [hnorm (by norm_num : ((0 : ℕ) : ℝ) + 2 = 2),
      hnorm (by norm_num : ((0 : ℕ) : ℝ) = 0),
      hnorm (by norm_num : ((0 : ℕ) : ℝ) + 1 = 1), L₁, ccToHsLin_apply] using hh Pu
  calc
    _ ≤ H * (‖ccTensorToHs g 0 0 Pu‖ + ‖L₁ (parameterDerivativeCcTensor g Pu)‖) := hgraph
    _ ≤ H * (V + Q * N) := mul_le_mul_of_nonneg_left (add_le_add hval hder) hH
    _ ≤ H * ((V + Q) * (1 + N)) := by
      apply mul_le_mul_of_nonneg_left _ hH
      nlinarith [mul_nonneg hV hN]
    _ = (H * (V + Q)) * (1 + N) := by ring

end AddCircle
