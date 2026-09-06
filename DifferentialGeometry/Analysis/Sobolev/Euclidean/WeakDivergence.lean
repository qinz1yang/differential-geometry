import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tsupport_sum_mul_fderiv_subset
    (C : Fin d → E → ℝ) (ψ : E → ℝ) :
    tsupport (fun x => ∑ i, C i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro x hx
  by_contra hxψ
  have hz (i : Fin d) : fderiv ℝ ψ x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1))
      (fun hy => hxψ (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hy))
  exact hx (by simp only [hz, mul_zero, Finset.sum_const_zero])

theorem integral_mul_sum_fderiv_eq_neg_sum_integral
    {Ω : Set E} {u : E → ℝ} {Du F : Fin d → E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hDu : ∀ i, DeGiorgi.HasWeakPartialDeriv i (Du i) u Ω)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (hFs : ∀ i, tsupport (F i) ⊆ Ω) :
    (∫ x in Ω, u x * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) =
      -∑ i, ∫ x in Ω, Du i x * F i x := by
  have hint (i : Fin d) : Integrable
      (fun x => u x * fderiv ℝ (F i) x (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    exact hu.integrable_smul_right_of_hasCompactSupport
      (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hFc i).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hDu _ _ (hF _) (hFc _) (hFs _), Finset.sum_neg_distrib]

theorem integral_mul_sum_fderiv_mul_eq_neg_sum_integral
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} {Du : Fin d → E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hDu : ∀ i, DeGiorgi.HasWeakPartialDeriv i (Du i) u Ω)
    {C : Fin d → Fin d → E → ℝ} (hC : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    (∫ x in Ω, u x * ∑ i, fderiv ℝ
      (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) =
      -∑ i, ∫ x in Ω, Du i x * ∑ j, C i j x * fderiv ℝ ψ x (EuclideanSpace.single j 1) := by
  let F := fun i y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)
  have hFs (i : Fin d) : tsupport (F i) ⊆ tsupport ψ :=
    tsupport_sum_mul_fderiv_subset (C i) ψ
  have hFc (i : Fin d) : HasCompactSupport (F i) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) (hFs i)
  have hF (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (F i) := by
    apply ContDiffOn.contDiff_of_tsupport_subset (s := Ω) _ hΩ ((hFs i).trans hψs)
    apply ContDiffOn.sum
    intro j _
    exact (hC i j).mul
      ((hψ.fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn
  exact integral_mul_sum_fderiv_eq_neg_sum_integral hu hDu hF hFc
    (fun i => (hFs i).trans hψs)

private theorem exists_contDiff_flux
    {Ω : Set E} (hΩ : IsOpen Ω)
    {C : Fin d → Fin d → E → ℝ} (hC : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω)
    {V : Fin d → E → ℝ} (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    ∃ F : Fin d → E → ℝ,
      (∀ i x, F i x = (∑ j, C i j x * fderiv ℝ ψ x (EuclideanSpace.single j 1)) - V i x * ψ x) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      (∀ i, tsupport (F i) ⊆ Ω) ∧
      ∀ x ∈ Ω, (∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) =
        (∑ i, fderiv ℝ (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) -
          (∑ i, V i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) -
          (∑ i, fderiv ℝ (V i) x (EuclideanSpace.single i 1)) * ψ x := by
  let P := fun i y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)
  let F := fun i y => P i y - V i y * ψ y
  have hP (i : Fin d) : ContDiffOn ℝ (⊤ : ℕ∞) (P i) Ω := by
    apply ContDiffOn.sum
    intro j _
    exact (hC i j).mul
      ((hψ.fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn
  have hFs (i : Fin d) : tsupport (F i) ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    by_contra hxψ
    have hz (j : Fin d) : fderiv ℝ ψ x (EuclideanSpace.single j 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y (EuclideanSpace.single j 1))
        (fun hy => hxψ (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1) hy))
    exact hx (by simp [F, P, hz, image_eq_zero_of_notMem_tsupport hxψ])
  have hFc (i : Fin d) : HasCompactSupport (F i) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) (hFs i)
  have hF (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (F i) :=
    ((hP i).sub ((hV i).mul hψ.contDiffOn)).contDiff_of_tsupport_subset
      hΩ ((hFs i).trans hψs)
  have heq (x : E) (hx : x ∈ Ω) :
      (∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) =
        (∑ i, fderiv ℝ (P i) x (EuclideanSpace.single i 1)) -
          (∑ i, V i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) -
          (∑ i, fderiv ℝ (V i) x (EuclideanSpace.single i 1)) * ψ x := by
    have hd (i : Fin d) : fderiv ℝ (F i) x (EuclideanSpace.single i 1) =
        fderiv ℝ (P i) x (EuclideanSpace.single i 1) -
          (V i x * fderiv ℝ ψ x (EuclideanSpace.single i 1) +
            fderiv ℝ (V i) x (EuclideanSpace.single i 1) * ψ x) := by
      have hPd := ((hP i).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
      have hVd := ((hV i).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
      have hψd := hψ.differentiable (by simp) x
      dsimp only [F]
      rw [fderiv_fun_sub hPd (hVd.fun_mul hψd), fderiv_fun_mul hVd hψd]
      simp only [sub_apply, add_apply,
        smul_apply, smul_eq_mul]
      ring
    simp_rw [hd, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  exact ⟨F, fun _ _ => rfl, hF, hFc, fun i => (hFs i).trans hψs, heq⟩

theorem integrable_mul_sum_fderiv_sub_mul
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    {C : Fin d → Fin d → E → ℝ} (hC : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω)
    {V : Fin d → E → ℝ} (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => u x *
      ((∑ i, fderiv ℝ (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) -
        (∑ i, V i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) -
        (∑ i, fderiv ℝ (V i) x (EuclideanSpace.single i 1)) * ψ x)) (volume.restrict Ω) := by
  obtain ⟨F, _, hF, hFc, _, heq⟩ := exists_contDiff_flux hΩ hC hV hψ hψc hψs
  have hint (i : Fin d) : Integrable
      (fun x => u x * fderiv ℝ (F i) x (EuclideanSpace.single i 1)) (volume.restrict Ω) :=
    hu.integrable_smul_right_of_hasCompactSupport
      (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hFc i).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  apply (integrable_finsetSum Finset.univ (fun i _ => hint i)).congr
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [← Finset.mul_sum, heq x hx]

theorem integral_mul_sum_fderiv_sub_mul_eq_neg_sum_integral
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} {Du : Fin d → E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hDu : ∀ i, DeGiorgi.HasWeakPartialDeriv i (Du i) u Ω)
    {C : Fin d → Fin d → E → ℝ} (hC : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω)
    {V : Fin d → E → ℝ} (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    (∫ x in Ω, u x *
      ((∑ i, fderiv ℝ (fun y => ∑ j, C i j y *
          fderiv ℝ ψ y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) -
        (∑ i, V i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) -
        (∑ i, fderiv ℝ (V i) x (EuclideanSpace.single i 1)) * ψ x)) =
      -∑ i, ∫ x in Ω, Du i x *
        ((∑ j, C i j x * fderiv ℝ ψ x (EuclideanSpace.single j 1)) - V i x * ψ x) := by
  obtain ⟨F, hFeq, hF, hFc, hFs, heq⟩ := exists_contDiff_flux hΩ hC hV hψ hψc hψs
  calc
    _ = ∫ x in Ω, u x * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1) := by
      apply setIntegral_congr_fun hΩ.measurableSet
      intro x hx
      exact congrArg (fun v => u x * v) (heq x hx).symm
    _ = _ := by
      rw [integral_mul_sum_fderiv_eq_neg_sum_integral hu hDu hF hFc hFs]
      simp_rw [hFeq]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
