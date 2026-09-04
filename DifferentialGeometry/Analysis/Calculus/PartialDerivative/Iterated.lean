import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ProductDifferenceBounds
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Defs

noncomputable section

open Set
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem partialDeriv_eq_iteratedFDeriv_one
    (u : E → ℝ) (i : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y =
      iteratedFDeriv ℝ 1 u y ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i] := by
  rw [iteratedFDeriv_one_apply]
  rfl

theorem partialDeriv_partialDeriv_eq_iteratedFDeriv_two
    (u : E → ℝ) {y : E} (hu : ContDiffAt ℝ ∞ u y)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j u) y =
      iteratedFDeriv ℝ 2 u y
        ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j] := by
  have hfderiv_diff : DifferentiableAt ℝ (fun z : E => fderiv ℝ u z) y := by
    have hderiv := hu.fderiv_right (m := ∞) le_rfl
    exact hderiv.differentiableAt (by simp)
  have hj : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j u =
      fun z : E => fderiv ℝ u z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
    funext z
    rfl
  rw [show DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j u) y =
      fderiv ℝ (fun z : E => fderiv ℝ u z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) y
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) from by rw [hj]; rfl]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply hfderiv_diff (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

lemma partialDeriv_contDiffOn_of_isOpen
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) s := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) s :=
    hu.fderiv_of_isOpen hs (by rw [ENat.coe_top_add_one])
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

lemma partialDeriv_sub_eqOn
    {u v : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    (i : Fin (Module.finrank ℝ E)) :
    EqOn (fun z => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u z - DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i v z)
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun z => u z - v z)) s := by
  intro y hy
  have hdu : DifferentiableAt ℝ u y :=
    (hu.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  have hdv : DifferentiableAt ℝ v y :=
    (hv.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv]
  have hfd : fderiv ℝ (fun z => u z - v z) y = fderiv ℝ u y - fderiv ℝ v y := by
    have hfun : (fun z => u z - v z) = u - v := by
      funext z
      rfl
    rw [hfun]
    exact fderiv_sub (𝕜 := ℝ) hdu hdv
  rw [hfd, sub_apply]

lemma partialDeriv_eqOn_fderivWithin_apply
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (i : Fin (Module.finrank ℝ E)) :
    EqOn (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u)
      (fun y => fderivWithin ℝ u s y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) s := by
  intro y hy
  simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv, fderivWithin_of_isOpen hs hy]

theorem partialDeriv_partialDeriv_partialDeriv_eq_iteratedFDeriv_three
    (u : E → ℝ) {y : E} (hu : ContDiffAt ℝ ∞ u y)
    (n m l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) n (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u)) y =
      iteratedFDeriv ℝ 3 u y
        ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l] := by
  obtain ⟨t, ht_nhds, hut⟩ := hu.contDiffOn (m := 3)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3) (by simp)
  obtain ⟨s, hst, hs_open, hys⟩ := mem_nhds_iff.mp ht_nhds
  have hu_s : ContDiffOn ℝ 3 u s := hut.mono hst
  have hpartial_at : ContDiffAt ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u) y := by
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiffAt_const
  have hfderiv_s : ContDiffOn ℝ 2 (fderivWithin ℝ u s) s :=
    hu_s.fderivWithin hs_open.uniqueDiffOn (by norm_num)
  calc
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) n (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u)) y =
        iteratedFDeriv ℝ 2 (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u) y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] :=
      partialDeriv_partialDeriv_eq_iteratedFDeriv_two
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u) hpartial_at n m
    _ = iteratedFDerivWithin ℝ 2 (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l u) s y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] := by
      rw [iteratedFDerivWithin_of_isOpen 2 hs_open hys]
    _ = iteratedFDerivWithin ℝ 2
          (fun z => fderivWithin ℝ u s z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l)) s y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] := by
      rw [iteratedFDerivWithin_congr
        (partialDeriv_eqOn_fderivWithin_apply hs_open l) hys 2]
    _ = iteratedFDerivWithin ℝ 2 (fderivWithin ℝ u s) s y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l) := by
      exact iteratedFDerivWithin_clm_apply_const_apply hs_open.uniqueDiffOn hfderiv_s
        (by norm_num) hys
    _ = iteratedFDerivWithin ℝ 3 u s y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l] := by
      have htuple :
          (![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l] : Fin 3 → E) =
            Fin.snoc (![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] : Fin 2 → E)
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l) := by
        funext i
        fin_cases i <;> rfl
      symm
      rw [htuple]
      simpa only [Fin.init_snoc, Fin.snoc_last] using
        iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ) (f := u)
        hs_open.uniqueDiffOn hys
          (Fin.snoc (![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m] : Fin 2 → E)
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l))
    _ = iteratedFDeriv ℝ 3 u y
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) n, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) l] := by
      rw [iteratedFDerivWithin_of_isOpen 3 hs_open hys]

theorem norm_iteratedFDerivWithin_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ N (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) s y‖ ≤
      ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i‖ * ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ := by
  have hcongr :
      iteratedFDerivWithin ℝ N (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) s y =
        iteratedFDerivWithin ℝ N
          (fun z => fderivWithin ℝ u s z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) s y :=
    iteratedFDerivWithin_congr (partialDeriv_eqOn_fderivWithin_apply hs i) hy N
  rw [hcongr]
  have hfderiv : ContDiffOn ℝ ∞ (fderivWithin ℝ u s) s :=
    hu.fderivWithin (hs.uniqueDiffOn) (by rw [ENat.coe_top_add_one])
  have hclm := norm_iteratedFDerivWithin_clm_apply_const
    (f := fderivWithin ℝ u s) (c := (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) (s := s) (x := y)
    (N := (⊤ : ℕ∞)) (n := N)
    (hfderiv.contDiffWithinAt hy) hs.uniqueDiffOn hy (by exact_mod_cast le_top)
  refine hclm.trans ?_
  have heq : ‖iteratedFDerivWithin ℝ N (fderivWithin ℝ u s) s y‖ =
      ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ :=
    norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hy
  rw [heq]

theorem iteratedFDerivSeminorm_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    iteratedFDerivSeminorm N (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) s y ≤
      ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i‖ * iteratedFDerivSeminorm (N + 1) u s y := by
  classical
  have hstep :
      iteratedFDerivSeminorm N (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) s y ≤
        ‖(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i‖ *
          ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ := by
    unfold iteratedFDerivSeminorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    exact norm_iteratedFDerivWithin_partialDeriv_le hs hu i l hy
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold iteratedFDerivSeminorm
  have himg :
      ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ =
        ∑ m ∈ (Finset.range (N + 1)).image (· + 1),
          ‖iteratedFDerivWithin ℝ m u s y‖ := by
    rw [Finset.sum_image (g := (· + 1))
      (f := fun m => ‖iteratedFDerivWithin ℝ m u s y‖)
      (by intro a _ b _ hab; simpa using hab)]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_range] at hl ⊢
  omega

end Calculus
end Analysis
end DifferentialGeometry

end
