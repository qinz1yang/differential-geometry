import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real


set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood


theorem eventuallyEq_inter_Iic_of_mem_nhdsWithin {J : Set ℝ} {t : ℝ}
    (h : Iic t ∈ 𝓝[J] t) : (J ∩ Iic t : Set ℝ) =ᶠ[𝓝 t] J := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h
  filter_upwards [Metric.ball_mem_nhds t hε] with y hy
  exact propext ⟨fun hy' => hy'.1, fun hy' => ⟨hy', hsub ⟨hy, hy'⟩⟩⟩

theorem derivWithin_inter_Iic_eq_of_mem_nhdsWithin {f : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (h : Iic t ∈ 𝓝[J] t) : derivWithin f (J ∩ Iic t) t = derivWithin f J t :=
  derivWithin_congr_set (eventuallyEq_inter_Iic_of_mem_nhdsWithin h)

theorem derivWithin_eq_derivWithin_Iic_of_mem_nhdsLE {f : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (hJ : J ∈ 𝓝[≤] t)
    (hu : UniqueDiffWithinAt ℝ J t) : derivWithin f J t = derivWithin f (Iic t) t :=
  (hasDerivWithinAt_left_of_mem_nhdsLE hf hJ).derivWithin hu

theorem derivWithin_inter_Iic_eq_of_differentiableWithinAt {f : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (h : UniqueDiffWithinAt ℝ (J ∩ Iic t) t) :
    derivWithin f (J ∩ Iic t) t = derivWithin f J t :=
  (hf.hasDerivWithinAt.mono inter_subset_left).derivWithin h

theorem not_mem_nhdsWithin_Iic_Icc_neg_one_one :
    Iic (0 : ℝ) ∉ 𝓝[Icc (-1 : ℝ) 1] 0 := by
  intro h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h
  set y : ℝ := min (ε / 2) (1 / 2) with hy
  have hypos : 0 < y := lt_min (by linarith) (by norm_num)
  have hyeps : y < ε := by
    have hle : y ≤ ε / 2 := min_le_left _ _
    linarith
  have hyball : y ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hyone : y ≤ 1 := by
    have hle : y ≤ 1 / 2 := min_le_right _ _
    linarith
  have hyIcc : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hyone⟩
  exact absurd (hsub ⟨hyball, hyIcc⟩) (not_le.mpr hypos)

theorem mem_nhdsWithin_Iic_self (t : ℝ) : Iic t ∈ 𝓝[Iic t] t := self_mem_nhdsWithin

theorem derivWithin_inter_Iic_self (f : ℝ → ℝ) (t : ℝ) :
    derivWithin f (Iic t ∩ Iic t) t = derivWithin f (Iic t) t :=
  derivWithin_inter_Iic_eq_of_mem_nhdsWithin (f := f) (mem_nhdsWithin_Iic_self t)

theorem derivWithin_id_Ioo_zero : derivWithin (fun s : ℝ => s) (Ioo (-1 : ℝ) 1) 0 = 1 := by
  rw [derivWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo (by norm_num))]
  simp

theorem derivWithin_id_Ioo_zero_eq_derivWithin_id_Iic_zero :
    derivWithin (fun s : ℝ => s) (Ioo (-1 : ℝ) 1) 0 =
      derivWithin (fun s : ℝ => s) (Iic 0) 0 :=
  derivWithin_eq_derivWithin_Iic_of_mem_nhdsLE
    (f := fun s : ℝ => s) (J := Ioo (-1 : ℝ) 1) (t := 0)
    differentiableAt_id.differentiableWithinAt
    (by
      refine Metric.mem_nhdsWithin_iff.mpr ⟨1, by norm_num, ?_⟩
      intro y hy
      obtain ⟨hyball, _hyIic⟩ := hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyball
      exact ⟨by linarith [hyball.1], by linarith [hyball.2]⟩)
    (uniqueDiffWithinAt_Ioo (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1))

theorem derivWithin_id_Icc_zero : derivWithin (fun s : ℝ => s) (Icc (-1 : ℝ) 1) 0 = 1 :=
  by
    rw [derivWithin_of_mem_nhds
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))]
    simp

theorem derivWithin_id_Icc_inter_Iic_zero :
    derivWithin (fun s : ℝ => s) (Icc (-1 : ℝ) 1 ∩ Iic 0) 0 =
      derivWithin (fun s : ℝ => s) (Icc (-1 : ℝ) 1) 0 := by
  have hset : Icc (-1 : ℝ) 1 ∩ Iic 0 = Icc (-1 : ℝ) 0 := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩
  refine derivWithin_inter_Iic_eq_of_differentiableWithinAt
    (f := fun s : ℝ => s) (J := Icc (-1 : ℝ) 1) (t := 0)
    (DifferentiableAt.differentiableWithinAt (differentiableAt_id (x := (0 : ℝ)))) ?_
  rw [hset]
  exact uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) 0 ⟨by norm_num, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
