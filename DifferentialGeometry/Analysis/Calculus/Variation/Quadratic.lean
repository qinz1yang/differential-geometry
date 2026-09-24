import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Support

section

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem tendsto_zero_of_quadratic_variations
    {ι : Type*} {l : Filter ι} {E S : ι → ℝ} {Q : ι → ℝ → ℝ}
    {m ε C : ℝ} (hε : 0 < ε) (hE : Tendsto E l (𝓝 m))
    (hlower : ∀ t : ℝ, |t| < ε → ∀ᶠ n in l, m ≤ Q n t)
    (hquadratic : ∀ t : ℝ, |t| < ε →
      ∀ᶠ n in l, |Q n t - E n - t * S n| ≤ C * t ^ 2 * E n) :
    Tendsto S l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let B : ℝ := |C| * (|m| + 1)
  have hB : 0 ≤ B := by positivity
  have hdenom : 0 < 4 * (B + 1) := by positivity
  let δ : ℝ := min (ε / 2) (η / (4 * (B + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hη hdenom)
  have hδ_le : δ ≤ ε / 2 := min_le_left _ _
  have hδ_lt : δ < ε := by linarith
  have hδ_scale : δ * (4 * (B + 1)) ≤ η :=
    (le_div_iff₀ hdenom).mp (min_le_right _ _)
  have hδB : δ * B < η / 2 := by nlinarith
  have hsmall : δ ^ 2 * B < δ * η / 2 := by
    nlinarith [mul_lt_mul_of_pos_left hδB hδ]
  have hδ_abs : |δ| < ε := by rwa [abs_of_pos hδ]
  have hnegδ_abs : |-δ| < ε := by rwa [abs_neg]
  filter_upwards [Metric.tendsto_nhds.mp hE 1 (by norm_num),
    Metric.tendsto_nhds.mp hE (δ * η / 2) (by positivity),
    hlower δ hδ_abs, hlower (-δ) hnegδ_abs,
    hquadratic δ hδ_abs, hquadratic (-δ) hnegδ_abs]
    with n hn_one hn_close hn_lower_pos hn_lower_neg hn_pos hn_neg
  rw [Real.dist_eq] at hn_one hn_close
  have hn_abs : |E n| ≤ |m| + 1 := by
    have hn := abs_lt.mp hn_one
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le m]
    · linarith [le_abs_self m]
  have hgap : E n - m < δ * η / 2 := (abs_lt.mp hn_close).2
  have hrem : C * δ ^ 2 * E n ≤ δ ^ 2 * B := by
    calc
      C * δ ^ 2 * E n ≤ |C * δ ^ 2 * E n| := le_abs_self _
      _ = |C| * δ ^ 2 * |E n| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg δ)]
      _ ≤ |C| * δ ^ 2 * (|m| + 1) :=
        mul_le_mul_of_nonneg_left hn_abs (by positivity)
      _ = δ ^ 2 * B := by dsimp [B]; ring
  have hpos := (abs_le.mp hn_pos).2
  have hneg := (abs_le.mp hn_neg).2
  rw [Real.dist_eq, sub_zero]
  apply abs_lt.mpr
  constructor
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hn_lower_pos, hpos, hrem, hgap, hsmall]
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hn_lower_neg, hneg, hrem, hgap, hsmall]

end DifferentialGeometry.Analysis

end

noncomputable section

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance formNormedAdd : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance formNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem hasDerivAt_quadraticVariation
    (A : F → (F →L[ℝ] F →L[ℝ] ℝ)) (u φ v w : F) (t : ℝ)
    (hA : DifferentiableAt ℝ A (u + t • φ)) :
    HasDerivAt (fun s : ℝ => A (u + s • φ) (v + s • w) (v + s • w))
      ((fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w) +
        A (u + t • φ) w (v + t • w) +
        A (u + t • φ) (v + t • w) w) t := by
  have hU : HasDerivAt (fun s : ℝ => u + s • φ) φ t := by
    have hmul : HasDerivAt (fun s : ℝ => s • φ) φ t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const φ
    simpa only [add_comm] using HasDerivAt.const_add u hmul
  have hV : HasDerivAt (fun s : ℝ => v + s • w) w t := by
    have hmul : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const w
    simpa only [add_comm] using HasDerivAt.const_add v hmul
  have hA' : HasDerivAt (fun s : ℝ => A (u + s • φ))
      ((fderiv ℝ A (u + t • φ)) φ) t := by
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := A) (f := fun s : ℝ => u + s • φ) (x := t)
      (hA.hasFDerivAt) hU rfl
    change HasDerivAt (A ∘ fun s : ℝ => u + s • φ)
      ((fderiv ℝ A (u + t • φ)) φ) t
    exact hcomp
  have h₁ := hA'.clm_apply hV
  have h₂ := h₁.clm_apply hV
  simpa only [add_apply] using h₂

theorem hasDerivAt_quadraticVariation_symmetric
    (A : F → (F →L[ℝ] F →L[ℝ] ℝ)) (u φ v w : F) (t : ℝ)
    (hA : DifferentiableAt ℝ A (u + t • φ))
    (hsym : ∀ x z, A (u + t • φ) x z = A (u + t • φ) z x) :
    HasDerivAt (fun s : ℝ => A (u + s • φ) (v + s • w) (v + s • w))
      ((fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w) +
        2 * A (u + t • φ) (v + t • w) w) t := by
  convert hasDerivAt_quadraticVariation A u φ v w t hA using 1
  rw [hsym]
  ring

theorem norm_deriv_quadraticVariation_le
    (A : F → (F →L[ℝ] F →L[ℝ] ℝ)) (u φ v w : F) (t C P : ℝ)
    (hA : DifferentiableAt ℝ A (u + t • φ))
    (ht : |t| ≤ 1)
    (hφ : ‖φ‖ ≤ P)
    (hAnorm : ‖A (u + t • φ)‖ ≤ C)
    (hDnorm : ‖fderiv ℝ A (u + t • φ)‖ ≤ C) :
    ‖deriv (fun s : ℝ => A (u + s • φ) (v + s • w) (v + s • w)) t‖ ≤
      C * (P * (‖v‖ + ‖w‖) ^ 2 + 2 * ‖w‖ * (‖v‖ + ‖w‖)) := by
  have hC : 0 ≤ C := (norm_nonneg (A (u + t • φ))).trans hAnorm
  have hP : 0 ≤ P := (norm_nonneg φ).trans hφ
  have hderiv := hasDerivAt_quadraticVariation A u φ v w t hA
  rw [hderiv.deriv]
  have hV : ‖v + t • w‖ ≤ ‖v‖ + ‖w‖ := by
    calc
      ‖v + t • w‖ ≤ ‖v‖ + ‖t • w‖ := norm_add_le _ _
      _ = ‖v‖ + |t| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ + 1 * ‖w‖ := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (norm_nonneg w))
      _ = ‖v‖ + ‖w‖ := by simp
  have hfirst :
      ‖(fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w)‖ ≤
        C * P * (‖v‖ + ‖w‖) ^ 2 := by
    calc
      _ ≤ (‖fderiv ℝ A (u + t • φ)‖ * ‖φ‖) *
          ‖v + t • w‖ * ‖v + t • w‖ := by
        calc
          _ ≤ ‖(fderiv ℝ A (u + t • φ)) φ‖ *
              (‖v + t • w‖ * ‖v + t • w‖) := by
            simpa only [mul_assoc] using
              ContinuousLinearMap.le_opNorm₂ (fderiv ℝ A (u + t • φ) φ)
                (v + t • w) (v + t • w)
          _ ≤ (‖fderiv ℝ A (u + t • φ)‖ * ‖φ‖) *
              (‖v + t • w‖ * ‖v + t • w‖) := by
            exact mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.le_opNorm (fderiv ℝ A (u + t • φ)) φ)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = _ := by ring
      _ ≤ (C * ‖φ‖) * ‖v + t • w‖ * ‖v + t • w‖ := by gcongr
      _ ≤ C * P * ‖v + t • w‖ * ‖v + t • w‖ := by gcongr
      _ ≤ C * P * (‖v‖ + ‖w‖) ^ 2 := by
        calc
          _ = (C * P) * (‖v + t • w‖ * ‖v + t • w‖) := by ring
          _ ≤ (C * P) * ((‖v‖ + ‖w‖) * (‖v‖ + ‖w‖)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul hV hV (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
            · exact mul_nonneg hC hP
          _ = _ := by ring
  have hsecond :
      ‖A (u + t • φ) w (v + t • w)‖ ≤ C * ‖w‖ * (‖v‖ + ‖w‖) := by
    calc
      _ ≤ ‖A (u + t • φ)‖ * ‖w‖ * ‖v + t • w‖ :=
        ContinuousLinearMap.le_opNorm₂ (A (u + t • φ)) w (v + t • w)
      _ ≤ C * ‖w‖ * (‖v‖ + ‖w‖) := by gcongr
  have hthird :
      ‖A (u + t • φ) (v + t • w) w‖ ≤ C * (‖v‖ + ‖w‖) * ‖w‖ := by
    calc
      _ ≤ ‖A (u + t • φ)‖ * ‖v + t • w‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm₂ (A (u + t • φ)) (v + t • w) w
      _ ≤ C * (‖v‖ + ‖w‖) * ‖w‖ := by gcongr
  calc
    _ ≤ ‖(fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w)‖ +
        ‖A (u + t • φ) w (v + t • w)‖ +
        ‖A (u + t • φ) (v + t • w) w‖ := by
      calc
        _ ≤ ‖((fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w) +
            A (u + t • φ) w (v + t • w))‖ +
            ‖A (u + t • φ) (v + t • w) w‖ := norm_add_le _ _
        _ ≤ ‖(fderiv ℝ A (u + t • φ) φ) (v + t • w) (v + t • w)‖ +
            ‖A (u + t • φ) w (v + t • w)‖ +
            ‖A (u + t • φ) (v + t • w) w‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ C * P * (‖v‖ + ‖w‖) ^ 2 +
        C * ‖w‖ * (‖v‖ + ‖w‖) + C * (‖v‖ + ‖w‖) * ‖w‖ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = C * (P * (‖v‖ + ‖w‖) ^ 2 +
        2 * ‖w‖ * (‖v‖ + ‖w‖)) := by ring

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance compactRangeFormNormedAdd : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactRangeFormNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance compactRangeDerivNormedAdd : NormedAddCommGroup (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactRangeDerivNormedSpace : NormedSpace ℝ (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedSpace

theorem exists_compact_metric_range_bounds
    [FiniteDimensional ℝ F]
    {V : Set F} {A : F → (F →L[ℝ] F →L[ℝ] ℝ)}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V)
    {K : Set F} (hK : IsCompact K) (hKV : K ⊆ V)
    (P : ℝ) (hP : 0 ≤ P) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ y ∈ K, ∀ v : F, ‖v‖ ≤ P →
      ∀ t : ℝ, |t| < δ →
        y + t • v ∈ V ∧ ‖A (y + t • v)‖ ≤ C ∧
          ‖fderiv ℝ A (y + t • v)‖ ≤ C := by
  obtain ⟨ε, hε, hεV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L : Set F := Metric.cthickening ε K
  have hL : IsCompact L := by
    dsimp [L]
    exact hK.cthickening
  have hAc : ContinuousOn A L := hA.continuousOn.mono (by
    intro x hx
    exact hεV hx)
  have hDc : ContinuousOn (fderiv ℝ A) L :=
    hA.continuousOn_fderiv_of_isOpen hV (by norm_num) |>.mono (by
      intro x hx
      exact hεV hx)
  obtain ⟨C₀, hC₀⟩ := hL.exists_bound_of_continuousOn hAc
  obtain ⟨C₁, hC₁⟩ := hL.exists_bound_of_continuousOn hDc
  let C : ℝ := max C₀ (max C₁ 0)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨ε / (P + 1), div_pos hε (by linarith), C, hC, ?_⟩
  intro y hy v hv t ht
  have hv₁ : ‖v‖ ≤ P + 1 := hv.trans (by linarith)
  have hprod₁ : |t| * ‖v‖ ≤ |t| * (P + 1) :=
    mul_le_mul_of_nonneg_left hv₁ (abs_nonneg t)
  have hprod₂ : |t| * (P + 1) < (ε / (P + 1)) * (P + 1) :=
    mul_lt_mul_of_pos_right ht (by linarith)
  have hprod : |t| * ‖v‖ < ε := by
    calc
      |t| * ‖v‖ ≤ |t| * (P + 1) := hprod₁
      _ < (ε / (P + 1)) * (P + 1) := hprod₂
      _ = ε := by rw [div_mul_cancel₀ _ (by linarith)]
  have hdist : dist (y + t • v) y < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact hprod
  have hmem : y + t • v ∈ L := by
    apply Metric.mem_cthickening_of_dist_le (y + t • v) y ε K hy
    exact hdist.le
  have hVmem : y + t • v ∈ V := hεV hmem
  have hAbound : ‖A (y + t • v)‖ ≤ C := by
    exact (hC₀ _ hmem).trans (le_max_left _ _)
  have hDbound : ‖fderiv ℝ A (y + t • v)‖ ≤ C := by
    exact (hC₁ _ hmem).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  exact ⟨hVmem, hAbound, hDbound⟩

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open Set
open scoped ENNReal ContDiff

namespace DeGiorgi

variable {d n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem affineVariation_eq_of_notMem_tsupport
    {X Y : Type*} [TopologicalSpace X] [AddZeroClass Y] [SMulZeroClass ℝ Y]
    {u φ : X → Y} (t : ℝ) {x : X} (hx : x ∉ tsupport φ) :
    u x + t • φ x = u x := by
  rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, add_zero]

end DeGiorgi

end
