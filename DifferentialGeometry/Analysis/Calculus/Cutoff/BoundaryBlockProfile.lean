import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalProfiles
import DifferentialGeometry.Analysis.Calculus.FlatTailDerivativeBounds
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The physical boundary profile and block (blueprint 207B, BCG.0 and BCG01)

`boundaryProfile` realizes `χ_∂ = χ_{20,30}(1 - χ_{80,90})` of (BCG.0) (B:8710–8726) by the tree's
plateau profile: zero for `t ≤ 20` and `t ≥ 90`, one on `[30, 80]`, smooth, valued in `[0,1]`.
`boundaryBlock t = (t χ_∂(t), χ_∂(t))` is the physical block `𝓑`. The global derivative constant
`P` of (BCG.0) and the zero-extension smoothness of BCG01 are proved here.
-/

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Analysis

/-- The boundary marker profile `χ_∂` (support `[20,90]`, plateau `[30,80]`). -/
noncomputable def boundaryProfile : ℝ → ℝ := intervalPlateauProfile 20 30 80 90

/-- The physical boundary block `𝓑(t) = (t χ_∂(t), χ_∂(t))` of (BCG.0). -/
noncomputable def boundaryBlock (t : ℝ) : ℝ × ℝ := (t * boundaryProfile t, boundaryProfile t)

theorem contDiff_boundaryProfile : ContDiff ℝ ∞ boundaryProfile :=
  contDiff_intervalPlateauProfile 20 30 80 90

theorem contDiff_boundaryBlock : ContDiff ℝ ∞ boundaryBlock :=
  (contDiff_id.mul contDiff_boundaryProfile).prodMk contDiff_boundaryProfile

theorem boundaryProfile_mem_Icc (t : ℝ) : boundaryProfile t ∈ Icc (0 : ℝ) 1 :=
  intervalPlateauProfile_mem_Icc 20 30 80 90 t

theorem boundaryProfile_eq_one {t : ℝ} (ht : t ∈ Icc (30 : ℝ) 80) : boundaryProfile t = 1 :=
  intervalPlateauProfile_one (by norm_num) (by norm_num) ht

theorem boundaryProfile_eq_zero_of_le {t : ℝ} (ht : t ≤ 20) : boundaryProfile t = 0 :=
  intervalPlateauProfile_zero_left (by norm_num) ht

theorem boundaryProfile_eq_zero_of_ge {t : ℝ} (ht : 90 ≤ t) : boundaryProfile t = 0 :=
  intervalPlateauProfile_zero_right (by norm_num) ht

theorem boundaryBlock_eq_zero_of_le {t : ℝ} (ht : t ≤ 20) : boundaryBlock t = 0 := by
  simp only [boundaryBlock, boundaryProfile_eq_zero_of_le ht, mul_zero, Prod.mk_zero_zero]

theorem boundaryBlock_eq_zero_of_ge {t : ℝ} (ht : 90 ≤ t) : boundaryBlock t = 0 := by
  simp only [boundaryBlock, boundaryProfile_eq_zero_of_ge ht, mul_zero, Prod.mk_zero_zero]

/-- A nonzero block forces the height into the open support band `(20, 90)` (BCG01, BCG04). -/
theorem mem_Ioo_of_boundaryBlock_ne_zero {t : ℝ} (h : boundaryBlock t ≠ 0) :
    t ∈ Ioo (20 : ℝ) 90 := by
  refine ⟨lt_of_not_ge fun ht => h (boundaryBlock_eq_zero_of_le ht),
    lt_of_not_ge fun ht => h (boundaryBlock_eq_zero_of_ge ht)⟩

theorem boundaryBlock_snd (t : ℝ) : (boundaryBlock t).2 = boundaryProfile t := rfl

theorem boundaryBlock_fst (t : ℝ) : (boundaryBlock t).1 = t * boundaryProfile t := rfl

theorem tsupport_boundaryBlock_subset : tsupport boundaryBlock ⊆ Icc (20 : ℝ) 90 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact Ioo_subset_Icc_self (mem_Ioo_of_boundaryBlock_ne_zero ht)

/-- On the open plateau the marker is locally constant one (BCG05, BCG06). -/
theorem boundaryProfile_eventuallyEq_one {t : ℝ} (ht : t ∈ Ioo (30 : ℝ) 80) :
    boundaryProfile =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact boundaryProfile_eq_one (Ioo_subset_Icc_self hs)

/-- The early profile constant `P` of (BCG.0): one finite bound for `‖𝓑'‖∞` and `‖𝓑''‖∞`. -/
theorem exists_boundaryBlock_derivative_bounds :
    ∃ P : ℝ, 1 ≤ P ∧ (∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) ∧
      ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P :=
  exists_derivative_bounds_of_constant_tails (contDiff_boundaryBlock.of_le (by norm_cast))
    (fun _ ht => boundaryBlock_eq_zero_of_le ht) (fun _ ht => boundaryBlock_eq_zero_of_ge ht)

theorem hasCompactSupport_boundaryBlock : HasCompactSupport boundaryBlock :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_boundaryBlock_subset

/-- The same constant `P` in the one-variable form `‖𝓑'‖∞, ‖𝓑''‖∞ ≤ P` used by BCG03. -/
theorem exists_boundaryBlock_deriv_bounds :
    ∃ P : ℝ, 1 ≤ P ∧ (∀ t, ‖deriv boundaryBlock t‖ ≤ P) ∧
      ∀ t, ‖deriv (deriv boundaryBlock) t‖ ≤ P := by
  have h2 : ContDiff ℝ (1 + 1) boundaryBlock := contDiff_boundaryBlock.of_le (by norm_cast)
  have hd : ContDiff ℝ 1 (deriv boundaryBlock) := h2.deriv'
  obtain ⟨A, hA⟩ := hd.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hasCompactSupport_boundaryBlock.deriv.comp_left norm_zero)
  obtain ⟨B, hB⟩ := hd.continuous_deriv_one.norm.bddAbove_range_of_hasCompactSupport
    (hasCompactSupport_boundaryBlock.deriv.deriv.comp_left norm_zero)
  refine ⟨max 1 (max A B), le_max_left _ _, ?_, ?_⟩
  · exact fun x => (hA (mem_range_self x)).trans ((le_max_left A B).trans (le_max_right _ _))
  · exact fun x => (hB (mem_range_self x)).trans ((le_max_right A B).trans (le_max_right _ _))

/-- The block is `P`-Lipschitz when `‖𝓑'‖ ≤ P` (normalized value error of BCG03). -/
theorem norm_boundaryBlock_sub_le {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (s t : ℝ) :
    ‖boundaryBlock s - boundaryBlock t‖ ≤ P * |s - t| := by
  have hd : Differentiable ℝ boundaryBlock :=
    contDiff_boundaryBlock.differentiable (by simp)
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hd x) (fun x _ => hP x) (mem_univ t) (mem_univ s)
  rwa [Real.norm_eq_abs] at h

/-- One-block chain-rule bound of BCG01: `‖d𝓑(η)‖ ≤ ‖𝓑'(η)‖ ‖dη‖ ≤ 2P` when `‖dη‖ < 1.01`. -/
theorem norm_boundaryBlock_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (hP1 : 0 ≤ P) (s : ℝ) (L : E →L[ℝ] ℝ)
    (hL : ‖L‖ < 1.01) : ‖(fderiv ℝ boundaryBlock s).comp L‖ ≤ 2 * P := by
  calc ‖(fderiv ℝ boundaryBlock s).comp L‖ ≤ ‖fderiv ℝ boundaryBlock s‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ P * 2 := mul_le_mul (hP s) (by linarith) (norm_nonneg _) hP1
    _ = 2 * P := mul_comm _ _

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Extension by zero of the block of a height defined on an open collar band `O` (BCG01):
if the block vanishes on `O \ T` for a closed `T ⊆ O`, the zero extension is smooth on all of `M`. -/
theorem contMDiff_indicator_boundaryBlock {O T : Set M} {η : M → ℝ} (hO : IsOpen O)
    (hT : IsClosed T) (hTO : T ⊆ O) (hη : ContMDiffOn I 𝓘(ℝ) ∞ η O)
    (hzero : ∀ x ∈ O, x ∉ T → boundaryBlock (η x) = 0) :
    ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (O.indicator (fun x => boundaryBlock (η x))) := by
  have hsupp : tsupport (O.indicator (fun x => boundaryBlock (η x))) ⊆ T := by
    apply closure_minimal _ hT
    intro x hx
    by_contra hxT
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO]; exact hzero x hxO hxT)
    · exact hx (indicator_of_notMem hxO _)
  apply contMDiff_of_tsupport
  intro x hx
  have hxO : x ∈ O := hTO (hsupp hx)
  have hsm : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => boundaryBlock (η x)) x :=
    contDiff_boundaryBlock.contMDiff.contMDiffAt.comp x
      ((hη x hxO).contMDiffAt (hO.mem_nhds hxO))
  apply hsm.congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy _

end Manifold

end DifferentialGeometry.Analysis
