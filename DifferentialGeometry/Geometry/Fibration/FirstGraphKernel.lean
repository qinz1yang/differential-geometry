import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockDerivatives
import DifferentialGeometry.Analysis.InnerProductSpace.BlockNormBounds
import DifferentialGeometry.Analysis.Calculus.SecondDerivativeComposition
import DifferentialGeometry.Analysis.Calculus.FlatTailDerivativeBounds
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import DifferentialGeometry.Geometry.Fibration.GraphModelBlocks
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap

/-!
# TCP05 kernel: block graphs over a planar source, compositions, pointwise `C¹` errors

Blueprint `master207B.tex`, TCP05 (`thm:fibration-actual-first-graph`, B:5518–5598). The model
graph `Φ_i : ℝ² → H` of a circle reference is a block graph `a ↦ (φ_t(a))_t` whose listed blocks
are fixed `C²` maps composed with affine maps of the plane. This file has the generic analysis.

* `fderiv_orthogonalBlocks_apply_KA6`, `orthogonalBlocks_support_bounds_KA6`: the components of the
  derivative of a block graph over any normed source, and `‖D‖, ‖D²‖ ≤ √#s · B` when the blocks
  vanish off a finite set `s` and have `C²` bounds `B` on `s`.
* `affine_comp_bounds_KA6` (`‖A‖ ≤ c`: bounds `cB`, `c²B`) and `clm_comp_bounds_KA6`
  (postcomposition with a map of norm at most one).
* `comp_c1_pointwise_KA6`: the pointwise `C¹` composition error of a fixed `C²` map `G`:
  `‖G y₁ − G y₂‖ ≤ A₁ε` and `‖DG(y₁) d₁ − DG(y₂) d₂‖ ≤ (A₁ + A₂L) ε ν` for
  `‖y₁ − y₂‖ ≤ ε`, `‖d₁ − d₂‖ ≤ εν`, `‖d₂‖ ≤ Lν` (directional derivatives along one tangent vector).
* `tcpProfileBound` (`P ≥ 1`): one early constant bounding the first two derivatives of the
  circle bump and of the four profiles of the edge network (`edgeCoordinateProfile`,
  `edgeHeightProfile`, `cgpEdgeH`, `edgeSumProfile`), and at least `sgpProfileBound`,
  `zeroProfileBound`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*} [Fintype κ]
  {V : κ → Type*} [∀ t, NormedAddCommGroup (V t)] [∀ t, InnerProductSpace ℝ (V t)]

omit [Fintype κ] in
/-- The components of the derivative of a block graph are the derivatives of its blocks. -/
theorem fderiv_orthogonalBlocks_apply_KA6 [Finite κ] {φ : ∀ t, E → V t}
    (hφ : ∀ t, Differentiable ℝ (φ t)) (a x : E) (t : κ) :
    fderiv ℝ (orthogonalBlocks φ) a x t = fderiv ℝ (φ t) a x := by
  have := Fintype.ofFinite κ
  have hΦ : Differentiable ℝ (orthogonalBlocks φ) := by
    have h : Differentiable ℝ (fun a => fun t => φ t a) := differentiable_pi.2 hφ
    exact (PiLp.continuousLinearEquiv 2 ℝ V).symm.differentiable.comp h
  let π : PiLp 2 V →L[ℝ] V t := PiLp.proj 2 V t
  have h := π.hasFDerivAt.comp a (hΦ a).hasFDerivAt
  have hfun : (π ∘ orthogonalBlocks φ) = φ t := rfl
  rw [hfun] at h
  rw [h.fderiv]
  rfl

/-- **Orthogonal square summation over the active blocks** (planar or any normed source). -/
theorem orthogonalBlocks_support_bounds_KA6 {φ : ∀ t, E → V t} (hφ : ∀ t, ContDiff ℝ 2 (φ t))
    (s : Finset κ) {B : ℝ} (hB : 0 ≤ B) (hz : ∀ t, t ∉ s → φ t = 0)
    (h1 : ∀ t, t ∈ s → ∀ a, ‖fderiv ℝ (φ t) a‖ ≤ B)
    (h2 : ∀ t, t ∈ s → ∀ a, ‖fderiv ℝ (fderiv ℝ (φ t)) a‖ ≤ B) (a : E) :
    ‖fderiv ℝ (orthogonalBlocks φ) a‖ ≤ Real.sqrt (s.card : ℝ) * B ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks φ)) a‖ ≤ Real.sqrt (s.card : ℝ) * B := by
  have hφd : ∀ t, Differentiable ℝ (φ t) := fun t => (hφ t).differentiable (by norm_num)
  have hcomp2 : ∀ (x y : E) (t : κ),
      fderiv ℝ (fderiv ℝ (orthogonalBlocks φ)) a x y t = fderiv ℝ (fderiv ℝ (φ t)) a x y := by
    intro x y t
    have hΦ : ContDiff ℝ 2 (orthogonalBlocks φ) := contDiff_orthogonalBlocks hφ
    have hDΦ : Differentiable ℝ (fderiv ℝ (orthogonalBlocks φ)) :=
      ((contDiff_succ_iff_fderiv (n := 1)).mp hΦ).2.2.differentiable (by norm_num)
    let π : PiLp 2 V →L[ℝ] V t := PiLp.proj 2 V t
    let Cπ : (E →L[ℝ] PiLp 2 V) →L[ℝ] (E →L[ℝ] V t) :=
      ContinuousLinearMap.compL ℝ E (PiLp 2 V) (V t) π
    have hfun : (Cπ ∘ fderiv ℝ (orthogonalBlocks φ)) = fderiv ℝ (φ t) := by
      funext b
      refine ContinuousLinearMap.ext fun z => ?_
      exact fderiv_orthogonalBlocks_apply_KA6 hφd b z t
    have h := Cπ.hasFDerivAt.comp a (hDΦ a).hasFDerivAt
    rw [hfun] at h
    rw [h.fderiv]
    rfl
  have hzero1 : ∀ t, t ∉ s → ∀ b, fderiv ℝ (φ t) b = 0 := by
    intro t ht b
    rw [hz t ht]
    exact fderiv_const_apply 0
  have hzero2 : ∀ t, t ∉ s → ∀ b, fderiv ℝ (fderiv ℝ (φ t)) b = 0 := by
    intro t ht b
    have : fderiv ℝ (φ t) = fun _ => 0 := funext (hzero1 t ht)
    rw [this]
    exact fderiv_const_apply 0
  constructor
  · refine ContinuousLinearMap.norm_le_sqrt_active_blocks _ s hB (fun x t ht => ?_)
      (fun x t ht => ?_)
    · rw [fderiv_orthogonalBlocks_apply_KA6 hφd]
      exact ((fderiv ℝ (φ t) a).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h1 t ht a) (norm_nonneg x))
    · rw [fderiv_orthogonalBlocks_apply_KA6 hφd, hzero1 t ht a]
      rfl
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have hBx : 0 ≤ B * ‖x‖ := mul_nonneg hB (norm_nonneg x)
    have h := ContinuousLinearMap.norm_le_sqrt_active_blocks
      (fderiv ℝ (fderiv ℝ (orthogonalBlocks φ)) a x) s hBx (fun y t ht => ?_) (fun y t ht => ?_)
    · calc _ ≤ Real.sqrt (s.card : ℝ) * (B * ‖x‖) := h
        _ = Real.sqrt (s.card : ℝ) * B * ‖x‖ := by ring
    · rw [hcomp2]
      refine ((fderiv ℝ (fderiv ℝ (φ t)) a x).le_opNorm y).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg y)
      exact ((fderiv ℝ (fderiv ℝ (φ t)) a).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h2 t ht a) (norm_nonneg x))
    · rw [hcomp2, hzero2 t ht a]
      rfl

end Blocks

section Compositions

variable {E F' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Precomposition with an affine map `a ↦ A a + y₀`, `‖A‖ ≤ c`, multiplies the `C²` bounds by
`c` and `c²`. -/
theorem affine_comp_bounds_KA6 {W : F' → G} (hW : ContDiff ℝ 2 W) {B c : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B)
    (A : E →L[ℝ] F') (hA : ‖A‖ ≤ c) (y₀ : F') (a : E) :
    ‖fderiv ℝ (fun a => W (A a + y₀)) a‖ ≤ c * B ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => W (A a + y₀))) a‖ ≤ c ^ 2 * B := by
  let k : E → F' := fun a => A a + y₀
  have hfun : (fun a => W (A a + y₀)) = W ∘ k := rfl
  have hk : ∀ b, HasFDerivAt k A b := fun b => A.hasFDerivAt.add_const y₀
  have hDk : fderiv ℝ k = fun _ => A := funext fun b => (hk b).fderiv
  have hkd : Differentiable ℝ k := fun b => (hk b).differentiableAt
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hDW : Differentiable ℝ (fderiv ℝ W) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hW).2.2.differentiable (by norm_num)
  have hDDk : fderiv ℝ (fderiv ℝ k) a = 0 := by
    rw [hDk]
    exact fderiv_const_apply A
  rw [hfun]
  constructor
  · rw [fderiv_comp a (hWd (k a)) (hkd a), (hk a).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ W (k a)‖ * ‖A‖ ≤ B * c := mul_le_mul (h1 _) hA (norm_nonneg _) hB
      _ = c * B := mul_comm _ _
  · have hDkd : DifferentiableAt ℝ (fderiv ℝ k) a := by
      rw [hDk]
      exact differentiableAt_const A
    refine (norm_second_fderiv_comp_le hWd hkd (hDW (k a)) hDkd).trans ?_
    rw [hDDk, norm_zero, mul_zero, add_zero, (hk a).fderiv]
    have hA2 : ‖A‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    calc ‖fderiv ℝ (fderiv ℝ W) (k a)‖ * ‖A‖ ^ 2 ≤ B * c ^ 2 :=
          mul_le_mul (h2 _) hA2 (sq_nonneg _) hB
      _ = c ^ 2 * B := mul_comm _ _

/-- Postcomposition with a continuous linear map of norm at most one keeps `C²` bounds. -/
theorem clm_comp_bounds_KA6 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (hL : ‖L‖ ≤ 1) {h : E → G} (hh : ContDiff ℝ 2 h) {B : ℝ}
    (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B) (a : E) :
    ‖fderiv ℝ (L ∘ h) a‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (L ∘ h)) a‖ ≤ B := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hDh : Differentiable ℝ (fderiv ℝ h) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hh).2.2.differentiable (by norm_num)
  have hDL : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  have hDDL : fderiv ℝ (fderiv ℝ L) (h a) = 0 := by
    rw [hDL]
    exact fderiv_const_apply L
  have hB : 0 ≤ B := (norm_nonneg _).trans (h1 a)
  constructor
  · rw [fderiv_comp a L.differentiableAt (hhd a), L.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hL (h1 a) (norm_nonneg _) zero_le_one).trans (by linarith))
  · have hDLd : DifferentiableAt ℝ (fderiv ℝ L) (h a) := by
      rw [hDL]
      exact differentiableAt_const L
    refine (norm_second_fderiv_comp_le L.differentiable hhd hDLd (hDh a)).trans ?_
    rw [hDDL, norm_zero, zero_mul, zero_add, L.fderiv]
    exact (mul_le_mul hL (h2 a) (norm_nonneg _) zero_le_one).trans (by linarith)

/-- **The pointwise `C¹` composition error of a fixed `C²` map** (FC05/FC10 at one point, along
one direction): `‖G y₁ − G y₂‖ ≤ A₁ε` and `‖DG(y₁) d₁ − DG(y₂) d₂‖ ≤ (A₁ + A₂L) ε ν` whenever
`‖y₁ − y₂‖ ≤ ε`, `‖d₁ − d₂‖ ≤ εν` and `‖d₂‖ ≤ Lν`. -/
theorem comp_c1_pointwise_KA6 {W : F' → G} (hW : ContDiff ℝ 2 W) {A₁ A₂ ε L ν : ℝ}
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ A₁) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ A₂)
    (y₁ y₂ d₁ d₂ : F') (hy : ‖y₁ - y₂‖ ≤ ε) (hd : ‖d₁ - d₂‖ ≤ ε * ν) (hd₂ : ‖d₂‖ ≤ L * ν) :
    ‖W y₁ - W y₂‖ ≤ A₁ * ε ∧
      ‖fderiv ℝ W y₁ d₁ - fderiv ℝ W y₂ d₂‖ ≤ (A₁ + A₂ * L) * ε * ν := by
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hDW : Differentiable ℝ (fderiv ℝ W) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hW).2.2.differentiable (by norm_num)
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (h1 y₁)
  have hA₂ : 0 ≤ A₂ := (norm_nonneg _).trans (h2 y₁)
  have hv := (convex_univ : Convex ℝ (Set.univ : Set F')).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hWd y) (fun y _ => h1 y) (Set.mem_univ y₂) (Set.mem_univ y₁)
  have hdd := (convex_univ : Convex ℝ (Set.univ : Set F')).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hDW y) (fun y _ => h2 y) (Set.mem_univ y₂) (Set.mem_univ y₁)
  refine ⟨hv.trans (mul_le_mul_of_nonneg_left hy hA₁), ?_⟩
  have hsplit : fderiv ℝ W y₁ d₁ - fderiv ℝ W y₂ d₂ =
      fderiv ℝ W y₁ (d₁ - d₂) + (fderiv ℝ W y₁ - fderiv ℝ W y₂) d₂ := by
    rw [map_sub, sub_apply]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have ha : ‖fderiv ℝ W y₁ (d₁ - d₂)‖ ≤ A₁ * (ε * ν) :=
    ((fderiv ℝ W y₁).le_opNorm _).trans (mul_le_mul (h1 y₁) hd (norm_nonneg _) hA₁)
  have hε : 0 ≤ ε := (norm_nonneg _).trans hy
  have hb : ‖(fderiv ℝ W y₁ - fderiv ℝ W y₂) d₂‖ ≤ A₂ * ε * (L * ν) := by
    refine ((fderiv ℝ W y₁ - fderiv ℝ W y₂).le_opNorm _).trans ?_
    exact mul_le_mul (hdd.trans (mul_le_mul_of_nonneg_left hy hA₂)) hd₂ (norm_nonneg _)
      (by positivity)
  calc _ ≤ A₁ * (ε * ν) + A₂ * ε * (L * ν) := add_le_add ha hb
    _ = (A₁ + A₂ * L) * ε * ν := by ring

end Compositions

section Profiles

/-- The circle bump has bounded first and second derivatives. -/
theorem exists_circleBump_bounds_KA6 : ∃ P : ℝ, 1 ≤ P ∧
    ∀ v : ℝ², ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ P ∧
      ‖fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) v‖ ≤ P := by
  have hsm : ContDiff ℝ ∞ (circleCutoffBump_LC87 : ℝ² → ℝ) := circleCutoffBump_LC87.contDiff
  have hcs : HasCompactSupport (circleCutoffBump_LC87 : ℝ² → ℝ) :=
    circleCutoffBump_LC87.hasCompactSupport
  have hD : ContDiff ℝ 1 (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) :=
    hsm.fderiv_right (by simp)
  have hDD : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ))) :=
    hD.fderiv_right (by simp)
  obtain ⟨A, hA⟩ := hD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hcs.fderiv (𝕜 := ℝ)).norm
  obtain ⟨B, hB⟩ := hDD.continuous.norm.bddAbove_range_of_hasCompactSupport
    ((hcs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).norm
  refine ⟨max 1 (max A B), le_max_left _ _, fun v => ⟨?_, ?_⟩⟩
  · exact (hA ⟨v, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB ⟨v, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- One early constant for the profiles of the first graph (see the module docstring). -/
theorem exists_tcpProfileBound : ∃ P : ℝ, 1 ≤ P ∧ sgpProfileBound ≤ P ∧
    zeroProfileBound ≤ P ∧
    (∀ v : ℝ², ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ P ∧
      ‖fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) v‖ ≤ P) ∧
    ∀ f ∈ ({edgeCoordinateProfile, edgeHeightProfile, cgpEdgeH, edgeSumProfile} :
      Set (ℝ → ℝ)), (∀ x, ‖fderiv ℝ f x‖ ≤ P) ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P := by
  obtain ⟨Pc, hPc, hc⟩ := exists_circleBump_bounds_KA6
  obtain ⟨Ph, hPh, hDh, hDDh⟩ := exists_derivative_bounds_of_constant_tails (a := 1 / 5)
    (b := 9) (cgpEdgeH_contDiff.of_le (by simp) : ContDiff ℝ 2 cgpEdgeH)
    (fun x hx => cgpEdgeH_eq_zero_of_le hx) (fun x hx => cgpEdgeH_eq_zero_of_ge hx)
  set P : ℝ := Pc + Ph + edgeProfileDerivativeBound + sgpProfileBound + zeroProfileBound
    with hP
  have hPe := edgeProfileDerivativeBound_ge_one
  have hPs := sgpProfileBound_spec.1
  have hPz := zeroProfileBound_spec.1
  refine ⟨P, by linarith, by linarith, by linarith, fun v => ⟨?_, ?_⟩, ?_⟩
  · exact (hc v).1.trans (by linarith)
  · exact (hc v).2.trans (by linarith)
  intro f hf
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have h := edgeProfiles_derivative_le (f := edgeCoordinateProfile) (by simp)
    exact ⟨fun x => (h.1 x).trans (by linarith), fun x => (h.2 x).trans (by linarith)⟩
  · have h := edgeProfiles_derivative_le (f := edgeHeightProfile) (by simp)
    exact ⟨fun x => (h.1 x).trans (by linarith), fun x => (h.2 x).trans (by linarith)⟩
  · exact ⟨fun x => (hDh x).trans (by linarith), fun x => (hDDh x).trans (by linarith)⟩
  · have h := edgeProfiles_derivative_le (f := edgeSumProfile) (by simp)
    exact ⟨fun x => (h.1 x).trans (by linarith), fun x => (h.2 x).trans (by linarith)⟩

/-- The early profile constant `P ≥ 1` of the first graph. -/
def tcpProfileBound : ℝ := Classical.choose exists_tcpProfileBound

theorem tcpProfileBound_spec : 1 ≤ tcpProfileBound ∧ sgpProfileBound ≤ tcpProfileBound ∧
    zeroProfileBound ≤ tcpProfileBound ∧
    (∀ v : ℝ², ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ tcpProfileBound ∧
      ‖fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) v‖ ≤ tcpProfileBound) ∧
    ∀ f ∈ ({edgeCoordinateProfile, edgeHeightProfile, cgpEdgeH, edgeSumProfile} :
      Set (ℝ → ℝ)), (∀ x, ‖fderiv ℝ f x‖ ≤ tcpProfileBound) ∧
        ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ tcpProfileBound :=
  Classical.choose_spec exists_tcpProfileBound

end Profiles

end DifferentialGeometry.Geometry.Collapse
