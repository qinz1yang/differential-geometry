import DifferentialGeometry.Analysis.Calculus.JointCutoffBounds
import DifferentialGeometry.Analysis.Calculus.WeightedCoordinateCutoff
import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockDerivatives
import DifferentialGeometry.Analysis.Calculus.CompositionBounds
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

noncomputable def jointCutoffBlockFamily (Δ : ℝ) (s : ι → ℝ) (f g h χ : ℝ → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) : Option ι → E → WithLp 2 (ℝ × ℝ)
  | none => weightedCoordinateCutoff 1 (jointEdgeCutoff Δ f g h χ u v) v
  | some i => weightedCoordinateCutoff (s i) (edgeCutoff Δ f g (u i) v) (u i)

noncomputable def jointCutoffNetwork (Δ : ℝ) (s : ι → ℝ) (f g h χ : ℝ → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) : E → PiLp 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) :=
  orthogonalBlocks (jointCutoffBlockFamily Δ s f g h χ u v)

theorem contDiff_jointCutoffNetwork {f g h χ : ℝ → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) (hχ : ContDiff ℝ n χ)
    (Δ : ℝ) (s : ι → ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) :
    ContDiff ℝ n (jointCutoffNetwork Δ s f g h χ u v) := by
  apply contDiff_orthogonalBlocks
  intro i
  cases i with
  | none => exact contDiff_weightedCoordinateCutoff (contDiff_jointEdgeCutoff hf hg hh hχ Δ u v) 1 v
  | some i => exact contDiff_weightedCoordinateCutoff (contDiff_edgeCutoff hf hg Δ (u i) v) (s i) (u i)

theorem jointCutoffNetwork_bounds {f g h χ : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ)
    {Δ P : ℝ} (hΔ : 1 ≤ Δ) (hP : 1 ≤ P)
    (hfv : ∀ x, f x ∈ Set.Icc 0 1) (hgv : ∀ x, g x ∈ Set.Icc 0 1)
    (hhv : ∀ x, h x ∈ Set.Icc 0 1) (hχv : ∀ x, χ x ∈ Set.Icc 0 1)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ P)
    (hDh : ∀ x, ‖fderiv ℝ h x‖ ≤ P) (hDχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ P)
    (hDDf : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P)
    (hDDg : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ P)
    (hDDh : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ P)
    (hDDχ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ P)
    (hfsupp : tsupport f ⊆ Set.Icc (-9) 9) (hhsupp : tsupport h ⊆ Set.Icc (1 / 5) 9)
    (s : ι → ℝ) (hs : ∀ i, s i ∈ Set.Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1) (x : E) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * P ^ 3
    ‖jointCutoffNetwork Δ s f g h χ u v x‖ ≤ 20 * Real.sqrt N * Δ ∧
      ‖fderiv ℝ (jointCutoffNetwork Δ s f g h χ u v) x‖ ≤ Real.sqrt N * (2 + 20 * K) ∧
      ‖fderiv ℝ (fderiv ℝ (jointCutoffNetwork Δ s f g h χ u v)) x‖ ≤
        24 * Real.sqrt N * K / Δ := by
  let N : ℝ := (Fintype.card ι : ℝ) + 1
  let K := 10 * N ^ 2 * P ^ 3
  have hΔ0 : 0 < Δ := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hconstants := joint_cutoff_common_constant (n := (Fintype.card ι : ℝ)) (by positivity) hP
  let b := jointCutoffBlockFamily Δ s f g h χ u v
  have hb (i : Option ι) (y : E) :
      ‖b i y‖ ≤ 20 * Δ ∧ ‖fderiv ℝ (b i) y‖ ≤ 2 + 20 * K ∧
        ‖fderiv ℝ (fderiv ℝ (b i)) y‖ ≤ 24 * K / Δ := by
    cases i with
    | none =>
      apply weightedCoordinateCutoff_bounds (contDiff_jointEdgeCutoff hf hg hh hχ Δ u v) v hv
        (by norm_num) hΔ hK (jointEdgeCutoff_mem_Icc hhv hχv Δ f g u v)
      · intro z
        have hbound := (jointEdgeCutoff_derivative_bounds hf hg hh hχ hΔ0 hP hfv hgv hhv hχv
          hDf hDg hDh hDχ hDDf hDDg hDDh hDDχ u v hu hv z).1
        exact hbound.trans (by simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hconstants.2.2.1 (inv_nonneg.mpr hΔ0.le))
      · intro z
        have hbound := (jointEdgeCutoff_derivative_bounds hf hg hh hχ hΔ0 hP hfv hgv hhv hχv
          hDf hDg hDh hDχ hDDf hDDg hDDh hDDχ u v hu hv z).2
        exact hbound.trans (by simpa only [div_eq_mul_inv, inv_pow] using
          mul_le_mul_of_nonneg_right hconstants.2.2.2 (sq_nonneg Δ⁻¹))
      · intro z hz
        exact jointEdgeCutoff_weight_bound hΔ0 hhsupp u v hz
    | some i =>
      apply weightedCoordinateCutoff_bounds (contDiff_edgeCutoff hf hg Δ (u i) v) (u i) (hu i)
        (abs_le.mpr ⟨by linarith [(hs i).1], (hs i).2⟩) hΔ hK
        (edgeCutoff_mem_Icc hfv hgv Δ (u i) v)
      · intro z
        have hbound := (edgeCutoff_derivative_bounds hf hg hΔ0 hP hfv hgv
          hDf hDg hDDf hDDg (u i) v (hu i) hv z).1
        exact hbound.trans (by simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hconstants.1 (inv_nonneg.mpr hΔ0.le))
      · intro z
        have hbound := (edgeCutoff_derivative_bounds hf hg hΔ0 hP hfv hgv
          hDf hDg hDDf hDDg (u i) v (hu i) hv z).2
        exact hbound.trans (by simpa only [div_eq_mul_inv, inv_pow] using
          mul_le_mul_of_nonneg_right hconstants.2.1 (sq_nonneg Δ⁻¹))
      · intro z hz
        exact edgeCutoff_weight_bound hΔ0 hfsupp (u i) v hz
  have hreg (i : Option ι) : ContDiff ℝ 2 (b i) := by
    cases i with
    | none => exact contDiff_weightedCoordinateCutoff (contDiff_jointEdgeCutoff hf hg hh hχ Δ u v) 1 v
    | some i => exact contDiff_weightedCoordinateCutoff (contDiff_edgeCutoff hf hg Δ (u i) v) (s i) (u i)
  have hout := orthogonalBlocks_derivative_bounds hreg (by positivity) (by positivity) (by positivity)
    (fun i z => (hb i z).1) (fun i z => (hb i z).2.1) (fun i z => (hb i z).2.2) x
  have hcard : (Fintype.card (Option ι) : ℝ) = N := by simp [N]
  rw [hcard] at hout
  exact ⟨hout.1.trans_eq (by ring), hout.2.1, hout.2.2.trans_eq (by ring)⟩

theorem jointCutoffNetwork_c1_comp_sub_le {f g h χ : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ)
    {Δ P : ℝ} (hΔ : 1 ≤ Δ) (hP : 1 ≤ P)
    (hfv : ∀ x, f x ∈ Set.Icc 0 1) (hgv : ∀ x, g x ∈ Set.Icc 0 1)
    (hhv : ∀ x, h x ∈ Set.Icc 0 1) (hχv : ∀ x, χ x ∈ Set.Icc 0 1)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ P)
    (hDh : ∀ x, ‖fderiv ℝ h x‖ ≤ P) (hDχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ P)
    (hDDf : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P)
    (hDDg : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ P)
    (hDDh : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ P)
    (hDDχ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ P)
    (hfsupp : tsupport f ⊆ Set.Icc (-9) 9) (hhsupp : tsupport h ⊆ Set.Icc (1 / 5) 9)
    (s : ι → ℝ) (hs : ∀ i, s i ∈ Set.Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V : X → E} {x : X}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    {ε L₀ : ℝ} (hε : 0 ≤ ε) (hL₀ : 0 ≤ L₀)
    (hclose : ‖U x - V x‖ ≤ ε) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ L₀) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * P ^ 3
    let W := jointCutoffNetwork Δ s f g h χ u v
    max ‖W (U x) - W (V x)‖ ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤
      (Real.sqrt N * (2 + 20 * K) + (24 * Real.sqrt N * K / Δ) * L₀) * ε := by
  have hP0 : 0 ≤ P := by linarith
  have hΔ0 : 0 ≤ Δ := by linarith
  have hW := contDiff_jointCutoffNetwork hf hg hh hχ Δ s u v
  have hDW : Differentiable ℝ (fderiv ℝ (jointCutoffNetwork Δ s f g h χ u v)) :=
    (hW.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hb (y : E) := jointCutoffNetwork_bounds hf hg hh hχ hΔ hP hfv hgv hhv hχv
    hDf hDg hDh hDχ hDDf hDDg hDDh hDDχ hfsupp hhsupp s hs u v hu hv y
  exact c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by norm_num)) hDW hU hV
    (by positivity) (by positivity) hL₀ hε (fun y => (hb y).2.1) (fun y => (hb y).2.2)
    hclose hDclose hDV

theorem jointCutoffNetwork_some (Δ : ℝ) (s : ι → ℝ) (f g h χ : ℝ → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (x : E) (i : ι) :
    jointCutoffNetwork Δ s f g h χ u v x (some i) =
      WithLp.toLp 2 (s i * (u i x * edgeCutoff Δ f g (u i) v x),
        s i * edgeCutoff Δ f g (u i) v x) := by
  apply (WithLp.equiv 2 (ℝ × ℝ)).injective
  simp only [jointCutoffNetwork, orthogonalBlocks, jointCutoffBlockFamily,
    weightedCoordinateCutoff, WithLp.equiv_apply, PiLp.toLp_apply,
    WithLp.ofLp_smul, Prod.smul_mk, smul_eq_mul]
  congr 1 <;> ring

theorem jointCutoffNetwork_none (Δ : ℝ) (s : ι → ℝ) (f g h χ : ℝ → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (x : E) :
    jointCutoffNetwork Δ s f g h χ u v x none =
      WithLp.toLp 2 (v x * jointEdgeCutoff Δ f g h χ u v x,
        jointEdgeCutoff Δ f g h χ u v x) := by
  apply (WithLp.equiv 2 (ℝ × ℝ)).injective
  simp only [jointCutoffNetwork, orthogonalBlocks, jointCutoffBlockFamily,
    weightedCoordinateCutoff, WithLp.equiv_apply, PiLp.toLp_apply,
    WithLp.ofLp_smul, Prod.smul_mk, smul_eq_mul, one_mul, mul_one]
  congr 1; ring

end DifferentialGeometry.Analysis
