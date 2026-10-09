import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# FC39 GROUP G, RIMBOX R2 kernel: normalized corner charts of one common scale

External draft 58 §三 R2, disposition D58-4 (lane FC39-G-RIMBOX). For a chart `κ` of a surface
centred at `c` (`κ c = 0`) and ONE scale `l > 0` (the same for both coordinates), the normalized
chart `v ↦ κ⁻¹ (l • v)` on the open square `rimBox r` is a partial diffeomorphism
(`scaledChart_GRIM`), in which `κ` reads `l • v` (`chart_scaledChart_GRIM`); every small scale puts
the CLOSED square `l • [-r, r]²` into the target of `κ` and its preimage into any prescribed open
neighbourhood of `c` (`exists_cornerScale_GRIM`). Applied (binding) to the labelled tube chart
`κ_e` of an actual endpoint with `r = 3`: the corner chart of the final circle region on `(-2, 2)²`
inside the buffer `(-3, 3)²`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem isOpen_rimBox_GRIM (r : ℝ) : IsOpen (rimBox r) := by
  have h : rimBox r = (fun v : ℝ × ℝ => |v.1|) ⁻¹' Iio r ∩ (fun v : ℝ × ℝ => |v.2|) ⁻¹' Iio r :=
    rfl
  rw [h]
  exact (isOpen_Iio.preimage (continuous_fst.abs)).inter (isOpen_Iio.preimage (continuous_snd.abs))

/-- **The scaled corner chart** `v ↦ κ⁻¹ (l • v)` on `rimBox r`, for a chart `κ` of a surface
whose target contains `l • rimBox r`. -/
def scaledChart_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞) (l r : ℝ) (hl : 0 < l)
    (hbox : ∀ v ∈ rimBox r, l • v ∈ κ.target) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) I (ℝ × ℝ) M ∞ where
  toFun v := κ.toPartialEquiv.symm (l • v)
  invFun c := l⁻¹ • κ c
  source := rimBox r
  target := κ.source ∩ (fun c => l⁻¹ • κ c) ⁻¹' rimBox r
  map_source' v hv := by
    refine ⟨κ.toPartialEquiv.map_target (hbox v hv), ?_⟩
    change l⁻¹ • κ (κ.toPartialEquiv.symm (l • v)) ∈ rimBox r
    rw [κ.toPartialEquiv.right_inv (hbox v hv), smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    exact hv
  map_target' c hc := hc.2
  left_inv' v hv := by
    rw [κ.toPartialEquiv.right_inv (hbox v hv), smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  right_inv' c hc := by
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    exact κ.toPartialEquiv.left_inv hc.1
  open_source := isOpen_rimBox_GRIM r
  open_target :=
    ((continuous_const_smul l⁻¹).comp_continuousOn κ.contMDiffOn.continuousOn).isOpen_inter_preimage
      κ.open_source (isOpen_rimBox_GRIM r)
  contMDiffOn_toFun := by
    have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun v : ℝ × ℝ => l • v) :=
      (contDiff_const_smul l).contMDiff
    exact κ.symm.contMDiffOn.comp hs.contMDiffOn fun v hv => hbox v hv
  contMDiffOn_invFun := by
    have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun v : ℝ × ℝ => l⁻¹ • v) :=
      (contDiff_const_smul l⁻¹).contMDiff
    exact hs.comp_contMDiffOn (κ.contMDiffOn.mono fun c hc => hc.1)

theorem scaledChart_apply_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞) (l r : ℝ)
    (hl : 0 < l) (hbox : ∀ v ∈ rimBox r, l • v ∈ κ.target) (v : ℝ × ℝ) :
    scaledChart_GRIM κ l r hl hbox v = κ.toPartialEquiv.symm (l • v) :=
  rfl

theorem scaledChart_source_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞) (l r : ℝ)
    (hl : 0 < l) (hbox : ∀ v ∈ rimBox r, l • v ∈ κ.target) :
    (scaledChart_GRIM κ l r hl hbox).source = rimBox r :=
  rfl

/-- In the scaled chart, `κ` reads `l • v`. -/
theorem chart_scaledChart_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞) (l r : ℝ)
    (hl : 0 < l) (hbox : ∀ v ∈ rimBox r, l • v ∈ κ.target) {v : ℝ × ℝ} (hv : v ∈ rimBox r) :
    κ (scaledChart_GRIM κ l r hl hbox v) = l • v :=
  κ.toPartialEquiv.right_inv (hbox v hv)

theorem scaledChart_mem_source_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞)
    (l r : ℝ) (hl : 0 < l) (hbox : ∀ v ∈ rimBox r, l • v ∈ κ.target) {v : ℝ × ℝ}
    (hv : v ∈ rimBox r) : scaledChart_GRIM κ l r hl hbox v ∈ κ.source :=
  κ.toPartialEquiv.map_target (hbox v hv)

/-- **Small scales.** For a chart `κ` centred at `c` (`κ c = 0`) and an open `O ∋ c`, every small
scale `l` puts the closed box `l • [-r, r]²` into the target and its preimage into `O`. -/
theorem exists_cornerScale_GRIM (κ : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞) {c : M}
    (hc : c ∈ κ.source) (hc0 : κ c = 0) {O : Set M} (hO : IsOpen O) (hcO : c ∈ O) {r : ℝ}
    (hr : 0 < r) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∀ v : ℝ × ℝ, |v.1| ≤ r → |v.2| ≤ r →
      l • v ∈ κ.target ∧ κ.toPartialEquiv.symm (l • v) ∈ O := by
  have h0 : (0 : ℝ × ℝ) ∈ κ.target := hc0 ▸ κ.map_source hc
  have hsymm0 : κ.toPartialEquiv.symm 0 = c := by
    rw [← hc0]
    exact κ.toPartialEquiv.left_inv hc
  have hnhds : κ.target ∩ κ.toPartialEquiv.symm ⁻¹' O ∈ 𝓝 (0 : ℝ × ℝ) := by
    refine Filter.inter_mem (κ.open_target.mem_nhds h0) ?_
    have hca : ContinuousAt κ.toPartialEquiv.symm 0 :=
      (κ.symm.contMDiffOn.continuousOn).continuousAt (κ.open_target.mem_nhds h0)
    exact hca.preimage_mem_nhds (hO.mem_nhds (hsymm0 ▸ hcO))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ε / (2 * r), div_pos hε (by positivity), fun l hl hll v hv1 hv2 => ?_⟩
  have hnorm : ‖l • v‖ < ε := by
    rw [norm_smul, Real.norm_of_nonneg hl.le]
    have hv : ‖v‖ ≤ r := by
      rw [Prod.norm_def]
      exact max_le (by rw [Real.norm_eq_abs]; exact hv1) (by rw [Real.norm_eq_abs]; exact hv2)
    calc l * ‖v‖ ≤ ε / (2 * r) * r := mul_le_mul hll hv (norm_nonneg _) (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  have hmem := hball (mem_ball_zero_iff.mpr hnorm)
  exact ⟨hmem.1, hmem.2⟩

end GC.GraphManifold.Assembly.FC39P0
