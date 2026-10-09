import DifferentialGeometry.Geometry.Fibration.GenericLaterTransport
import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChartApplications
import DifferentialGeometry.Geometry.Metric.UniformCutoffConsumer

/-!
# Consumers of the naive CGP08 layer (G3 of lane C14-BASES-PRE)

* `cgp08_stage_two_slimCutoff_BPRE`: the stage-two assembly with the tree's ACTUAL third-stage
  cutoff, CFS22/CFS25's slim cutoff `cfsUniformAxisCutoff χ ℓ R u v` with slim blocks that are
  `Q₂`-coordinates; its `π₂`-invariance is `cfsUniformAxisCutoff_comp_of_factor`, and CFS18's
  smoothness of `Ψ₃` at a point `y` transfers to `π₂ y`.
* `cgp08_stage_two_complex_BPRE`: concrete data in `ℂ`: `Q₂ = ℂ`, `Q₃ = ℝ`, `P₃ = 0`, cutoff
  `1` (so `Ψ₃ z = i Im z`), the edge patch on the imaginary axis with `u = v = Im`: `Θ₂` is
  injective on `V₂⁰`, and (RF) holds on the carrier for the identity source map.
* `cgp08_stage_one_complex_BPRE`: `Q₂ = ℝ`, `Q₃ = 0`, `P₂ = 0`: `Θ₁` is injective on the same patch.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis GC.MetricGeometry

/-- **G3 consumer (actual slim cutoff).** The stage-two CGP08 assembly with the third-stage cutoff
`cfsUniformAxisCutoff χ ℓ Rs us vs` of the tree, whose slim blocks are `Q₂`-coordinates; plus the
smoothness transfer `Ψ₃` smooth at `y` ⇒ smooth at `π₂ y`. -/
theorem cgp08_stage_two_slimCutoff_BPRE {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] {M ι : Type*}
    {I : Type*} [Fintype I] {Es : I → Type*} [∀ i, NormedAddCommGroup (Es i)]
    [∀ i, InnerProductSpace ℝ (Es i)] (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {P₃ : H → H} (hP₃ : ∀ z, P₃ z ∈ Q₃)
    (χ : ℝ → ℝ) (ℓs : ℝ) (Rs : I → ℝ) (us : ∀ i, H →L[ℝ] Es i) (vs : I → H →L[ℝ] ℝ)
    (hus : ∀ i z, us i (Q₂.starProjection z) = us i z)
    (hvs : ∀ i z, vs i (Q₂.starProjection z) = vs i z) (g₂ : M → H)
    (Z : Set H) (u : ι → H →L[ℝ] E) (v : ι → H →L[ℝ] ℝ) (R ℓ : ι → ℝ)
    (hu : ∀ i, ∀ q ∈ Q₃, u i q = 0) (hv : ∀ i, ∀ q ∈ Q₃, v i q = 0)
    (hinj : ∀ i, InjOn (u i) (markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i))) :
    (∀ p, Q₂.starProjection (adjustmentMap Q₃ P₃ (cfsUniformAxisCutoff χ ℓs Rs us vs) (g₂ p)) =
      adjustmentMap Q₃ P₃ (cfsUniformAxisCutoff χ ℓs Rs us vs) (Q₂.starProjection (g₂ p))) ∧
    InjOn (adjustmentMap Q₃ P₃ (cfsUniformAxisCutoff χ ℓs Rs us vs))
      (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
    ∀ y, ContDiffAt ℝ ∞ (adjustmentMap Q₃ P₃ (cfsUniformAxisCutoff χ ℓs Rs us vs)) y →
      ContDiffAt ℝ ∞ (adjustmentMap Q₃ P₃ (cfsUniformAxisCutoff χ ℓs Rs us vs))
        (Q₂.starProjection y) := by
  have hψ : ∀ z, cfsUniformAxisCutoff χ ℓs Rs us vs (Q₂.starProjection z) =
      cfsUniformAxisCutoff χ ℓs Rs us vs z := fun z =>
    congrFun (GC.MetricGeometry.cfsUniformAxisCutoff_comp_of_factor χ ℓs Rs us vs
      Q₂.starProjection hus hvs) z
  obtain ⟨h1, h2, -, -, -⟩ := cgp08_stage_two_BPRE Q₂ Q₃ h32 hP₃ hψ g₂ univ Z u v R ℓ hu hv hinj
  exact ⟨h1, h2, fun y hy => contDiffAt_adjustmentMap_starProjection_BPRE Q₂ Q₃ h32 P₃ hψ hy⟩

/-- The imaginary axis of `ℂ`. -/
abbrev imaginaryAxis_BPRE : Set ℂ := {z : ℂ | z.re = 0}

theorem injOn_im_imaginaryAxis_BPRE (R ℓ : ℝ) :
    InjOn Complex.imCLM (markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM R ℓ) := by
  intro z₁ h₁ z₂ h₂ h
  have hre₁ : z₁.re = 0 := h₁.1
  have hre₂ : z₂.re = 0 := h₂.1
  have him : z₁.im = z₂.im := h
  exact Complex.ext (hre₁.trans hre₂.symm) him

theorem im_kills_realAxis_BPRE : ∀ q ∈ realAxis_BPRE, Complex.imCLM q = 0 := fun _ hq =>
  im_eq_zero_of_mem_realAxis_BPRE hq

/-- **G3 consumer (concrete, stage two).** `Q₂ = ℂ`, `Q₃ = ℝ`, `P₃ = 0`, cutoff `1`, edge patch on
the imaginary axis with `u = v = Im`, `R = ℓ = 1`, source map the identity: `Θ₂` is injective on
the patch and the final fibre over `Θ₂ w₀` on the carrier is the stage fibre over `w₀`. -/
theorem cgp08_stage_two_complex_BPRE :
    InjOn (adjustmentMap realAxis_BPRE (fun _ => 0) (fun _ => 1))
      (⋃ _k : Unit, markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1) ∧
    ∀ w₀ ∈ ⋃ _k : Unit, markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1,
      {p : ℂ | p ∈ univ ∩ (fun q => (⊤ : Submodule ℝ ℂ).starProjection (id q)) ⁻¹'
          (⋃ _k : Unit, markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1) ∧
        (⊤ : Submodule ℝ ℂ).starProjection
            (adjustmentMap realAxis_BPRE (fun _ => 0) (fun _ => 1) (id p)) =
          adjustmentMap realAxis_BPRE (fun _ => 0) (fun _ => 1) w₀} =
      {p : ℂ | p ∈ univ ∩ (fun q => (⊤ : Submodule ℝ ℂ).starProjection (id q)) ⁻¹'
          (⋃ _k : Unit, markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1) ∧
        (⊤ : Submodule ℝ ℂ).starProjection (id p) = w₀} := by
  have hψ : ∀ z, (fun _ : ℂ => (1 : ℝ)) ((⊤ : Submodule ℝ ℂ).starProjection z) =
      (fun _ : ℂ => (1 : ℝ)) z := fun _ => rfl
  obtain ⟨-, h2, -, h4, -⟩ := cgp08_stage_two_BPRE (⊤ : Submodule ℝ ℂ) realAxis_BPRE le_top
    (P₃ := fun _ => 0) (ψ₃ := fun _ => 1) (fun _ => realAxis_BPRE.zero_mem) hψ id univ imaginaryAxis_BPRE
    (fun _ : Unit => Complex.imCLM) (fun _ : Unit => Complex.imCLM) (fun _ => 1) (fun _ => 1)
    (fun _ => im_kills_realAxis_BPRE) (fun _ => im_kills_realAxis_BPRE)
    (fun _ => injOn_im_imaginaryAxis_BPRE 1 1)
  exact ⟨h2, h4⟩

/-- **G3 consumer (concrete, stage one).** `Q₂ = ℝ ⊆ ℂ`, `Q₃ = 0`, `P₂ = P₃ = 0`, cutoffs `1`:
`Θ₁ = Ψ₃ ∘ Ψ₂` is injective on the imaginary-axis patch, and `Im ∘ E = Im` for `E = Θ₁ ∘ id`. -/
theorem cgp08_stage_one_complex_BPRE :
    InjOn (fun w => adjustmentMap (⊥ : Submodule ℝ ℂ) (fun _ => 0) (fun _ => 1)
        (adjustmentMap realAxis_BPRE (fun _ => 0) (fun _ => 1) w))
      (⋃ _k : Unit, markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1) ∧
    ∀ p : ℂ, Complex.imCLM (adjustmentMap (⊥ : Submodule ℝ ℂ) (fun _ => 0) (fun _ => 1)
        (adjustmentMap realAxis_BPRE (fun _ => 0) (fun _ => 1) (id p))) = Complex.imCLM (id p) := by
  obtain ⟨h1, -, -, h4⟩ := cgp08_stage_one_BPRE realAxis_BPRE (⊥ : Submodule ℝ ℂ) bot_le
    (P₂ := fun _ => 0) (P₃ := fun _ => 0) (fun _ => realAxis_BPRE.zero_mem)
    (fun _ => (⊥ : Submodule ℝ ℂ).zero_mem) (fun _ => 1) (fun _ => 1) id univ imaginaryAxis_BPRE
    (fun _ : Unit => Complex.imCLM) (fun _ : Unit => Complex.imCLM) (fun _ => 1) (fun _ => 1)
    (fun _ => im_kills_realAxis_BPRE) (fun _ => im_kills_realAxis_BPRE)
    (fun _ => injOn_im_imaginaryAxis_BPRE 1 1)
  exact ⟨h1, fun p => h4 () p⟩

/-- **G3 consumer (threshold 5).** The point `i` (full marker `Im = 1`, `|η| = 1 < 5`, zero error)
lies in the imaginary-axis patch. -/
theorem I_mem_markedPatch_BPRE :
    Complex.I ∈ markedPatch_BPRE imaginaryAxis_BPRE Complex.imCLM Complex.imCLM 1 1 :=
  mem_markedPatch_of_full_marker_BPRE (M := ℂ) imaginaryAxis_BPRE Complex.imCLM
    Complex.imCLM_norm.le Complex.imCLM Complex.imCLM_norm.le id id (fun z => z.im) (fun _ => 1)
    (c := 0) one_pos le_rfl (by simp) (by simp) (by simp) (by norm_num) (by simp) (by norm_num)
    (by norm_num) (by norm_num)

end DifferentialGeometry.Geometry.Collapse
