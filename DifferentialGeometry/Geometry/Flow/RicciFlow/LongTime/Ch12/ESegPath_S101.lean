import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PathDrift_S101

set_option autoImplicit false

/-! # CH12-S101 G2c (helper for the `hflow` producer): the isotopy segment `s ↦ E (μ₁ + s (μ₂ - μ₁), p)` is a
`C¹` path with `h`-speed `≤ η` whenever the `E`-orbit of `p` has speed `≤ η` on `[0,1]` (`hispeed` of the S8 list)
and `μ₁, μ₂ ∈ [0,1]`.  Ball membership (`⊆ B(4ρ_j)`) is a separate (bijectivity + `hsupp`) fact. -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem eseg_path_S101 (H : FiniteVolumeHyperbolicModel.{u}) (E : ℝ × H.Carrier → H.Carrier)
    (hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E) (p : H.Carrier) {η : ℝ}
    (hspd : ∀ μ ∈ Icc (0 : ℝ) 1,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
      H.metric.inner (E (μ, p)) v v ≤ η ^ 2)
    {μ₁ μ₂ : ℝ} (h₁ : μ₁ ∈ Icc (0 : ℝ) 1) (h₂ : μ₂ ∈ Icc (0 : ℝ) 1) :
    ∃ γ : ℝ → H.Carrier, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1) ∧ γ 0 = E (μ₁, p) ∧ γ 1 = E (μ₂, p) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ s = E (μ₁ + s * (μ₂ - μ₁), p)) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) ≤ η ^ 2 := by
  set u : ℝ → H.Carrier := fun μ => E (μ, p) with hudef
  have hu : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ u :=
    hE.comp (contMDiff_id.prodMk contMDiff_const)
  set φ : ℝ → ℝ := fun s => μ₁ + s * (μ₂ - μ₁) with hφdef
  have hφ : ∀ s, HasDerivAt φ (μ₂ - μ₁) s := fun s => by
    have := ((hasDerivAt_id s).mul_const (μ₂ - μ₁)).const_add μ₁
    simpa only [id, one_mul] using this
  have hφs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ := by
    rw [contMDiff_iff_contDiff]; fun_prop
  refine ⟨fun s => u (φ s), ?_, by simp [φ, u], by simp [φ, u], fun s _ => rfl, ?_⟩
  · exact ((hu.comp hφs).contMDiffOn).of_le (by exact_mod_cast le_top)
  · intro s hs
    have hmem : φ s ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hs0, hs1⟩ := hs
      constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    have h := mfderiv_curve_comp_scalar_CX5 (hu.mdifferentiableAt (by simp) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) u (φ s)) (hφ s)
    have h1 := hspd (φ s) hmem
    simp only at h1
    have hc : (μ₂ - μ₁) ^ 2 ≤ 1 := by nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    change H.metric.inner (u (φ s)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => u (φ r)) s (timeVector_CX5 s))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => u (φ r)) s (timeVector_CX5 s)) ≤ _
    rw [h]
    change H.metric.inner _ ((μ₂ - μ₁) • _) ((μ₂ - μ₁) • _) ≤ _
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hn := metric_inner_self_nonneg H.metric (u (φ s)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s)))
    calc (μ₂ - μ₁) * ((μ₂ - μ₁) * H.metric.inner (u (φ s)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s)))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s))))
        = (μ₂ - μ₁) ^ 2 * H.metric.inner (u (φ s)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s)))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s))) := by ring
      _ ≤ 1 * H.metric.inner (u (φ s)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s)))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) u (φ s) (timeVector_CX5 (φ s))) := mul_le_mul_of_nonneg_right hc hn
      _ ≤ η ^ 2 := by rw [one_mul]; exact h1

/-- `E_μ` (bijective, identity outside the ball) maps a point of the ball into the ball. -/
theorem E_mem_ball_S101 (H : FiniteVolumeHyperbolicModel.{u}) (E : ℝ × H.Carrier → H.Carrier) {ρ' : ℝ}
    (hbij : ∀ μ, Function.Bijective (fun p => E (μ, p)))
    (hsupp : ∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint ρ' → E (μ, p) = p) (μ : ℝ) {p : H.Carrier}
    (hp : p ∈ riemannianBallOf H.metric H.basepoint ρ') :
    E (μ, p) ∈ riemannianBallOf H.metric H.basepoint ρ' := by
  by_contra hy
  have h1 : E (μ, E (μ, p)) = E (μ, p) := hsupp μ _ hy
  have h2 : E (μ, p) = p := (hbij μ).1 h1
  exact hy (by rw [h2]; exact hp)

/-- The isotopy segment of `eseg_path_S101`, with its ball membership (the S8 conjuncts `hE`, `hbij`, `hsupp`,
`hispeed` for window `j`, `ρ' = 4 ρ_j`, `p ∈ B(ρ')`): this is the NEW-track path of `hflow` for r, t in one window. -/
theorem eseg_path_ball_S101 (H : FiniteVolumeHyperbolicModel.{u}) (E : ℝ × H.Carrier → H.Carrier)
    (hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E) {ρ' : ℝ}
    (hbij : ∀ μ, Function.Bijective (fun p => E (μ, p)))
    (hsupp : ∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint ρ' → E (μ, p) = p) {p : H.Carrier}
    (hp : p ∈ riemannianBallOf H.metric H.basepoint ρ') {η : ℝ}
    (hspd : ∀ μ ∈ Icc (0 : ℝ) 1,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
      H.metric.inner (E (μ, p)) v v ≤ η ^ 2)
    {μ₁ μ₂ : ℝ} (h₁ : μ₁ ∈ Icc (0 : ℝ) 1) (h₂ : μ₂ ∈ Icc (0 : ℝ) 1) :
    ∃ γ : ℝ → H.Carrier, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1) ∧ γ 0 = E (μ₁, p) ∧ γ 1 = E (μ₂, p) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ riemannianBallOf H.metric H.basepoint ρ') ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) ≤ η ^ 2 := by
  obtain ⟨γ, hγ, h0, h1, hform, hspeed⟩ := eseg_path_S101 H E hE p hspd h₁ h₂
  exact ⟨γ, hγ, h0, h1, fun s hs => (hform s hs) ▸ E_mem_ball_S101 H E hbij hsupp _ hp, hspeed⟩

end GC.LongTime.Ch12
