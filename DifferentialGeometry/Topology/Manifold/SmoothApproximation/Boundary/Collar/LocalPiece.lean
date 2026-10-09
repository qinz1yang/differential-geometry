import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.BlendKernel
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The local step of the collar straightening at a boundary point

`eventually_injOn_isInvertible_of_collarBlend`: let `κ : E₁ → M` parametrise a neighbourhood of a
point of a manifold `M` (possibly with boundary) by a convex set `S` (a half-space region in
collar coordinates), and let maps `f j : M → N` satisfy `Γ ∘ f j ∘ κ = P ∘ X j` on `S`, where `Γ`
is differentiable, `P` is `C¹` near `G z₀`, and the Euclidean maps `X j` converge to `G` in the
sense of the blend kernel (`collarBlend_close`): derivatives uniformly close to `G' z₀` near `z₀`,
values `o(δ j)`-close. If `G' z₀` is injective and `P` fixes `G` to first order, then on one fixed
neighbourhood of `κ z₀` all `f j` are eventually injective with invertible `mfderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- If a composite `L₃ ∘ L₂ ∘ L₁` of linear maps between spaces of the same finite dimension
`dim E₁ = dim E = dim E'` is injective, then the middle factor is invertible. -/
theorem isInvertible_of_injective_comp [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (hd₁ : Module.finrank ℝ E₁ = Module.finrank ℝ E)
    (hd₂ : Module.finrank ℝ E = Module.finrank ℝ E') (L₁ : E₁ →L[ℝ] E) (L₂ : E →L[ℝ] E')
    (L₃ : E' →L[ℝ] F) (h : Injective (L₃.comp (L₂.comp L₁))) : L₂.IsInvertible := by
  have h1 : Injective L₁ := fun u v huv => h (by simp [huv])
  have h1s : Surjective L₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd₁ (f := (L₁ : E₁ →ₗ[ℝ] E))).mp h1
  have h2 : Injective L₂ := by
    intro u v huv
    obtain ⟨u', rfl⟩ := h1s u
    obtain ⟨v', rfl⟩ := h1s v
    exact congrArg L₁ (h (by simp [huv]))
  let e : E ≃ₗ[ℝ] E' := LinearMap.linearEquivOfInjective (L₂ : E →ₗ[ℝ] E') h2 hd₂
  exact ⟨e.toContinuousLinearEquiv, by ext v; rfl⟩


/-- **Local step at a boundary point.** -/
theorem eventually_injOn_isInvertible_of_collarBlend
    (hd₁ : Module.finrank ℝ E₁ = Module.finrank ℝ E)
    (hd₂ : Module.finrank ℝ E = Module.finrank ℝ E')
    {S : Set E₁} (hS : Convex ℝ S) (hSu : UniqueDiffOn ℝ S) {z₀ : E₁}
    {κ : E₁ → M} (hκ : ∀ z ∈ S, MDifferentiableWithinAt 𝓘(ℝ, E₁) I κ S z)
    (hκn : ∀ r > 0, κ '' (S ∩ ball z₀ r) ∈ 𝓝 (κ z₀))
    {Γ : N → F} {f : ℕ → M → N} (hf : ∀ j, ∀ z ∈ S, MDifferentiableAt I J (f j) (κ z))
    (hΓ : ∀ j, ∀ z ∈ S, MDifferentiableAt J 𝓘(ℝ, F) Γ (f j (κ z)))
    {P : F → F} {P' : F → F →L[ℝ] F} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {G : E₁ → F} {L : E₁ →L[ℝ] F}
    (hP : ∀ w ∈ ball (G z₀) ρ₀, HasFDerivAt P (P' w) w) (hP' : ContinuousAt P' (G z₀))
    (hPL : (P' (G z₀)).comp L = L) (hGc : ContinuousWithinAt G S z₀) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    {X : ℕ → E₁ → F} {X' : ℕ → E₁ → E₁ →L[ℝ] F} {δ : ℕ → ℝ} (hδ : ∀ᶠ j in atTop, δ j ≤ 1)
    (hXd : ∀ j, ∀ z ∈ S, HasFDerivWithinAt (X j) (X' j z) S z)
    (hX : ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball z₀ r,
      ‖X' j z - L‖ ≤ ε ∧ ‖X j z - G z‖ ≤ ε * δ j)
    (hfac : ∀ j, ∀ z ∈ S, Γ (f j (κ z)) = P (X j z)) :
    ∃ U ∈ 𝓝 (κ z₀), ∀ᶠ j in atTop,
      InjOn (f j) U ∧ ∀ x ∈ U, (mfderiv I J (f j) x).IsInvertible := by
  obtain ⟨r₁, hr₁, hev₁⟩ := comp_collarBlend_close hGc hδ hX hP' hPL (c / 2) (half_pos hc)
  -- the blends stay in the ball where `P` is differentiable
  obtain ⟨r₂, hr₂, hGb⟩ := Metric.continuousWithinAt_iff.mp hGc (ρ₀ / 2) (half_pos hρ₀)
  obtain ⟨r₃, hr₃, hev₃⟩ := hX (ρ₀ / 2) (half_pos hρ₀)
  set r := min r₁ (min r₂ r₃) with hr
  have hrpos : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  set T := S ∩ ball z₀ r with hT
  have hTS : T ⊆ S := inter_subset_left
  have hTconv : Convex ℝ T := hS.inter (convex_ball _ _)
  have hTu : UniqueDiffOn ℝ T := hSu.inter isOpen_ball
  refine ⟨κ '' T, hκn r hrpos, ?_⟩
  filter_upwards [hev₁, hev₃, hδ] with j hj₁ hj₃ hjδ
  have hT₁ : ∀ z ∈ T, z ∈ S ∩ ball z₀ r₁ := fun z hz =>
    ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  have hXball : ∀ z ∈ T, X j z ∈ ball (G z₀) ρ₀ := by
    intro z hz
    have hz₃ : z ∈ S ∩ ball z₀ r₃ :=
      ⟨hz.1, ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz.2⟩
    have hv := (hj₃ z hz₃).2
    have hδ0 : 0 ≤ δ j := by
      by_contra hneg
      rw [not_le] at hneg
      have := (norm_nonneg _).trans hv
      nlinarith [half_pos hρ₀]
    have h1 : ‖X j z - G z‖ ≤ ρ₀ / 2 := hv.trans
      ((mul_le_mul_of_nonneg_left hjδ (half_pos hρ₀).le).trans (le_of_eq (mul_one _)))
    have h2 : dist (G z) (G z₀) < ρ₀ / 2 := hGb hz.1
      (lt_of_lt_of_le (mem_ball.mp hz.2) ((min_le_right _ _).trans (min_le_left _ _)))
    rw [mem_ball, dist_eq_norm]
    rw [dist_eq_norm] at h2
    calc ‖X j z - G z₀‖ = ‖(X j z - G z) + (G z - G z₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖X j z - G z‖ + ‖G z - G z₀‖ := norm_add_le _ _
      _ < ρ₀ / 2 + ρ₀ / 2 := add_lt_add_of_le_of_lt h1 h2
      _ = ρ₀ := add_halves ρ₀
  have hD : ∀ z ∈ T, HasFDerivWithinAt (fun z => P (X j z)) ((P' (X j z)).comp (X' j z)) T z :=
    fun z hz => (hP _ (hXball z hz)).comp_hasFDerivWithinAt z ((hXd j z hz.1).mono hTS)
  have hclose : ∀ z ∈ T, ‖(P' (X j z)).comp (X' j z) - L‖ ≤ c / 2 := fun z hz => hj₁ z (hT₁ z hz)
  have hinj : InjOn (fun z => P (X j z)) T :=
    injOn_of_hasFDerivWithinAt_close hTconv hD hc hL hclose
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ he
    have h : P (X j z) = P (X j z') := by rw [← hfac j z hz.1, ← hfac j z' hz'.1, he]
    rw [hinj hz hz' h]
  · rintro _ ⟨z, hz, rfl⟩
    have hDinj : Injective ((P' (X j z)).comp (X' j z)) :=
      injective_of_norm_sub_le hc hL (hclose z hz)
    -- the composite `Γ ∘ f j ∘ κ` has derivative `D` within `T`
    have h1 : HasFDerivWithinAt (fun z => Γ (f j (κ z))) ((P' (X j z)).comp (X' j z)) T z :=
      (hD z hz).congr (fun w hw => hfac j w hw.1) (hfac j z hz.1)
    have h2 : HasMFDerivWithinAt 𝓘(ℝ, E₁) 𝓘(ℝ, F) (fun z => Γ (f j (κ z))) T z
        ((mfderiv J 𝓘(ℝ, F) Γ (f j (κ z))).comp
          ((mfderiv I J (f j) (κ z)).comp (mfderivWithin 𝓘(ℝ, E₁) I κ T z))) :=
      (hΓ j z hz.1).hasMFDerivAt.comp_hasMFDerivWithinAt z
        ((hf j z hz.1).hasMFDerivAt.comp_hasMFDerivWithinAt z
          ((hκ z hz.1).mono hTS).hasMFDerivWithinAt)
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, E₁) T z :=
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt).mpr (hTu z hz)
    have heq := hu.eq h2 (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mpr h1)
    have h3 : ((mfderiv J 𝓘(ℝ, F) Γ (f j (κ z)) : E' →L[ℝ] F).comp
        ((mfderiv I J (f j) (κ z) : E →L[ℝ] E').comp
          (mfderivWithin 𝓘(ℝ, E₁) I κ T z : E₁ →L[ℝ] E))) = (P' (X j z)).comp (X' j z) := heq
    have h4 := isInvertible_of_injective_comp (E₁ := E₁) (E := E) (E' := E') (F := F) hd₁ hd₂
      (mfderivWithin 𝓘(ℝ, E₁) I κ T z : E₁ →L[ℝ] E) (mfderiv I J (f j) (κ z) : E →L[ℝ] E')
      (mfderiv J 𝓘(ℝ, F) Γ (f j (κ z)) : E' →L[ℝ] F) (by have h5 := hDinj; rw [← h3] at h5; exact h5)
    exact h4

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
