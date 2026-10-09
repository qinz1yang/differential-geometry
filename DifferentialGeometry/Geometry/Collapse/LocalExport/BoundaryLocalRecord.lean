import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# O-WF G2e: a LOCAL base-chart record from a local inverse on the native zero set

`exists_localRecord_OWF` (generic, chain-free). Data: a stage with source `X ⊆ M`, native map
`f₀ : M → H` (values in the native zero set `Z` on `X`), later map `Θ : H → H` (smooth at the
native values, `κ ∘ Θ = κ`, a topological embedding of `f₀(X)`), a chart coordinate
`κ : H →L F`, and at one point `x₀` (`ι x₀ ∈ X`, `ι : N → M`): a smooth local inverse `ζ` of `κ`
on `Z ∩ V` around `w₀ = f₀(ι x₀)` and the open-mapping property of `κ ∘ f₀ ∘ ι` at `x₀`. Then
there are an open `Mk ∋ Θ w₀`, an open `Dset ∋ κ w₀` and `σ₀ = Θ ∘ ζ` smooth on `Dset` with
`σ₀(Dset) ⊆ B ∩ Mk`, `κ ∘ σ₀ = id` on `Dset` and `σ₀ ∘ κ = id` on `B ∩ Mk`, `B = Θ(f₀(X))`:
the record shape of `smoothProductChartAt_of_localRecord_OWF` (with `Wb = B`, `O' = univ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- **A local record at one base point** (see the module docstring). -/
theorem exists_localRecord_OWF {N M H F : Type*} [TopologicalSpace N] [TopologicalSpace M]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : N → M} (hι : Continuous ι) {X : Set M} (hXo : IsOpen (ι ⁻¹' X))
    {f₀ : M → H} (hf₀ : Continuous f₀) {Zs : Set H} (hZ : ∀ p ∈ X, f₀ p ∈ Zs)
    {Θ : H → H} (κ : H →L[ℝ] F) (hκΘ : ∀ x, κ (Θ x) = κ x)
    (hΘs : ∀ p ∈ X, ContDiffAt ℝ ∞ Θ (f₀ p))
    (hemb : Topology.IsEmbedding (fun x : f₀ '' X => Θ x))
    {x₀ : N} (hx₀ : ι x₀ ∈ X) {V : Set H} (hV : IsOpen V) (hw₀V : f₀ (ι x₀) ∈ V) {δ : ℝ}
    (hδ : 0 < δ) {ζ : F → H} (hζs : ContDiffOn ℝ ∞ ζ (ball (κ (f₀ (ι x₀))) δ))
    (hl : ∀ w ∈ Zs ∩ V, ζ (κ w) = w)
    (hmap : map (fun x => κ (f₀ (ι x))) (𝓝 x₀) = 𝓝 (κ (f₀ (ι x₀)))) :
    ∃ (σ₀ : F → H) (Mk : Set H) (Dset : Set F), IsOpen Mk ∧ IsOpen Dset ∧
      Θ (f₀ (ι x₀)) ∈ Mk ∧ κ (f₀ (ι x₀)) ∈ Dset ∧ ContDiffOn ℝ ∞ σ₀ Dset ∧
      (∀ b ∈ Dset, σ₀ b ∈ Θ '' (f₀ '' X) ∩ Mk ∧ κ (σ₀ b) = b) ∧
      (∀ y ∈ Θ '' (f₀ '' X) ∩ Mk, κ y ∈ Dset ∧ σ₀ (κ y) = y) := by
  set w₀ := f₀ (ι x₀) with hw₀
  -- the open mapping step
  let Nset : Set N := ι ⁻¹' X ∩ (f₀ ∘ ι) ⁻¹' V
  have hNo : IsOpen Nset := hXo.inter (hV.preimage (hf₀.comp hι))
  have hN : (fun x => κ (f₀ (ι x))) '' Nset ∈ 𝓝 (κ w₀) := by
    rw [hw₀, ← hmap]
    exact image_mem_map (hNo.mem_nhds ⟨hx₀, hw₀V⟩)
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
  set Dset : Set F := ball (κ w₀) (min δ δ₁) with hDset
  have hDo : IsOpen Dset := isOpen_ball
  have hDδ : Dset ⊆ ball (κ w₀) δ := ball_subset_ball (min_le_left _ _)
  have key : ∀ b ∈ Dset, ∃ p ∈ X, f₀ p ∈ V ∧ κ (f₀ p) = b ∧ ζ b = f₀ p := by
    intro b hb
    obtain ⟨x, ⟨hxX, hxV⟩, hxb⟩ := hball₁ (ball_subset_ball (min_le_right _ _) hb)
    refine ⟨ι x, hxX, hxV, hxb, ?_⟩
    rw [← hxb]
    exact hl _ ⟨hZ _ hxX, hxV⟩
  -- the open set `Mk` from the embedding
  let U' : Set (f₀ '' X) := {x | (x : H) ∈ V ∧ κ x ∈ Dset}
  have hU' : IsOpen U' :=
    (hV.inter (hDo.preimage κ.continuous)).preimage continuous_subtype_val
  obtain ⟨Mk, hMk, hMkU⟩ := hemb.isInducing.isOpen_iff.mp hU'
  have hmemMk : ∀ p ∈ X, f₀ p ∈ V → κ (f₀ p) ∈ Dset → Θ (f₀ p) ∈ Mk := by
    intro p hp hpV hpD
    have h : (⟨f₀ p, p, hp, rfl⟩ : f₀ '' X) ∈ U' := ⟨hpV, hpD⟩
    rw [← hMkU] at h
    exact h
  refine ⟨fun b => Θ (ζ b), Mk, Dset, hMk, hDo, hmemMk _ hx₀ hw₀V (mem_ball_self
    (lt_min hδ hδ₁)), mem_ball_self (lt_min hδ hδ₁), ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨p, hp, -, -, hζb⟩ := key b hb
    have hΘ : ContDiffAt ℝ ∞ Θ (ζ b) := by rw [hζb]; exact hΘs p hp
    exact (hΘ.comp b (hζs.contDiffAt (isOpen_ball.mem_nhds (hDδ hb)))).contDiffWithinAt
  · intro b hb
    obtain ⟨p, hp, hpV, hpb, hζb⟩ := key b hb
    refine ⟨⟨⟨f₀ p, ⟨p, hp, rfl⟩, by change Θ (f₀ p) = Θ (ζ b); rw [hζb]⟩, ?_⟩, ?_⟩
    · change Θ (ζ b) ∈ Mk
      rw [hζb]
      exact hmemMk p hp hpV (by rw [hpb]; exact hb)
    · change κ (Θ (ζ b)) = b
      rw [hκΘ, hζb, hpb]
  · rintro y ⟨⟨x, ⟨p, hp, rfl⟩, rfl⟩, hyMk⟩
    have h : (⟨f₀ p, p, hp, rfl⟩ : f₀ '' X) ∈ (fun x : f₀ '' X => Θ x) ⁻¹' Mk := hyMk
    rw [hMkU] at h
    obtain ⟨hpV, hpD⟩ := h
    refine ⟨by rw [hκΘ]; exact hpD, ?_⟩
    change Θ (ζ (κ (Θ (f₀ p)))) = Θ (f₀ p)
    rw [hκΘ, hl _ ⟨hZ p hp, hpV⟩]

end DifferentialGeometry.Geometry.Collapse
