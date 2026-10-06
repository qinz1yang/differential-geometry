import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Trivial
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition

/-!
# G17 kernel (e): connectedness / standard type of the whole adjusted fibre from the original one
(S-BAUG-D2)

`connected_adjusted_level_of_isotopy_BAUGD` (generic, chain-free): on an open `U ⊆ N` of a smooth
boundaryless manifold, `η, g : U → F` smooth with `‖g − η‖ < 1/800`, a right inverse of `Dη` of
bounded size in a gauge `ν`, `‖Dg − Dη‖ ≤ c ν` with `c K < 1`, a compact trace
`{‖η‖ ≤ 4.01 ℓ}`, a level `‖a‖ < 4ℓ` and `dim F < dim N`: if the ORIGINAL level
`{y ∈ U | η y = a}` is connected, so is the WHOLE adjusted level `{y ∈ U | g y = a}`. This is FC34a
(`exists_embedding_pair_level_on_open_GAFD`: one manifold `S` with smooth embeddings onto the two
levels) with the connectedness transported through `S`. It is the connectedness input of the
circle stage of the whole-fibre layer (`smoothProductChartAt_circle_of_record_BAUGD` asks the
connectedness of the whole fibre); the stage-level hypotheses (`‖g − η‖ < 1/800`, the right
inverse, `‖Dg − Dη‖`) are the chain's.

`exists_embedding_adjusted_level_BAUGD`: with the same hypotheses, if the ORIGINAL level is the
image of a smooth embedding `e₀ : P → N` of a (boundaryless) standard model `P` (circle, `S²`,
`T²`), then the WHOLE adjusted level is the image of a smooth embedding `ψ : P → N`
(`ψ = ι₁ ∘ lift e₀`): the standard-fibre input `ψ` of `smoothProductChartAt_of_record_BAUGD` for
the circle, slim `S²` and slim `T²` stages. Closed twin: `gaf07_slim_whole_fibre_standard_GAFC`
(via `SlimChart.exists_standard_level_embedding_SSTD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

section Connected

variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] [SecondCountableTopology M]

/-- **The whole adjusted level is connected when the original level is** (FC34a, see the module
docstring). -/
theorem connected_adjusted_level_of_isotopy_BAUGD
    (hdim : Module.finrank ℝ F < Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) {η g : M → F}
    (hη : ContMDiffOn I 𝓘(ℝ, F) ∞ η U) (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) {a : F} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hgη : ∀ y ∈ U, ‖g y - η y‖ < 1 / 800) (ν : M → E → ℝ)
    {c K : ℝ} (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y ∈ U, ∃ R : F →L[ℝ] E,
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y ∈ U, ∀ v : E, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v)
    (hQ : IsCompact {y | y ∈ U ∧ ‖η y‖ ≤ 401 / 100 * ℓ})
    (hconn : IsConnected {y | y ∈ U ∧ η y = a}) :
    IsConnected {y | y ∈ U ∧ g y = a} := by
  obtain ⟨S, _, _, _, ι₀, ι₁, h₀, h₁, r₀, r₁⟩ :=
    exists_embedding_pair_level_on_open_GAFD hdim hU hη hg hℓ ha hgη ν hc hcK hright hDg hQ
  have h0pre : IsPreconnected (range ι₀) := by rw [r₀]; exact hconn.isPreconnected
  have hS : IsPreconnected (univ : Set S) := by
    rw [← image_univ] at h0pre
    exact h₀.isEmbedding.toIsInducing.isPreconnected_image.mp h0pre
  have h1pre : IsPreconnected (range ι₁) := by
    rw [← image_univ]
    exact hS.image ι₁ h₁.contMDiff.continuous.continuousOn
  obtain ⟨p, hp⟩ := hconn.nonempty
  have hSne : Nonempty S := by
    have : p ∈ range ι₀ := by rw [r₀]; exact hp
    obtain ⟨s, -⟩ := this
    exact ⟨s⟩
  rw [← r₁]
  exact ⟨range_nonempty ι₁, h1pre⟩

/-- **The whole adjusted level is a standard smooth fibre when the original level is** (FC34a, see
the module docstring): `ψ = ι₁ ∘ lift e₀`. -/
theorem exists_embedding_adjusted_level_BAUGD
    (hdim : Module.finrank ℝ F < Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) {η g : M → F}
    (hη : ContMDiffOn I 𝓘(ℝ, F) ∞ η U) (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) {a : F} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hgη : ∀ y ∈ U, ‖g y - η y‖ < 1 / 800) (ν : M → E → ℝ)
    {c K : ℝ} (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y ∈ U, ∃ R : F →L[ℝ] E,
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y ∈ U, ∀ v : E, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v)
    (hQ : IsCompact {y | y ∈ U ∧ ‖η y‖ ≤ 401 / 100 * ℓ})
    {EF HF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    [TopologicalSpace HF] (IF : ModelWithCorners ℝ EF HF) [IF.Boundaryless]
    {P : Type} [TopologicalSpace P] [ChartedSpace HF P] [IsManifold IF ∞ P]
    (e₀ : P → M) (he₀ : IsSmoothEmbedding IF I ∞ e₀)
    (he₀r : range e₀ = {y | y ∈ U ∧ η y = a}) :
    ∃ ψ : P → M, IsSmoothEmbedding IF I ∞ ψ ∧ range ψ = {y | y ∈ U ∧ g y = a} := by
  obtain ⟨S, _, _, hSm, ι₀, ι₁, h₀, h₁, r₀, r₁⟩ :=
    exists_embedding_pair_level_on_open_GAFD hdim hU hη hg hℓ ha hgη ν hc hcK hright hDg hQ
  have hsub : range e₀ ⊆ range ι₀ := by rw [he₀r, ← r₀]
  have hlift : IsSmoothEmbedding IF
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞ (h₀.lift e₀ hsub) :=
    h₀.isSmoothEmbedding_lift he₀ (by simp) hsub
  have hsurj : ∀ s : S, ∃ z, h₀.lift e₀ hsub z = s := by
    intro s
    have : ι₀ s ∈ range e₀ := by rw [he₀r, ← r₀]; exact mem_range_self s
    obtain ⟨z, hz⟩ := this
    exact ⟨z, h₀.isEmbedding.injective ((h₀.comp_lift hsub z).trans hz)⟩
  refine ⟨ι₁ ∘ h₀.lift e₀ hsub, h₁.comp hlift (by simp), ?_⟩
  rw [range_comp, ← r₁]
  have : range (h₀.lift e₀ hsub) = univ := eq_univ_of_forall fun s => hsurj s
  rw [this, image_univ]

end Connected

end DifferentialGeometry.Geometry.Collapse
