import DifferentialGeometry.Topology.Manifold.SmoothChartEmbeddingPieceOBD

/-!
# A subset with embedded parametrizations at each point is a smooth manifold (lane S-BD2, `_OBD`)

Stage bases of the boundary landing. A subset `B` of a finite-dimensional normed space `H`, with at
every point `y ∈ B` a smooth topological embedding `σ : E → H` (injective differential, `σ 0 = y`)
onto `B ∩ O`
    (`O` open) — the `SmoothProductChartAt_BIFc` data of the whole-fibre layer — is a smooth
`E`-manifold, the inclusion is smooth, and a map into `B` is smooth as soon as its composite with
the inclusion is.

* **`exists_smoothChartedBase_OBD`**: `∃ ChartedSpace E B`, `IsManifold 𝓘(ℝ, E) ∞ B`, smooth
  inclusion, and the smoothness of maps into `B` from the smoothness of their composite.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A subset with embedded parametrizations is a smooth manifold.** -/
theorem exists_smoothChartedBase_OBD (B : Set H)
    (hchart : ∀ y ∈ B, ∃ (σ : E → H) (O : Set H), σ 0 = y ∧ ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧
      (∀ x, Injective (fderiv ℝ σ x)) ∧ IsOpen O ∧ range σ = B ∩ O) :
    ∃ _ : ChartedSpace E B, IsManifold 𝓘(ℝ, E) ∞ B ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (Subtype.val : B → H) ∧
      (∀ y : B, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : B → H) y)) ∧
      ∀ {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
        [TopologicalSpace M] [ChartedSpace HM M] (IM : ModelWithCorners ℝ EM HM) (g : M → B),
        ContMDiff IM 𝓘(ℝ, H) ∞ (fun z => (g z : H)) → ContMDiff IM 𝓘(ℝ, E) ∞ g := by
  classical
  have hpiece : ∀ y : B, ∃ (κ : H → E) (φ : E → H) (O' : Set H), ContDiff ℝ ∞ κ ∧ IsOpen O' ∧
      (y : H) ∈ O' ∧ ContDiffOn ℝ ∞ φ (ball 0 1) ∧
      (∀ b ∈ ball (0 : E) 1, φ b ∈ B ∩ O' ∧ κ (φ b) = b) ∧
      ∀ y' ∈ B ∩ O', κ y' ∈ ball (0 : E) 1 ∧ φ (κ y') = y' := by
    intro y
    obtain ⟨σ, O, h0, hs, he, hi, hO, hr⟩ := hchart y y.2
    obtain ⟨κ, φ, O', hκ, hO', hσ0, hφ, h1, h2⟩ :=
      exists_chartPiece_of_embedding_OBD hs he (hi 0) hO hr
    exact ⟨κ, φ, O', hκ, hO', h0 ▸ hσ0, hφ, h1, h2⟩
  choose κ φ O hκs hO hyO hφs hφ hκ using hpiece
  have hcov : B ⊆ ⋃ y : B, O y := fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩
  refine ⟨linearChartedSpace_OBD B κ hκs φ O 1 hO hφs hφ hκ hcov,
    linearIsManifold_OBD B κ hκs φ O 1 hO hφs hφ hκ hcov,
    contMDiff_linearInclusion_OBD B κ hκs φ O 1 hO hφs hφ hκ hcov,
    mfderiv_linearInclusion_injective_OBD B κ hκs φ O 1 hO hφs hφ hκ hcov, ?_⟩
  intro EM HM M _ _ _ _ _ IM g hg
  let _ := linearChartedSpace_OBD B κ hκs φ O 1 hO hφs hφ hκ hcov
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨((Topology.IsInducing.subtypeVal.continuous_iff).2 hg.continuous).continuousAt, ?_⟩
  have hgx : ContMDiffAt IM 𝓘(ℝ, H) ∞ (fun z => (g z : H)) x := hg x
  have h1 := ((hκs (linearChartIdx_OBD B O hcov (g x))).contMDiff).contMDiffAt.comp x hgx
  exact h1

end DifferentialGeometry.Topology.Manifold
