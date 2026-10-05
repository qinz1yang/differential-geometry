import DifferentialGeometry.Topology.Handle.DiffeomorphExtension
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm
import DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# Rim collar of a closed cell: ambient extension and the collar isotopy

For a diffeomorphism `μ` of the closed cell `ClosedCell (m + 1)` that fixes the boundary sphere
pointwise:

* `exists_partialDiffeomorph_extension_of_fix_boundary`: `μ` extends to a partial diffeomorphism
  `F` of `ℝ^(m+1)` whose source contains the closed unit ball; `F` fixes the unit sphere pointwise
  and maps the closed ball (inside its source) into the closed ball. This is the smooth embedding
  `Subtype.val ∘ μ` fed to `Handle.exists_partialDiffeomorph_extension_closedCell`.
* `exists_ambient_isotopy_eq_closedCell_diffeomorph_near_boundary`: the collar (Alexander-type)
  isotopy. An ambient isotopy `Φ` of `ℝ^(m+1)`, jointly smooth with jointly smooth inverses, starts
  at the identity, fixes the unit sphere pointwise at every time, preserves the closed ball for
  `t ∈ [0, 1]`, and at time `1` agrees with `μ` on an open neighbourhood `V` of the sphere. This is
  `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood`
  (`Topology/Diffeomorph/SphereGerm.lean`: the linear interpolation `(1 - t) p + t F p` near the
  sphere, cut off) applied to the extension `F`.
* `contMDiff_closedCell_family_of_val`: a family of self-maps of the closed cell whose ambient
  values are given by a smooth map of `ℝ × ℝ^(m+1)` is jointly smooth.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

local instance closedCellChartsExt_D2S1RIM :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

local instance closedCellSmoothExt_D2S1RIM : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

/-- A diffeomorphism of the closed cell fixing the boundary sphere pointwise extends to a partial
diffeomorphism of the ambient space whose source contains the closed ball; the extension fixes the
unit sphere pointwise and maps the closed ball into itself. -/
theorem exists_partialDiffeomorph_extension_of_fix_boundary
    (μ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1))
    (hμ : ∀ x : ClosedCell (m + 1), ‖x.val‖ = 1 → μ x = x) :
    ∃ F : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin (m + 1))) ∞,
      closedBall 0 1 ⊆ F.source ∧ (∀ x : ClosedCell (m + 1), F x.val = (μ x).val) ∧
      EqOn F id (sphere 0 1) ∧ MapsTo F (closedBall 0 1 ∩ F.source) (closedBall 0 1) := by
  have hu : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val ∘ μ : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) :=
    (isSmoothEmbedding_closedCell_inclusion m).comp_diffeomorph μ
  obtain ⟨F, hsrc, hF⟩ := Handle.exists_partialDiffeomorph_extension_closedCell m hu
  refine ⟨F, hsrc, hF, ?_, ?_⟩
  · intro y hy
    have hy1 : ‖y‖ = 1 := by simpa using hy
    have h1 := hF ⟨y, hy1.le⟩
    have h2 := hμ ⟨y, hy1.le⟩ hy1
    simp only [comp_apply, h2] at h1
    exact h1
  · intro y hy
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy.1
    have h1 := hF ⟨y, hy1⟩
    simp only [comp_apply] at h1
    change F y ∈ closedBall 0 1
    rw [h1, mem_closedBall_zero_iff]
    exact (μ ⟨y, hy1⟩).property

/-- A family of self-maps of the closed cell, indexed by `ℝ`, whose ambient values are given by a
smooth map `G` of `ℝ × ℝ^(m+1)` is jointly smooth. -/
theorem contMDiff_closedCell_family_of_val {g : ClosedCell (m + 1) × ℝ → ClosedCell (m + 1)}
    {G : ℝ × EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hG : ContDiff ℝ ∞ G) (hg : ∀ x : ClosedCell (m + 1) × ℝ, (g x).val = G (x.2, x.1.val)) :
    ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞ g := by
  have hin : ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡 (m + 1)) ∞
      (fun x : ClosedCell (m + 1) × ℝ => x.1.val) :=
    (isSmoothEmbedding_closedCell_inclusion m).contMDiff.comp contMDiff_fst
  have hval : ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡 (m + 1)) ∞
      (Subtype.val ∘ g) := by
    have h := hG.contMDiff.comp (contMDiff_snd.prodMk_space hin)
    convert h using 1
    funext x
    exact hg x
  refine (ContMDiff.iff_comp_isImmersion
    (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr ⟨?_, hval⟩
  exact continuous_induced_rng.2 hval.continuous

/-- **Rim collar isotopy.** For a diffeomorphism `μ` of the closed cell fixing the boundary sphere
pointwise there is an ambient isotopy `Φ` of `ℝ^(m+1)` (jointly smooth, with jointly smooth
inverses) from the identity, fixing the unit sphere pointwise at all times, preserving the closed
ball for `t ∈ [0, 1]`, whose time-`1` map agrees with `μ` on an open neighbourhood `V` of the
sphere. -/
theorem exists_ambient_isotopy_eq_closedCell_diffeomorph_near_boundary
    (μ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1))
    (hμ : ∀ x : ClosedCell (m + 1), ‖x.val‖ = 1 → μ x = x) :
    ∃ V : Set (EuclideanSpace ℝ (Fin (m + 1))), IsOpen V ∧ sphere 0 1 ⊆ V ∧
      ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
          EuclideanSpace ℝ (Fin (m + 1))),
        ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => (Φ z.1).symm z.2) ∧
        (∀ y, Φ 0 y = y) ∧ (∀ x : ClosedCell (m + 1), x.val ∈ V → Φ 1 x.val = (μ x).val) ∧
        (∀ t y, ‖y‖ = 1 → Φ t y = y) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, Φ t '' closedBall 0 1 = closedBall 0 1 := by
  obtain ⟨F, hsrc, hF, hfix, hmap⟩ := exists_partialDiffeomorph_extension_of_fix_boundary μ hμ
  obtain ⟨V, hV, hSV, -, Φ, hΦ, hΦi, hΦ0, hΦ1, hΦfix, hΦball, -⟩ :=
    PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood F one_pos
      (sphere_subset_closedBall.trans hsrc) hfix hmap isOpen_univ (subset_univ _)
  refine ⟨V, hV, hSV, Φ, hΦ, hΦi, fun y => by rw [hΦ0]; rfl, fun x hx => ?_, fun t y hy => ?_,
    hΦball⟩
  · rw [hΦ1 hx, hF]
  · exact (hΦfix t).1 (by simpa using hy)

end DifferentialGeometry.Topology.Manifold
