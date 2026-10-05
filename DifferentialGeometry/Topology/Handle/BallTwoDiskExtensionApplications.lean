import DifferentialGeometry.Topology.Handle.BallTwoDiskExtension
import DifferentialGeometry.Topology.Handle.BallIsotopy

/-!
# Two boundary disks of the closed 3-cell (consumer of group G2 of lane ASM-L1)

The ball model of L1 is `ClosedCell 3` with its `𝓡∂ 3` structure. A diffeomorphism of `ℝ³`
preserving the closed unit ball restricts to a diffeomorphism of `ClosedCell 3`
(`closedCellDiffeomorphOfImageEq`), so the two-disk normalization
`exists_diffeomorph_closedBall_eqOn_two_boundary_disks` gives a self-diffeomorphism of the closed
3-cell which agrees with the two prescribed germs near the cap and near `K₁`
(`exists_closedCell_diffeomorph_eqOn_two_boundary_disks`, the form route A consumes).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- A diffeomorphism of `ℝ³` preserving the closed unit ball, restricted to the closed 3-cell. -/
def closedCellDiffeomorphOfImageEq
    (Q : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hQ : Q '' closedBall 0 1 = closedBall 0 1) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (ClosedCell 3) (ClosedCell 3) ∞ := by
  have hmem (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ ≤ 1 ↔ ‖Q x‖ ≤ 1 := by
    constructor
    · intro hx
      have h : Q x ∈ Q '' closedBall 0 1 := ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
      rw [hQ] at h
      exact mem_closedBall_zero_iff.mp h
    · intro hx
      have h : Q x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := mem_closedBall_zero_iff.mpr hx
      rw [← hQ] at h
      obtain ⟨y, hy, hyx⟩ := h
      rw [← Q.injective hyx]
      exact mem_closedBall_zero_iff.mp hy
  let e : ClosedCell 3 ≃ ClosedCell 3 := Q.toEquiv.subtypeEquiv (fun x => hmem x)
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding 2).isImmersion).mpr
    exact ⟨(Q.continuous.comp continuous_subtype_val).subtype_mk _,
      Q.contMDiff.comp (closedCellInclusion_contMDiff 2)⟩
  · apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding 2).isImmersion).mpr
    exact ⟨(Q.symm.continuous.comp continuous_subtype_val).subtype_mk _,
      Q.symm.contMDiff.comp (closedCellInclusion_contMDiff 2)⟩

theorem closedCellDiffeomorphOfImageEq_val
    (Q : EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hQ : Q '' closedBall 0 1 = closedBall 0 1) (x : ClosedCell 3) :
    ((closedCellDiffeomorphOfImageEq Q hQ x : ClosedCell 3) : EuclideanSpace ℝ (Fin 3)) =
      Q (x : EuclideanSpace ℝ (Fin 3)) :=
  rfl

/-- **Consumer (closed 3-cell form of G2).** Under the hypotheses of
`exists_diffeomorph_closedBall_eqOn_two_boundary_disks`, a self-diffeomorphism of `ClosedCell 3`
agrees with `F₀` on the cell points of a neighbourhood of the round cap and with `F₁` on the cell
points of a neighbourhood of `K₁`. -/
theorem exists_closedCell_diffeomorph_eqOn_two_boundary_disks
    (F₀ F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) ∞)
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ₀ : closedBall 0 R ⊆ φ₀.source) (hφ₁ : closedBall 0 R ⊆ φ₁.source)
    (hF₀ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₀ x : EuclideanSpace ℝ (Fin 3)) ∈ F₀.source)
    (hF₁ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₁ x : EuclideanSpace ℝ (Fin 3)) ∈ F₁.source)
    (hbd₀ : MapsTo F₀ (sphere 0 1 ∩ F₀.source) (sphere 0 1))
    (hbd₁ : MapsTo F₁ (sphere 0 1 ∩ F₁.source) (sphere 0 1))
    (hside₀ : MapsTo F₀ (closedBall 0 1 ∩ F₀.source) (closedBall 0 1))
    (hside₁ : MapsTo F₁ (closedBall 0 1 ∩ F₁.source) (closedBall 0 1))
    (p₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {a : ℝ} (ha : -1 < a) (ha' : a < 1)
    (hcap : {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆ φ₀ '' ball 0 R)
    (hφ₁cap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(φ₁ x : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a)
    (hdisj : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ →
          F₁ (φ₁ x : EuclideanSpace ℝ (Fin 3)) ≠ F₀ (θ : EuclideanSpace ℝ (Fin 3)))
    (hori : 0 < (fderiv ℝ F₀ (p₀ : EuclideanSpace ℝ (Fin 3))).det *
      (fderiv ℝ F₁ (φ₁ 0 : EuclideanSpace ℝ (Fin 3))).det)
    {K₁ : Set (EuclideanSpace ℝ (Fin 3))} (hK₁ : IsCompact K₁)
    (hK₁φ : K₁ ⊆ Subtype.val '' (φ₁ '' ball 0 R)) :
    ∃ D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (ClosedCell 3) (ClosedCell 3) ∞,
      (∃ V₀ : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V₀ ∧
        Subtype.val '' {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
          a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p₀ : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆ V₀ ∧
        V₀ ⊆ F₀.source ∧ ∀ x : ClosedCell 3, (x : EuclideanSpace ℝ (Fin 3)) ∈ V₀ →
          (D x : EuclideanSpace ℝ (Fin 3)) = F₀ (x : EuclideanSpace ℝ (Fin 3))) ∧
      (∃ V₁ : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V₁ ∧ K₁ ⊆ V₁ ∧ V₁ ⊆ F₁.source ∧
        ∀ x : ClosedCell 3, (x : EuclideanSpace ℝ (Fin 3)) ∈ V₁ →
          (D x : EuclideanSpace ℝ (Fin 3)) = F₁ (x : EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨Q, hQ, ⟨V₀, hV₀, hKV₀, hV₀F, hQ₀⟩, ⟨V₁, hV₁, hKV₁, hV₁F, hQ₁⟩⟩ :=
    exists_diffeomorph_closedBall_eqOn_two_boundary_disks F₀ F₁ φ₀ φ₁ hR hφ₀ hφ₁ hF₀ hF₁ hbd₀
      hbd₁ hside₀ hside₁ p₀ ha ha' hcap hφ₁cap hdisj hori hK₁ hK₁φ
  exact ⟨closedCellDiffeomorphOfImageEq Q hQ,
    ⟨V₀, hV₀, hKV₀, hV₀F, fun x hx => hQ₀ hx⟩, ⟨V₁, hV₁, hKV₁, hV₁F, fun x hx => hQ₁ hx⟩⟩

end DifferentialGeometry.Topology.Handle
