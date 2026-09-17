import DifferentialGeometry.Topology.Handle.BallPairExtension
import DifferentialGeometry.Topology.Manifold.SectorRoundingComparison
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable (m : ℕ)

private local instance :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + 1))) = (m + 1) + 1) := ⟨by simp⟩

theorem exists_diffeomorph_eqOn_of_diffeomorphic_balls
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hD₀ : D₀ '' closedBall 0 1 = A) (hD₁ : D₁ '' closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage A B)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ : closedBall 0 R ⊆ φ.source)
    (hsource : ∀ x ∈ closedBall 0 R, D₀ (φ x).val ∈ c.source)
    {K : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} (hK : IsCompact K)
    (hKφ : K ⊆ D₀ '' (Subtype.val '' (φ '' ball 0 R))) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' A = B ∧ ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ c.source ∧ EqOn Q c V := by
  let E := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let F := (D₀.toPartialDiffeomorph.trans c).trans D₁.symm.toPartialDiffeomorph
  have hFs : F.source = D₀ ⁻¹' c.source := by
    ext x
    change ((x ∈ (univ : Set E) ∧ D₀ x ∈ c.source) ∧ c (D₀ x) ∈ (univ : Set E)) ↔ _
    simp
  have hF (x : E) : F x = D₁.symm (c (D₀ x)) := rfl
  have h₀ (x : E) : D₀ x ∈ A ↔ x ∈ closedBall 0 1 := by
    rw [← hD₀]
    exact D₀.injective.mem_set_image
  have h₁ (x : E) : D₁.symm x ∈ closedBall 0 1 ↔ x ∈ B := by
    rw [← hD₁]
    exact (Set.mem_image_iff_of_inverse D₁.symm_apply_apply D₁.apply_symm_apply).symm
  have hFi : F.toOpenPartialHomeomorph.IsImage (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    change F x ∈ closedBall 0 1 ↔ x ∈ closedBall 0 1
    rw [hF, h₁]
    have hx' : D₀ x ∈ c.source := by
      have hs : x ∈ F.source := hx
      rwa [hFs] at hs
    exact (hc hx').trans (h₀ x)
  have hFb : MapsTo F (closedBall 0 1 ∩ F.source) (closedBall 0 1) :=
    fun x hx => (hFi hx.2).mpr hx.1
  have hFsphere : MapsTo F (sphere 0 1 ∩ F.source) (sphere 0 1) := by
    intro x hx
    have h := hFi.frontier hx.2
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.mpr hx.1
  have hFφ (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : x ∈ closedBall 0 R) :
      (φ x).val ∈ F.source := by
    rw [hFs]
    exact hsource x hx
  have hK' : IsCompact (D₀.symm '' K) := hK.image D₀.symm.continuous
  have hKφ' : D₀.symm '' K ⊆ Subtype.val '' (φ '' ball 0 R) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hKφ hy
    simpa only [D₀.symm_apply_apply] using hw
  obtain ⟨q, hq, U, hU, hKU, hUF, heq⟩ :=
    F.exists_diffeomorph_eqOn_of_boundary_disk_chart m φ hR hφ hFφ hFsphere hFb hK' hKφ'
  let Q := (D₀.symm.trans q).trans D₁
  let V := D₀ '' U
  refine ⟨Q, ?_, V, D₀.toHomeomorph.isOpenMap U hU, ?_, ?_, ?_⟩
  · rw [← hD₀, ← hD₁]
    change (D₁ ∘ q ∘ D₀.symm) '' (D₀ '' closedBall 0 1) = D₁ '' closedBall 0 1
    rw [image_comp, image_comp, image_image D₀.symm D₀]
    simp only [D₀.symm_apply_apply, image_id']
    rw [hq]
  · intro x hx
    exact ⟨D₀.symm x, hKU (mem_image_of_mem D₀.symm hx), D₀.apply_symm_apply x⟩
  · rintro x ⟨y, hy, rfl⟩
    have h := hUF hy
    rwa [hFs] at h
  · rintro x ⟨y, hy, rfl⟩
    change D₁ (q (D₀.symm (D₀ y))) = c (D₀ y)
    rw [D₀.symm_apply_apply, heq hy, hF, D₁.apply_symm_apply]


theorem exists_diffeomorph_eqOn_neighborhood_of_boundary_disk
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hD₀ : D₀ '' closedBall 0 1 = A) (hD₁ : D₁ '' closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage A B)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    (hφ : closedBall 0 1 ⊆ φ.source)
    (hsource : ∀ x ∈ closedBall 0 1, D₀ (φ x).val ∈ c.source) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' A = B ∧ ∃ V, IsOpen V ∧
        D₀ '' (Subtype.val '' (φ '' closedBall 0 1)) ⊆ V ∧ V ⊆ c.source ∧ EqOn Q c V := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let f : E → EuclideanSpace ℝ (Fin ((m + 1) + 1)) := fun x => D₀ (φ x).val
  have hf : ContinuousOn f φ.source := D₀.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn φ.toOpenPartialHomeomorph.continuousOn)
  let U := φ.source ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.isOpen_inter_preimage φ.open_source c.open_source
  have hballU : closedBall 0 1 ⊆ U := fun x hx => ⟨hφ hx, hsource x hx⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : E) 1).exists_thickening_subset_open hU hballU
  rw [thickening_closedBall hδ zero_le_one] at hδU
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRU : closedBall (0 : E) R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith : R < δ + 1)).trans hδU
  let K := D₀ '' (Subtype.val '' (φ '' closedBall 0 1))
  have hK : IsCompact K := by
    exact (((isCompact_closedBall (0 : E) 1).image_of_continuousOn
      (φ.toOpenPartialHomeomorph.continuousOn.mono hφ)).image continuous_subtype_val).image D₀.continuous
  have hKφ : K ⊆ D₀ '' (Subtype.val '' (φ '' ball 0 R)) :=
    image_mono (image_mono (image_mono (closedBall_subset_ball hR)))
  exact c.exists_diffeomorph_eqOn_of_diffeomorphic_balls m D₀ D₁ hD₀ hD₁ hc φ
    (zero_lt_one.trans hR) (fun x hx => (hRU hx).1) (fun x hx => (hRU hx).2) hK hKφ


theorem exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk
    {P : Type*} [TopologicalSpace P]
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin ((m + 1) + 1))) (P × (ℝ × ℝ)))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hc : c.toOpenPartialHomeomorph.IsImage A B) (ε : ℝ)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    (hD₀ : D₀ '' closedBall 0 1 = e.smoothAbsQuadrantSet A ε)
    (hD₁ : D₁ '' closedBall 0 1 =
      (c.symm.toOpenPartialHomeomorph.trans e).smoothAbsQuadrantSet B ε)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    (hφ : closedBall 0 1 ⊆ φ.source)
    (hsource : ∀ x ∈ closedBall 0 1, D₀ (φ x).val ∈ c.source) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' e.smoothAbsQuadrantSet A ε =
        (c.symm.toOpenPartialHomeomorph.trans e).smoothAbsQuadrantSet B ε ∧
      ∃ V, IsOpen V ∧ D₀ '' (Subtype.val '' (φ '' closedBall 0 1)) ⊆ V ∧
        V ⊆ c.source ∧ EqOn Q c V := by
  exact c.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk m D₀ D₁ hD₀ hD₁
    (hc.smoothAbsQuadrantSet e ε) φ hφ hsource

end PartialDiffeomorph
