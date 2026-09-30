import DifferentialGeometry.Topology.Cellular.Cellular
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

theorem exists_embeddedClosedCell_in_openEmbedding {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    {φ : EuclideanSpace ℝ (Fin n) → X} (hφ : IsOpenEmbedding φ)
    {K : Set X} (hK : IsCompact K) (hKφ : K ⊆ range φ) :
    ∃ c : EmbeddedClosedCell n X, K ⊆ c.interiorSet ∧ c.carrier ⊆ range φ := by
  have hpre : IsCompact (φ ⁻¹' K) := hφ.isInducing.isCompact_preimage' hK hKφ
  obtain ⟨R, hR, hKR⟩ := hpre.isBounded.subset_ball_lt 0 0
  let s : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    Homeomorph.smulOfNeZero R hR.ne'
  let ψ := φ ∘ s
  have hψ : IsOpenEmbedding ψ := hφ.comp s.isOpenEmbedding
  let g : Disk n → X := fun v => ψ v
  have hgi : g '' diskInterior n = ψ '' ball 0 1 := by
    change (ψ ∘ Subtype.val) '' (Subtype.val ⁻¹' ball 0 1) = _
    rw [image_comp, image_preimage_eq_of_subset]
    simpa only [Subtype.range_coe] using (ball_subset_closedBall :
      ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ closedBall 0 1)
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let c : EmbeddedClosedCell n X :=
    { map := g
      isClosedEmbedding := (hψ.continuous.comp continuous_subtype_val).isClosedEmbedding
        (hψ.injective.comp Subtype.val_injective)
      isOpen_interior := by rw [hgi]; exact hψ.isOpenMap _ isOpen_ball }
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := hKφ hx
    have hv : ‖v‖ < R := mem_ball_zero_iff.mp (hKR hx)
    have hnorm : ‖R⁻¹ • v‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      exact (inv_mul_lt_one₀ hR).mpr hv
    let w : Disk n := ⟨R⁻¹ • v, mem_closedBall_zero_iff.mpr hnorm.le⟩
    refine ⟨w, mem_diskInterior.mpr hnorm, ?_⟩
    change φ (R • (R⁻¹ • v)) = φ v
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  · rintro _ ⟨v, rfl⟩
    exact ⟨s (v : EuclideanSpace ℝ (Fin n)), rfl⟩

theorem exists_embeddedClosedCell_sphere_of_isCompact {n : ℕ}
    {K : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hK : IsCompact K) (hproper : K ≠ univ) :
    ∃ c : EmbeddedClosedCell n (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      K ⊆ c.interiorSet ∧ c.carrier ≠ univ := by
  obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hproper
  let e := sphereComplSingletonHomeomorph q
  let φ := Subtype.val ∘ e.symm
  have hφ : IsOpenEmbedding φ :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  have hrange : range φ = {q}ᶜ := by
    change range (Subtype.val ∘ e.symm) = {q}ᶜ
    rw [range_comp, e.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  obtain ⟨c, hKc, hc⟩ := exists_embeddedClosedCell_in_openEmbedding hφ hK
    (by rw [hrange]; intro x hx heq; exact hq (heq ▸ hx))
  refine ⟨c, hKc, ?_⟩
  intro hu
  have hq' := hc (hu ▸ mem_univ q)
  rw [hrange] at hq'
  exact hq' rfl

end DifferentialGeometry.Topology
