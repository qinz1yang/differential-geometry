/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.exists_isPolyhedron_nhdsWithin_inter
    {A B : Set E} {x : E} (hcross : HasPLCrossingAt A B x) :
    ∃ C : Set E, IsPolyhedron C ∧ C ⊆ A ∩ B ∧ C ∈ 𝓝[A ∩ B] x := by
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, -, -, hloc⟩ :=
    hcross.exists_coordinateChart
  obtain ⟨P, hP, hPball, hPnhds⟩ := exists_isHPolytope_subset_mem_nhds
    (E := ℝ × ℝ × ℝ) (x := 0)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  let ℓ₁ : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let ℓ₂ : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let R := (((P ∩ ℓ₁ ⁻¹' {0}) ∩ {z | -α z ≤ 0}) ∩ ℓ₂ ⁻¹' {0}) ∩ {z | -β z ≤ 0}
  have hR : IsPolyhedron R :=
    ((((hP.inter_preimage (isHPolytope_singleton (0 : ℝ)) ℓ₁.toAffineMap).inter_affine_le
      (-α).toAffineMap 0).inter_preimage (isHPolytope_singleton (0 : ℝ))
      ℓ₂.toAffineMap).inter_affine_le (-β).toAffineMap 0).isPolyhedron
  have hRiff (z : ℝ × ℝ × ℝ) : z ∈ R ↔
      z ∈ P ∧ ((z.2.2 = 0 ∧ 0 ≤ α z) ∧ (z.2.1 = 0 ∧ 0 ≤ β z)) := by
    simp only [R, ℓ₁, ℓ₂, mem_inter_iff, mem_preimage, mem_singleton_iff,
      LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply, mem_ofPred_eq,
      neg_nonpos]
    tauto
  have hRball : R ⊆ Metric.ball 0 ρ := fun z hz => hPball ((hRiff z).mp hz).1
  refine ⟨U ∩ φ ⁻¹' R, hφ.isPolyhedron_preimage hR hRball, ?_, ?_⟩
  · intro y hy
    have hmodel := ((hRiff (φ y)).mp hy.2).2
    exact ⟨(hloc y hy.1).1.mpr hmodel.1, (hloc y hy.1).2.mpr hmodel.2⟩
  · have hcont : ContinuousAt φ x :=
      hφ.isPiecewiseAffineOn.continuousOn.continuousAt (hU.mem_nhds hxU)
    have hpre : φ ⁻¹' P ∈ 𝓝 x := hcont.preimage_mem_nhds (hφx.symm ▸ hPnhds)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU),
      mem_nhdsWithin_of_mem_nhds hpre, self_mem_nhdsWithin] with y hyU hyP hyAB
    exact ⟨hyU, (hRiff (φ y)).mpr ⟨hyP, (hloc y hyU).1.mp hyAB.1,
      (hloc y hyU).2.mp hyAB.2⟩⟩

theorem isLocallyPolyhedral_inter_of_hasPLCrossingAt {A B : Set E}
    (hcross : ∀ x ∈ A ∩ B, HasPLCrossingAt A B x) : IsLocallyPolyhedral (A ∩ B) :=
  fun x hx => (hcross x hx).exists_isPolyhedron_nhdsWithin_inter

theorem isPolyhedron_inter_of_isCompact_of_hasPLCrossingAt {A B : Set E}
    (hcompact : IsCompact (A ∩ B))
    (hcross : ∀ x ∈ A ∩ B, HasPLCrossingAt A B x) : IsPolyhedron (A ∩ B) :=
  (isLocallyPolyhedral_inter_of_hasPLCrossingAt hcross).isPolyhedron_of_isCompact hcompact

theorem isPolyhedron_chart_inter_of_isCompact_of_hasPLCrossingAt
    {M : Type*} [TopologicalSpace M] (c : OpenPartialHomeomorph M E) {A B : Set M}
    (hcompact : IsCompact (A ∩ B)) (hsource : A ∩ B ⊆ c.source)
    (hcross : ∀ x ∈ c '' (A ∩ c.source) ∩ c '' (B ∩ c.source),
      HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) x) :
    IsPolyhedron (c '' (A ∩ c.source) ∩ c '' (B ∩ c.source)) := by
  have hsets : (A ∩ c.source) ∩ (B ∩ c.source) = A ∩ B := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2.1⟩,
      fun hx => ⟨⟨hx.1, hsource hx⟩, ⟨hx.2, hsource hx⟩⟩⟩
  have himage : c '' (A ∩ c.source) ∩ c '' (B ∩ c.source) = c '' (A ∩ B) := by
    rw [← c.injOn.image_inter inter_subset_right inter_subset_right, hsets]
  apply isPolyhedron_inter_of_isCompact_of_hasPLCrossingAt _ hcross
  rw [himage]
  exact hcompact.image_of_continuousOn (c.continuousOn.mono hsource)

end DifferentialGeometry.Topology.PiecewiseLinear
