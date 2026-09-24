import DifferentialGeometry.Topology.SphereSeparation.HeightDisk
import DifferentialGeometry.Topology.SphereSeparation.CylinderSides
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_height_cylinder_chart {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree),
        IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) = e '' range η ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε := by
  obtain ⟨ε, hε, hεW, η, γ, Φ, D, b, hη, hcompat, hγ, hΦ, hball, hclosed,
    hD, hDa, hb, hbsmooth, hbemb, hbheight, hsource, hsection,
    ⟨δ, hδ, hclear⟩, K, hK, hKW, hfix⟩ :=
      exists_innermost_height_level_disk_family he hne hr hW haW
  have hopen : IsOpen (Φ ⁻¹' thickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1)) :=
    isOpen_thickening.preimage Φ.continuous
  have hsub : closedBall (0 : Schoenflies.Plane) 1 ⊆
      Φ ⁻¹' thickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) := by
    intro x hx
    change Φ x ∈ thickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1)
    exact self_subset_thickening hδ (Φ '' closedBall (0 : Schoenflies.Plane) 1)
      (mem_image_of_mem Φ hx)
  obtain ⟨R, hR, hRU⟩ := DifferentialGeometry.Analysis.exists_larger_closedBall_subset_open
    (by norm_num : (0 : ℝ) ≤ 1) hopen hsub
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let T : ℝ ≃ₘ[ℝ] ℝ :=
    { toEquiv := Equiv.addRight a
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let P := Φ.prodCongr T
  let P' : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ) :=
    { toEquiv := P.toEquiv
      contMDiff_toFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact P.contMDiff
      contMDiff_invFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact P.symm.contMDiff }
  let Ψ := P'.trans (L.symm.toDiffeomorph.trans D)
  have hΨ (x : Schoenflies.Plane) (t : ℝ) : Ψ (x, t) = D (L.symm (Φ x, a + t)) := by
    change D (L.symm (Φ x, t + a)) = _
    rw [add_comm t a]
  have hclear' (x : Schoenflies.Plane) (hx : x ∈ closedBall 0 R)
      (t : ℝ) (ht : t ∈ Icc (-ε) ε) : Ψ (x, t) ∈ range e ↔ x ∈ sphere 0 1 := by
    have ht' : a + t ∈ Icc (a - ε) (a + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hxD : Φ x ∈ cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) :=
      thickening_subset_cthickening _ _ (hRU hx)
    have hmem : Ψ (x, t) ∈ range e ↔ Φ x ∈ range γ := by
      rw [hΨ]
      exact ⟨fun h => (hclear (a + t) ht').subset ⟨h, hxD⟩,
        fun h => ((hclear (a + t) ht').symm.subset h).1⟩
    rw [hmem, ← hΦ]
    exact Φ.injective.mem_set_image
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, hη, ?_, ?_, ?_⟩
  · rintro ⟨x, t⟩
    rw [hΨ, hD]
    exact EuclideanSpace.equivProdLast_symm_last 2 _
  · rw [← hsource]
    ext z
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      obtain rfl : t = 0 := ht
      refine ⟨⟨x, by simpa using hx⟩, ?_⟩
      rw [Function.comp_apply, hb, hΨ, add_zero]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val, 0), ⟨by simpa using x.property, rfl⟩, ?_⟩
      rw [hΨ, Function.comp_apply, hb, add_zero]
      rfl
  · ext p
    rcases p with ⟨x, t⟩
    constructor
    · rintro ⟨hxe, hx, ht⟩
      exact ⟨(hclear' x hx t ht).mp hxe, ht⟩
    · rintro ⟨hx, ht⟩
      have hxR : x ∈ closedBall 0 R := closedBall_subset_closedBall hR.le (sphere_subset_closedBall hx)
      exact ⟨(hclear' x hxR t ht).mpr hx, hxR, ht⟩

theorem exists_innermost_height_cylinder_chart_with_radial_sides {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (d : SphereSides (range e))
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree),
        IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) = e '' range η ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε ∧
        (((∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ d.compactSide ↔ ‖p.1‖ < 1) ∧
          (∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ d.endSide ↔ 1 < ‖p.1‖) ∧
          (∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ closure d.compactSide ↔ ‖p.1‖ ≤ 1)) ∨
        ((∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ d.endSide ↔ ‖p.1‖ < 1) ∧
          (∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ d.compactSide ↔ 1 < ‖p.1‖) ∧
          (∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
            Ψ p ∈ closure d.compactSide ↔ 1 ≤ ‖p.1‖))) := by
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, hη, hheight, hboundary, hsphere⟩ :=
    exists_innermost_height_cylinder_chart he hne hr hW haW
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, hη, hheight, hboundary, hsphere, ?_⟩
  apply d.radial_sides_of_cylinder_chart Ψ.toHomeomorph (by
    rw [← Module.finrank_eq_rank']
    norm_num [Schoenflies.Plane, Module.finrank_fin_fun]) hε zero_lt_one hR
  intro x hx t ht
  have hxR : x ∈ closedBall (0 : Schoenflies.Plane) R := ball_subset_closedBall hx
  have htε : t ∈ Icc (-ε) ε := Ioo_subset_Icc_self ht
  constructor
  · intro hxS
    have hp : (x, t) ∈ sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε :=
      hsphere.subset ⟨hxS, hxR, htε⟩
    exact mem_sphere_zero_iff_norm.mp hp.1
  · intro hxn
    have hp : (x, t) ∈ Ψ ⁻¹' range e ∩
        (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) :=
      hsphere.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hxn, htε⟩
    exact hp.1

end DifferentialGeometry.Topology.SphereSeparation
