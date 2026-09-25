import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Sphere
import DifferentialGeometry.Topology.Diffeomorph.SphereExtension
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm

section

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hsource : sphere (0 : E3) 1 ⊆ A.source)
    (himage : A '' sphere (0 : E3) 1 = sphere (0 : E3) 1)
    (hmap : MapsTo A (closedBall (0 : E3) 1 ∩ A.source) (closedBall (0 : E3) 1)) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ A.source ∧ EqOn D A V := by
  obtain ⟨f, hf, _hfi⟩ := exists_sphere_diffeomorph_of_partialDiffeomorph A hsource himage
  obtain ⟨D, hnorm, hD⟩ := exists_norm_preserving_diffeomorph_extension_sphere f
  let B := A.trans D.symm.toPartialDiffeomorph
  have hBsource : B.source = A.source := by
    ext x
    change (x ∈ A.source ∧ A x ∈ (univ : Set E3)) ↔ x ∈ A.source
    exact ⟨And.left, fun hx => ⟨hx, mem_univ _⟩⟩
  have hBfixed : EqOn B id (sphere (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) = x
    rw [← hf ⟨x, hx⟩, ← hD ⟨x, hx⟩]
    exact D.symm_apply_apply x
  have hDinvnorm (x : E3) : ‖D.symm x‖ = ‖x‖ := by
    rw [← hnorm (D.symm x), D.apply_symm_apply]
  have hBmap : MapsTo B (closedBall (0 : E3) 1 ∩ B.source) (closedBall (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) ∈ closedBall (0 : E3) 1
    rw [mem_closedBall_zero_iff, hDinvnorm]
    have hh := hmap ⟨hx.1, hx.2.1⟩
    exact mem_closedBall_zero_iff.mp hh
  obtain ⟨V, hVo, hSV, hVB, H, _hH, _hHi, _hH0, hH, _hfixed, hball, _hsupport⟩ :=
    B.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood zero_lt_one
      (by rw [hBsource]; exact hsource) hBfixed hBmap isOpen_univ (subset_univ _)
  have hDball : D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_closedBall_zero_iff, hnorm] using hx
    · intro hy
      exact ⟨D.symm y, by simpa only [mem_closedBall_zero_iff, hDinvnorm] using hy, D.apply_symm_apply y⟩
  refine ⟨(H 1).trans D, ?_, V, hVo, hSV, hVB.trans hBsource.le, ?_⟩
  · change (D ∘ H 1) '' closedBall (0 : E3) 1 = _
    rw [image_comp, hball 1 ⟨zero_le_one, le_rfl⟩, hDball]
  · intro x hx
    change D (H 1 x) = A x
    rw [hH hx]
    exact D.apply_symm_apply (A x)

theorem exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hsource : sphere (0 : E3) 1 ⊆ A.source)
    (himage : A '' sphere (0 : E3) 1 = sphere (0 : E3) 1)
    (hmap : MapsTo A ((ball (0 : E3) 1)ᶜ ∩ A.source) (ball (0 : E3) 1)ᶜ) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ A.source ∧ EqOn D A V := by
  obtain ⟨f, hf, _hfi⟩ := exists_sphere_diffeomorph_of_partialDiffeomorph A hsource himage
  obtain ⟨D, hnorm, hD⟩ := exists_norm_preserving_diffeomorph_extension_sphere f
  let B := A.trans D.symm.toPartialDiffeomorph
  have hBsource : B.source = A.source := by
    ext x
    change (x ∈ A.source ∧ A x ∈ (univ : Set E3)) ↔ x ∈ A.source
    exact ⟨And.left, fun hx => ⟨hx, mem_univ _⟩⟩
  have hBfixed : EqOn B id (sphere (0 : E3) 1) := by
    intro x hx
    change D.symm (A x) = x
    rw [← hf ⟨x, hx⟩, ← hD ⟨x, hx⟩]
    exact D.symm_apply_apply x
  have hDinvnorm (x : E3) : ‖D.symm x‖ = ‖x‖ := by
    rw [← hnorm (D.symm x), D.apply_symm_apply]
  have hBmap : MapsTo B ((ball (0 : E3) 1)ᶜ ∩ B.source) (ball (0 : E3) 1)ᶜ := by
    intro x hx
    change D.symm (A x) ∉ ball (0 : E3) 1
    rw [mem_ball_zero_iff, hDinvnorm]
    have hh := hmap ⟨hx.1, hx.2.1⟩
    intro hlt
    exact hh (mem_ball_zero_iff.mpr hlt)
  obtain ⟨V, hVo, hSV, hVB, H, _hH, _hHi, _hH0, hH, _hfixed, hball, _hsupport⟩ :=
    B.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball zero_lt_one
      (by rw [hBsource]; exact hsource) hBfixed hBmap isOpen_univ (subset_univ _)
  have hDball : D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_closedBall_zero_iff, hnorm] using hx
    · intro hy
      exact ⟨D.symm y, by simpa only [mem_closedBall_zero_iff, hDinvnorm] using hy, D.apply_symm_apply y⟩
  refine ⟨(H 1).trans D, ?_, V, hVo, hSV, hVB.trans hBsource.le, ?_⟩
  · change (D ∘ H 1) '' closedBall (0 : E3) 1 = _
    rw [image_comp, hball 1 ⟨zero_le_one, le_rfl⟩, hDball]
  · intro x hx
    change D (H 1 x) = A x
    rw [hH hx]
    exact D.apply_symm_apply (A x)

end DifferentialGeometry.Topology.Manifold

end

end
