import DifferentialGeometry.Geometry.Exponential.Flat.AxisSeparation

/-!
# Small-rotation displacements based at an actual point

Translation conjugation recentres the given affine group. Its orbit remains cocompact, its
rotational norms are unchanged, and the resulting spanning set is exactly the actual movements
of the original group at the specified point. This supplies the axis-point spanning step.
-/

set_option autoImplicit false

noncomputable section

open Set Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

omit instFD in
theorem affine_recenter_zero (g : V ≃ᵃⁱ[ℝ] V) (p : V) :
    (MulAut.conj (AffineIsometryEquiv.constVAdd ℝ V (-p)) g) 0 = g p - p := by
  rw [MulAut.conj_apply]
  have hinv : (AffineIsometryEquiv.constVAdd ℝ V (-p))⁻¹ =
      AffineIsometryEquiv.constVAdd ℝ V p := by rw [affine_constVAdd_neg, inv_inv]
  rw [hinv]
  change -p + g (p + 0) = g p - p
  simp only [add_zero, sub_eq_add_neg, add_comm]

theorem smallRotation_displacements_span_at (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R ε : ℝ}
    (hcov : ∀ x : V, ∃ g : G, ‖x - (g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hε : 0 < ε) (p : V) :
    Submodule.span ℝ {v : V | ∃ g : G,
      affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) < ε ∧ (g : V ≃ᵃⁱ[ℝ] V) p - p = v} = ⊤ := by
  let a := AffineIsometryEquiv.constVAdd ℝ V (-p)
  let Φ : (V ≃ᵃⁱ[ℝ] V) →* (V ≃ᵃⁱ[ℝ] V) := (MulAut.conj a).toMonoidHom
  let H := G.map Φ
  have hHcov : ∀ x : V, ∃ g : H, ‖x - (g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R + ‖p‖ := by
    intro x
    obtain ⟨g, hg⟩ := hcov (x + p)
    let g' : H := ⟨Φ g, Subgroup.mem_map_of_mem Φ g.property⟩
    refine ⟨g', ?_⟩
    have hzero : (g' : V ≃ᵃⁱ[ℝ] V) 0 = (g : V ≃ᵃⁱ[ℝ] V) p - p :=
      affine_recenter_zero (g : V ≃ᵃⁱ[ℝ] V) p
    rw [hzero]
    have hdist := norm_add_le (x + p - (g : V ≃ᵃⁱ[ℝ] V) 0)
      ((g : V ≃ᵃⁱ[ℝ] V) 0 - (g : V ≃ᵃⁱ[ℝ] V) p)
    have hnorm : ‖(g : V ≃ᵃⁱ[ℝ] V) 0 - (g : V ≃ᵃⁱ[ℝ] V) p‖ = ‖p‖ := by
      rw [← dist_eq_norm, (g : V ≃ᵃⁱ[ℝ] V).isometry.dist_eq, dist_zero_left]
    rw [hnorm] at hdist
    have heq : x - ((g : V ≃ᵃⁱ[ℝ] V) p - p) =
        (x + p - (g : V ≃ᵃⁱ[ℝ] V) 0) +
          ((g : V ≃ᵃⁱ[ℝ] V) 0 - (g : V ≃ᵃⁱ[ℝ] V) p) := by abel
    rw [heq]
    exact hdist.trans (add_le_add hg le_rfl)
  have hspan := smallRotation_displacements_span H hHcov hε
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro v ⟨g', hrot, hv⟩
  obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp g'.property
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · have hnorm := affineRotationNorm_conjugate g a
    rw [← heq] at hrot
    exact hnorm ▸ hrot
  · rw [← hv, ← heq]
    exact (affine_recenter_zero g p).symm

end DifferentialGeometry.Geometry.FlatSurface
