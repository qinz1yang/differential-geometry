import DifferentialGeometry.Topology.Manifold.CylinderCollar.Coordinates
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cylinderRadialGerm (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  ((cylinderExponentialChart v).symm.trans A).trans (cylinderExponentialChart v)

theorem cylinderRadialGerm_source (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (x : E3) :
    x ∈ (cylinderRadialGerm v A).source ↔ x ≠ 0 ∧ (cylinderExponentialChart v).symm x ∈ A.source := by
  change ((x ∈ (cylinderExponentialChart v).target ∧ _ ∈ A.source) ∧ _ ∈ (cylinderExponentialChart v).source) ↔ _
  rw [cylinderExponentialChart_target, cylinderExponentialChart_source]
  simp only [mem_compl_iff, mem_singleton_iff, OpenPartialHomeomorph.symm_symm, mem_univ, and_true, ne_eq,
    PartialDiffeomorph.symm_toPartialEquiv, and_congr_right_iff]
  intro _
  rfl

theorem cylinderRadialGerm_sphere_source (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source) :
    sphere (0 : E3) 1 ⊆ (cylinderRadialGerm v A).source := by
  intro x hx
  rw [cylinderRadialGerm_source]
  refine ⟨ne_zero_of_mem_unit_sphere ⟨x, hx⟩, ?_⟩
  rw [cylinderExponentialChart_symm_sphere v ⟨x, hx⟩]
  exact hsource _

theorem cylinderRadialGerm_sphere_fixed (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0)) :
    EqOn (cylinderRadialGerm v A) id (sphere (0 : E3) 1) := by
  intro x hx
  change cylinderExponentialChart v (A ((cylinderExponentialChart v).symm x)) = x
  rw [cylinderExponentialChart_symm_sphere v ⟨x, hx⟩, hfixed, cylinderExponentialChart_zero]

theorem cylinderRadialGerm_mapsTo_closedBall (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0) :
    MapsTo (cylinderRadialGerm v A)
      (closedBall (0 : E3) 1 ∩ (cylinderRadialGerm v A).source) (closedBall (0 : E3) 1) := by
  intro x hx
  obtain ⟨hx0, hxA⟩ := (cylinderRadialGerm_source v A x).mp hx.2
  have hq : ((cylinderExponentialChart v).symm x).2 ≤ 0 := by
    rw [cylinderExponentialChart_symm_apply v x hx0]
    exact Real.log_nonpos (norm_nonneg x) (mem_closedBall_zero_iff.mp hx.1)
  change ‖cylinderExponentialChart v (A ((cylinderExponentialChart v).symm x)) - 0‖ ≤ 1
  rw [sub_zero, norm_cylinderExponentialChart]
  exact Real.exp_le_one_iff.mpr (hside _ hxA hq)

theorem exists_supported_radial_diffeomorph_eq_cylinder_germ
    (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ F : E3 ≃ₘ[ℝ] E3,
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ (cylinderRadialGerm v A).source ∧
        EqOn F (cylinderRadialGerm v A) V ∧ F 0 = 0 ∧
        ∃ K : Set E3, IsCompact K ∧ K ⊆ {x : E3 | Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u} ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  let O : Set E3 := {x | Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u}
  have hO : IsOpen O := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hSO : sphere (0 : E3) 1 ⊆ O := by
    intro x hx
    change Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u
    rw [mem_sphere_zero_iff_norm.mp hx]
    exact ⟨Real.exp_lt_one_iff.mpr hl, Real.one_lt_exp_iff.mpr hu⟩
  obtain ⟨V, hV, hSV, hVA, Φ, _, _, _, hΦ, _, _, K, hK, hKO, hfix⟩ :=
    (cylinderRadialGerm v A).exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood zero_lt_one
      (cylinderRadialGerm_sphere_source v A hsource) (cylinderRadialGerm_sphere_fixed v A hfixed)
      (cylinderRadialGerm_mapsTo_closedBall v A hside) hO hSO
  refine ⟨Φ 1, V, hV, hSV, hVA, hΦ, ?_, K, hK, hKO, (hfix 1).1, (hfix 1).2⟩
  apply (hfix 1).1
  intro hz
  have hbad := (hKO hz).1
  rw [norm_zero] at hbad
  exact (not_lt_of_ge (Real.exp_pos l).le) hbad

end DifferentialGeometry.Topology.Manifold
