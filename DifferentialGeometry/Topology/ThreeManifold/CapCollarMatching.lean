import DifferentialGeometry.Topology.ThreeManifold.CapCollar
import DifferentialGeometry.Topology.ThreeManifold.CoreBoundaryCollar
import DifferentialGeometry.Topology.Manifold.SphereCollarCoordinates
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T) (b : T.Boundary)

private def collarTransition
    (d e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  (e.reverse.radialPartialDiffeomorph v).trans (d.radialPartialDiffeomorph v).symm

private theorem collarTransition_sphere_source
    (d e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2) :
    sphere (0 : E3) 1 ⊆ (collarTransition C b d e v).source := by
  intro x hx
  refine ⟨e.reverse.sphere_subset_radialPartialDiffeomorph_source v hx, ?_⟩
  change e.reverse.radialPartialDiffeomorph v x ∈ (d.radialPartialDiffeomorph v).target
  rw [e.reverse.radialPartialDiffeomorph_sphere v ⟨x, hx⟩]
  rw [← d.radialPartialDiffeomorph_sphere v ⟨x, hx⟩]
  exact (d.radialPartialDiffeomorph v).map_source (d.sphere_subset_radialPartialDiffeomorph_source v hx)

private theorem collarTransition_sphere
    (d e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2) :
    EqOn (collarTransition C b d e v) id (sphere (0 : E3) 1) := by
  intro x hx
  change (d.radialPartialDiffeomorph v).symm (e.reverse.radialPartialDiffeomorph v x) = x
  rw [e.reverse.radialPartialDiffeomorph_sphere v ⟨x, hx⟩,
    ← d.radialPartialDiffeomorph_sphere v ⟨x, hx⟩]
  exact (d.radialPartialDiffeomorph v).left_inv (d.sphere_subset_radialPartialDiffeomorph_source v hx)

private theorem collarTransition_mapsTo_compl_ball
    (d e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2)
    (hd : d.radius ≤ 1 / 2) (he : e.radius ≤ 1 / 2)
    (hcore : ∀ (x : T.core) (hx : C.coreInclusion x ∈ d.neighborhood),
      ((d.toDiffeomorph.symm ⟨C.coreInclusion x, hx⟩).2 : ℝ) ≤ 0)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b
        (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩)) :
    MapsTo (collarTransition C b d e v)
      ((ball (0 : E3) 1)ᶜ ∩ (collarTransition C b d e v).source) (ball (0 : E3) 1)ᶜ := by
  let _ : Nonempty S2 := ⟨v⟩
  intro x hx
  have hnorm : 1 ≤ ‖x‖ := by simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt] using hx.1
  have hsrc : x ∈ (e.reverse.radialPartialDiffeomorph v).source := hx.2.1
  have hxne := ((e.reverse.mem_radialPartialDiffeomorph_source_iff v x).mp hsrc).1
  have ht := ((e.reverse.mem_radialPartialDiffeomorph_source_iff v x).mp hsrc).2
  have ht' : ‖x‖ - 1 ∈ Ioo (-e.radius) e.radius := by
    change -e.radius < 1 - ‖x‖ ∧ 1 - ‖x‖ < e.radius at ht
    constructor <;> linarith [ht.1, ht.2]
  let z := Manifold.sphereDirection v x
  let q : S2 × symmetricOpenInterval e.radius := (z, ⟨‖x‖ - 1, ht'⟩)
  have hq : e.reverse.radialPartialDiffeomorph v x = e.toFun q := by
    have h := e.reverse.radialPartialDiffeomorph_apply v z ‖x‖ (norm_pos_iff.mpr hxne) ht
    rw [Manifold.norm_smul_sphereDirection v hxne] at h
    rw [h]
    erw [e.reverse_toFun]
    apply congrArg e.toFun
    apply Prod.ext
    · rfl
    apply Subtype.ext
    dsimp [q]
    ring
  have hp : 0 ≤ q.2.val := sub_nonneg.mpr hnorm
  rw [heq q hp] at hq
  let qcore := C.coreBoundaryHalfCollar b (q.1, ⟨q.2.val, hp, q.2.property.2.trans_le he⟩)
  have hqcore : e.reverse.radialPartialDiffeomorph v x = C.coreInclusion qcore := hq
  have htarget : e.reverse.radialPartialDiffeomorph v x ∈ (d.radialPartialDiffeomorph v).target := hx.2.2
  have hN : C.coreInclusion qcore ∈ d.neighborhood := by
    have h := htarget.1
    rw [hqcore] at h
    change C.coreInclusion qcore ∈ d.toPartialDiffeomorph.target at h
    rwa [d.toPartialDiffeomorph_target] at h
  rw [mem_compl_iff, mem_ball_zero_iff]
  change ¬ ‖(d.radialPartialDiffeomorph v).symm (e.reverse.radialPartialDiffeomorph v x)‖ < 1
  rw [hqcore, d.norm_radialPartialDiffeomorph_symm v (by linarith) ⟨C.coreInclusion qcore, hN⟩]
  linarith [hcore qcore hN]

theorem exists_cap_core_collar_matching (v : S2) :
    ∃ d e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell),
      d.radius ≤ 1 / 2 ∧ ∃ he : e.radius ≤ 1 / 2,
      (∀ (p : S2 × symmetricOpenInterval d.radius), 0 ≤ p.2.val →
        ∃ x : ClosedCell 3, x.val = (1 - p.2.val) • p.1.val ∧ d.toFun p = C.cap b x) ∧
      (∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
        e.toFun p = C.coreInclusionHalfCollar b
          (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩)) ∧
      ∃ (D : E3 ≃ₘ[ℝ] E3) (V : Set E3), IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧
        (∀ x ∈ V, x ∈ (e.reverse.radialPartialDiffeomorph v).source ∧
          D x ∈ (d.radialPartialDiffeomorph v).source) ∧
        (∀ x ∈ V, d.radialPartialDiffeomorph v (D x) = e.reverse.radialPartialDiffeomorph v x) ∧
        EqOn D id (sphere (0 : E3) 1) ∧
        D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
        (∀ x : E3, ‖x‖ ≤ 1 / 2 → D x = x ∧ D.symm x = x) ∧
        ∃ K : Set E3, IsCompact K ∧ K ⊆ {x : E3 | 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 2} ∧
          ∀ x, x ∉ K → D x = x ∧ D.symm x = x := by
  obtain ⟨d, hd, hdin, _, _, hcore⟩ := C.exists_capCollar b
  obtain ⟨e, he, heq⟩ := C.exists_coreBoundaryCollar b
  let A := collarTransition C b d e v
  let O : Set E3 := {x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 2}
  have hO : IsOpen O := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hSO : sphere (0 : E3) 1 ⊆ O := by
    intro x hx
    have hn := mem_sphere_zero_iff_norm.mp hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 2
    rw [hn]
    norm_num
  obtain ⟨V, hV, hSV, hVA, Φ, _, _, _, hΦ, hfixS, hball, K, hK, hKO, hfix⟩ :=
    A.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball zero_lt_one
      (collarTransition_sphere_source C b d e v) (collarTransition_sphere C b d e v)
      (collarTransition_mapsTo_compl_ball C b d e v hd he hcore heq) hO hSO
  refine ⟨d, e, hd, he, ?_, heq, Φ 1, V, hV, hSV, ?_, ?_, (hfixS 1).1, hball 1 ⟨zero_le_one, le_rfl⟩, ?_, K, hK, hKO, ?_⟩
  · intro p hp
    exact ⟨_, rfl, hdin p hp⟩
  · intro x hx
    refine ⟨(hVA hx).1, ?_⟩
    rw [hΦ hx]
    exact (d.radialPartialDiffeomorph v).symm.map_source (hVA hx).2
  · intro x hx
    rw [hΦ hx]
    exact (d.radialPartialDiffeomorph v).right_inv (hVA hx).2
  · intro x hx
    have hnot : x ∉ K := fun h => (not_lt_of_ge hx) (hKO h).1
    exact ⟨(hfix 1).1 hnot, (hfix 1).2 hnot⟩
  · intro x hx
    exact ⟨(hfix 1).1 hx, (hfix 1).2 hx⟩

end DifferentialGeometry.Topology.SphericalCapping
