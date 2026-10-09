/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarGraphRegion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_continuousOn_extension_of_crosscut_half {X : Set E3}
    {Pl W Bp : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsPLBall 2 W)
    (hfrW : frontier W = W ∩ frontier Pl ∪ Bp) (hBpc : IsClosed Bp) (hPlc : IsClosed Pl)
    {ρ φ : EuclideanSpace ℝ (Fin 2) → E3} (hρ : ContinuousOn ρ Pl) (hφ : ContinuousOn φ Bp)
    (hφρ : ∀ x ∈ Bp ∩ frontier Pl, φ x = ρ x) {S₁ : Set E3} (hS₁X : S₁ ⊆ X)
    (hS₁ : ρ '' (W ∩ frontier Pl) ∪ φ '' Bp ⊆ S₁)
    (hn₁ : (⟨Set.inclusion hS₁X, continuous_inclusion hS₁X⟩ : C(S₁, X)).Nullhomotopic) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → E3, ContinuousOn G W ∧ MapsTo G W X ∧
      (∀ x ∈ W ∩ frontier Pl, G x = ρ x) ∧ ∀ x ∈ Bp, G x = φ x := by
  classical
  let F : EuclideanSpace ℝ (Fin 2) → E3 := Bp.piecewise φ ρ
  have hFBp : ∀ x ∈ Bp, F x = φ x := fun x hx => piecewise_eq_of_mem Bp φ ρ hx
  have hFfr : ∀ x ∈ frontier Pl, F x = ρ x := by
    intro x hx
    by_cases hxB : x ∈ Bp
    · rw [hFBp x hxB, hφρ x ⟨hxB, hx⟩]
    · exact piecewise_eq_of_notMem Bp φ ρ hxB
  have hfrPl : frontier Pl ⊆ Pl := hPlc.frontier_subset
  have hFc : ContinuousOn F (frontier W) := by
    rw [hfrW]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (hW.isPolyhedron.isClosed.inter isClosed_frontier)
      hBpc
    · exact (hρ.mono (inter_subset_right.trans hfrPl)).congr fun x hx => hFfr x hx.2
    · exact hφ.congr fun x hx => hFBp x hx
  have hFS : ∀ z ∈ frontier W, F z ∈ S₁ := by
    intro z hz
    rw [hfrW] at hz
    by_cases hzB : z ∈ Bp
    · rw [hFBp z hzB]
      exact hS₁ (Or.inr (mem_image_of_mem φ hzB))
    · have hzW : z ∈ W ∩ frontier Pl := hz.resolve_right hzB
      rw [hFfr z hzW.2]
      exact hS₁ (Or.inl (mem_image_of_mem ρ hzW))
  let k : C(frontier W, S₁) := ⟨fun z => ⟨F z, hFS z z.2⟩,
    hFc.domRestrict.subtype_mk _⟩
  let b : C(frontier W, X) := ⟨fun z => ⟨F z, hS₁X (hFS z z.2)⟩,
    hFc.domRestrict.subtype_mk _⟩
  have hb : b.Nullhomotopic := by
    have heq : b = (⟨Set.inclusion hS₁X, continuous_inclusion hS₁X⟩ : C(S₁, X)).comp k := by
      ext z
      rfl
    rw [heq]
    exact hn₁.comp_left k
  have hJ : Schoenflies.IsJordanCurve (frontier W) :=
    isJordanCurve_of_isPLSphere_one hW.isPLSphere_frontier
  obtain ⟨G, hGc, hGX, hGb⟩ := exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic hJ b hb
  rw [hW.closure_inside_frontier] at hGc hGX
  refine ⟨G, hGc, hGX, fun x hx => ?_, fun x hx => ?_⟩
  · have hxfr : x ∈ frontier W := by
      rw [hfrW]
      exact Or.inl hx
    rw [← hFfr x hx.2]
    exact hGb ⟨x, hxfr⟩
  · have hxfr : x ∈ frontier W := by
      rw [hfrW]
      exact Or.inr hx
    rw [← hFBp x hx]
    exact hGb ⟨x, hxfr⟩

theorem nullhomotopic_of_crosscut_halves {X : Set E3}
    {Pl U V Bp : Set (EuclideanSpace ℝ (Fin 2))} (hPl : IsPLBall 2 Pl) (hU : IsPLBall 2 U)
    (hV : IsPLBall 2 V) (hUV : U ∪ V = Pl) (hUVi : U ∩ V = Bp)
    (hfrU : frontier U = U ∩ frontier Pl ∪ Bp) (hfrV : frontier V = V ∩ frontier Pl ∪ Bp)
    {ρ φ : EuclideanSpace ℝ (Fin 2) → E3} (hρ : ContinuousOn ρ Pl) (hφ : ContinuousOn φ Bp)
    (hφρ : ∀ x ∈ Bp ∩ frontier Pl, φ x = ρ x) (hρX : MapsTo ρ (frontier Pl) X)
    {S₁ S₂ S : Set E3} (hS₁X : S₁ ⊆ X) (hS₂X : S₂ ⊆ X) (hSX : S ⊆ X)
    (hS₁ : ρ '' (U ∩ frontier Pl) ∪ φ '' Bp ⊆ S₁) (hS₂ : ρ '' (V ∩ frontier Pl) ∪ φ '' Bp ⊆ S₂)
    {σ : E3 → EuclideanSpace ℝ (Fin 2)} (hσ : ContinuousOn σ S)
    (hσS : MapsTo σ S (frontier Pl)) (hρσ : ∀ y ∈ S, ρ (σ y) = y)
    (hn₁ : (⟨Set.inclusion hS₁X, continuous_inclusion hS₁X⟩ : C(S₁, X)).Nullhomotopic)
    (hn₂ : (⟨Set.inclusion hS₂X, continuous_inclusion hS₂X⟩ : C(S₂, X)).Nullhomotopic) :
    (⟨Set.inclusion hSX, continuous_inclusion hSX⟩ : C(S, X)).Nullhomotopic := by
  classical
  have hPlc : IsClosed Pl := hPl.isPolyhedron.isClosed
  have hUc : IsClosed U := hU.isPolyhedron.isClosed
  have hVc : IsClosed V := hV.isPolyhedron.isClosed
  have hBpc : IsClosed Bp := hUVi ▸ hUc.inter hVc
  obtain ⟨GU, hGUc, hGUX, hGUρ, hGUφ⟩ := exists_continuousOn_extension_of_crosscut_half hU hfrU
    hBpc hPlc hρ hφ hφρ hS₁X hS₁ hn₁
  obtain ⟨GV, hGVc, hGVX, hGVρ, hGVφ⟩ := exists_continuousOn_extension_of_crosscut_half hV hfrV
    hBpc hPlc hρ hφ hφρ hS₂X hS₂ hn₂
  let G : EuclideanSpace ℝ (Fin 2) → E3 := U.piecewise GU GV
  have hGU : ∀ x ∈ U, G x = GU x := fun x hx => piecewise_eq_of_mem U GU GV hx
  have hGV : ∀ x ∈ V, G x = GV x := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hxB : x ∈ Bp := hUVi ▸ ⟨hxU, hx⟩
      rw [hGU x hxU, hGUφ x hxB, hGVφ x hxB]
    · exact piecewise_eq_of_notMem U GU GV hxU
  have hGc : ContinuousOn G Pl := by
    rw [← hUV]
    exact ContinuousOn.union_of_isClosed (hGUc.congr hGU) (hGVc.congr hGV) hUc hVc
  have hGX : MapsTo G Pl X := by
    intro x hx
    rw [← hUV] at hx
    rcases hx with hx | hx
    · rw [hGU x hx]
      exact hGUX hx
    · rw [hGV x hx]
      exact hGVX hx
  have hfrPl : frontier Pl ⊆ Pl := hPlc.frontier_subset
  let b : C(frontier Pl, X) := ⟨fun z => ⟨ρ z, hρX z.2⟩,
    (hρ.mono hfrPl).domRestrict.subtype_mk _⟩
  have hGb : ∀ z : frontier Pl, (b z : E3) = G z := by
    intro z
    have hz : (z : EuclideanSpace ℝ (Fin 2)) ∈ U ∪ V := by
      rw [hUV]
      exact hfrPl z.2
    rcases hz with hz | hz
    · rw [hGU z hz, hGUρ z ⟨hz, z.2⟩]
      rfl
    · rw [hGV z hz, hGVρ z ⟨hz, z.2⟩]
      rfl
  have hbnull : b.Nullhomotopic := hPl.nullhomotopic_of_continuousOn hfrPl hGc hGX b hGb
  let kσ : C(S, frontier Pl) := ⟨fun y => ⟨σ y, hσS y.2⟩, hσ.domRestrict.subtype_mk _⟩
  have heq : (⟨Set.inclusion hSX, continuous_inclusion hSX⟩ : C(S, X)) = b.comp kσ := by
    refine ContinuousMap.ext fun y => Subtype.ext ?_
    exact (hρσ y y.2).symm
  rw [heq]
  exact hbnull.comp_left kσ

end DifferentialGeometry.Topology.PiecewiseLinear
