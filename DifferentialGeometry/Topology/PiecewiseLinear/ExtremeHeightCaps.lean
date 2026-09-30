/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightCapCone
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberCircle
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSpanningDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_height_between_lowest_vertices
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) :
    ∃ p ∈ K.vertices, ∃ r : ℝ, ℓ p < r ∧
      (∀ v ∈ K.vertices, v ≠ p → r < ℓ v) ∧ ∃ z ∈ K.space, r < ℓ z := by
  classical
  obtain ⟨p, hp, w, -, hbound, -, -⟩ := exists_extreme_height_fibers K hK.nonempty ℓ hinj
  obtain ⟨s, hs, hps, hcard⟩ := exists_face_superset_card_eq_of_isPLSphere K hK hp
  have hpS : p ∈ s := hps (Finset.mem_singleton_self p)
  have herase : (s.erase p).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hpS, hcard]
    omega)
  obtain ⟨v, hv⟩ := herase
  have hvK : v ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hv)) (Finset.singleton_nonempty v)
  obtain ⟨q, hq, hqmin⟩ := Set.exists_min_image (K.vertices \ {p}) ℓ
    (SimplicialComplex.finite_vertices K).sdiff
    ⟨v, hvK, Finset.ne_of_mem_erase hv⟩
  have hpq : ℓ p < ℓ q := lt_of_le_of_ne (hbound q (K.vertices_subset_space hq.1)).1
    (fun h => hq.2 (hinj hq.1 hp h.symm))
  obtain ⟨r, hpr, hrq⟩ := exists_between hpq
  exact ⟨p, hp, r, hpr, fun z hz hzp => hrq.trans_le (hqmin z ⟨hz, hzp⟩),
    q, K.vertices_subset_space hq.1, hrq⟩

theorem exists_isSimplyEmbedded_lower_cap_of_heightIndex_eq_zero (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) (hzero : heightIndex K.space ℓ = 0)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (r : ℝ) (D : Set (EuclideanSpace ℝ (Fin 3))) (g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      (∃ y ∈ K.space, ℓ y < r) ∧ (∃ z ∈ K.space, r < ℓ z) ∧
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r} ∧
      D ⊆ W ∩ {x | ℓ x = r} ∧ IsSimplyEmbedded ((K.space ∩ {x | ℓ x ≤ r}) ∪ D) := by
  obtain ⟨p, hp, r, hpr, hother, habove⟩ := exists_height_between_lowest_vertices K hK ℓ.toLinearMap
      hinj
  have hbelow : ∃ y ∈ K.space, ℓ y < r := ⟨p, K.vertices_subset_space hp, hpr⟩
  have hJ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK (by simp) ℓ hℓ hinj hzero r hbelow
      habove
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
  obtain ⟨D, g, hg, hgJ, hDW⟩ := hJ.exists_isPLHomeomorphOn_disk_of_subset_fiber (by simp)
    ℓ.toLinearMap hlinear inter_subset_right hW hWconv (inter_subset_left.trans hKW)
  exact ⟨r, D, g, hbelow, habove, hg, hgJ, hDW,
    isSimplyEmbedded_lower_cap_of_lt_other_vertices I K ℓ.toLinearMap hp hpr hother hg
      (hDW.trans inter_subset_right) hgJ⟩

theorem exists_isSimplyEmbedded_upper_cap_of_heightIndex_eq_zero (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) (hzero : heightIndex K.space ℓ = 0)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (r : ℝ) (D : Set (EuclideanSpace ℝ (Fin 3))) (g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      (∃ y ∈ K.space, ℓ y < r) ∧ (∃ z ∈ K.space, r < ℓ z) ∧
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r} ∧
      D ⊆ W ∩ {x | ℓ x = r} ∧ IsSimplyEmbedded ((K.space ∩ {x | r ≤ ℓ x}) ∪ D) := by
  have hinj' : InjOn (-ℓ.toLinearMap) K.vertices := fun x hx y hy h => hinj hx hy (neg_injective h)
  obtain ⟨p, hp, t, hpt, hother, z, hz, htz⟩ := exists_height_between_lowest_vertices K hK
      (-ℓ.toLinearMap) hinj'
  have hpr : -t < ℓ p := by
    change -ℓ p < t at hpt
    linarith
  have hother' : ∀ v ∈ K.vertices, v ≠ p → ℓ v < -t := by
    intro v hv hvp
    have h := hother v hv hvp
    change t < -ℓ v at h
    linarith
  have hbelow : ∃ y ∈ K.space, ℓ y < -t := ⟨z, hz, by
    change t < -ℓ z at htz
    linarith⟩
  have habove : ∃ y ∈ K.space, -t < ℓ y := ⟨p, K.vertices_subset_space hp, hpr⟩
  have hJ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK (by simp) ℓ hℓ hinj hzero (-t) hbelow
      habove
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
  obtain ⟨D, g, hg, hgJ, hDW⟩ := hJ.exists_isPLHomeomorphOn_disk_of_subset_fiber (by simp)
    ℓ.toLinearMap hlinear inter_subset_right hW hWconv (inter_subset_left.trans hKW)
  exact ⟨-t, D, g, hbelow, habove, hg, hgJ, hDW,
    isSimplyEmbedded_upper_cap_of_other_vertices_lt I K ℓ.toLinearMap hp hpr hother' hg
      (hDW.trans inter_subset_right) hgJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
