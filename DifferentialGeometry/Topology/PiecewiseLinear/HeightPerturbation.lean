/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linearMap_lt_on_convexHull_sdiff_singleton
    (ℓ : E →ₗ[ℝ] ℝ) (T : Finset E) (p : E)
    (hT : ∀ v ∈ T, v ≠ p → ℓ p < ℓ v) :
    ∀ x ∈ convexHull ℝ (T : Set E) \ {p}, ℓ p < ℓ x := by
  classical
  have hsub : T ⊆ insert p (T.erase p) := by
    intro v hv
    by_cases hvp : v = p
    · simp only [hvp, Finset.mem_insert_self]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvp, hv⟩)
  have hconv : convexHull ℝ ((T.erase p : Finset E) : Set E) ⊆ {x | ℓ p < ℓ x} :=
    convexHull_min (fun v hv => hT v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1)
      (convex_halfSpace_gt ℓ.isLinear (ℓ p))
  rintro x ⟨hx, hxp⟩
  have hx' := convexHull_mono (Finset.coe_subset.mpr hsub) hx
  rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase p T) hx' with h | ⟨z, hz, s, hs,
      -, rfl⟩
  · exact (hxp h).elim
  · rw [map_add, map_smul, map_sub, smul_eq_mul]
    have hpos := mul_pos hs (sub_pos.mpr (hconv hz))
    linarith

theorem eventually_preserves_strict_order
    {A : Set E} (hA : A.Finite) (ℓ : E →L[ℝ] ℝ) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ x ∈ A, ∀ y ∈ A, ℓ x < ℓ y → f x < f y := by
  let _ : Finite A := hA.to_subtype
  have h : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      ∀ x y : A, ℓ x < ℓ y → f x < f y := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro y
    by_cases hxy : ℓ x < ℓ y
    · filter_upwards [(ContinuousLinearMap.apply ℝ ℝ (x : E)).continuous.continuousAt.eventually_lt
        (ContinuousLinearMap.apply ℝ ℝ (y : E)).continuous.continuousAt hxy] with f hf
      exact fun _ => hf
    · exact Filter.Eventually.of_forall fun _ h => (hxy h).elim
  filter_upwards [h] with f hf x hx y hy hxy
  exact hf ⟨x, hx⟩ ⟨y, hy⟩ hxy

theorem exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace
    [FiniteDimensional ℝ E] {A B : Set E} (hA : A.Finite) (hB : B.Finite)
    (ℓ m : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (T : Finset E) (p : E)
    (hlevel : ∀ v ∈ T, ℓ v = ℓ p) (hside : ∀ v ∈ T, v ≠ p → m p < m v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E →L[ℝ] ℝ, dist f ℓ < ε ∧ f ≠ 0 ∧ InjOn f A ∧
      (∀ x ∈ B, ∀ y ∈ B, ℓ x < ℓ y → f x < f y) ∧
      ∀ x ∈ convexHull ℝ (T : Set E) \ {p}, f p < f x := by
  have horder := eventually_preserves_strict_order hB ℓ
  have hclose : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, dist f ℓ < ε := Metric.ball_mem_nhds ℓ hε
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hℓ
  have hgood := hclose.and (hne.and horder)
  have hcont : Filter.Tendsto (fun t : ℝ => ℓ + t • m) (𝓝 0) (𝓝 ℓ) := by
    have h : Continuous (fun t : ℝ => ℓ + t • m) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (h.continuousAt (x := 0)).tendsto
  obtain ⟨δ, hδ, hδgood⟩ := Metric.mem_nhds_iff.mp (hcont hgood)
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  obtain ⟨hαclose, hαne, hαorder⟩ := hδgood htball
  let α := ℓ + t • m
  have hαside : ∀ v ∈ T, v ≠ p → α p < α v := by
    intro v hv hvp
    change ℓ p + t * m p < ℓ v + t * m v
    rw [hlevel v hv]
    linarith [mul_lt_mul_of_pos_left (hside v hv hvp) ht]
  have hsideNear : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 α, ∀ v : T, (v : E) ≠ p → f p < f v := by
    rw [Filter.eventually_all]
    intro v
    by_cases hvp : (v : E) = p
    · exact Filter.Eventually.of_forall fun _ h => (h hvp).elim
    · filter_upwards [(ContinuousLinearMap.apply ℝ ℝ p).continuous.continuousAt.eventually_lt
        (ContinuousLinearMap.apply ℝ ℝ (v : E)).continuous.continuousAt (hαside v v.2 hvp)] with f
            hf
      exact fun _ => hf
  have horderNear := eventually_preserves_strict_order hB α
  have hcloseNear : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 α, dist f ℓ < ε :=
    Metric.isOpen_ball.mem_nhds hαclose
  have hneNear : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 α, f ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hαne
  obtain ⟨η, hη, hηgood⟩ := Metric.mem_nhds_iff.mp
    (hcloseNear.and (hneNear.and (horderNear.and hsideNear)))
  obtain ⟨f, hfclose, hfinj⟩ := exists_continuousLinearMap_injOn hA α hη
  obtain ⟨hfε, hfne, hforder, hfside⟩ := hηgood hfclose
  refine ⟨f, hfε, hfne, hfinj, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hforder x hx y hy (hαorder x hx y hy hxy)
  · exact linearMap_lt_on_convexHull_sdiff_singleton f.toLinearMap T p
      (fun v hv hvp => hfside ⟨v, hv⟩ hvp)

theorem exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron
    [FiniteDimensional ℝ E] {A B : Set E} (hA : A.Finite) (hB : B.Finite)
    (ℓ m : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {D : Set E} (hD : IsPolyhedron D) (p : E)
    (hlevel : ∀ x ∈ D, ℓ x = ℓ p) (hside : ∀ x ∈ D \ {p}, m p < m x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E →L[ℝ] ℝ, dist f ℓ < ε ∧ f ≠ 0 ∧ InjOn f A ∧
      (∀ x ∈ B, ∀ y ∈ B, ℓ x < ℓ y → f x < f y) ∧
      ∀ x ∈ D \ {p}, f p < f x := by
  classical
  obtain ⟨K, hKfin, hKD⟩ := hD.exists_simplicialComplex
  have hvertices : K.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn hKfin
  let T := hvertices.toFinset
  have hT : (T : Set E) = K.vertices := hvertices.coe_toFinset
  have hTD : (T : Set E) ⊆ D := hT.trans_le (K.vertices_subset_space.trans_eq hKD)
  have hDconv : D ⊆ convexHull ℝ (T : Set E) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp (hKD.symm ▸ hx)
    apply convexHull_mono (t := (T : Set E)) ?_ hxs
    intro v hv
    rw [hT]
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨f, hfε, hfne, hfinj, hforder, hfside⟩ :=
    exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace hA hB ℓ m hℓ T p
      (fun v hv => hlevel v (hTD hv)) (fun v hv hvp => hside v ⟨hTD hv, hvp⟩) hε
  exact ⟨f, hfε, hfne, hfinj, hforder, fun x hx => hfside x ⟨hDconv hx.1, hx.2⟩⟩
end DifferentialGeometry.Topology.PiecewiseLinear
