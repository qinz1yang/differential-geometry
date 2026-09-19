/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

/-! Small piecewise affine perturbations preserving a half-space. -/

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane
  [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (ℓ : E →ₗ[ℝ] ℝ)
    (hℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (v : E) (hv : 0 < ℓ v)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) :
    ∃ (b : E → ℝ) (k : NNReal), IsPiecewiseAffineOn b univ ∧ LipschitzWith k b ∧
      EqOn b (simplicialMap K (fun w => if w = v then 1 else 0)) K.space ∧
        EqOn b (fun _ => 0) Uᶜ ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ ∀ x, ℓ x = 0 → b x = 0 := by
  obtain ⟨b, k, hb, hk, hfix, hzero, hbound⟩ :=
    exists_piecewiseAffine_lipschitz_vertex_function K v hU hKU
  let A : E →L[ℝ] ℝ := (ℓ v)⁻¹ • ℓ.toContinuousLinearMap
  let c : E → ℝ := fun x => min (b x) (max 0 (A x))
  have hA : IsPiecewiseAffineOn A univ := isPiecewiseAffineOn_of_affine
    A.toLinearMap.toAffineMap isOpen_univ
  have hc : IsPiecewiseAffineOn c univ := hb.min
    ((isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : ℝ)) isOpen_univ).max hA)
  have hclip : ∀ x ∈ K.space, b x ≤ A x := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have hsℓ : ∀ w ∈ s, 0 ≤ ℓ w := fun w hw => hℓ w
      (K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w))
    have hsum : ℓ x = ∑ w ∈ s, weights s x w * ℓ w := by
      calc ℓ x = ℓ (∑ w ∈ s, weights s x w • w) := congrArg ℓ (sum_weights_smul hxs).symm
        _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
    have hbℓ : b x * ℓ v ≤ ℓ x := by
      rw [hfix hx, simplicialMap_eq_of_mem K _ hs hxs, hsum]
      simp only [smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro w hw
      by_cases hwv : w = v
      · subst w
        simp
      · simp only [if_neg hwv, mul_zero, zero_mul]
        exact mul_nonneg (weights_nonneg hxs hw) (hsℓ w hw)
    change b x ≤ (ℓ v)⁻¹ * ℓ x
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hv).mpr hbℓ
  refine ⟨c, max k (max 0 ‖A‖₊), hc, hk.min ((LipschitzWith.const 0).max A.lipschitz), ?_, ?_,
    ?_, ?_⟩
  · intro x hx
    change min (b x) (max 0 (A x)) = _
    rw [min_eq_left ((hclip x hx).trans (le_max_right _ _)), hfix hx]
  · intro x hx
    change min (b x) (max 0 (A x)) = 0
    rw [hzero hx, min_eq_left (le_max_left _ _)]
  · intro x
    exact ⟨le_min (hbound x).1 (le_max_left _ _), (min_le_left _ _).trans (hbound x).2⟩
  · intro x hx
    have hAx : A x = 0 := by change (ℓ v)⁻¹ * ℓ x = 0; rw [hx, mul_zero]
    change min (b x) (max 0 (A x)) = 0
    rw [hAx, max_self, min_eq_right (hbound x).1]

open Classical in
theorem exists_piecewiseAffine_lipschitz_extension_tangent_on_hyperplane
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ℓ : E →ₗ[ℝ] ℝ) (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) :
    ∃ c : NNReal, 0 < c ∧ ∀ (v : E → E) (δ : NNReal),
      (∀ x ∈ K.vertices, ‖v x‖ ≤ δ) →
      (∀ x ∈ K.vertices, ℓ x = 0 → ℓ (v x) = 0) →
      ∃ a : E → E, IsPiecewiseAffineOn a univ ∧ LipschitzWith (c * δ) a ∧
        EqOn a (simplicialMap K v) K.space ∧ EqOn a (fun _ => 0) Uᶜ ∧
        (∀ x, ‖a x‖ ≤ (c * δ : NNReal)) ∧ ∀ x, ℓ x = 0 → ℓ (a x) = 0 := by
  have hfunctions : ∀ v : E, ∃ (b : E → ℝ) (k : NNReal), IsPiecewiseAffineOn b univ ∧
      LipschitzWith k b ∧ EqOn b (simplicialMap K (fun w => if w = v then 1 else 0)) K.space ∧
      EqOn b (fun _ => 0) Uᶜ ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      (0 < ℓ v → ∀ x, ℓ x = 0 → b x = 0) := by
    intro v
    by_cases hv : 0 < ℓ v
    · obtain ⟨b, k, hb, hk, hfix, hzero, hbound, hplane⟩ :=
        exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane
          K ℓ hKℓ v hv hU hKU
      exact ⟨b, k, hb, hk, hfix, hzero, hbound, fun _ => hplane⟩
    · obtain ⟨b, k, hb, hk, hfix, hzero, hbound⟩ :=
        exists_piecewiseAffine_lipschitz_vertex_function K v hU hKU
      exact ⟨b, k, hb, hk, hfix, hzero, hbound, fun hv' => (hv hv').elim⟩
  choose b k hb hk hfix hzero hbound hplane using hfunctions
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let V := hvertices.toFinset
  have hV : K.vertices ⊆ (V : Set E) := fun _ hv => hvertices.mem_toFinset.mpr hv
  have hV' : ∀ v ∈ V, v ∈ K.vertices := fun _ hv => hvertices.mem_toFinset.mp hv
  let C : ℝ := (∑ v ∈ V, (k v : ℝ)) + V.card + 1
  have hsum : 0 ≤ ∑ v ∈ V, (k v : ℝ) := Finset.sum_nonneg fun v _ => (k v).property
  have hC : 0 < C := by dsimp only [C]; positivity
  have hkC : (∑ v ∈ V, (k v : ℝ)) ≤ C := by
    dsimp only [C]
    linarith [Nat.cast_nonneg (α := ℝ) V.card]
  have hNC : (V.card : ℝ) ≤ C := by dsimp only [C]; linarith
  let c : NNReal := ⟨C, hC.le⟩
  refine ⟨c, hC, fun v δ hv hvplane => ?_⟩
  let a : E → E := fun x => ∑ w ∈ V, b w x • v w
  have ha : IsPiecewiseAffineOn a univ := by
    apply IsPiecewiseAffineOn.sum V isOpen_univ
    intro w _
    exact ((hb w).affine_comp (LinearMap.toSpanSingleton ℝ E (v w)).toAffineMap).congr
      (fun _ _ => rfl)
  refine ⟨a, ha, ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (∑ w ∈ V, b w x • v w) (∑ w ∈ V, b w y • v w) ≤ _
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ w ∈ V, (b w x • v w - b w y • v w)‖ ≤
          ∑ w ∈ V, ‖b w x • v w - b w y • v w‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ V, (k w : ℝ) * δ * dist x y := by
        apply Finset.sum_le_sum
        intro w hw
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
        calc dist (b w x) (b w y) * ‖v w‖ ≤ ((k w : ℝ) * dist x y) * δ :=
            mul_le_mul ((hk w).dist_le_mul x y) (hv w (hV' w hw)) (norm_nonneg _)
              (mul_nonneg (k w).property dist_nonneg)
          _ = (k w : ℝ) * δ * dist x y := by ring
      _ = (∑ w ∈ V, (k w : ℝ)) * δ * dist x y := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ (c * δ : NNReal) * dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkC δ.property) dist_nonneg
  · intro x hx
    exact sum_vertex_functions_smul_eq_simplicialMap K V hV b (fun w _ => hfix w) v hx
  · intro x hx
    exact Finset.sum_eq_zero fun w _ => by rw [hzero w hx, zero_smul]
  · intro x
    calc ‖a x‖ ≤ ∑ w ∈ V, ‖b w x • v w‖ := norm_sum_le _ _
      _ ≤ ∑ _w ∈ V, (δ : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbound w x).1]
        exact (mul_le_mul (hbound w x).2 (hv w (hV' w hw)) (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _)
      _ = (V.card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (c * δ : NNReal) := mul_le_mul_of_nonneg_right hNC δ.property
  · intro x hx
    change ℓ (∑ w ∈ V, b w x • v w) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hw0 : ℓ w = 0
    · rw [map_smul, hvplane w (hV' w hw) hw0, smul_zero]
    · have hwpos : 0 < ℓ w := lt_of_le_of_ne (hKℓ w (hV' w hw)) (Ne.symm hw0)
      rw [hplane w hwpos x hx, zero_smul, map_zero]

private theorem halfSpace_preserved_of_lipschitz_displacement
    (ℓ : E →L[ℝ] ℝ) {w : E} (hw : ℓ w = 1)
    {a : E → E} {k : NNReal} (ha : LipschitzWith k a)
    (hplane : ∀ x, ℓ x = 0 → ℓ (a x) = 0)
    (hsmall : ‖ℓ‖ * (k : ℝ) * ‖w‖ < 1) :
    ∀ x, (ℓ (x + a x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (x + a x) ↔ 0 ≤ ℓ x) := by
  intro x
  let q := x - ℓ x • w
  have hq : ℓ q = 0 := by
    dsimp only [q]
    rw [map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
  have habs : |ℓ (a x)| ≤ (‖ℓ‖ * (k : ℝ) * ‖w‖) * |ℓ x| := by
    calc |ℓ (a x)| = ‖ℓ (a x - a q)‖ := by
          change |ℓ (a x)| = |ℓ (a x - a q)|
          rw [map_sub, hplane q hq, sub_zero]
      _ ≤ ‖ℓ‖ * ‖a x - a q‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * ((k : ℝ) * dist x q) := mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using ha.dist_le_mul x q) (norm_nonneg _)
      _ = (‖ℓ‖ * (k : ℝ) * ‖w‖) * |ℓ x| := by
        rw [dist_eq_norm, show x - q = ℓ x • w by dsimp only [q]; abel,
          norm_smul, Real.norm_eq_abs]
        ring
  have hstrict : ℓ x ≠ 0 → |ℓ (a x)| < |ℓ x| := by
    intro hx
    exact habs.trans_lt (mul_lt_of_lt_one_left (abs_pos.mpr hx) hsmall)
  rw [map_add]
  rcases lt_trichotomy (ℓ x) 0 with hx | hx | hx
  · have h := abs_lt.mp (hstrict (ne_of_lt hx))
    rw [abs_of_neg hx] at h
    have hsum : ℓ x + ℓ (a x) < 0 := by linarith [h.2]
    exact ⟨iff_of_false (ne_of_lt hsum) (ne_of_lt hx),
      iff_of_false (not_le_of_gt hsum) (not_le_of_gt hx)⟩
  · simp only [hx, hplane x hx, add_zero, and_self]
  · have h := abs_lt.mp (hstrict (ne_of_gt hx))
    rw [abs_of_pos hx] at h
    have hsum : 0 < ℓ x + ℓ (a x) := by linarith [h.1]
    exact ⟨iff_of_false (ne_of_gt hsum) (ne_of_gt hx), iff_of_true hsum.le hx.le⟩

open Classical in
theorem exists_lipschitz_displacement_extending_vertex_perturbation_preserving_halfSpace
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → E, (∀ v ∈ K.vertices, dist (φ v) v < δ) →
      (∀ v ∈ K.vertices, ℓ v = 0 → ℓ (φ v) = 0) →
      ∃ (a : E → E) (k : NNReal), IsPiecewiseAffineOn a univ ∧ LipschitzWith k a ∧
        (k : ℝ) < η ∧ k < 1 ∧ (∀ x, ‖a x‖ < ε) ∧ EqOn a (fun _ => 0) Uᶜ ∧
        (∀ x, ℓ x = 0 → ℓ (a x) = 0) ∧
        EqOn (fun x => x + a x) (simplicialMap K φ) K.space ∧
        IsPLHomeomorphOn (fun x => x + a x) univ univ ∧
        ∀ x, (ℓ (x + a x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (x + a x) ↔ 0 ≤ ℓ x) := by
  obtain ⟨c, hc, hext⟩ :=
    exists_piecewiseAffine_lipschitz_extension_tangent_on_hyperplane K ℓ hKℓ hU hKU
  obtain ⟨w, hw⟩ := LinearMap.surjective_of_ne_zero hℓ (1 : ℝ)
  let L : E →L[ℝ] ℝ := ℓ.toContinuousLinearMap
  let B : ℝ := ‖L‖ * ‖w‖ + 1
  have hB1 : 1 ≤ B := le_add_of_nonneg_left (mul_nonneg (norm_nonneg L) (norm_nonneg w))
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have htarget : 0 < min ε (min η (1 / (2 * B))) :=
    lt_min hε (lt_min hη (by positivity))
  obtain ⟨δ, hδ, hδc⟩ := exists_pos_mul_lt (a := min ε (min η (1 / (2 * B)))) htarget (c : ℝ)
  refine ⟨δ, hδ, fun φ hφ hφplane => ?_⟩
  have hv : ∀ x ∈ K.vertices, ‖φ x - x‖ ≤ (⟨δ, hδ.le⟩ : NNReal) := by
    intro x hx
    exact (show ‖φ x - x‖ < δ from (dist_eq_norm (φ x) x) ▸ hφ x hx).le
  have hvplane : ∀ x ∈ K.vertices, ℓ x = 0 → ℓ (φ x - x) = 0 := by
    intro x hx hx0
    rw [map_sub, hφplane x hx hx0, hx0, sub_self]
  obtain ⟨a, ha, halip, hagree, hzero, hnorm, hplane⟩ :=
    hext (fun x => φ x - x) ⟨δ, hδ.le⟩ hv hvplane
  let k : NNReal := c * ⟨δ, hδ.le⟩
  have hkε : (k : ℝ) < ε := hδc.trans_le (min_le_left _ _)
  have hkη : (k : ℝ) < η := hδc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hkB : (k : ℝ) * B < 1 / 2 := by
    have h := hδc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h' := (lt_div_iff₀ (show 0 < 2 * B by positivity)).mp h
    change (k : ℝ) * (2 * B) < 1 at h'
    nlinarith
  have hk1 : k < 1 := by
    have h := mul_le_mul_of_nonneg_left hB1 k.property
    change (k : ℝ) < 1
    nlinarith
  have hsmall : ‖L‖ * (k : ℝ) * ‖w‖ < 1 := by
    have hL : ‖L‖ * ‖w‖ ≤ B := le_add_of_nonneg_right zero_le_one
    calc ‖L‖ * (k : ℝ) * ‖w‖ = (k : ℝ) * (‖L‖ * ‖w‖) := by ring
      _ ≤ (k : ℝ) * B := mul_le_mul_of_nonneg_left hL k.property
      _ < 1 := hkB.trans (by norm_num)
  refine ⟨a, k, ha, halip, hkη, hk1, fun x => (hnorm x).trans_lt hkε, hzero, hplane,
    ?_, isPLHomeomorphOn_id_add_of_lipschitz ha halip hk1,
    halfSpace_preserved_of_lipschitz_displacement L hw halip hplane hsmall⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  change x + a x = simplicialMap K φ x
  rw [hagree hx, simplicialMap_eq_of_mem K _ hs hxs,
    simplicialMap_eq_of_mem K φ hs hxs]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sum_weights_smul hxs]
  abel

open Classical in
theorem exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → E, (∀ v ∈ K.vertices, dist (φ v) v < δ) →
      (∀ v ∈ K.vertices, ℓ v = 0 → ℓ (φ v) = 0) →
        ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧
          EqOn h id Uᶜ ∧ EqOn h (simplicialMap K φ) K.space ∧
            ∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x) := by
  obtain ⟨δ, hδ, hext⟩ :=
    exists_lipschitz_displacement_extending_vertex_perturbation_preserving_halfSpace
      K ℓ hℓ hKℓ hU hKU hε zero_lt_one
  refine ⟨δ, hδ, fun φ hφ hφplane => ?_⟩
  obtain ⟨a, k, _, _, _, _, hnorm, hzero, _, hagree, hh, hheight⟩ := hext φ hφ hφplane
  refine ⟨fun x => x + a x, hh, ?_, ?_, hagree, hheight⟩
  · intro x
    simpa only [dist_eq_norm, add_sub_cancel_left] using hnorm x
  · intro x hx
    change x + a x = x
    rw [hzero hx, add_zero]

end DifferentialGeometry.Topology.PiecewiseLinear
