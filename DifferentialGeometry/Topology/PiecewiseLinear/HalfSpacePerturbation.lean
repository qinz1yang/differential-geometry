import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (ℓ : E →ₗ[ℝ] ℝ)
    (hℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (v : E) (hv : 0 < ℓ v)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) :
    ∃ (b : E → ℝ) (k : NNReal), IsPiecewiseAffineOn b univ ∧ LipschitzWith k b ∧
      EqOn b (simplicialMap K (fun w => if w = v then 1 else 0)) K.space ∧
        EqOn b (fun _ => 0) Uᶜ ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ ∀ x, ℓ x = 0 → b x = 0 := by
  obtain ⟨b, k, hb, hk, hfix, hzero, hbound⟩ := exists_piecewiseAffine_lipschitz_vertex_function K v hU hKU
  let A : E →L[ℝ] ℝ := (ℓ v)⁻¹ • ℓ.toContinuousLinearMap
  let c : E → ℝ := fun x => min (b x) (max 0 (A x))
  have hA : IsPiecewiseAffineOn A univ := isPiecewiseAffineOn_of_affine A.toLinearMap.toAffineMap isOpen_univ
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
  refine ⟨c, max k (max 0 ‖A‖₊), hc, hk.min ((LipschitzWith.const 0).max A.lipschitz), ?_, ?_, ?_, ?_⟩
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
theorem exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → E, (∀ v ∈ K.vertices, dist (φ v) v < δ) →
      (∀ v ∈ K.vertices, ℓ v = 0 → ℓ (φ v) = 0) →
        ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧
          EqOn h id Uᶜ ∧ EqOn h (simplicialMap K φ) K.space ∧
            ∀ x, (ℓ (h x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (h x) ↔ 0 ≤ ℓ x) := by
  have hfunctions : ∀ v : E, ∃ (b : E → ℝ) (k : NNReal), IsPiecewiseAffineOn b univ ∧
      LipschitzWith k b ∧ EqOn b (simplicialMap K (fun w => if w = v then 1 else 0)) K.space ∧
        EqOn b (fun _ => 0) Uᶜ ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (0 < ℓ v → ∀ x, ℓ x = 0 → b x = 0) := by
    intro v
    by_cases hv : 0 < ℓ v
    · obtain ⟨b, k, hb, hk, hfix, hzero, hbound, hplane⟩ :=
        exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane K ℓ hKℓ v hv hU hKU
      exact ⟨b, k, hb, hk, hfix, hzero, hbound, fun _ => hplane⟩
    · obtain ⟨b, k, hb, hk, hfix, hzero, hbound⟩ := exists_piecewiseAffine_lipschitz_vertex_function K v hU hKU
      exact ⟨b, k, hb, hk, hfix, hzero, hbound, fun hv' => (hv hv').elim⟩
  choose b k hb hk hfix hzero hbound hplane using hfunctions
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let V := hvertices.toFinset
  have hV : K.vertices ⊆ (V : Set E) := fun _ hv => hvertices.mem_toFinset.mpr hv
  have hV' : ∀ v ∈ V, v ∈ K.vertices := fun _ hv => hvertices.mem_toFinset.mp hv
  obtain ⟨w, hw⟩ := LinearMap.surjective_of_ne_zero hℓ (1 : ℝ)
  let L : E →L[ℝ] ℝ := ℓ.toContinuousLinearMap
  let B : ℝ := ‖L‖ * ‖w‖ + 1
  have hB1 : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg L, norm_nonneg w]
  have hB : 0 < B := zero_lt_one.trans_le hB1
  let C : ℝ := ∑ v ∈ V, (k v : ℝ)
  have hC : 0 ≤ C := Finset.sum_nonneg fun v _ => (k v).property
  let δ : ℝ := min (ε / ((V.card : ℝ) + 1)) (1 / (2 * (C + 1) * B))
  have hδ : 0 < δ := lt_min (div_pos hε (by positivity)) (by positivity)
  have hδN : (V.card : ℝ) * δ < ε := by
    have h := (le_div_iff₀ (show 0 < (V.card : ℝ) + 1 by positivity)).mp (min_le_left
      (ε / ((V.card : ℝ) + 1)) (1 / (2 * (C + 1) * B)))
    change δ * ((V.card : ℝ) + 1) ≤ ε at h
    nlinarith
  have hδCB : C * δ * B < 1 := by
    have h := (le_div_iff₀ (show 0 < 2 * (C + 1) * B by positivity)).mp (min_le_right
      (ε / ((V.card : ℝ) + 1)) (1 / (2 * (C + 1) * B)))
    change δ * (2 * (C + 1) * B) ≤ 1 at h
    calc C * δ * B = C * (δ * B) := by ring
      _ < (C + 1) * (δ * B) := mul_lt_mul_of_pos_right (lt_add_one C) (mul_pos hδ hB)
      _ ≤ 1 / 2 := by nlinarith [h]
      _ < 1 := by norm_num
  have hδC : C * δ < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hB1 (mul_nonneg hC hδ.le)
    nlinarith [hδCB]
  have hsmall : ‖L‖ * (C * δ) * ‖w‖ < 1 := by
    have hnorm : ‖L‖ * ‖w‖ ≤ B := by dsimp [B]; linarith
    calc ‖L‖ * (C * δ) * ‖w‖ = (C * δ) * (‖L‖ * ‖w‖) := by ring
      _ ≤ (C * δ) * B := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC hδ.le)
      _ < 1 := hδCB
  refine ⟨δ, hδ, fun φ hφ hφplane => ?_⟩
  let d : E → E := fun x => ∑ v ∈ V, b v x • (φ v - v)
  let kd : NNReal := ⟨C * δ, mul_nonneg hC hδ.le⟩
  have hnorm : ∀ v ∈ V, ‖φ v - v‖ ≤ δ := by
    intro v hv
    simpa only [dist_eq_norm] using (hφ v (hV' v hv)).le
  have hd : IsPiecewiseAffineOn d univ := by
    apply IsPiecewiseAffineOn.sum V isOpen_univ
    intro v _
    exact ((hb v).affine_comp (LinearMap.toSpanSingleton ℝ E (φ v - v)).toAffineMap).congr (fun _ _ => rfl)
  have hdlip : LipschitzWith kd d := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (∑ v ∈ V, b v x • (φ v - v)) (∑ v ∈ V, b v y • (φ v - v)) ≤ _
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ v ∈ V, (b v x • (φ v - v) - b v y • (φ v - v))‖ ≤
          ∑ v ∈ V, ‖b v x • (φ v - v) - b v y • (φ v - v)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ V, (k v : ℝ) * δ * dist x y := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
        calc dist (b v x) (b v y) * ‖φ v - v‖ ≤ ((k v : ℝ) * dist x y) * δ :=
            mul_le_mul ((hk v).dist_le_mul x y) (hnorm v hv) (norm_nonneg _)
              (mul_nonneg (k v).property dist_nonneg)
          _ = (k v : ℝ) * δ * dist x y := by ring
      _ = kd * dist x y := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl
  have hdnorm : ∀ x, ‖d x‖ < ε := by
    intro x
    apply lt_of_le_of_lt _ hδN
    calc ‖d x‖ ≤ ∑ v ∈ V, ‖b v x • (φ v - v)‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ V, δ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbound v x).1]
        calc b v x * ‖φ v - v‖ ≤ 1 * δ :=
            mul_le_mul (hbound v x).2 (hnorm v hv) (norm_nonneg _) zero_le_one
          _ = δ := one_mul _
      _ = (V.card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hdplane : ∀ x, ℓ x = 0 → ℓ (d x) = 0 := by
    intro x hx
    change ℓ (∑ v ∈ V, b v x • (φ v - v)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hv0 : ℓ v = 0
    · rw [map_smul, map_sub, hφplane v (hV' v hv) hv0, hv0, sub_self, smul_zero]
    · have hvpos : 0 < ℓ v := lt_of_le_of_ne (hKℓ v (hV' v hv)) (Ne.symm hv0)
      rw [hplane v hvpos x hx, zero_smul, map_zero]
  have hheight : ∀ x, (ℓ (x + d x) = 0 ↔ ℓ x = 0) ∧ (0 ≤ ℓ (x + d x) ↔ 0 ≤ ℓ x) := by
    intro x
    let q := x - ℓ x • w
    have hq : ℓ q = 0 := by dsimp [q]; rw [map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
    have habs : |ℓ (d x)| ≤ (‖L‖ * (kd : ℝ) * ‖w‖) * |ℓ x| := by
      calc
        |ℓ (d x)| = ‖L (d x - d q)‖ := by
          change |ℓ (d x)| = |ℓ (d x - d q)|
          rw [map_sub, hdplane q hq, sub_zero]
        _ ≤ ‖L‖ * ‖d x - d q‖ := L.le_opNorm _
        _ ≤ ‖L‖ * ((kd : ℝ) * dist x q) := mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using hdlip.dist_le_mul x q) (norm_nonneg _)
        _ = (‖L‖ * (kd : ℝ) * ‖w‖) * |ℓ x| := by
          rw [dist_eq_norm, show x - q = ℓ x • w by dsimp [q]; abel, norm_smul, Real.norm_eq_abs]
          ring
    have hstrict : ℓ x ≠ 0 → |ℓ (d x)| < |ℓ x| := by
      intro hx
      apply habs.trans_lt
      exact mul_lt_of_lt_one_left (abs_pos.mpr hx) hsmall
    rw [map_add]
    rcases lt_trichotomy (ℓ x) 0 with hx | hx | hx
    · have h := abs_lt.mp (hstrict (ne_of_lt hx))
      rw [abs_of_neg hx] at h
      have hsum : ℓ x + ℓ (d x) < 0 := by linarith [h.2]
      exact ⟨iff_of_false (ne_of_lt hsum) (ne_of_lt hx), iff_of_false (not_le_of_gt hsum) (not_le_of_gt hx)⟩
    · simp only [hx, hdplane x hx, add_zero, and_self]
    · have h := abs_lt.mp (hstrict (ne_of_gt hx))
      rw [abs_of_pos hx] at h
      have hsum : 0 < ℓ x + ℓ (d x) := by linarith [h.1]
      exact ⟨iff_of_false (ne_of_gt hsum) (ne_of_gt hx), iff_of_true hsum.le hx.le⟩
  refine ⟨fun x => x + d x, isPLHomeomorphOn_id_add_of_lipschitz hd hdlip hδC, ?_, ?_, ?_, hheight⟩
  · intro x
    simpa only [dist_eq_norm, add_sub_cancel_left] using hdnorm x
  · intro x hx
    have hd0 : d x = 0 := Finset.sum_eq_zero fun v _ => by rw [hzero v hx, zero_smul]
    change x + d x = x
    rw [hd0, add_zero]
  · intro x hx
    have hdmap : d x = simplicialMap K (fun v => φ v - v) x :=
      sum_vertex_functions_smul_eq_simplicialMap K V hV b (fun v _ => hfix v) _ hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have hsub : simplicialMap K (fun v => φ v - v) x = simplicialMap K φ x - x := by
      rw [simplicialMap_eq_of_mem K _ hs hxs, simplicialMap_eq_of_mem K φ hs hxs]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, sum_weights_smul hxs]
    change x + d x = simplicialMap K φ x
    rw [hdmap, hsub]
    abel

end DifferentialGeometry.Topology.PiecewiseLinear
