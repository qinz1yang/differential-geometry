import DifferentialGeometry.Geometry.Comparison.SimplexStrutNeighborhood
import DifferentialGeometry.Geometry.Comparison.AngularDistanceEmbedding

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric Filter
open scoped Topology NNReal

noncomputable def strutChartDistortion (n : ℕ) : ℝ :=
  max (Real.sqrt n) (2 / Real.sin (8 * (n : ℝ))⁻¹)

private noncomputable def euclideanZeroPadding {m n : ℕ} (hmn : m ≤ n) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := by
  let e : Fin m ⊕ Fin (n-m) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hmn))
  let Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin (n-m))) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin (n-m) => ℝ))
  let I : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin (n-m))) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp (LinearMap.inl ℝ _ _)
      norm_map' := fun v => by
        change ‖WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (n-m))))‖ = ‖v‖
        exact WithLp.norm_toLp_fst 2 _ _ v }
  exact Q.symm.toLinearIsometry.comp I

theorem exists_uniform_strut_chart_of_dense_directions
    {X : Type*} {T : Type*} [MetricSpace X] {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p q : X} {R η : ℝ} (hR : 0 < R) (hq : dist q p < R / 2) (hη : 0 < η)
    (ξ : T → {v : EuclideanSpace ℝ (Fin m) // ‖v‖ = 1})
    (γ : T → ℝ → X) (r : T → ℝ)
    (hr : ∀ t, 0 < r t)
    (hradial : ∀ t, ∀ s ∈ Ioc (0 : ℝ) (r t), dist q (γ t s) = s)
    (hdense : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ t, InnerProductGeometry.angle v (ξ t).val < ε)
    (hangle : ∀ t u, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (γ t s) (γ u s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (ξ t).val (ξ u).val)))
    (D : ball p R → Type*) [∀ x, MetricSpace (D x)]
    (direction : ∀ x y : ball p R, x.val ≠ y.val → D x)
    (hangular : ∀ x : ball p R, dist x.val q < η →
      AngularObstruction (D x) m (8 * (n : ℝ))⁻¹)
    (hhinges : ∀ x a y : ball p R, ∀ ha : x.val ≠ a.val, ∀ hy : x.val ≠ y.val,
      ∃ H : MinimizingHinge a.val y.val,
        H.center = x.val ∧ H.germAngle 1 = dist (direction x y hy) (direction x a ha) ∧
          dist a.val y.val ≤ H.modelSide 1) :
    ∃ (d : Fin (m + 1) → T) (s ρ : ℝ), 0 < s ∧ s < R / 8 ∧
      (∀ i, s ≤ r (d i)) ∧ (∀ i, dist q (γ (d i) s) = s) ∧
      ∃ hρ : 0 < ρ, ρ < s / 8 ∧ ρ < η ∧
      (∀ i, γ (d i) s ∈ ball p R) ∧ ball q ρ ⊆ ball p R ∧
      1 ≤ strutChartDistortion n ∧
      ∃ (E : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (F : ball q ρ → EuclideanSpace ℝ (Fin n)),
        (∀ x, F x = E (distanceCoordinates 2 (fun j : Fin m => γ (d j.succ) s) x.val -
          distanceCoordinates 2 (fun j : Fin m => γ (d j.succ) s) q)) ∧
        F ⟨q, mem_ball_self hρ⟩ = 0 ∧
        (∀ x y, (strutChartDistortion n)⁻¹ * dist x y ≤ dist (F x) (F y) ∧
          dist (F x) (F y) ≤ strutChartDistortion n * dist x y) ∧
        ∃ e : ball q ρ ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = F x := by
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmn
  let θ : ℝ := (8 * (n : ℝ))⁻¹
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθle : θ ≤ 1 / 8 := by
    dsimp [θ]
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hθhalf : θ < Real.pi / 2 := by
    have hp := Real.sin_le (show 0 ≤ Real.pi / 2 by positivity)
    rw [Real.sin_pi_div_two] at hp
    linarith
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
  obtain ⟨d, s, hs, hsR, hsr, hsa, _hdirangle, hcomp⟩ :=
    exists_common_shortening_strut_of_dense_directions hm hmn q ξ γ r hr hradial hdense hangle
      (show 0 < R / 8 by positivity)
  let a : Fin (m + 1) → X := fun i => γ (d i) s
  have hscale : 0 < shortHingeScale (s / 2) θ :=
    shortHingeScale_pos (by positivity) hθ hθhalf
  obtain ⟨ρ, hρ, hρs, hρcap, hdist, hstrut⟩ := exists_ball_strut_margin hs hθ
    (lt_min hη (half_pos hscale)) a hsa hcomp
  have hρη : ρ < η := hρcap.trans_le (min_le_left _ _)
  have hρscale : 2 * ρ ≤ shortHingeScale (s / 2) θ := by
    have hh := hρcap.trans_le (min_le_right _ _)
    linarith
  have haR (i : Fin (m + 1)) : a i ∈ ball p R := by
    have ht := dist_triangle (a i) q p
    rw [dist_comm (a i) q, hsa] at ht
    change dist (a i) p < R
    linarith
  have hsubset : ball q ρ ⊆ ball p R := by
    intro x hx
    have ht := dist_triangle x q p
    have hx' : dist x q < ρ := hx
    change dist x p < R
    linarith
  let lift : ball q ρ → ball p R := fun x => ⟨x.val, hsubset x.property⟩
  let aa (i : Fin (m + 1)) : ball p R := ⟨a i, haR i⟩
  have hne (x : ball q ρ) (i : Fin (m + 1)) : x.val ≠ a i :=
    dist_pos.mp ((half_pos hs).trans (hdist x.val x.property i))
  let ζ (x : ball q ρ) (i : Fin (m + 1)) : D (lift x) := direction (lift x) (aa i) (hne x i)
  have hsep (x : ball q ρ) (i j : Fin (m + 1)) (hij : i ≠ j) :
      Real.pi / 2 + θ < dist (ζ x i) (ζ x j) := by
    obtain ⟨H, hc, hHangle, hHcomp⟩ := hhinges (lift x) (aa j) (aa i) (hne x j) (hne x i)
    have hbound := (H.comparisonAngle_le_iff_dist_le_modelSide (by norm_num : (0 : ℝ) ≤ 1)
      (by rw [hc]; exact dist_pos.mpr (hne x j))
      (by rw [hc]; exact dist_pos.mpr (hne x i))).mpr hHcomp
    rw [hc, hHangle] at hbound
    have hstrict := hstrut x.val x.property j i hij.symm
    change Real.pi / 2 + θ < dist (direction (lift x) (aa i) (hne x i))
      (direction (lift x) (aa j) (hne x j))
    linarith
  have hH (x y : ball q ρ) (hxy : x ≠ y) :
      ∃ ξ' : D (lift x), ∀ j, ∃ H : MinimizingHinge (a j) y.val,
        H.center = x.val ∧ H.germAngle 1 = dist ξ' (ζ x j) ∧ dist (a j) y.val ≤ H.modelSide 1 := by
    have hxy' : x.val ≠ y.val := fun hh => hxy (Subtype.ext hh)
    exact ⟨direction (lift x) (lift y) hxy', fun j => hhinges (lift x) (aa j) (lift y) (hne x j) hxy'⟩
  obtain ⟨hzero, hlo, hLip, _he⟩ := exists_centered_distance_embedding_of_angular_obstruction
    hρ (half_pos hs) hθ hθhalf a (fun x => D (lift x)) ζ
    (fun x i => (hdist x.val x.property i).le) hρscale hsep
    (fun x => hangular (lift x) ((show dist x.val q < ρ from x.property).trans hρη)) hH
  let G : ball q ρ → EuclideanSpace ℝ (Fin m) := fun x =>
    distanceCoordinates 2 (fun j : Fin m => a j.succ) x.val -
      distanceCoordinates 2 (fun j : Fin m => a j.succ) q
  let E := euclideanZeroPadding hmn
  let F : ball q ρ → EuclideanSpace ℝ (Fin n) := fun x => E (G x)
  have hL : 1 ≤ strutChartDistortion n := by
    have hh : 1 ≤ 2 / Real.sin θ := (le_div_iff₀ hsin).mpr (by linarith [Real.sin_le_one θ])
    exact hh.trans (le_max_right _ _)
  have hLipF : LipschitzWith (NNReal.sqrt m) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (E (G x)) (E (G y)) ≤ _
    rw [E.isometry.dist_eq]
    exact hLip.dist_le_mul x y
  have hloF (x y : ball q ρ) : (Real.sin θ / 2) * dist x y ≤ dist (F x) (F y) := by
    change (Real.sin θ / 2) * dist x y ≤ dist (E (G x)) (E (G y))
    rw [E.isometry.dist_eq]
    exact hlo x y
  have hLinv : (strutChartDistortion n)⁻¹ ≤ Real.sin θ / 2 := by
    have hpositive : 0 < strutChartDistortion n := lt_of_lt_of_le zero_lt_one hL
    have hh : 2 / Real.sin θ ≤ strutChartDistortion n := le_max_right _ _
    apply (mul_le_mul_iff_of_pos_left hpositive).mp
    rw [mul_inv_cancel₀ hpositive.ne']
    have ht := (div_le_iff₀ hsin).mp hh
    nlinarith
  have hsqrt : (NNReal.sqrt m : ℝ) ≤ strutChartDistortion n := by
    rw [Real.coe_sqrt, NNReal.coe_natCast]
    exact (Real.sqrt_le_sqrt (by exact_mod_cast hmn)).trans (le_max_left _ _)
  obtain ⟨e, he, _, _⟩ := exists_homeomorph_range_of_lipschitz_lower_bound
    (ε := ⟨Real.sin θ / 2, by positivity⟩) hLipF
      (show (0 : ℝ) < Real.sin θ / 2 by positivity) hloF
  refine ⟨d, s, ρ, hs, hsR, hsr, hsa, hρ, hρs, hρη, haR, hsubset, hL, E, F,
    (fun _ => rfl), ?_, ?_, e, he⟩
  · change E (G ⟨q, mem_ball_self hρ⟩) = 0
    rw [show G ⟨q, mem_ball_self hρ⟩ = 0 from hzero, map_zero]
  · intro x y
    exact ⟨(mul_le_mul_of_nonneg_right hLinv dist_nonneg).trans (hloF x y),
      (hLipF.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hsqrt dist_nonneg)⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
