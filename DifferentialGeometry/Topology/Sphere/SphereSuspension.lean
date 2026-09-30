import DifferentialGeometry.Topology.HighDimensional.TwistedSphere

namespace DifferentialGeometry.Topology

open Set Metric

abbrev SuspensionInterval : Type := Icc (-1 : ℝ) 1

noncomputable def suspensionRadius (t : SuspensionInterval) : ℝ :=
  Real.sqrt (1 - (t : ℝ) ^ 2)

theorem one_sub_suspensionHeight_sq_nonneg (t : SuspensionInterval) :
    0 ≤ 1 - (t : ℝ) ^ 2 := by
  have ht := t.property
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 0 ≤ (t : ℝ) + 1)]

theorem suspensionRadius_nonneg (t : SuspensionInterval) : 0 ≤ suspensionRadius t :=
  Real.sqrt_nonneg _

theorem suspensionRadius_sq (t : SuspensionInterval) :
    suspensionRadius t ^ 2 = 1 - (t : ℝ) ^ 2 :=
  Real.sq_sqrt (one_sub_suspensionHeight_sq_nonneg t)

theorem suspensionRadius_eq_zero_iff (t : SuspensionInterval) :
    suspensionRadius t = 0 ↔ (t : ℝ) = -1 ∨ (t : ℝ) = 1 := by
  rw [suspensionRadius, Real.sqrt_eq_zero (one_sub_suspensionHeight_sq_nonneg t)]
  constructor
  · intro ht
    have hprod : ((t : ℝ) + 1) * ((t : ℝ) - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (ht | ht) <;> rw [ht] <;> norm_num

theorem continuous_suspensionRadius : Continuous suspensionRadius :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_subtype_val.pow 2))

noncomputable def sphereSuspension (m : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  ⟨euclidSnoc (suspensionRadius p.2 • (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) p.2, by
    rw [mem_sphere_zero_iff_norm]
    have hs : ‖(p.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp p.1.property
    have hsq : ‖euclidSnoc (suspensionRadius p.2 •
        (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) p.2‖ ^ 2 = 1 := by
      rw [norm_euclidSnoc_sq, norm_smul, Real.norm_of_nonneg (suspensionRadius_nonneg _),
        hs, mul_one, suspensionRadius_sq]
      ring
    have hn := norm_nonneg (euclidSnoc (suspensionRadius p.2 •
      (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) p.2)
    nlinarith⟩

theorem sphereSuspension_coe (m : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
    (sphereSuspension m p : EuclideanSpace ℝ (Fin (m + 2))) =
      euclidSnoc (suspensionRadius p.2 • (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) p.2 := rfl

theorem continuous_sphereSuspension (m : ℕ) : Continuous (sphereSuspension m) := by
  apply Continuous.subtype_mk
  exact continuous_euclidSnoc
    ((continuous_suspensionRadius.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst))
    (continuous_subtype_val.comp continuous_snd)

theorem sphereSuspension_last (m : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
    (sphereSuspension m p : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = p.2 :=
  euclidSnoc_apply_last _ _

theorem sphereSuspension_eq_iff {m : ℕ}
    (s r : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (t u : SuspensionInterval) :
    sphereSuspension m (s, t) = sphereSuspension m (r, u) ↔
      t = u ∧ (s = r ∨ (t : ℝ) = -1 ∨ (t : ℝ) = 1) := by
  constructor
  · intro h
    have he := euclidSnoc_inj.mp (congrArg Subtype.val h)
    have htu : t = u := Subtype.ext he.2
    subst u
    refine ⟨rfl, ?_⟩
    by_cases ht : suspensionRadius t = 0
    · exact Or.inr ((suspensionRadius_eq_zero_iff t).mp ht)
    · exact Or.inl (Subtype.ext (smul_right_injective _ ht he.1))
  · rintro ⟨rfl, h | h⟩
    · rw [h]
    · apply Subtype.ext
      rw [sphereSuspension_coe, sphereSuspension_coe]
      have hz := (suspensionRadius_eq_zero_iff t).mpr h
      simp only [hz, zero_smul]

noncomputable def sphereSouthPole (m : ℕ) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  ⟨euclidSnoc (0 : EuclideanSpace ℝ (Fin (m + 1))) (-1), by
    rw [mem_sphere_zero_iff_norm]
    have hs := norm_euclidSnoc_sq (0 : EuclideanSpace ℝ (Fin (m + 1))) (-1)
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), neg_one_sq, zero_add] at hs
    have hn := norm_nonneg (euclidSnoc (0 : EuclideanSpace ℝ (Fin (m + 1))) (-1))
    nlinarith⟩

noncomputable def sphereNorthPole (m : ℕ) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  ⟨euclidSnoc (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, by
    rw [mem_sphere_zero_iff_norm]
    have hs := norm_euclidSnoc_sq (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, zero_add] at hs
    have hn := norm_nonneg (euclidSnoc (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    nlinarith⟩

@[simp]
theorem sphereSuspension_south {m : ℕ}
    (s : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    sphereSuspension m (s, ⟨-1, by norm_num⟩) = sphereSouthPole m := by
  apply Subtype.ext
  simp [sphereSuspension, sphereSouthPole, suspensionRadius]

@[simp]
theorem sphereSuspension_north {m : ℕ}
    (s : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    sphereSuspension m (s, ⟨1, by norm_num⟩) = sphereNorthPole m := by
  apply Subtype.ext
  simp [sphereSuspension, sphereNorthPole, suspensionRadius]

theorem sphereSouthPole_ne_northPole (m : ℕ) : sphereSouthPole m ≠ sphereNorthPole m := by
  intro h
  have he := congrArg (fun z : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 =>
    (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))) h
  norm_num [sphereSouthPole, sphereNorthPole, euclidSnoc_apply_last] at he

theorem sphereSuspension_eq_south_iff {m : ℕ}
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
    sphereSuspension m p = sphereSouthPole m ↔ (p.2 : ℝ) = -1 := by
  constructor
  · intro h
    have he := congrArg (fun z : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 =>
      (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))) h
    simpa only [sphereSuspension_last, sphereSouthPole, euclidSnoc_apply_last] using he
  · intro ht
    obtain ⟨s, t⟩ := p
    have he : t = ⟨-1, by norm_num⟩ := Subtype.ext ht
    subst t
    exact sphereSuspension_south s

theorem sphereSuspension_eq_north_iff {m : ℕ}
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
    sphereSuspension m p = sphereNorthPole m ↔ (p.2 : ℝ) = 1 := by
  constructor
  · intro h
    have he := congrArg (fun z : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 =>
      (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))) h
    simpa only [sphereSuspension_last, sphereNorthPole, euclidSnoc_apply_last] using he
  · intro ht
    obtain ⟨s, t⟩ := p
    have he : t = ⟨1, by norm_num⟩ := Subtype.ext ht
    subst t
    exact sphereSuspension_north s

theorem sphereSuspension_surjective (m : ℕ) : Function.Surjective (sphereSuspension m) := by
  intro z
  let x := euclidInit (z : EuclideanSpace ℝ (Fin (m + 2)))
  let t := (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))
  have hzx : euclidSnoc x t = z := euclidSnoc_euclidInit _
  have hz : ‖(z : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp z.property
  have hsq : ‖x‖ ^ 2 + t ^ 2 = 1 := by
    rw [← norm_euclidSnoc_sq, hzx, hz]
    norm_num
  have ht : t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg ‖x‖, sq_nonneg (t - 1), sq_nonneg (t + 1)]
  let ti : SuspensionInterval := ⟨t, ht⟩
  have hr : suspensionRadius ti = ‖x‖ := by
    unfold suspensionRadius
    change Real.sqrt (1 - t ^ 2) = ‖x‖
    rw [show 1 - t ^ 2 = ‖x‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg x)]
  by_cases hx : x = 0
  · obtain ⟨s⟩ : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
    refine ⟨(s, ti), Subtype.ext ?_⟩
    rw [sphereSuspension_coe]
    change euclidSnoc (suspensionRadius ti • (s : EuclideanSpace ℝ (Fin (m + 1)))) t = z
    rw [hr, hx, norm_zero, zero_smul]
    exact hx ▸ hzx
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let s : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv,
          Real.norm_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hxn]⟩
    refine ⟨(s, ti), Subtype.ext ?_⟩
    rw [sphereSuspension_coe]
    change euclidSnoc (suspensionRadius ti • ‖x‖⁻¹ • x) t = z
    rw [hr, smul_inv_smul₀ hxn]
    exact hzx

noncomputable def sphereEquator (m : ℕ)
    (s : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  sphereSuspension m (s, ⟨0, by norm_num⟩)

theorem sphereEquator_coe {m : ℕ}
    (s : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (sphereEquator m s : EuclideanSpace ℝ (Fin (m + 2))) =
      euclidSnoc (s : EuclideanSpace ℝ (Fin (m + 1))) 0 := by
  simp [sphereEquator, sphereSuspension, suspensionRadius]

theorem continuous_sphereEquator (m : ℕ) : Continuous (sphereEquator m) :=
  (continuous_sphereSuspension m).comp (continuous_id.prodMk continuous_const)

theorem sphereEquator_injective (m : ℕ) : Function.Injective (sphereEquator m) := by
  intro s r h
  have hh := (sphereSuspension_eq_iff s r ⟨0, by norm_num⟩ ⟨0, by norm_num⟩).mp h
  simpa using hh.2

end DifferentialGeometry.Topology
