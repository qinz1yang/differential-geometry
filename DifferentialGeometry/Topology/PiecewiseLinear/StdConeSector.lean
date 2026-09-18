import DifferentialGeometry.Topology.PiecewiseLinear.StdConeLayers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def stdConeSector (u u' : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1 ∧ u * (z.1 + z.2) ≤ z.2 ∧ z.2 ≤ u' * (z.1 + z.2)}

noncomputable def sectorCoeffFst (u u' : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (u' / (u' - u)) • LinearMap.fst ℝ ℝ ℝ + ((u' - 1) / (u' - u)) • LinearMap.snd ℝ ℝ ℝ

noncomputable def sectorCoeffSnd (u u' : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (-u / (u' - u)) • LinearMap.fst ℝ ℝ ℝ + ((1 - u) / (u' - u)) • LinearMap.snd ℝ ℝ ℝ

noncomputable def sectorCoord (u u' : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (sectorCoeffFst u u').prod (sectorCoeffSnd u u')

theorem sectorCoord_apply (u u' : ℝ) (z : ℝ × ℝ) :
    sectorCoord u u' z =
      (u' / (u' - u) * z.1 + (u' - 1) / (u' - u) * z.2,
        -u / (u' - u) * z.1 + (1 - u) / (u' - u) * z.2) := rfl

theorem sectorCoord_fst (u u' : ℝ) (z : ℝ × ℝ) :
    (sectorCoord u u' z).1 = (u' * (z.1 + z.2) - z.2) / (u' - u) := by
  rw [sectorCoord_apply]
  simp only
  ring

theorem sectorCoord_snd (u u' : ℝ) (z : ℝ × ℝ) :
    (sectorCoord u u' z).2 = (z.2 - u * (z.1 + z.2)) / (u' - u) := by
  rw [sectorCoord_apply]
  simp only
  ring

theorem sectorCoord_add {u u' : ℝ} (h : u < u') (z : ℝ × ℝ) :
    (sectorCoord u u' z).1 + (sectorCoord u u' z).2 = z.1 + z.2 := by
  have hne : u' - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  rw [sectorCoord_fst, sectorCoord_snd]
  field_simp
  ring

theorem mapsTo_sectorCoord {u u' : ℝ} (h : u < u') :
    MapsTo (sectorCoord u u') (stdConeSector u u') stdCone := by
  rintro z ⟨h1, h2, h3, h4, h5⟩
  have hd : 0 < u' - u := sub_pos.mpr h
  refine ⟨?_, ?_, ?_⟩
  · rw [sectorCoord_fst]
    exact div_nonneg (by linarith) hd.le
  · rw [sectorCoord_snd]
    exact div_nonneg (by linarith) hd.le
  · rw [sectorCoord_add h]
    exact h3

theorem sectorCoord_smul_left {u u' : ℝ} (h : u < u') (t : ℝ) :
    sectorCoord u u' (t * (1 - u), t * u) = (t, 0) := by
  have hne : u' - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  rw [sectorCoord_apply]
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

theorem sectorCoord_smul_right {u u' : ℝ} (h : u < u') (t : ℝ) :
    sectorCoord u u' (t * (1 - u'), t * u') = (0, t) := by
  have hne : u' - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  rw [sectorCoord_apply]
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

theorem sectorCoord_outer {u u' : ℝ} (h : u < u') (r : ℝ) :
    sectorCoord u u' (1 - r, r) = ((u' - r) / (u' - u), (r - u) / (u' - u)) := by
  have hne : u' - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  rw [sectorCoord_apply]
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

theorem mem_stdConeSector_smul_left {u u' : ℝ} (h : u ≤ u') (hu : 0 ≤ u) (hu' : u' ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((t * (1 - u), t * u) : ℝ × ℝ) ∈ stdConeSector u u' := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem mem_stdConeSector_smul_right {u u' : ℝ} (h : u ≤ u') (hu : 0 ≤ u) (hu' : u' ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((t * (1 - u'), t * u') : ℝ × ℝ) ∈ stdConeSector u u' := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem stdConeSector_subset (u u' : ℝ) :
    stdConeSector u u' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro z ⟨h1, h2, h3, -, -⟩
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩

theorem stdConeSector_subset_stdCone (u u' : ℝ) : stdConeSector u u' ⊆ stdCone := by
  rintro z ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, h2, h3⟩

theorem isHPolytope_stdConeSector (u u' : ℝ) : IsHPolytope (stdConeSector u u') := by
  refine ⟨?_, Fin 5, inferInstance,
    ![-(LinearMap.fst ℝ ℝ ℝ), -(LinearMap.snd ℝ ℝ ℝ),
      LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ,
      u • LinearMap.fst ℝ ℝ ℝ + (u - 1) • LinearMap.snd ℝ ℝ ℝ,
      (-u') • LinearMap.fst ℝ ℝ ℝ + (1 - u') • LinearMap.snd ℝ ℝ ℝ],
    ![0, 0, 1, 0, 0], ?_⟩
  · refine IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) ?_
      (stdConeSector_subset u u')
    have hrw : stdConeSector u u' = ({z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | 0 ≤ z.2}) ∩
        ({z : ℝ × ℝ | z.1 + z.2 ≤ 1} ∩
          ({z : ℝ × ℝ | u * (z.1 + z.2) ≤ z.2} ∩ {z : ℝ × ℝ | z.2 ≤ u' * (z.1 + z.2)})) := by
      ext z
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩⟩,
        fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2⟩⟩
    rw [hrw]
    exact ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)).inter
      ((isClosed_le (continuous_fst.add continuous_snd) continuous_const).inter
        ((isClosed_le (continuous_const.mul (continuous_fst.add continuous_snd)) continuous_snd).inter
          (isClosed_le continuous_snd (continuous_const.mul (continuous_fst.add continuous_snd)))))
  · ext z
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩ i
      fin_cases i <;> simp <;> linarith
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      have h4 := h 4
      simp at h0 h1 h2 h3 h4
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_mem_Icc_of_subdivision {N : ℕ} {σ : ℕ → ℝ} (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k ≤ N, t ∈ Icc (σ k) (σ (k + 1)) := by
  classical
  have hP0 : (fun j => σ j ≤ t) 0 := by
    change σ 0 ≤ t
    rw [hσ0]
    exact ht.1
  set k := Nat.findGreatest (fun j => σ j ≤ t) N with hk
  have hkle : k ≤ N := Nat.findGreatest_le N
  have hspec : (fun j => σ j ≤ t) k := Nat.findGreatest_spec (P := fun j => σ j ≤ t)
    (Nat.zero_le N) hP0
  refine ⟨k, hkle, hspec, ?_⟩
  rcases eq_or_lt_of_le hkle with heq | hlt
  · rw [heq, hσN]
    exact ht.2
  · by_contra hcon
    have hkk : Nat.findGreatest (fun j => σ j ≤ t) N < k + 1 := by rw [← hk]; omega
    have hgt : ¬ ((fun j => σ j ≤ t) (k + 1)) :=
      Nat.findGreatest_is_greatest (P := fun j => σ j ≤ t) hkk (by omega)
    exact absurd ((not_le.mp hcon).le : σ (k + 1) ≤ t) hgt

theorem stdConeSector_union {M : ℕ} {u : ℕ → ℝ} (hu0 : u 0 = 0) (huM : u (M + 1) = 1) :
    ⋃ j ≤ M, stdConeSector (u j) (u (j + 1)) = stdCone := by
  ext z
  constructor
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨j, -, hj⟩ := hz
    exact stdConeSector_subset_stdCone _ _ hj
  · rintro ⟨h1, h2, h3⟩
    simp only [Set.mem_iUnion]
    rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ z.1 + z.2) with hzero | hpos
    · refine ⟨0, by omega, ?_⟩
      have hx : z.1 = 0 := by linarith
      have hy : z.2 = 0 := by linarith
      refine ⟨by linarith, by linarith, by linarith, ?_, ?_⟩ <;> rw [hx, hy] <;> simp
    · have hmem : z.2 / (z.1 + z.2) ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg h2 hpos.le
        · rw [div_le_one hpos]
          linarith
      obtain ⟨j, hj, hj1, hj2⟩ := exists_mem_Icc_of_subdivision hu0 huM hmem
      refine ⟨j, by omega, h1, h2, h3, ?_, ?_⟩
      · rw [le_div_iff₀ hpos] at hj1
        linarith
      · rw [div_le_iff₀ hpos] at hj2
        linarith

theorem eq_smul_of_snd_eq {u : ℝ} {z : ℝ × ℝ} (h : z.2 = u * (z.1 + z.2)) :
    z = ((z.1 + z.2) * (1 - u), (z.1 + z.2) * u) := by
  refine Prod.ext ?_ ?_ <;> simp only <;> nlinarith

theorem eq_smul_of_mem_inter {ua ub uc ud : ℝ} (h : ub ≤ uc) {z : ℝ × ℝ}
    (hz : z ∈ stdConeSector ua ub) (hz' : z ∈ stdConeSector uc ud) :
    z = ((z.1 + z.2) * (1 - uc), (z.1 + z.2) * uc) := by
  obtain ⟨h1, h2, -, -, h5⟩ := hz
  obtain ⟨-, -, -, h9, -⟩ := hz'
  exact eq_smul_of_snd_eq (by nlinarith)

end DifferentialGeometry.Topology.PiecewiseLinear
