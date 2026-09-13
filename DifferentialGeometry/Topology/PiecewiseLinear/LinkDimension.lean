import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stdSimplex_fin_one_subsingleton : (stdSimplex ℝ (Fin 1)).Subsingleton := by
  rw [stdSimplex_unique]
  exact subsingleton_singleton

theorem stdSimplexBoundary_one_finite : (stdSimplexBoundary 1).Finite := by
  have hfin2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  have hsub : stdSimplexBoundary 1 ⊆
      {fun j => if j = 0 then (1 : ℝ) else 0, fun j => if j = 0 then (0 : ℝ) else 1} := by
    rintro x ⟨⟨hx0, hx1⟩, i, hi⟩
    rw [Fin.sum_univ_two] at hx1
    have h0 : (0 : ℝ) ≤ x 0 := hx0 0
    have h1 : (0 : ℝ) ≤ x 1 := hx0 1
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hfin2 i with rfl | rfl
    · refine Or.inr (funext fun j => ?_)
      rcases hfin2 j with rfl | rfl
      · simpa using hi
      · rw [if_neg (by decide : ¬ (1 : Fin 2) = 0)]
        linarith
    · refine Or.inl (funext fun j => ?_)
      rcases hfin2 j with rfl | rfl
      · rw [if_pos (rfl : (0 : Fin 2) = 0)]
        linarith
      · simpa using hi
  exact ((finite_singleton _).insert _).subset hsub

theorem IsPLBall.subsingleton_of_zero {P : Set E} (h : IsPLBall 0 P) : P.Subsingleton := by
  obtain ⟨f, hf⟩ := h
  rw [← hf.1.image_eq]
  exact stdSimplex_fin_one_subsingleton.image f

theorem IsPLSphere.finite_of_zero {P : Set E} (h : IsPLSphere 0 P) : P.Finite := by
  obtain ⟨f, hf⟩ := h
  rw [← hf.1.image_eq]
  exact stdSimplexBoundary_one_finite.image f

theorem infinite_convexHull_pair {a b : E} (hab : a ≠ b) :
    (convexHull ℝ ({a, b} : Set E)).Infinite := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hinj : InjOn (fun θ : ℝ => (1 - θ) • a + θ • b) (Icc (0 : ℝ) 1) := by
    intro θ _ θ' _ h
    have h' : (1 - θ) • a + θ • b = (1 - θ') • a + θ' • b := h
    have hsmul : (θ - θ') • (b - a) = 0 := by
      have hrw : ((1 - θ) • a + θ • b) - ((1 - θ') • a + θ' • b) = (θ - θ') • (b - a) := by
        module
      rw [← hrw, h', sub_self]
    by_contra hne
    have hθ : θ - θ' ≠ 0 := sub_ne_zero.mpr hne
    refine hba ?_
    calc b - a = (θ - θ')⁻¹ • ((θ - θ') • (b - a)) := by
          rw [smul_smul, inv_mul_cancel₀ hθ, one_smul]
      _ = 0 := by rw [hsmul, smul_zero]
  rw [convexHull_pair, segment_eq_image]
  exact Set.infinite_of_injOn_mapsTo hinj (mapsTo_image _ _)
    (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1))

theorem card_le_of_isPLBall_or_isPLSphere [FiniteDimensional ℝ E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall m K.space ∨ IsPLSphere m K.space) {s : Finset E} (hs : s ∈ K.faces) :
    s.card ≤ m + 1 := by
  classical
  have key : ∀ (n : ℕ) (L : Geometry.SimplicialComplex ℝ E), Finite L.faces →
      (IsPLBall n L.space ∨ IsPLSphere n L.space) → ∀ t ∈ L.faces, Finset.card t ≤ n + 1 := by
    intro n
    induction n with
    | zero =>
      intro L _ hL t ht
      by_contra hcon
      obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := t)).mp (by omega)
      have hpair : ({a, b} : Set E) ⊆ (t : Set E) := by
        intro y hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hb
      have hsub : convexHull ℝ ({a, b} : Set E) ⊆ L.space :=
        (convexHull_mono hpair).trans (L.convexHull_subset_space ht)
      have hfin : L.space.Finite := by
        rcases hL with h | h
        · exact h.subsingleton_of_zero.finite
        · exact h.finite_of_zero
      exact infinite_convexHull_pair hab (hfin.subset hsub)
    | succ n ih =>
      intro L hLfin hL t ht
      have hinst : Finite L.faces := hLfin
      by_contra hcon
      obtain ⟨v, hv⟩ : t.Nonempty := Finset.card_pos.mp (by omega)
      have hcard : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hv
      have hv' : {v} ∈ L.faces :=
        L.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hmem : t.erase v ∈ (SimplicialComplex.geometricLink L {v}).faces :=
        (SimplicialComplex.mem_geometricLink_singleton L v (t.erase v)).mpr
          ⟨Finset.card_pos.mp (by omega), Finset.notMem_erase v t, by
            rw [Finset.insert_erase hv]; exact ht⟩
      have hlink : IsPLBall n (SimplicialComplex.geometricLink L {v}).space ∨
          IsPLSphere n (SimplicialComplex.geometricLink L {v}).space := by
        rcases hL with h | h
        · exact (isPLSphere_or_isPLBall_geometricLink_of_isPLBall L h hv').symm
        · exact Or.inr (isPLSphere_geometricLink_of_isPLSphere L h hv')
      have hle := ih _ inferInstance hlink _ hmem
      omega
  exact key m K inferInstance hK s hs

theorem card_le_of_isPLBall [FiniteDimensional ℝ E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall m K.space)
    {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ m + 1 :=
  card_le_of_isPLBall_or_isPLSphere K (Or.inl hK) hs

theorem card_le_of_isPLSphere [FiniteDimensional ℝ E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere m K.space)
    {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ m + 1 :=
  card_le_of_isPLBall_or_isPLSphere K (Or.inr hK) hs

theorem convexHull_subset_closure_openSimplex {s : Finset E} (hs : s.Nonempty) :
    convexHull ℝ (s : Set E) ⊆ closure (openSimplex s) := by
  intro x hx
  obtain ⟨w, hw₀, hw₁, hwx⟩ := mem_convexHull_iff_exists_weights.mp hx
  have hNpos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hNne : ((s.card : ℝ)) ≠ 0 := ne_of_gt hNpos
  have hcont : Continuous fun ε : ℝ => (1 - ε) • x + ε • ∑ v ∈ s, ((s.card : ℝ)⁻¹ • v) := by
    fun_prop
  have htend : Filter.Tendsto
      (fun ε : ℝ => (1 - ε) • x + ε • ∑ v ∈ s, ((s.card : ℝ)⁻¹ • v))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x) := by
    have h0 := (hcont.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi (0 : ℝ)))
    rwa [sub_zero, one_smul, zero_smul, add_zero] at h0
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [inter_mem_nhdsWithin (Ioi (0 : ℝ))
    (isOpen_Iio.mem_nhds (mem_Iio.mpr (by norm_num : (0 : ℝ) < 1)))] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  rw [mem_Ioi] at hε0
  rw [mem_Iio] at hε1
  refine ⟨fun v => (1 - ε) * w v + ε * ((s.card : ℝ)⁻¹), ?_, ?_, ?_⟩
  · intro v hv
    have hp1 : 0 ≤ (1 - ε) * w v := mul_nonneg (by linarith) (hw₀ v hv)
    have hp2 : 0 < ε * ((s.card : ℝ)⁻¹) := mul_pos hε0 (inv_pos.mpr hNpos)
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw₁, Finset.sum_const,
      nsmul_eq_mul, mul_inv_cancel₀ hNne]
    ring
  · have hterm : ∀ v ∈ s, ((1 - ε) * w v + ε * ((s.card : ℝ)⁻¹)) • v
        = (1 - ε) • (w v • v) + ε • (((s.card : ℝ)⁻¹) • v) := by
      intro v _
      rw [add_smul, mul_smul, mul_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.smul_sum,
      ← Finset.smul_sum, hwx]

end DifferentialGeometry.Topology.PiecewiseLinear
