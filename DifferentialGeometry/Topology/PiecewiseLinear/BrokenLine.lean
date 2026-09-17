import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineMap_apply_eq_interp (A : ℝ →ᵃ[ℝ] F) {p q : ℝ} (hpq : p ≠ q) (x : ℝ) :
    A x = A p + ((x - p) / (q - p)) • (A q - A p) := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have e1 : A x - A p = (x - p) • A.linear 1 := by
    have h := A.linearMap_vsub x p
    simp only [vsub_eq_sub] at h
    rw [← h, ← LinearMap.map_smul]
    simp
  have e2 : A q - A p = (q - p) • A.linear 1 := by
    have h := A.linearMap_vsub q p
    simp only [vsub_eq_sub] at h
    rw [← h, ← LinearMap.map_smul]
    simp
  rw [e2, smul_smul, div_mul_cancel₀ _ hd, ← e1]
  abel

theorem convexHull_coe_finset_real {u : Finset ℝ} (hu : u.Nonempty) :
    convexHull ℝ (u : Set ℝ) = Icc (u.min' hu) (u.max' hu) := by
  refine Subset.antisymm (convexHull_min (fun x hx => ⟨u.min'_le x hx, u.le_max' x hx⟩)
    (convex_Icc _ _)) ?_
  rw [← segment_eq_Icc (u.min'_le _ (u.max'_mem hu))]
  exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (u.min'_mem hu))
    (subset_convexHull ℝ _ (u.max'_mem hu))

open Classical in
theorem exists_partition_affineOn_two {f g : ℝ → F}
    (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1)) (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (s : ℕ → ℝ), s 0 = 0 ∧ s n = 1 ∧ (∀ i < n, s i < s (i + 1)) ∧
      (∀ i < n, s (i + 1) - s i < δ) ∧
      (∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
        f x = f (s i) + ((x - s i) / (s (i + 1) - s i)) • (f (s (i + 1)) - f (s i))) ∧
      (∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
        g x = g (s i) + ((x - s i) / (s (i + 1) - s i)) • (g (s (i + 1)) - g (s i))) := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ :=
    IsPolyhedron.exists_simplicialComplex (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨K₀, hK₀, hK₀fin, haff₀⟩ :=
    exists_isSubdivision_affineOn_faces_finite K (fun i : Bool => cond i f g) (by
      intro i
      rw [hKspace]
      cases i
      · exact hg
      · exact hf)
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  obtain ⟨K', hK'sub, hK'fin, -, hK'diam⟩ :=
    exists_isSubdivision_diam_lt K₀ (N := Module.finrank ℝ ℝ)
      (fun t ht => card_le_finrank_succ_of_mem_faces K₀ ht) hδ
  have haff : ∀ i : Bool, ∀ t ∈ K'.faces, ∃ A : ℝ →ᵃ[ℝ] F,
      EqOn (cond i f g) A (convexHull ℝ (t : Set ℝ)) := by
    intro i t ht
    obtain ⟨t₀, ht₀, hsub⟩ := hK'sub.exists_face_subset ht
    obtain ⟨A, hA⟩ := haff₀ i t₀ ht₀
    exact ⟨A, fun x hx => hA (hsub hx)⟩
  have hK' : IsSubdivision K' K := hK'sub.trans hK₀
  have hK'space : K'.space = Icc (0 : ℝ) 1 := by rw [hK'.space_eq, hKspace]
  set P : Finset ℝ := hK'fin.toFinset.biUnion id with hPdef
  have hmemP : ∀ x, x ∈ P ↔ ∃ u ∈ K'.faces, x ∈ u := by
    intro x
    rw [hPdef, Finset.mem_biUnion]
    exact ⟨fun ⟨u, hu, hx⟩ => ⟨u, hK'fin.mem_toFinset.mp hu, hx⟩,
      fun ⟨u, hu, hx⟩ => ⟨u, hK'fin.mem_toFinset.mpr hu, hx⟩⟩
  have hPsub : ∀ x ∈ P, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (hmemP x).mp hx
    rw [← hK'space]
    exact K'.convexHull_subset_space hu (subset_convexHull ℝ _ hxu)
  have hend : ∀ y ∈ Icc (0 : ℝ) 1, (∀ z ∈ Icc (0 : ℝ) 1, y ≤ z) ∨ (∀ z ∈ Icc (0 : ℝ) 1, z ≤ y) →
      y ∈ P := by
    intro y hy hext
    obtain ⟨u, hu, hyu⟩ := K'.mem_space_iff.mp (by rw [hK'space]; exact hy)
    have hune : u.Nonempty := K'.nonempty_of_mem_faces hu
    rw [convexHull_coe_finset_real hune] at hyu
    have husub : ∀ z ∈ u, z ∈ Icc (0 : ℝ) 1 := fun z hz =>
      hPsub z ((hmemP z).mpr ⟨u, hu, hz⟩)
    rcases hext with h | h
    · have : y = u.min' hune := le_antisymm (h _ (husub _ (u.min'_mem hune))) hyu.1
      rw [this]
      exact (hmemP _).mpr ⟨u, hu, u.min'_mem hune⟩
    · have : y = u.max' hune := le_antisymm hyu.2 (h _ (husub _ (u.max'_mem hune)))
      rw [this]
      exact (hmemP _).mpr ⟨u, hu, u.max'_mem hune⟩
  have h0P : (0 : ℝ) ∈ P := hend 0 ⟨le_rfl, zero_le_one⟩ (Or.inl fun z hz => hz.1)
  have h1P : (1 : ℝ) ∈ P := hend 1 ⟨zero_le_one, le_rfl⟩ (Or.inr fun z hz => hz.2)
  have hN2 : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨0, h0P, 1, h1P, by norm_num⟩
  set N := P.card with hNdef
  set e := P.orderIsoOfFin (rfl : P.card = N) with hedef
  set s : ℕ → ℝ := fun i => if h : i < N then ((e ⟨i, h⟩ : ℝ)) else 1 with hsdef
  have hsval : ∀ i, ∀ h : i < N, s i = ((e ⟨i, h⟩ : ℝ)) := by
    intro i h
    rw [hsdef]
    simp only [dif_pos h]
  have hsmem : ∀ i, ∀ h : i < N, s i ∈ P := by
    intro i h
    rw [hsval i h]
    exact (e ⟨i, h⟩).2
  have hsmono : ∀ i j, ∀ (hi : i < N) (hj : j < N), i < j → s i < s j := by
    intro i j hi hj hij
    rw [hsval i hi, hsval j hj]
    exact e.lt_iff_lt.mpr (by exact hij)
  have hsmin : ∀ x ∈ P, s 0 ≤ x := by
    intro x hx
    rw [hsval 0 (by omega)]
    have := e.monotone (show (⟨0, by omega⟩ : Fin N) ≤ e.symm ⟨x, hx⟩ from
      Fin.le_def.mpr (Nat.zero_le _))
    rw [e.apply_symm_apply] at this
    exact this
  have hsmax : ∀ x ∈ P, x ≤ s (N - 1) := by
    intro x hx
    rw [hsval (N - 1) (by omega)]
    have hlt := (e.symm ⟨x, hx⟩).is_lt
    have := e.monotone (show e.symm ⟨x, hx⟩ ≤ (⟨N - 1, by omega⟩ : Fin N) from
      Fin.le_def.mpr (show ((e.symm ⟨x, hx⟩ : Fin N) : ℕ) ≤ N - 1 by omega))
    rw [e.apply_symm_apply] at this
    exact this
  have hs0 : s 0 = 0 := le_antisymm (hsmin 0 h0P) (hPsub _ (hsmem 0 (by omega))).1
  have hsn : s (N - 1) = 1 := le_antisymm (hPsub _ (hsmem (N - 1) (by omega))).2 (hsmax 1 h1P)
  have hgap : ∀ i, i + 1 < N → ∀ x ∈ P, ¬(s i < x ∧ x < s (i + 1)) := by
    rintro i hi1 x hx ⟨h1, h2⟩
    rw [hsval i (by omega)] at h1
    rw [hsval (i + 1) hi1] at h2
    have k1 : (⟨i, by omega⟩ : Fin N) < e.symm ⟨x, hx⟩ := by
      rw [← e.lt_iff_lt, e.apply_symm_apply]
      exact h1
    have k2 : e.symm ⟨x, hx⟩ < (⟨i + 1, hi1⟩ : Fin N) := by
      rw [← e.lt_iff_lt, e.apply_symm_apply]
      exact h2
    simp only [Fin.lt_def] at k1 k2
    omega
  have hcell : ∀ i, i < N - 1 → ∃ u ∈ K'.faces,
      Icc (s i) (s (i + 1)) ⊆ convexHull ℝ (u : Set ℝ) := by
    intro i hi
    have hi1 : i + 1 < N := by omega
    have hlt : s i < s (i + 1) := hsmono i (i + 1) (by omega) hi1 (by omega)
    have hm : (s i + s (i + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
      have h1 := hPsub _ (hsmem i (by omega))
      have h2 := hPsub _ (hsmem (i + 1) hi1)
      exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    obtain ⟨u, hu, hmu⟩ := K'.mem_space_iff.mp (by rw [hK'space]; exact hm)
    have hune := K'.nonempty_of_mem_faces hu
    rw [convexHull_coe_finset_real hune] at hmu
    refine ⟨u, hu, ?_⟩
    rw [convexHull_coe_finset_real hune]
    refine Icc_subset_Icc ?_ ?_
    · by_contra hcon
      push Not at hcon
      exact hgap i hi1 (u.min' hune) ((hmemP _).mpr ⟨u, hu, u.min'_mem hune⟩)
        ⟨hcon, lt_of_le_of_lt hmu.1 (by linarith)⟩
    · by_contra hcon
      push Not at hcon
      exact hgap i hi1 (u.max' hune) ((hmemP _).mpr ⟨u, hu, u.max'_mem hune⟩)
        ⟨lt_of_lt_of_le (by linarith) hmu.2, hcon⟩
  refine ⟨N - 1, s, hs0, hsn, fun i hi => hsmono i (i + 1) (by omega) (by omega) (by omega),
    ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨u, hu, hsub⟩ := hcell i hi
    have hlt : s i < s (i + 1) := hsmono i (i + 1) (by omega) (by omega) (by omega)
    have hbdd : Bornology.IsBounded (convexHull ℝ (u : Set ℝ)) :=
      isBounded_convexHull.mpr u.finite_toSet.isBounded
    have hd := dist_le_diam_of_mem hbdd (hsub ⟨le_rfl, hlt.le⟩) (hsub ⟨hlt.le, le_rfl⟩)
    rw [Real.dist_eq, abs_of_nonpos (by linarith)] at hd
    have := hK'diam u hu
    linarith
  · intro i hi x hx
    obtain ⟨u, hu, hsub⟩ := hcell i hi
    obtain ⟨A, hA⟩ := haff true u hu
    have hA' : EqOn f A (convexHull ℝ (u : Set ℝ)) := hA
    have hlt : s i < s (i + 1) := hsmono i (i + 1) (by omega) (by omega) (by omega)
    rw [hA' (hsub hx), hA' (hsub ⟨le_rfl, hlt.le⟩), hA' (hsub ⟨hlt.le, le_rfl⟩)]
    exact affineMap_apply_eq_interp A (ne_of_lt hlt) x
  · intro i hi x hx
    obtain ⟨u, hu, hsub⟩ := hcell i hi
    obtain ⟨A, hA⟩ := haff false u hu
    have hA' : EqOn g A (convexHull ℝ (u : Set ℝ)) := hA
    have hlt : s i < s (i + 1) := hsmono i (i + 1) (by omega) (by omega) (by omega)
    rw [hA' (hsub hx), hA' (hsub ⟨le_rfl, hlt.le⟩), hA' (hsub ⟨hlt.le, le_rfl⟩)]
    exact affineMap_apply_eq_interp A (ne_of_lt hlt) x

end DifferentialGeometry.Topology.PiecewiseLinear
