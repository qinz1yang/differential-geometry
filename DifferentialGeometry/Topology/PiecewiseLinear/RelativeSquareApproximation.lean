import DifferentialGeometry.Topology.PiecewiseLinear.PrismHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def collarReparam (ε t : ℝ) : ℝ := max 0 ((t - ε) / (1 - ε))

theorem collarReparam_eq_zero {ε t : ℝ} (hε1 : ε < 1) (ht : t ≤ ε) : collarReparam ε t = 0 := by
  rw [collarReparam, max_eq_left]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem collarReparam_mem {ε t : ℝ} (hε1 : ε < 1) (ht : t ≤ 1) :
    collarReparam ε t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  rw [div_le_one (by linarith)]
  linarith

theorem continuous_collarReparam (ε : ℝ) : Continuous (collarReparam ε) := by
  refine continuous_const.max ?_
  exact (continuous_id.sub continuous_const).div_const _

theorem exists_isPiecewiseAffineOn_square_eqOn_bottom
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : ℝ × ℝ → F} (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfL : MapsTo f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space)
    (hbot : IsPiecewiseAffineOn (fun x : ℝ => f (x, 0)) (Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hbotface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (a, 0), f (b, 0)} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ g : ℝ × ℝ → F, IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, g (x, 0) = f (x, 0)) := by
  classical
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 : ℝ) / 2 < 1 := by norm_num
  set ρ : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, collarReparam (1 / 2) z.2) with hρdef
  have hρcont : Continuous ρ :=
    continuous_fst.prodMk ((continuous_collarReparam _).comp continuous_snd)
  have hρmaps : MapsTo ρ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hz.1, collarReparam_mem hε1 hz.2.2⟩
  have hf' : ContinuousOn (f ∘ ρ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hf.comp hρcont.continuousOn hρmaps
  have hf'L : MapsTo (f ∘ ρ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space :=
    fun z hz => hfL (hρmaps hz)
  obtain ⟨K, hKfin, hKspace⟩ := IsPolyhedron.exists_simplicialComplex
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨K', φ, hK', hK'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation K L (by rw [hKspace]; exact hf')
      (by rw [hKspace]; exact hf'L)
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by rw [hK'.space_eq, hKspace]
  have hG : IsPiecewiseAffineOn (simplicialMap K' φ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hK'space]
    exact isPiecewiseAffineOn_simplicialMap K' φ
  have hGL : MapsTo (simplicialMap K' φ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space := by
    rw [← hK'space]
    exact simplicialMap_mapsTo K' L φ hφ
  have hslice : ∀ a : ℝ, (f ∘ ρ) (a, 1 / 2) = f (a, 0) := by
    intro a
    rw [Function.comp_apply, hρdef]
    simp only
    rw [collarReparam_eq_zero hε1 le_rfl]
  have hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (a, 0), f (b, 0), simplicialMap K' φ (a, 1 / 2),
        simplicialMap K' φ (b, 1 / 2)} : Set F) ⊆ convexHull ℝ (u : Set F) := by
    intro a ha b hb hle hab hgap
    obtain ⟨u, hu, hsub⟩ := hbotface a ha b hb hle hab hgap
    have hmemu : ∀ c : ℝ, c ∈ Icc (0 : ℝ) 1 → f (c, 0) ∈ convexHull ℝ (u : Set F) →
        simplicialMap K' φ (c, 1 / 2) ∈ convexHull ℝ (u : Set F) := by
      intro c hc hfc
      have hcK : ((c, (1 : ℝ) / 2) : ℝ × ℝ) ∈ K.space := by
        rw [hKspace]
        exact ⟨hc, hε.le, hε1.le⟩
      have h1 := hclose _ hcK
      rw [hslice c] at h1
      have h2 : carrierFace L (f (c, 0)) ⊆ u :=
        carrierFace_subset (L.convexHull_subset_space hu hfc) hu hfc
      exact convexHull_mono (Finset.coe_subset.mpr h2) h1
    refine ⟨u, hu, ?_⟩
    rintro y (rfl | rfl | rfl | rfl)
    · exact hsub (mem_insert _ _)
    · exact hsub (mem_insert_of_mem _ rfl)
    · exact hmemu a ha (hsub (mem_insert _ _))
    · exact hmemu b hb (hsub (mem_insert_of_mem _ rfl))
  obtain ⟨g, hgPA, hgL, hgbot, -⟩ :=
    exists_isPiecewiseAffineOn_glue_prism_collar L hG hGL hbot hε hε1.le hδ T hT hface
  exact ⟨g, hgPA, hgL, hgbot⟩

open Classical in
theorem exists_face_of_no_partition_point_between
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) {h : ℝ → F} {n : ℕ} {s : ℕ → ℝ}
    (hs0 : s 0 = 0) (hsn : s n = 1) (hn : 0 < n) (hmono : ∀ i < n, s i < s (i + 1))
    (hcell : ∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)),
      h x ∈ convexHull ℝ (u : Set F))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (hgap : ∀ i ≤ n, ¬(a < s i ∧ s i < b)) :
    ∃ u ∈ L.faces, ({h a, h b} : Set F) ⊆ convexHull ℝ (u : Set F) := by
  classical
  have hP0 : (fun i => s i ≤ a) 0 := by
    change s 0 ≤ a
    rw [hs0]
    exact ha.1
  have hPlam : (fun i => s i ≤ a) (Nat.findGreatest (fun i => s i ≤ a) n) :=
    Nat.findGreatest_spec (P := fun i => s i ≤ a) (Nat.zero_le n) hP0
  have hPi : s (Nat.findGreatest (fun i => s i ≤ a) n) ≤ a := hPlam
  have hle : Nat.findGreatest (fun i => s i ≤ a) n ≤ n :=
    Nat.findGreatest_le n
  have key : ∃ i < n, a ∈ Icc (s i) (s (i + 1)) ∧ b ∈ Icc (s i) (s (i + 1)) := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hsna : s n ≤ a := heq ▸ hPi
      have ha1 : a = 1 := le_antisymm ha.2 (by rw [← hsn]; exact hsna)
      have hb1 : b = 1 := le_antisymm hb.2 (ha1 ▸ hab)
      have hlast : s (n - 1) ≤ 1 :=
        (mem_Icc_of_forall_lt_succ hmono hs0 hsn (by omega : n - 1 ≤ n)).2
      refine ⟨n - 1, by omega, ?_, ?_⟩
      · rw [show n - 1 + 1 = n by omega, hsn, ha1]
        exact ⟨hlast, le_rfl⟩
      · rw [show n - 1 + 1 = n by omega, hsn, hb1]
        exact ⟨hlast, le_rfl⟩
    · have hnotlam : ¬ (fun i => s i ≤ a) (Nat.findGreatest (fun i => s i ≤ a) n + 1) :=
        Nat.findGreatest_is_greatest (P := fun i => s i ≤ a) (Nat.lt_succ_self _)
          (Nat.succ_le_of_lt hlt)
      have hnotP : ¬ (s (Nat.findGreatest (fun i => s i ≤ a) n + 1) ≤ a) := hnotlam
      have hagt : a < s (Nat.findGreatest (fun i => s i ≤ a) n + 1) := lt_of_not_ge hnotP
      have hble : b ≤ s (Nat.findGreatest (fun i => s i ≤ a) n + 1) := by
        by_contra hcon
        exact hgap _ (Nat.succ_le_of_lt hlt) ⟨hagt, lt_of_not_ge hcon⟩
      exact ⟨_, hlt, ⟨hPi, hagt.le⟩, ⟨hPi.trans hab, hble⟩⟩
  obtain ⟨i, hi, hai, hbi⟩ := key
  obtain ⟨u, hu, hfu⟩ := hcell i hi
  exact ⟨u, hu, by rintro y (rfl | rfl); exacts [hfu _ hai, hfu _ hbi]⟩

theorem exists_isPiecewiseAffineOn_square_eqOn_bottom_of_cells
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : ℝ × ℝ → F} (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfL : MapsTo f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space)
    (hbot : IsPiecewiseAffineOn (fun x : ℝ => f (x, 0)) (Icc (0 : ℝ) 1))
    {n : ℕ} {s : ℕ → ℝ} (hs0 : s 0 = 0) (hsn : s n = 1) (hn : 0 < n)
    (hmono : ∀ i < n, s i < s (i + 1))
    (hbotcell : ∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)),
      f (x, 0) ∈ convexHull ℝ (u : Set F)) :
    ∃ g : ℝ × ℝ → F, IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, g (x, 0) = f (x, 0)) := by
  classical
  refine exists_isPiecewiseAffineOn_square_eqOn_bottom L hf hfL hbot one_pos
    ((Finset.range (n + 1)).image s) ?_ ?_
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact mem_Icc_of_forall_lt_succ hmono hs0 hsn
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro a ha b hb hle _ hgap
    exact exists_face_of_no_partition_point_between L hs0 hsn hn hmono hbotcell ha hb hle
      (fun i hi hcon => hgap (s i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩) hcon)

end DifferentialGeometry.Topology.PiecewiseLinear
