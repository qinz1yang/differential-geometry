import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonSideDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalFibers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleSubfamily

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_cylindrical_cancellation_of_two_crossing_crosscuts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N J L : Set (EuclideanSpace ℝ (Fin 2))} (hN : IsPLBall 2 N)
    {γ δ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (t : Fin 2 → ℝ) (h₀ : 0 < t 0) (h₀₁ : t 0 < t 1) (h₁ : t 1 < 1)
    (htrace : J ∩ L = {γ (t 0), γ (t 1)})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ L ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J)
    {f : EuclideanSpace ℝ (Fin 2) × ℝ → E} {S X Y : Set E}
    (hf : IsCylindricalDiagram f N S) (hends : ∀ x ∈ N, f (x, 0) = f (x, 1))
    (hfront : frontier S ⊆ f '' (frontier N ×ˢ Icc (0 : ℝ) 1))
    (hX : X ∩ S = f '' (J ×ˢ Icc (0 : ℝ) 1))
    (hY : Y ∩ S = f '' (L ×ˢ Icc (0 : ℝ) 1)) :
    ∃ H : E ≃ₜ E, IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      H '' X ∩ Y = (X ∩ Y) \ S ∧
      ∃ (A J' : Set (EuclideanSpace ℝ (Fin 2))) (γ' : ℝ → EuclideanSpace ℝ (Fin 2)),
        IsPLBall 2 A ∧ A ⊆ N ∧ A ∩ (L ∪ frontier N) ⊆ frontier A ∧
        IsPLHomeomorphOn γ' (Icc 0 1) J' ∧ J' ⊆ A ∧
        γ' 0 = γ 0 ∧ γ' 1 = γ 1 ∧ Disjoint J' L ∧
        H '' (X ∩ S) = f '' (J' ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨A, hA, hAN, hside, hA₀, hA₁, h₀L, h₁L⟩ :=
    exists_bigon_side_disk_of_two_crossing_charts hN hγ hJN hJends hδ hLN hLends
      t h₀ h₀₁ h₁ htrace e ε hε hsource hcenter hcurve haxis
  obtain ⟨r, hr⟩ := hA
  obtain ⟨J', γ', hγ', hJ'A, hγ'₀, hγ'₁, hJ'ends⟩ :=
    hr.exists_crosscut_between_boundary_points
      (hr.image_stdSimplexBoundary.symm ▸ hA₀)
      (hr.image_stdSimplexBoundary.symm ▸ hA₁)
      (fun h => zero_ne_one (hγ.bijOn.injOn (by norm_num) (by norm_num) h))
  rw [hr.image_stdSimplexBoundary] at hJ'ends
  have hJ'N : J' ⊆ N := hJ'A.trans hAN
  have hJ'front : J' ∩ frontier N = {γ' 0, γ' 1} := by
    rw [hγ'₀, hγ'₁]
    apply Subset.antisymm
    · intro x hx
      exact hJ'ends.subset ⟨hx.1, hside ⟨hJ'A hx.1, Or.inr hx.2⟩⟩
    · rintro x (rfl | rfl)
      · exact ⟨(hJ'ends.symm.subset (by simp)).1, (hJends.symm.subset (by simp)).2⟩
      · exact ⟨(hJ'ends.symm.subset (by simp)).1, (hJends.symm.subset (by simp)).2⟩
  have hdis : Disjoint J' L := by
    refine disjoint_left.mpr fun x hx hxL => ?_
    rcases hJ'ends.subset ⟨hx, hside ⟨hJ'A hx, Or.inl hxL⟩⟩ with hx | hx
    · exact h₀L (hx ▸ hxL)
    · exact h₁L (hx ▸ hxL)
  obtain ⟨n, hn⟩ := hN
  obtain ⟨H, hH, hoff, hpatch, hnew⟩ := hf.exists_supported_crosscut_replacement hends hn
    hn.image_stdSimplexBoundary hfront hγ hJN hJends hγ' hJ'N hJ'front
    hγ'₀.symm hγ'₁.symm
  have hlocal : Disjoint (H '' (X ∩ S)) (Y ∩ S) := by
    rw [hX, hY, disjoint_iff_inter_eq_empty, inter_comm]
    rw [hnew L hLN, disjoint_iff_inter_eq_empty.mp hdis.symm, empty_prod, image_empty]
  refine ⟨H, hH, hoff, ?_, A, J', γ', ⟨r, hr⟩, hAN, hside,
    hγ', hJ'A, hγ'₀, hγ'₁, hdis, by simpa only [hX] using hpatch⟩
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyY⟩
    by_cases hyS : y ∈ S
    · have hxS : x ∈ S := by
        by_contra hxS
        have heq : x = y := (hoff hxS).symm.trans hxy
        exact hxS (heq.symm ▸ hyS)
      exact False.elim (disjoint_left.mp hlocal ⟨x, ⟨hx, hxS⟩, hxy⟩ ⟨hyY, hyS⟩)
    · have hxy' : x = y := H.injective (hxy.trans (hoff hyS).symm)
      exact ⟨⟨hxy' ▸ hx, hyY⟩, hyS⟩
  · rintro ⟨⟨hyX, hyY⟩, hyS⟩
    exact ⟨⟨y, hyX, hoff hyS⟩, hyY⟩

theorem exists_strict_cylindrical_cancellation_of_two_crossing_crosscuts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N J L : Set (EuclideanSpace ℝ (Fin 2))} (hN : IsPLBall 2 N)
    {γ δ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (t : Fin 2 → ℝ) (h₀ : 0 < t 0) (h₀₁ : t 0 < t 1) (h₁ : t 1 < 1)
    (htrace : J ∩ L = {γ (t 0), γ (t 1)})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ L ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J)
    {f : EuclideanSpace ℝ (Fin 2) × ℝ → E} {S X Y : Set E}
    (hf : IsCylindricalDiagram f N S) (hends : ∀ x ∈ N, f (x, 0) = f (x, 1))
    (hfront : frontier S ⊆ f '' (frontier N ×ˢ Icc (0 : ℝ) 1))
    (hX : X ∩ S = f '' (J ×ˢ Icc (0 : ℝ) 1))
    (hY : Y ∩ S = f '' (L ×ˢ Icc (0 : ℝ) 1))
    {ι : Type*} [Finite ι] {Γ : ι → Set E} (hΓ : ∀ i, IsPLSphere 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : X ∩ Y = ⋃ i, Γ i) :
    ∃ (I : Set ι) (H : E ≃ₜ E), Nat.card I < Nat.card ι ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      (∀ i : I, Disjoint S (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, H =ᶠ[𝓝 x] id) ∧ H '' X ∩ Y = ⋃ i : I, Γ i.1 := by
  obtain ⟨H, hH, hoff, hcancel, -⟩ := exists_cylindrical_cancellation_of_two_crossing_crosscuts
    hN hγ hJN hJends hδ hLN hLends t h₀ h₀₁ h₁ htrace e ε hε hsource hcenter hcurve haxis
    hf hends hfront hX hY
  have ht (k : Fin 2) : t k ∈ Icc (0 : ℝ) 1 := by
    fin_cases k
    · exact ⟨h₀.le, (h₀₁.trans h₁).le⟩
    · exact ⟨(h₀.trans h₀₁).le, h₁.le⟩
  have hpt (k : Fin 2) : γ (t k) ∈ N := hJN (hγ.bijOn.mapsTo (ht k))
  let C : Fin 2 → Set E := fun k => f '' ({γ (t k)} ×ˢ Icc (0 : ℝ) 1)
  have hC (k) : IsPLSphere 1 (C k) := hf.isPLSphere_fiber hends (hpt k)
  have hneq : γ (t 0) ≠ γ (t 1) :=
    fun h => h₀₁.ne (hγ.bijOn.injOn (ht 0) (ht 1) h)
  have hCdis : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hf.disjoint_fibers hends (hpt 0) (hpt 1) hneq
    · exact hf.disjoint_fibers hends (hpt 1) (hpt 0) hneq.symm
    · exact (hij rfl).elim
  have hlocal : (⋃ i, Γ i) ∩ S = ⋃ k, C k := by
    calc
      (⋃ i, Γ i) ∩ S = (X ∩ S) ∩ (Y ∩ S) := by
        rw [← hfull]
        ext x
        simp only [mem_inter_iff]
        tauto
      _ = f '' ((J ∩ L) ×ˢ Icc (0 : ℝ) 1) := by
        rw [hX, hY, hf.inter_images_base_regions hends hJN hLN]
      _ = ⋃ k, C k := by
        rw [htrace, ← singleton_union, union_prod, image_union]
        change C 0 ∪ C 1 = ⋃ k, C k
        ext x
        simp only [mem_union, mem_iUnion]
        constructor
        · rintro (hx | hx)
          · exact ⟨0, hx⟩
          · exact ⟨1, hx⟩
        · rintro ⟨k, hk⟩
          fin_cases k
          · exact Or.inl hk
          · exact Or.inr hk
  obtain ⟨I, hcard, hI, hkeep⟩ :=
    exists_strict_circle_subfamily_after_deleting_region hΓ hC hΓdis hCdis hlocal
  have hSc : IsClosed S := by
    rw [← hf.image_eq]
    exact ((hN.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
      hf.isPiecewiseAffineOn.continuousOn).isClosed
  refine ⟨I, H, hcard, hH, hoff, hkeep, ?_, by rwa [hfull, hI] at hcancel⟩
  intro i x hx
  filter_upwards [hSc.isOpen_compl.mem_nhds (disjoint_right.mp (hkeep i) hx)] with y hy
  exact hoff hy

end DifferentialGeometry.Topology.PiecewiseLinear
