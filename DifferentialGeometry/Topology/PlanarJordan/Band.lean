import DifferentialGeometry.Topology.Connected.FiniteClosedCover
import DifferentialGeometry.Topology.PlanarJordan.Innermost

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_band_edge_components {ι : Type*} [Finite ι]
    (C : ι → Set Schoenflies.Plane) (hC : ∀ i, Schoenflies.IsJordanCurve (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    {B : ℝ × ℝ → Schoenflies.Plane} {h : ℝ}
    (hB : ContinuousOn B (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h)) (hh : 0 ≤ h)
    (hlevel : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
      B z ∈ ⋃ i, C i ↔ z.1 = -1 ∨ z.1 = 1) :
    (∀ a ∈ ({-1, 1} : Set ℝ), ∃! i,
      (fun u => B (a, u)) '' Icc (-h) h ⊆ C i) ∧
      ∀ i, B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.inside (C i) ∨
        B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ Schoenflies.outside (C i) := by
  have hI : IsConnected (Icc (-h) h) := isConnected_Icc (by linarith)
  constructor
  · intro a ha
    have haedge : a = -1 ∨ a = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using ha
    have haI : a ∈ Icc (-1 : ℝ) 1 := by rcases haedge with ha | ha <;> rw [ha] <;> norm_num
    have hcont : ContinuousOn (fun u => B (a, u)) (Icc (-h) h) :=
      hB.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨haI, hu⟩)
    apply (hI.image _ hcont).exists_unique_subset_of_iUnion_disjoint_closed
      (fun i => (hC i).isCompact.isClosed) hdisj
    rintro _ ⟨u, hu, rfl⟩
    exact (hlevel (a, u) ⟨haI, hu⟩).mpr haedge
  · intro i
    have hrect : IsConnected (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) :=
      (isConnected_Ioo (by norm_num : (-1 : ℝ) < 1)).prod hI
    have himage := hrect.image B (hB.mono (prod_mono Ioo_subset_Icc_self Subset.rfl))
    have havoid : Disjoint (B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h)) (C i) := by
      apply disjoint_left.mpr
      rintro y ⟨z, hz, rfl⟩ hy
      have heq := (hlevel z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩).mp (mem_iUnion.mpr ⟨i, hy⟩)
      rcases heq with heq | heq <;> linarith [hz.1.1, hz.1.2]
    obtain ⟨W, V, hWV, hsub⟩ := (Schoenflies.jordan_curve_theorem (hC i)).exists_isRegionPair_subset
      himage.isPreconnected himage.nonempty havoid
    rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hsub
    · exact Or.inr hsub

private theorem band_subset_region_of_edge
    {C V : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    (hV : Schoenflies.IsRegionOf C V) {B : ℝ × ℝ → Schoenflies.Plane}
    {h : ℝ} (hB : ContinuousOn B (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h)) (hh : 0 ≤ h)
    (havoid : ∀ z ∈ Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h, B z ∉ C)
    {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hedge : B (a, 0) ∈ V) :
    B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ V := by
  let S := B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h)
  have hS : IsConnected S := ((isConnected_Ioo (by norm_num : (-1 : ℝ) < 1)).prod
    (isConnected_Icc (by linarith : -h ≤ h))).image B
      (hB.mono (prod_mono Ioo_subset_Icc_self Subset.rfl))
  have hp : B (a, 0) ∈ closure S := by
    apply ((hB (a, 0) ⟨ha, by constructor <;> linarith⟩).mono
      (prod_mono Ioo_subset_Icc_self Subset.rfl)).mem_closure_image
    rw [closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), isClosed_Icc.closure_eq]
    exact ⟨ha, by constructor <;> linarith⟩
  have hmeet : (S ∩ V).Nonempty := by
    obtain ⟨x, hxV, hxS⟩ := mem_closure_iff.mp hp V (hV.isOpen hC) hedge
    exact ⟨x, hxS, hxV⟩
  obtain ⟨W, hVW⟩ : ∃ W, Schoenflies.IsRegionPair C V W := by
    rcases hV with rfl | rfl
    · exact ⟨Schoenflies.outside C, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Schoenflies.inside C, Or.inr ⟨rfl, rfl⟩⟩
  apply hS.isPreconnected.subset_left_of_subset_union (hVW.left.isOpen hC)
    (hVW.right.isOpen hC) hVW.disjoint ?_ hmeet
  rw [hVW.union_eq]
  rintro _ ⟨z, hz, rfl⟩
  exact havoid z hz

theorem band_regions_of_disjoint_attaching_curves
    {C J : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hJ : Schoenflies.IsJordanCurve J) (hdisj : Disjoint C J)
    {B : ℝ × ℝ → Schoenflies.Plane} {h : ℝ}
    (hB : ContinuousOn B (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h)) (hh : 0 ≤ h)
    (havoid : ∀ z ∈ Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h, B z ∉ C ∧ B z ∉ J)
    (hleft : B (-1, 0) ∈ C) (hright : B (1, 0) ∈ J) :
    let S := B '' (Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h)
    (C ⊆ Schoenflies.inside J ∧ J ⊆ Schoenflies.outside C ∧
      S ⊆ Schoenflies.outside C ∩ Schoenflies.inside J) ∨
      (J ⊆ Schoenflies.inside C ∧ C ⊆ Schoenflies.outside J ∧
        S ⊆ Schoenflies.inside C ∩ Schoenflies.outside J) ∨
      (C ⊆ Schoenflies.outside J ∧ J ⊆ Schoenflies.outside C ∧
        S ⊆ Schoenflies.outside C ∩ Schoenflies.outside J) := by
  have hCs := Schoenflies.jordan_curve_theorem hC
  have hJs := Schoenflies.jordan_curve_theorem hJ
  rcases disjoint_jordan_curves_trichotomy hC hJ hdisj with ⟨hCJ, hJC⟩ | ⟨hJC, hCJ⟩ | ⟨hCJ, hJC⟩
  · exact Or.inl ⟨hCJ, hJC, subset_inter
      (band_subset_region_of_edge hCs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inl rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩
  · exact Or.inr (Or.inl ⟨hJC, hCJ, subset_inter
      (band_subset_region_of_edge hCs (Or.inl rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩)
  · exact Or.inr (Or.inr ⟨hCJ, hJC, subset_inter
      (band_subset_region_of_edge hCs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩)

end DifferentialGeometry.Topology.PlanarJordan
