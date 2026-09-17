import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLOn_dist_lt_of_mapsTo_chart {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P) (hPc : IsCompact P)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P)
    (e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ (plGroupoid m).maximalAtlas N) (hmap : MapsTo f P e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ ∀ x ∈ P, dist (g x) (f x) < ε := by
  classical
  have hφc : ContinuousOn (e ∘ f) P :=
    (e.continuousOn.comp hf hmap)
  have himg : IsCompact ((e ∘ f) '' P) := hPc.image_of_continuousOn hφc
  have hsub : (e ∘ f) '' P ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hmap hx)
  obtain ⟨r, hr, hrsub⟩ := himg.exists_thickening_subset_open e.open_target hsub
  set C := cthickening (r / 2) ((e ∘ f) '' P) with hC
  have hCsub : C ⊆ e.target :=
    (cthickening_subset_thickening' hr (by linarith) _).trans hrsub
  have hCcompact : IsCompact C := himg.cthickening
  have hsymmc : ContinuousOn e.symm C := e.symm.continuousOn.mono hCsub
  obtain ⟨δ, hδ, hδclose⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hCcompact.uniformContinuousOn_of_continuous hsymmc) ε hε
  obtain ⟨g', hg'pa, hg'dist⟩ :=
    exists_isPiecewiseAffineOn_dist_lt hP hPc hφc (ε := min δ (r / 2))
      (lt_min hδ (by linarith))
  have hg'mem : ∀ x ∈ P, g' x ∈ C := by
    intro x hx
    refine mem_cthickening_of_dist_le _ _ (r / 2) _ ⟨x, hx, rfl⟩ ?_
    exact le_of_lt (lt_of_lt_of_le (hg'dist x hx) (min_le_right _ _))
  have hφmem : ∀ x ∈ P, (e ∘ f) x ∈ C := fun x hx =>
    self_subset_cthickening _ ⟨x, hx, rfl⟩
  have hg'target : MapsTo g' P e.target := fun x hx => hCsub (hg'mem x hx)
  refine ⟨fun y => e.symm (g' y), ?_, ?_⟩
  · have hmapsTo : MapsTo (fun y => e.symm (g' y)) P e.source := fun x hx =>
      e.map_target (hg'target hx)
    rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart e he hmapsTo]
    refine hg'pa.congr ?_
    intro x hx
    exact e.right_inv (hg'target hx)
  · intro x hx
    have := hδclose (g' x) (hg'mem x hx) ((e ∘ f) x) (hφmem x hx)
      (lt_of_lt_of_le (hg'dist x hx) (min_le_left _ _))
    simpa only [Function.comp_apply, e.left_inv (hmap hx)] using this

theorem exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P Q : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P) (hPc : IsCompact P)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P) (hfQ : IsPLOn n m f Q)
    (e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ (plGroupoid m).maximalAtlas N) (hmap : MapsTo f P e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ EqOn g f Q ∧
      ∀ x ∈ P, dist (g x) (f x) < ε := by
  classical
  have hφc : ContinuousOn (e ∘ f) P :=
    (e.continuousOn.comp hf hmap)
  have himg : IsCompact ((e ∘ f) '' P) := hPc.image_of_continuousOn hφc
  have hsub : (e ∘ f) '' P ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hmap hx)
  obtain ⟨r, hr, hrsub⟩ := himg.exists_thickening_subset_open e.open_target hsub
  set C := cthickening (r / 2) ((e ∘ f) '' P) with hC
  have hCsub : C ⊆ e.target :=
    (cthickening_subset_thickening' hr (by linarith) _).trans hrsub
  have hCcompact : IsCompact C := himg.cthickening
  have hsymmc : ContinuousOn e.symm C := e.symm.continuousOn.mono hCsub
  obtain ⟨δ, hδ, hδclose⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hCcompact.uniformContinuousOn_of_continuous hsymmc) ε hε
  have hφQ : IsPiecewiseAffineOn (e ∘ f) Q :=
    (isPLOn_iff_isPiecewiseAffineOn_comp_chart e he (hmap.mono_left hQP)).mp hfQ
  obtain ⟨g', hg'pa, hg'eq, hg'dist⟩ :=
    exists_isPiecewiseAffineOn_dist_lt_eqOn hP hQ hQP hPc hφc hφQ (ε := min δ (r / 2))
      (lt_min hδ (by linarith))
  have hg'mem : ∀ x ∈ P, g' x ∈ C := by
    intro x hx
    refine mem_cthickening_of_dist_le _ _ (r / 2) _ ⟨x, hx, rfl⟩ ?_
    exact le_of_lt (lt_of_lt_of_le (hg'dist x hx) (min_le_right _ _))
  have hφmem : ∀ x ∈ P, (e ∘ f) x ∈ C := fun x hx =>
    self_subset_cthickening _ ⟨x, hx, rfl⟩
  have hg'target : MapsTo g' P e.target := fun x hx => hCsub (hg'mem x hx)
  refine ⟨fun y => e.symm (g' y), ?_, ?_, ?_⟩
  · have hmapsTo : MapsTo (fun y => e.symm (g' y)) P e.source := fun x hx =>
      e.map_target (hg'target hx)
    rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart e he hmapsTo]
    refine hg'pa.congr ?_
    intro x hx
    exact e.right_inv (hg'target hx)
  · intro x hx
    simp only [hg'eq hx, Function.comp_apply]
    exact e.left_inv (hmap (hQP hx))
  · intro x hx
    have := hδclose (g' x) (hg'mem x hx) ((e ∘ f) x) (hφmem x hx)
      (lt_of_lt_of_le (hg'dist x hx) (min_le_left _ _))
    simpa only [Function.comp_apply, e.left_inv (hmap hx)] using this

theorem exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart {n m : ℕ} {N : Type*}
    [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P Q : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P) (hPc : IsCompact P)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P)
    (e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ (plGroupoid m).maximalAtlas N) (hmap : MapsTo f P e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ u : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m u Q →
      (∀ x ∈ Q, dist (u x) (f x) < η) →
        ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ EqOn g u Q ∧
          ∀ x ∈ P, dist (g x) (f x) < ε := by
  classical
  have hφc : ContinuousOn (e ∘ f) P := e.continuousOn.comp hf hmap
  have himg : IsCompact ((e ∘ f) '' P) := hPc.image_of_continuousOn hφc
  have hsub : (e ∘ f) '' P ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hmap hx)
  obtain ⟨r, hr, hrsub⟩ := himg.exists_thickening_subset_open e.open_target hsub
  set C := cthickening (r / 2) ((e ∘ f) '' P) with hC
  have hCsub : C ⊆ e.target := (cthickening_subset_thickening' hr (by linarith) _).trans hrsub
  have hCcompact : IsCompact C := himg.cthickening
  obtain ⟨δ₁, hδ₁, hδ₁close⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hCcompact.uniformContinuousOn_of_continuous (e.symm.continuousOn.mono hCsub)) ε hε
  set δ := min δ₁ (r / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (by linarith)
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hfimg : IsCompact (f '' P) := hPc.image_of_continuousOn hf
  have hfsub : f '' P ⊆ e.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap hx
  have hloc : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) N
  obtain ⟨D, hDcompact, hfD, hDsub⟩ := exists_compact_between hfimg e.open_source hfsub
  obtain ⟨ρ, hρ, hρsub⟩ := hfimg.exists_thickening_subset_open isOpen_interior hfD
  obtain ⟨η₀, hη₀, hη₀close⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hDcompact.uniformContinuousOn_of_continuous (e.continuousOn.mono hDsub)) (δ / 2) hδ2
  refine ⟨min η₀ ρ, lt_min hη₀ hρ, ?_⟩
  intro u hu hclose
  have hfmem : ∀ x ∈ P, f x ∈ D := fun x hx => interior_subset (hfD ⟨x, hx, rfl⟩)
  have humem : ∀ x ∈ Q, u x ∈ D := by
    intro x hx
    refine interior_subset (hρsub (Metric.mem_thickening_iff.mpr ⟨f x, ⟨x, hQP hx, rfl⟩, ?_⟩))
    exact lt_of_lt_of_le (hclose x hx) (min_le_right _ _)
  have humap : MapsTo u Q e.source := fun x hx => hDsub (humem x hx)
  have hchartclose : ∀ x ∈ Q, dist ((e ∘ u) x) ((e ∘ f) x) ≤ δ / 2 := fun x hx =>
    le_of_lt (hη₀close (u x) (humem x hx) (f x) (hfmem x (hQP hx))
      (lt_of_lt_of_le (hclose x hx) (min_le_left _ _)))
  have hψQ : IsPiecewiseAffineOn (e ∘ u) Q :=
    (isPLOn_iff_isPiecewiseAffineOn_comp_chart e he humap).mp hu
  obtain ⟨g', hg'pa, hg'eq, hg'dist⟩ :=
    exists_isPiecewiseAffineOn_dist_lt_eqOn_of_dist_le (δ := δ / 2) (ε := δ / 2)
      hP hQ hQP hPc hφc hψQ hδ2.le hchartclose hδ2
  have hg'lt : ∀ x ∈ P, dist (g' x) ((e ∘ f) x) < δ := by
    intro x hx
    have h := hg'dist x hx
    linarith
  have hg'mem : ∀ x ∈ P, g' x ∈ C := by
    intro x hx
    refine mem_cthickening_of_dist_le _ _ (r / 2) _ ⟨x, hx, rfl⟩ ?_
    exact le_of_lt (lt_of_lt_of_le (hg'lt x hx) (min_le_right _ _))
  have hφmem : ∀ x ∈ P, (e ∘ f) x ∈ C := fun x hx => self_subset_cthickening _ ⟨x, hx, rfl⟩
  have hg'target : MapsTo g' P e.target := fun x hx => hCsub (hg'mem x hx)
  refine ⟨fun y => e.symm (g' y), ?_, ?_, ?_⟩
  · have hmapsTo : MapsTo (fun y => e.symm (g' y)) P e.source := fun x hx =>
      e.map_target (hg'target hx)
    rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart e he hmapsTo]
    exact hg'pa.congr (fun x hx => e.right_inv (hg'target hx))
  · intro x hx
    simp only [hg'eq hx, Function.comp_apply]
    exact e.left_inv (humap hx)
  · intro x hx
    have h := hδ₁close (g' x) (hg'mem x hx) ((e ∘ f) x) (hφmem x hx)
      (lt_of_lt_of_le (hg'lt x hx) (min_le_left _ _))
    simpa only [Function.comp_apply, e.left_inv (hmap hx)] using h

theorem exists_isPLOn_dist_lt_eqOn_of_biUnion {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {ι : Type*} {C : ι → Set (EuclideanSpace ℝ (Fin n))} (hC : ∀ i, IsPolyhedron (C i))
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsPolyhedron Q)
    {f : EuclideanSpace ℝ (Fin n) → N} (hfQ : IsPLOn n m f Q) (s : Finset ι)
    (hf : ContinuousOn f (Q ∪ ⋃ i ∈ s, C i))
    (hchart : ∀ i ∈ s, ∃ e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
      e ∈ (plGroupoid m).maximalAtlas N ∧ MapsTo f (C i) e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g (Q ∪ ⋃ i ∈ s, C i) ∧ EqOn g f Q ∧
      ∀ x ∈ Q ∪ ⋃ i ∈ s, C i, dist (g x) (f x) < ε := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    refine ⟨f, ?_, fun x _ => rfl, ?_⟩
    · simpa using hfQ
    · intro x _
      rw [dist_self]
      exact hε
  | insert j t hj ih =>
    have hset : Q ∪ ⋃ i ∈ insert j t, C i = C j ∪ (Q ∪ ⋃ i ∈ t, C i) := by
      rw [Finset.set_biUnion_insert, Set.union_left_comm]
    rw [hset] at hf ⊢
    set U := Q ∪ ⋃ i ∈ t, C i with hUdef
    have hU : IsPolyhedron U := hQ.union (IsPolyhedron.finsetBiUnion t hC)
    obtain ⟨e, he, hemap⟩ := hchart j (Finset.mem_insert_self j t)
    have hQ' : IsPolyhedron (U ∩ C j) := hU.inter (hC j)
    obtain ⟨η, hη, hηprop⟩ :=
      exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart (hC j) (hC j).isCompact
        hQ' inter_subset_right (hf.mono subset_union_left) e he hemap hε
    obtain ⟨g₀, hg₀, hg₀Q, hg₀d⟩ :=
      ih (hf.mono subset_union_right) (fun i hi => hchart i (Finset.mem_insert_of_mem hi))
        (lt_min hε hη)
    obtain ⟨g₁, hg₁, hg₁eq, hg₁d⟩ :=
      hηprop g₀ (hg₀.mono_of_isPolyhedron hQ' inter_subset_left)
        (fun x hx => lt_of_lt_of_le (hg₀d x hx.1) (min_le_right _ _))
    refine ⟨(C j).piecewise g₁ g₀, ?_, ?_, ?_⟩
    · exact hg₁.piecewise_of_isClosed hg₀ (hC j).isClosed hU.isClosed
        (fun x hx => hg₁eq ⟨hx.2, hx.1⟩)
    · intro x hx
      have hxU : x ∈ U := subset_union_left hx
      by_cases hxV : x ∈ C j
      · rw [Set.piecewise_eq_of_mem _ _ _ hxV, hg₁eq ⟨hxU, hxV⟩]
        exact hg₀Q hx
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxV]
        exact hg₀Q hx
    · intro x hx
      by_cases hxV : x ∈ C j
      · rw [Set.piecewise_eq_of_mem _ _ _ hxV]
        exact hg₁d x hxV
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxV]
        exact lt_of_lt_of_le (hg₀d x (hx.resolve_left hxV)) (min_le_left _ _)

theorem exists_isPLOn_dist_lt_of_biUnion {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {ι : Type*} {C : ι → Set (EuclideanSpace ℝ (Fin n))} (hC : ∀ i, IsPolyhedron (C i))
    {f : EuclideanSpace ℝ (Fin n) → N} (s : Finset ι)
    (hf : ContinuousOn f (⋃ i ∈ s, C i))
    (hchart : ∀ i ∈ s, ∃ e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
      e ∈ (plGroupoid m).maximalAtlas N ∧ MapsTo f (C i) e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g (⋃ i ∈ s, C i) ∧
      ∀ x ∈ ⋃ i ∈ s, C i, dist (g x) (f x) < ε := by
  obtain ⟨g, hg, -, hgd⟩ :=
    exists_isPLOn_dist_lt_eqOn_of_biUnion hC IsPolyhedron.empty
      (Q := (∅ : Set (EuclideanSpace ℝ (Fin n)))) (fun x hx => absurd hx (by simp)) s
      (by simpa using hf) hchart hε
  rw [Set.empty_union] at hg hgd
  exact ⟨g, hg, hgd⟩

theorem exists_finsetBiUnion_eq_mapsTo_chart {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P) :
    ∃ (C : Finset (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n)))
      (T : Finset (Finset (EuclideanSpace ℝ (Fin n)))),
      (∀ s, IsPolyhedron (C s)) ∧ (⋃ s ∈ T, C s) = P ∧
        ∀ s ∈ T, ∃ e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
          e ∈ (plGroupoid m).maximalAtlas N ∧ MapsTo f (C s) e.source := by
  classical
  have hPc : IsCompact P := hP.isCompact
  have hnhds : ∀ x : P, ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ (x : EuclideanSpace ℝ (Fin n)) ∈ W ∧
      W ∩ P ⊆ f ⁻¹' (chartAt (EuclideanSpace ℝ (Fin m)) (f x)).source := by
    intro x
    exact mem_nhdsWithin.mp (hf x x.2
      ((chartAt (EuclideanSpace ℝ (Fin m)) (f x)).open_source.mem_nhds (mem_chart_source _ _)))
  choose W hWopen hWmem hWsub using hnhds
  obtain ⟨d, hd, hdsub⟩ := lebesgue_number_lemma_of_metric hPc hWopen
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hWmem ⟨x, hx⟩⟩)
  obtain ⟨K, hKfin, hKspace⟩ := IsPolyhedron.exists_simplicialComplex hP
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨K', hK', hK'fin, -, hK'diam⟩ :=
    exists_isSubdivision_diam_lt K (N := Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
      (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hd
  have hK'space : K'.space = P := by rw [hK'.space_eq, hKspace]
  set C : Finset (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun s => if s ∈ K'.faces then convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))) else ∅ with hCdef
  have hC : ∀ s, IsPolyhedron (C s) := by
    intro s
    by_cases hs : s ∈ K'.faces
    · rw [hCdef]
      simp only [hs, if_true]
      exact isPolyhedron_convexHull_of_affineIndependent _ (K'.indep hs)
    · rw [hCdef]
      simp only [hs, if_false]
      exact IsPolyhedron.empty
  set T : Finset (Finset (EuclideanSpace ℝ (Fin n))) :=
    hK'fin.toFinset.filter fun s => s.Nonempty with hTdef
  have hCsub : ∀ s ∈ K'.faces, C s ⊆ P := by
    intro s hs y hy
    rw [hCdef] at hy
    simp only [hs, if_true] at hy
    rw [← hK'space]
    exact K'.convexHull_subset_space hs hy
  have hunion : ⋃ s ∈ T, C s = P := by
    apply Subset.antisymm
    · refine iUnion₂_subset fun s hs => hCsub s ?_
      exact hK'fin.mem_toFinset.mp (Finset.mem_filter.mp hs).1
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := K'.mem_space_iff.mp (by rw [hK'space]; exact hx)
      have hsne : s.Nonempty := by
        rcases Finset.eq_empty_or_nonempty s with rfl | h
        · simp at hxs
        · exact h
      refine mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hK'fin.mem_toFinset.mpr hs, hsne⟩, ?_⟩
      rw [hCdef]
      simpa only [hs, if_true] using hxs
  have hchart : ∀ s ∈ T, ∃ e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
      e ∈ (plGroupoid m).maximalAtlas N ∧ MapsTo f (C s) e.source := by
    intro s hs
    obtain ⟨hsf, hsne⟩ := Finset.mem_filter.mp hs
    have hsK : s ∈ K'.faces := hK'fin.mem_toFinset.mp hsf
    obtain ⟨v, hv⟩ := hsne
    have hCs : C s = convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [hCdef]; simp only [hsK, if_true]
    have hvC : v ∈ C s := by rw [hCs]; exact subset_convexHull ℝ _ hv
    have hvP : v ∈ P := hCsub s hsK hvC
    obtain ⟨i, hi⟩ := hdsub v hvP
    refine ⟨chartAt (EuclideanSpace ℝ (Fin m)) (f i),
      StructureGroupoid.chart_mem_maximalAtlas (plGroupoid m) _, fun y hy => ?_⟩
    have hbdd : Bornology.IsBounded (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n)))) :=
      isBounded_convexHull.mpr s.finite_toSet.isBounded
    have hyball : y ∈ ball v d := by
      rw [mem_ball]
      refine lt_of_le_of_lt ?_ (hK'diam s hsK)
      rw [dist_comm]
      exact dist_le_diam_of_mem hbdd (by rw [← hCs]; exact hvC) (by rw [← hCs]; exact hy)
    exact hWsub i ⟨hi hyball, hCsub s hsK hy⟩
  exact ⟨C, T, hC, hunion, hchart⟩

theorem exists_isPLOn_dist_lt {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P)
    {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ ∀ x ∈ P, dist (g x) (f x) < ε := by
  obtain ⟨C, T, hC, hunion, hchart⟩ := exists_finsetBiUnion_eq_mapsTo_chart (m := m) hP hf
  obtain ⟨g, hg, hgd⟩ :=
    exists_isPLOn_dist_lt_of_biUnion hC T (by rw [hunion]; exact hf) hchart hε
  rw [hunion] at hg hgd
  exact ⟨g, hg, hgd⟩

theorem exists_isPLOn_dist_lt_eqOn {n m : ℕ} {N : Type*} [MetricSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [HasGroupoid N (plGroupoid m)]
    {P Q : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hQP : Q ⊆ P) {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P)
    (hfQ : IsPLOn n m f Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ EqOn g f Q ∧
      ∀ x ∈ P, dist (g x) (f x) < ε := by
  obtain ⟨C, T, hC, hunion, hchart⟩ := exists_finsetBiUnion_eq_mapsTo_chart (m := m) hP hf
  have hQunion : Q ∪ ⋃ s ∈ T, C s = P := by rw [hunion]; exact union_eq_self_of_subset_left hQP
  obtain ⟨g, hg, hgQ, hgd⟩ :=
    exists_isPLOn_dist_lt_eqOn_of_biUnion hC hQ hfQ T (by rw [hQunion]; exact hf) hchart hε
  rw [hQunion] at hg hgd
  exact ⟨g, hg, hgQ, hgd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
