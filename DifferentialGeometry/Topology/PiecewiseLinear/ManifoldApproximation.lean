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
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty => exact ⟨f, fun x hx => absurd hx (by simp), fun x hx => absurd hx (by simp)⟩
  | insert j t hj ih =>
    rw [Finset.set_biUnion_insert] at hf ⊢
    set U := ⋃ i ∈ t, C i with hUdef
    have hU : IsPolyhedron U := IsPolyhedron.finsetBiUnion t hC
    obtain ⟨e, he, hemap⟩ := hchart j (Finset.mem_insert_self j t)
    have hQ : IsPolyhedron (U ∩ C j) := hU.inter (hC j)
    obtain ⟨η, hη, hηprop⟩ :=
      exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart (hC j) (hC j).isCompact
        hQ inter_subset_right (hf.mono subset_union_left) e he hemap hε
    obtain ⟨g₀, hg₀, hg₀d⟩ :=
      ih (hf.mono subset_union_right) (fun i hi => hchart i (Finset.mem_insert_of_mem hi))
        (lt_min hε hη)
    obtain ⟨g₁, hg₁, hg₁eq, hg₁d⟩ :=
      hηprop g₀ (hg₀.mono_of_isPolyhedron hQ inter_subset_left)
        (fun x hx => lt_of_lt_of_le (hg₀d x hx.1) (min_le_right _ _))
    refine ⟨(C j).piecewise g₁ g₀, ?_, ?_⟩
    · exact hg₁.piecewise_of_isClosed hg₀ (hC j).isClosed hU.isClosed
        (fun x hx => hg₁eq ⟨hx.2, hx.1⟩)
    · intro x hx
      by_cases hxV : x ∈ C j
      · rw [Set.piecewise_eq_of_mem _ _ _ hxV]
        exact hg₁d x hxV
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxV]
        exact lt_of_lt_of_le (hg₀d x (hx.resolve_left hxV)) (min_le_left _ _)

end DifferentialGeometry.Topology.PiecewiseLinear
