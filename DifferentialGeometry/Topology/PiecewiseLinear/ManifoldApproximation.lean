import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

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

end DifferentialGeometry.Topology.PiecewiseLinear
