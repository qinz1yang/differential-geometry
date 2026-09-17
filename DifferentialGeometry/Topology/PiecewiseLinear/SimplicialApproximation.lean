import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_carrierFace_of_mem_openStar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) {w y : F} (hy : y ∈ openStar L w) :
    w ∈ carrierFace L y := by
  by_contra hw
  exact hy.2 (mem_biUnion (s := {t ∈ L.faces | w ∉ t})
    (t := fun t => convexHull ℝ (t : Set F)) ⟨carrierFace_mem hy.1, hw⟩
    (mem_convexHull_carrierFace hy.1))

open Classical in
theorem exists_isSubdivision_simplicialApproximation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F} (hf : ContinuousOn f K.space) (hmap : MapsTo f K.space L.space) :
    ∃ (K' : Geometry.SimplicialComplex ℝ E) (φ : E → F),
      IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s ∈ K'.faces, s.image φ ∈ L.faces) ∧
      ∀ x ∈ K.space, simplicialMap K' φ x ∈
        convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F) := by
  classical
  have hKc : IsCompact K.space := (isPolyhedron_space K).isCompact
  choose V hVopen hVeq using fun w : {w : F // {w} ∈ L.faces} =>
    continuousOn_iff'.mp hf (avoidingUnion L w.1)ᶜ (isClosed_avoidingUnion L w.1).isOpen_compl
  obtain ⟨d, hd, hdsub⟩ := lebesgue_number_lemma_of_metric hKc hVopen (by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := exists_vertex_mem_openStar L (hmap hx)
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
    have hx' : x ∈ f ⁻¹' (avoidingUnion L w)ᶜ ∩ K.space := ⟨hxw.2, hx⟩
    rw [hVeq ⟨w, hw⟩] at hx'
    exact hx'.1)
  obtain ⟨K', hK', hK'fin, -, hK'diam⟩ :=
    exists_isSubdivision_diam_lt K (N := Module.finrank ℝ E)
      (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hd
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  have hstarball : ∀ v : E, closedStar K' v ⊆ ball v d := by
    intro v y hy
    obtain ⟨s, ⟨hs, hvs⟩, hys⟩ := mem_iUnion₂.mp hy
    have hbdd : Bornology.IsBounded (convexHull ℝ (s : Set E)) :=
      isBounded_convexHull.mpr s.finite_toSet.isBounded
    rw [mem_ball]
    exact lt_of_le_of_lt (dist_le_diam_of_mem hbdd hys hvs) (hK'diam s hs)
  have hvert : ∀ v : {v : E // {v} ∈ K'.faces}, ∃ w : F, {w} ∈ L.faces ∧
      ∀ y ∈ closedStar K' v.1 ∩ K.space, f y ∈ openStar L w := by
    rintro ⟨v, hv⟩
    have hvK : v ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
    obtain ⟨w, hw⟩ := hdsub v hvK
    refine ⟨w.1, w.2, fun y hy => ?_⟩
    have hy' : y ∈ f ⁻¹' (avoidingUnion L w.1)ᶜ ∩ K.space := by
      rw [hVeq w]
      exact ⟨hw (hstarball v hy.1), hy.2⟩
    exact ⟨hmap hy.2, hy'.1⟩
  choose ψ hψmem hψstar using hvert
  set φ : E → F := fun x => if h : {x} ∈ K'.faces then ψ ⟨x, h⟩ else 0 with hφdef
  have hkey : ∀ s ∈ K'.faces, ∀ x ∈ convexHull ℝ (s : Set E), ∀ v ∈ s,
      φ v ∈ carrierFace L (f x) := by
    intro s hs x hxs v hv
    have hv' : {v} ∈ K'.faces :=
      K'.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hxK : x ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hs hxs
    have hxstar : x ∈ closedStar K' v :=
      mem_biUnion (s := {s ∈ K'.faces | v ∈ convexHull ℝ (s : Set E)})
        (t := fun s => convexHull ℝ (s : Set E)) ⟨hs, subset_convexHull ℝ _ hv⟩ hxs
    have hφv : φ v = ψ ⟨v, hv'⟩ := by
      rw [hφdef]
      simp only [hv', dif_pos]
    rw [hφv]
    exact mem_carrierFace_of_mem_openStar L (hψstar ⟨v, hv'⟩ x ⟨hxstar, hxK⟩)
  refine ⟨K', φ, hK', hK'fin, ?_, ?_⟩
  · intro s hs
    obtain ⟨p, hp⟩ := K'.nonempty_of_mem_faces hs
    have hpH : p ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hp
    have hpK : p ∈ K.space := by
      rw [← hK'space]
      exact K'.convexHull_subset_space hs hpH
    refine L.down_closed (carrierFace_mem (hmap hpK)) ?_ ((K'.nonempty_of_mem_faces hs).image φ)
    exact Finset.image_subset_iff.mpr fun v hv => hkey s hs p hpH v hv
  · intro x hx
    have hxK' : x ∈ K'.space := by rw [hK'space]; exact hx
    refine convexHull_mono ?_
      (simplicialMap_mem_convexHull_image K' φ (carrierFace_mem hxK')
        (mem_convexHull_carrierFace hxK'))
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hkey _ (carrierFace_mem hxK') x (mem_convexHull_carrierFace hxK') v hv

open Classical in
theorem exists_isPiecewiseAffineOn_mapsTo_dist_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F} (hf : ContinuousOn f K.space) (hmap : MapsTo f K.space L.space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, IsPiecewiseAffineOn g K.space ∧ MapsTo g K.space L.space ∧
      ∀ x ∈ K.space, dist (g x) (f x) < ε := by
  classical
  obtain ⟨L', hL', hL'fin, -, hL'diam⟩ :=
    exists_isSubdivision_diam_lt L (N := Module.finrank ℝ F)
      (fun s hs => card_le_finrank_succ_of_mem_faces L hs) hε
  let _ : Finite L'.faces := hL'fin.to_subtype
  have hL'space : L'.space = L.space := hL'.space_eq
  obtain ⟨K', φ, hK', hK'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation K L' hf (by rw [hL'space]; exact hmap)
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  refine ⟨simplicialMap K' φ, ?_, ?_, ?_⟩
  · rw [← hK'space]
    exact isPiecewiseAffineOn_simplicialMap K' φ
  · rw [← hL'space, ← hK'space]
    exact simplicialMap_mapsTo K' L' φ hφ
  · intro x hx
    have hxL : f x ∈ L'.space := by rw [hL'space]; exact hmap hx
    have hbdd : Bornology.IsBounded (convexHull ℝ ((carrierFace L' (f x) : Finset F) : Set F)) :=
      isBounded_convexHull.mpr (carrierFace L' (f x)).finite_toSet.isBounded
    exact lt_of_le_of_lt
      (dist_le_diam_of_mem hbdd (hclose x hx) (mem_convexHull_carrierFace hxL))
      (hL'diam _ (carrierFace_mem hxL))

end DifferentialGeometry.Topology.PiecewiseLinear
