import DifferentialGeometry.Topology.PiecewiseLinear.SingularManifoldLocal
import DifferentialGeometry.Topology.PiecewiseLinear.SingularNormalForm

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_small_simplicialMap_transverse_on_subcomplex_mapsTo
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K B : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hBK : B.faces ⊆ K.faces)
    (hcard : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ F + 1)
    (φ₀ : E → F)
    (hB : ∀ s ∈ B.faces, AffineIndependent ℝ (fun v : s => φ₀ v) ∧
      ∀ t ∈ L.faces, (convexHull ℝ (s.image φ₀ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ₀ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤)
    {U : Set F} (hU : IsOpen U) (hmap : MapsTo (simplicialMap K φ₀) K.space U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K' : Geometry.SimplicialComplex ℝ E) (φ : E → F),
      IsSubdivision K' K ∧ K'.faces.Finite ∧ B.faces ⊆ K'.faces ∧
        IsPiecewiseAffineOn (simplicialMap K' φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap K' φ x) (simplicialMap K φ₀ x) < ε) ∧
        EqOn (simplicialMap K' φ) (simplicialMap K φ₀) B.space ∧
        MapsTo (simplicialMap K' φ) K.space U ∧
        ∀ s ∈ K'.faces, AffineIndependent ℝ (fun v : s => φ v) ∧
          InjOn (simplicialMap K' φ) (convexHull ℝ (s : Set E)) ∧
          ∀ t ∈ L.faces, (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
            vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤ := by
  have hcompact : IsCompact (simplicialMap K φ₀ '' K.space) :=
    (isPolyhedron_space K).isCompact.image_of_continuousOn
      (isPiecewiseAffineOn_simplicialMap K φ₀).continuousOn
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_cthickening_subset_open hU hmap.image_subset
  obtain ⟨K', φ, hK', hfinite, hB', hpl, hclose, hfix, hgood⟩ :=
    exists_small_simplicialMap_transverse_on_subcomplex K B L hBK hcard φ₀ hB (lt_min hε hδ)
  refine ⟨K', φ, hK', hfinite, hB', hpl,
    fun x hx => (hclose x hx).trans_le (min_le_left ε δ), hfix, ?_, hgood⟩
  intro x hx
  exact hδU (mem_cthickening_of_dist_le _ _ δ _ ⟨x, hx, rfl⟩
    ((hclose x hx).trans_le (min_le_right ε δ)).le)

open Classical in
theorem exists_small_simplicialMap_doublePointSet_manifold_mapsTo
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    {U : Set F} (hU : IsOpen U) (hmap : MapsTo f K.space U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
        MapsTo (simplicialMap R φ) K.space U ∧
        (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
          (simplicialMap R φ '' (starComplex R v).space)) ∧
        IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
        (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
        G.faces.Finite ∧ G.space = doublePointSet (simplicialMap R φ) K.space ∧
        IsCombinatorialManifoldWithBoundary 1 G ∧
        ∀ y ∈ G.space, HasPLDoubleCrossingAt (simplicialMap R φ) K.space y := by
  have hcompact : IsCompact (f '' K.space) :=
    (isPolyhedron_space K).isCompact.image_of_continuousOn hf.continuousOn
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_cthickening_subset_open hU hmap.image_subset
  obtain ⟨R, φ, G, hR, hfinite, hpl, hclose, hstar, hlocal, hfiber, hGfinite, hGspace, hGman, hcross⟩ :=
    exists_small_simplicialMap_doublePointSet_manifold K hK hdim f hf hloc hcard (lt_min hε hδ)
  refine ⟨R, φ, G, hR, hfinite, hpl, fun x hx => (hclose x hx).trans_le (min_le_left ε δ),
    ?_, hstar, hlocal, hfiber, hGfinite, hGspace, hGman, hcross⟩
  intro x hx
  exact hδU (mem_cthickening_of_dist_le _ _ δ _ ⟨x, hx, rfl⟩
    ((hclose x hx).trans_le (min_le_right ε δ)).le)

theorem exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart_mapsTo
    {d : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [HasGroupoid X (plGroupoid 3)]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (f : EuclideanSpace ℝ (Fin d) → X)
    (hf : IsPLOn d 3 f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ z, (K.space ∩ f ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    {y : X} (hy : y ∈ doublePointSet f K.space) (hye : y ∈ e.source)
    {P : Set X} (hmap : MapsTo f K.space P) (hyP : y ∈ interior P)
    {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∩ interior P ∧ W ⊆ e.source ∧
      ∀ ε : ℝ, 0 < ε → ∃ (g : EuclideanSpace ℝ (Fin d) → X)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        IsPLOn d 3 g K.space ∧ (∀ x, dist (g x) (f x) < ε) ∧
        MapsTo g K.space P ∧
        IsLocallyInjective (K.space.domRestrict g) ∧ (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
        (∀ z ∉ V ∩ interior P, g ⁻¹' {z} = f ⁻¹' {z}) ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet g K.space ↔ e z ∈ G.space) ∧
        ∀ z ∈ W ∩ doublePointSet g K.space,
          HasPLDoubleCrossingAt (e ∘ g) (K.space ∩ g ⁻¹' e.source) (e z) := by
  obtain ⟨W, hW, hyW, hWV, hWe, hsmall⟩ :=
    exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart K hK f hf hloc hcard e he hy hye
      (Filter.inter_mem hV (isOpen_interior.mem_nhds hyP))
  refine ⟨W, hW, hyW, hWV, hWe, fun ε hε => ?_⟩
  obtain ⟨g, G, hg, hclose, hgloc, hgcard, hfiber, hGfinite, hGman, hGspace, hcross⟩ := hsmall ε hε
  exact ⟨g, G, hg, hclose, Topology.mapsTo_of_preimage_singleton_eq_off hmap
    (inter_subset_right.trans interior_subset) hfiber, hgloc, hgcard, hfiber,
    hGfinite, hGman, hGspace, hcross⟩

theorem SingularTwoCell.exists_compact_piece_with_perturbation_radius
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [HasGroupoid M (plGroupoid 3)] (D : SingularTwoCell M) :
    ∃ P : Set M, ∃ T : PLPiece 3 M P,
      IsCompact P ∧ IsCombinatorialManifoldWithBoundary 3 T.piece.complex ∧
      D '' D.domain ⊆ interior P ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ g : EuclideanSpace ℝ (Fin 2) → M,
          (∀ x ∈ D.domain, dist (g x) (D x) < δ) → MapsTo g D.domain (interior P) := by
  let _ : Nonempty M := ⟨D 0⟩
  obtain ⟨P, T, hP, hT, hDP⟩ := D.exists_compact_piece_neighborhood
  have hcompact : IsCompact (D '' D.domain) :=
    D.isPLBall_domain.isPolyhedron.isCompact.image_of_continuousOn D.continuousOn
  obtain ⟨δ, hδ, hδP⟩ := hcompact.exists_cthickening_subset_open isOpen_interior hDP
  refine ⟨P, T, hP, hT, hDP, δ, hδ, fun g hclose x hx => ?_⟩
  exact hδP (mem_cthickening_of_dist_le _ _ δ _ ⟨x, hx, rfl⟩ (hclose x hx).le)

end DifferentialGeometry.Topology.PiecewiseLinear
