import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineWithinAt.union {f : E → F} {s t : Set E} {x : E}
    (hs : IsPiecewiseAffineWithinAt f s x) (ht : IsPiecewiseAffineWithinAt f t x) :
    IsPiecewiseAffineWithinAt f (s ∪ t) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hs
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := ht
  have := hι
  have := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim C D, Sum.elim A B, ?_, ?_⟩
  · rintro (i | j)
    · exact ⟨(hC i).1, (hC i).2.1.trans subset_union_left, (hC i).2.2⟩
    · exact ⟨(hD j).1, (hD j).2.1.trans subset_union_right, (hD j).2.2⟩
  · rw [iUnion_sum, nhdsWithin_union, Filter.mem_sup]
    exact ⟨Filter.mem_of_superset hCx subset_union_left,
      Filter.mem_of_superset hDx subset_union_right⟩

theorem IsPiecewiseAffineOn.union_of_open [FiniteDimensional ℝ E] {f : E → F} {s t : Set E}
    (hs : IsPiecewiseAffineOn f s) (ht : IsPiecewiseAffineOn f t)
    (hs' : ∀ x ∈ s, x ∉ t → ∃ O, IsOpen O ∧ x ∈ O ∧ (s ∪ t) ∩ O ⊆ s)
    (ht' : ∀ x ∈ t, x ∉ s → ∃ O, IsOpen O ∧ x ∈ O ∧ (s ∪ t) ∩ O ⊆ t) :
    IsPiecewiseAffineOn f (s ∪ t) := by
  intro x hx
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t
  · exact (hs x hxs).union (ht x hxt)
  · obtain ⟨O, hO, hxO, hsub⟩ := hs' x hxs hxt
    have h := (hs x hxs).inter_of_mem_nhds (hO.mem_nhds hxO)
    have heq : s ∩ O = (s ∪ t) ∩ O :=
      Subset.antisymm (inter_subset_inter_left _ subset_union_left) fun y hy => ⟨hsub hy, hy.2⟩
    rw [heq] at h
    exact h.of_inter_of_mem_nhds (hO.mem_nhds hxO)
  · obtain ⟨O, hO, hxO, hsub⟩ := ht' x hxt hxs
    have h := (ht x hxt).inter_of_mem_nhds (hO.mem_nhds hxO)
    have heq : t ∩ O = (s ∪ t) ∩ O :=
      Subset.antisymm (inter_subset_inter_left _ subset_union_right) fun y hy => ⟨hsub hy, hy.2⟩
    rw [heq] at h
    exact h.of_inter_of_mem_nhds (hO.mem_nhds hxO)
  · exact absurd hx (by simp [hxs, hxt])

theorem IsPiecewiseAffineOn.union_of_isClosed [FiniteDimensional ℝ E] {f : E → F} {s t : Set E}
    (hs : IsPiecewiseAffineOn f s) (ht : IsPiecewiseAffineOn f t) (hsc : IsClosed s)
    (htc : IsClosed t) : IsPiecewiseAffineOn f (s ∪ t) := by
  refine hs.union_of_open ht (fun x _ hxt => ⟨tᶜ, htc.isOpen_compl, hxt, ?_⟩)
    fun x _ hxs => ⟨sᶜ, hsc.isOpen_compl, hxs, ?_⟩
  · rintro y ⟨hy | hy, hyt⟩
    · exact hy
    · exact absurd hy hyt
  · rintro y ⟨hy | hy, hys⟩
    · exact absurd hy hys
    · exact hy

theorem IsPLHomeomorphOn.union [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P Q : Set E} {R S : Set F}
    (hf : IsPLHomeomorphOn f P R) (hg : IsPLHomeomorphOn f Q S)
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hmeet : f '' (P ∩ Q) = R ∩ S) :
    IsPLHomeomorphOn f (P ∪ Q) (R ∪ S) := by
  have hcross : ∀ x ∈ P, ∀ y ∈ Q, f x = f y → x = y := by
    intro x hx y hy hxy
    have hfy : f y ∈ R ∩ S := ⟨hxy ▸ hf.bijOn.mapsTo hx, hg.bijOn.mapsTo hy⟩
    obtain ⟨z, hz, hfz⟩ := hmeet.symm.subset hfy
    exact (hf.bijOn.injOn hx hz.1 (hxy.trans hfz.symm)).trans
      (hg.bijOn.injOn hz.2 hy hfz)
  have hinj : InjOn f (P ∪ Q) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hf.bijOn.injOn hx hy hxy
    · exact hcross x hx y hy hxy
    · exact (hcross y hy x hx hxy.symm).symm
    · exact hg.bijOn.injOn hx hy hxy
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (hP.union hQ)
    (hf.isPiecewiseAffineOn.union_of_isClosed hg.isPiecewiseAffineOn hP.isClosed hQ.isClosed)
    (hf.bijOn.union hg.bijOn hinj)

open Classical in
theorem IsPLHomeomorphOn.piecewise [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f g : E → F} {P Q : Set E} {R S : Set F}
    (hf : IsPLHomeomorphOn f P R) (hg : IsPLHomeomorphOn g Q S)
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hfg : EqOn f g (P ∩ Q))
    (hmeet : f '' (P ∩ Q) = R ∩ S) :
    IsPLHomeomorphOn (P.piecewise f g) (P ∪ Q) (R ∪ S) := by
  have hleft : EqOn (P.piecewise f g) f P := P.piecewise_eqOn f g
  have hright : EqOn (P.piecewise f g) g Q := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [P.piecewise_eq_of_mem f g hxP, hfg ⟨hxP, hx⟩]
    · exact P.piecewise_eq_of_notMem f g hxP
  exact (hf.congr hleft).union (hg.congr hright) hP hQ
    (((hleft.mono inter_subset_left).image_eq).trans hmeet)

theorem IsPiecewiseAffineWithinAt.inter_preimage_of_isHPolytope [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} {x : E} (hf : IsPiecewiseAffineWithinAt f s x) {C : Set F}
    (hC : IsHPolytope C) : IsPiecewiseAffineWithinAt f (s ∩ f ⁻¹' C) x := by
  obtain ⟨ι, hι, Cs, A, hCA, hnhds⟩ := hf
  have := hι
  refine ⟨ι, inferInstance, fun i => Cs i ∩ A i ⁻¹' C, A, fun i =>
    ⟨(hCA i).1.inter_preimage hC _, ?_, (hCA i).2.2.mono inter_subset_left⟩, ?_⟩
  · rintro y ⟨hy, hyA⟩
    refine ⟨(hCA i).2.1 hy, ?_⟩
    rw [mem_preimage, (hCA i).2.2 hy]
    exact hyA
  · have heq : (⋃ i, Cs i ∩ A i ⁻¹' C) = (⋃ i, Cs i) ∩ f ⁻¹' C := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨i, hy, hyA⟩
        refine ⟨⟨i, hy⟩, ?_⟩
        rw [(hCA i).2.2 hy]
        exact hyA
      · rintro ⟨⟨i, hy⟩, hyf⟩
        refine ⟨i, hy, ?_⟩
        rw [← (hCA i).2.2 hy]
        exact hyf
    rw [heq]
    exact Filter.inter_mem (nhdsWithin_mono x inter_subset_left hnhds)
      (Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right)

theorem IsPiecewiseAffineOn.inter_preimage_of_isHPolytope [FiniteDimensional ℝ E] {f : E → F}
    {s : Set E} (hf : IsPiecewiseAffineOn f s) {C : Set F} (hC : IsHPolytope C) :
    IsPiecewiseAffineOn f (s ∩ f ⁻¹' C) :=
  fun x hx => (hf x hx.1).inter_preimage_of_isHPolytope hC

theorem IsPiecewiseAffineWithinAt.inter_of_isHPolytope [FiniteDimensional ℝ E] {f : E → F}
    {s : Set E} {x : E} (hf : IsPiecewiseAffineWithinAt f s x) {C : Set E} (hC : IsHPolytope C) :
    IsPiecewiseAffineWithinAt f (s ∩ C) x := by
  obtain ⟨ι, hι, Cs, A, hCA, hnhds⟩ := hf
  have := hι
  refine ⟨ι, inferInstance, fun i => Cs i ∩ C, A, fun i => ⟨(hCA i).1.inter hC,
    inter_subset_inter_left _ (hCA i).2.1, (hCA i).2.2.mono inter_subset_left⟩, ?_⟩
  rw [← iUnion_inter]
  exact Filter.inter_mem (nhdsWithin_mono x inter_subset_left hnhds)
    (Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right)

theorem IsPiecewiseAffineOn.inter_of_isHPolytope [FiniteDimensional ℝ E] {f : E → F} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) {C : Set E} (hC : IsHPolytope C) :
    IsPiecewiseAffineOn f (s ∩ C) :=
  fun x hx => (hf x hx.1).inter_of_isHPolytope hC

theorem isPolyhedron_inter_preimage_of_isCompact [FiniteDimensional ℝ E] {f : E → F} {S : Set E}
    (hf : IsPiecewiseAffineOn f S) {C : Set F} (hC : IsHPolytope C)
    (hcomp : IsCompact (S ∩ f ⁻¹' C)) : IsPolyhedron (S ∩ f ⁻¹' C) := by
  classical
  choose! ι hι Cs A hCA hnhds using hf
  choose! u hu using fun x (hx : x ∈ S) => mem_nhdsWithin.mp (hnhds x hx)
  obtain ⟨t, ht, hcover⟩ := hcomp.elim_nhds_subcover u
    fun x hx => (hu x hx.1).1.mem_nhds (hu x hx.1).2.1
  have hfin : ∀ x : t, Finite (ι x) := fun x => hι x (ht x x.2).1
  have heq : S ∩ f ⁻¹' C = ⋃ p : (Σ x : t, ι x), Cs p.1 p.2 ∩ A p.1 p.2 ⁻¹' C := by
    apply Subset.antisymm
    · rintro y ⟨hyS, hyC⟩
      obtain ⟨x, hxt, hyu⟩ := mem_iUnion₂.mp (hcover ⟨hyS, hyC⟩)
      obtain ⟨i, hyi⟩ := mem_iUnion.mp ((hu x (ht x hxt).1).2.2 ⟨hyu, hyS⟩)
      refine mem_iUnion.mpr ⟨⟨⟨x, hxt⟩, i⟩, hyi, ?_⟩
      rw [mem_preimage, ← (hCA x (ht x hxt).1 i).2.2 hyi]
      exact hyC
    · refine iUnion_subset fun p => ?_
      rintro y ⟨hyC, hyA⟩
      refine ⟨(hCA p.1 (ht p.1 p.1.2).1 p.2).2.1 hyC, ?_⟩
      rw [mem_preimage, (hCA p.1 (ht p.1 p.1.2).1 p.2).2.2 hyC]
      exact hyA
  rw [heq]
  exact IsPolyhedron.iUnion fun p =>
    ((hCA p.1 (ht p.1 p.1.2).1 p.2).1.inter_preimage hC _).isPolyhedron

universe u

structure PLPieceIn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (Y : Set X) where
  complex : Geometry.SimplicialComplex ℝ E
  finite_faces : complex.faces.Finite
  map : E → X
  bijOn : BijOn map complex.space Y
  continuousOn : ContinuousOn map complex.space
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' Y)

structure PLPiece (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (Y : Set X) where
  ambientDim : ℕ
  piece : PLPieceIn (EuclideanSpace ℝ (Fin ambientDim)) n X Y

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

def PLPiece.toPLTriangulation (T : PLPiece n X univ) : PLTriangulation n X where
  ambientDim := T.ambientDim
  complex := T.piece.complex
  finite_faces := T.piece.finite_faces.to_subtype
  map := T.piece.map
  bijOn := T.piece.bijOn
  continuousOn := T.piece.continuousOn
  isPiecewiseAffineOn_chart := T.piece.isPiecewiseAffineOn_chart
  isPiecewiseAffineOn_chart_symm := fun e he => by
    have := T.piece.isPiecewiseAffineOn_chart_symm e he
    rwa [preimage_univ, inter_univ] at this

def PLPieceIn.subdivide {Y : Set X} (T : PLPieceIn E n X Y)
    (K' : Geometry.SimplicialComplex ℝ E) (h : IsSubdivision K' T.complex)
    (hfin : K'.faces.Finite) : PLPieceIn E n X Y where
  complex := K'
  finite_faces := hfin
  map := T.map
  bijOn := by
    rw [h.space_eq]
    exact T.bijOn
  continuousOn := by
    rw [h.space_eq]
    exact T.continuousOn
  isPiecewiseAffineOn_chart := fun e he => by
    rw [h.space_eq]
    exact T.isPiecewiseAffineOn_chart e he
  isPiecewiseAffineOn_chart_symm := fun e he => by
    rw [h.space_eq]
    exact T.isPiecewiseAffineOn_chart_symm e he

theorem space_bot : (⊥ : Geometry.SimplicialComplex ℝ E).space = ∅ := by
  ext x
  simp only [Geometry.SimplicialComplex.space, mem_iUnion, mem_empty_iff_false, iff_false,
    not_exists]
  intro s hs
  exact absurd hs (Set.notMem_empty s)

noncomputable def PLPieceIn.empty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty X] :
    PLPieceIn E n X ∅ where
  complex := ⊥
  finite_faces := Set.finite_empty
  map := fun _ => Classical.arbitrary X
  bijOn := by
    rw [space_bot]
    exact ⟨fun x hx => absurd hx (Set.notMem_empty x), fun x hx => absurd hx (Set.notMem_empty x),
      fun y hy => absurd hy (Set.notMem_empty y)⟩
  continuousOn := by
    rw [space_bot]
    exact continuousOn_empty _
  isPiecewiseAffineOn_chart := fun e _ => by
    rw [space_bot, empty_inter]
    exact fun x hx => absurd hx (Set.notMem_empty x)
  isPiecewiseAffineOn_chart_symm := fun e _ => by
    rw [preimage_empty, inter_empty]
    exact fun x hx => absurd hx (Set.notMem_empty x)

theorem PLPieceIn.isCompact [FiniteDimensional ℝ E] {Y : Set X} (T : PLPieceIn E n X Y) :
    IsCompact Y := by
  rw [← T.bijOn.image_eq]
  have := T.finite_faces.to_subtype
  exact (PiecewiseLinear.isPolyhedron_space T.complex).isCompact.image_of_continuousOn
    T.continuousOn

theorem PLPieceIn.isPolyhedron_space [FiniteDimensional ℝ E] {Y : Set X}
    (T : PLPieceIn E n X Y) : IsPolyhedron T.complex.space := by
  have := T.finite_faces.to_subtype
  exact PiecewiseLinear.isPolyhedron_space T.complex

theorem PLPieceIn.exists_transport [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq F] {Y : Set X} (T : PLPieceIn E n X Y) (L : E ≃ₗ[ℝ] F) :
    ∃ T' : PLPieceIn F n X Y, T'.complex.faces = simplicialImageFaces T.complex L ∧
      ∀ x ∈ T.complex.space, T'.map (L x) = T.map x := by
  classical
  have := T.finite_faces.to_subtype
  have hind : ∀ s ∈ T.complex.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ s.image L} → F) := fun _ hs =>
    affineIndependent_image_of_injOn_convexHull (L : E →ₗ[ℝ] F).toAffineMap (T.complex.indep hs)
      L.injective.injOn
  have hmap : EqOn (simplicialMap T.complex L) L T.complex.space :=
    simplicialMap_eq_of_forall_affineOn T.complex L fun _ _ =>
      ⟨(L : E →ₗ[ℝ] F).toAffineMap, fun _ _ => rfl⟩
  have hinj : InjOn (simplicialMap T.complex L) T.complex.space := fun x hx y hy hxy =>
    L.injective ((hmap hx).symm.trans (hxy.trans (hmap hy)))
  let K' := simplicialImage T.complex L hind hinj
  have hfin' : K'.faces.Finite := simplicialImage_faces_finite T.complex L hind hinj
  have hpl : IsPLHomeomorphOn L T.complex.space K'.space :=
    (isPLHomeomorphOn_simplicialImage T.complex L hind hinj).congr hmap.symm
  set Linv := Function.invFunOn (⇑L) T.complex.space with hLinv
  have hinvpl : IsPiecewiseAffineOn Linv K'.space := hpl.symm.isPiecewiseAffineOn
  have hinvbij : BijOn Linv K'.space T.complex.space := hpl.symm.bijOn
  have hinv_mem : ∀ z ∈ K'.space, Linv z ∈ T.complex.space := fun z hz => hinvbij.mapsTo hz
  refine ⟨⟨K', hfin', T.map ∘ Linv, T.bijOn.comp hinvbij,
    T.continuousOn.comp hinvpl.continuousOn hinvbij.mapsTo, fun e he => ?_, fun e he => ?_⟩, rfl, ?_⟩
  · have h := (T.isPiecewiseAffineOn_chart e he).comp hinvpl
    have heq : K'.space ∩ Linv ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source) =
        K'.space ∩ (T.map ∘ Linv) ⁻¹' e.source := by
      ext z
      constructor
      · rintro ⟨hz, -, hz'⟩
        exact ⟨hz, hz'⟩
      · rintro ⟨hz, hz'⟩
        exact ⟨hz, hinv_mem z hz, hz'⟩
    rw [heq] at h
    exact h.congr fun _ _ => rfl
  · have h := hpl.isPiecewiseAffineOn.comp (T.isPiecewiseAffineOn_chart_symm e he)
    have hsub : e.target ∩ e.symm ⁻¹' Y ⊆
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' T.complex.space := fun y hy =>
      T.bijOn.surjOn.mapsTo_invFunOn hy.2
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun y hy => ?_
    have hbij : BijOn (T.map ∘ Linv) K'.space Y := T.bijOn.comp hinvbij
    have h1 : Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y) ∈ K'.space :=
      hbij.surjOn.mapsTo_invFunOn hy.2
    have h2 : (T.map ∘ Linv) (Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y)) = e.symm y :=
      hbij.invOn_invFunOn.2 hy.2
    have h3 : Function.invFunOn T.map T.complex.space (e.symm y) ∈ T.complex.space :=
      T.bijOn.surjOn.mapsTo_invFunOn hy.2
    have h4 : T.map (Function.invFunOn T.map T.complex.space (e.symm y)) = e.symm y :=
      T.bijOn.invOn_invFunOn.2 hy.2
    have h5 : Linv (Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y)) =
        Function.invFunOn T.map T.complex.space (e.symm y) :=
      T.bijOn.injOn (hinv_mem _ h1) h3 (h2.trans h4.symm)
    have h6 : L (Linv (Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y))) =
        Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y) := hpl.bijOn.invOn_invFunOn.2 h1
    change Function.invFunOn (T.map ∘ Linv) K'.space (e.symm y) =
      L (Function.invFunOn T.map T.complex.space (e.symm y))
    rw [← h5, h6]
  · intro x hx
    exact congrArg T.map (hpl.bijOn.invOn_invFunOn.1 hx)

theorem PLPieceIn.transport [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {Y : Set X}
    (T : PLPieceIn E n X Y) (L : E ≃ₗ[ℝ] F) : Nonempty (PLPieceIn F n X Y) := by
  classical
  obtain ⟨T', -, -⟩ := T.exists_transport L
  exact ⟨T'⟩

theorem PLPieceIn.exists_pLPiece [FiniteDimensional ℝ E] {Y : Set X} (T : PLPieceIn E n X Y) :
    Nonempty (PLPiece n X Y) := by
  let L : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  obtain ⟨T'⟩ := T.transport L
  exact ⟨⟨_, T'⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
