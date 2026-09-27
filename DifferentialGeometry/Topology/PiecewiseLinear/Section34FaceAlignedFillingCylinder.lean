import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedAnnulusRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.eq_closed_complement {M : Type*} [TopologicalSpace M] [T2Space M]
    {A B D J K : Set M} (hB : IsAnnulusOn B J K) (hD : IsClosed D)
    (hcover : D ∪ A = B ∪ A) (hDA : D ∩ A = J ∪ K) (hBA : B ∩ A = J ∪ K) :
    D = B := by
  have hDB : D ⊆ B := by
    intro x hxD
    rcases hcover.subset (Or.inl hxD) with hxB | hxA
    · exact hxB
    · exact (hBA.symm.subset (hDA.subset ⟨hxD, hxA⟩)).1
  have hcore : B \ (J ∪ K) ⊆ D := by
    intro x hx
    exact (hcover.symm.subset (Or.inl hx.1)).resolve_right
      (fun hxA => hx.2 (hBA.subset ⟨hx.1, hxA⟩))
  exact hDB.antisymm (hB.closure_sdiff_ends ▸ closure_minimal hcore hD)

theorem IsCylindricalDiagram.exists_base_arcs_of_annulus_pair
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] [T2Space M] {P Q : Set E} {S : Set V} {T D F : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) T]
    {g : E × ℝ → V} (hg : IsCylindricalDiagram g P S)
    (hends : ∀ x ∈ P, g (x, 0) = g (x, 1))
    (hQ : IsPLSphere 1 Q) (hQP : Q ⊆ P) {u : V → M}
    (hu : ContinuousOn u S) (hi : InjOn u S)
    (hside : (u ∘ g) '' (Q ×ˢ Icc (0 : ℝ) 1) = T)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hF : IsAnnulusOn F ((u ∘ g) '' ({x} ×ˢ Icc (0 : ℝ) 1))
      ((u ∘ g) '' ({y} ×ˢ Icc (0 : ℝ) 1)))
    (hD : IsClosed D) (hfront : D ∪ F = T)
    (hDF : D ∩ F = (u ∘ g) '' ({x} ×ˢ Icc (0 : ℝ) 1) ∪
      (u ∘ g) '' ({y} ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (A B : Set E) (δ ε : ℝ → E),
      IsPLHomeomorphOn δ (Icc 0 1) A ∧ IsPLHomeomorphOn ε (Icc 0 1) B ∧
      δ 0 = x ∧ δ 1 = y ∧ ε 0 = x ∧ ε 1 = y ∧ A ∪ B = Q ∧ A ∩ B = {x, y} ∧
      (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g) '' (B ×ˢ Icc (0 : ℝ) 1) = D := by
  obtain ⟨A, B, δ, ε, hδ, hε, hδ₀, hδ₁, hε₀, hε₁, hcover, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hQ hx hy hxy
  have hAQ : A ⊆ Q := hcover ▸ subset_union_left
  have hBQ : B ⊆ Q := hcover ▸ subset_union_right
  have hsub {L : Set E} (hL : L ⊆ Q) : g '' (L ×ˢ Icc (0 : ℝ) 1) ⊆ S :=
    (image_mono (prod_mono_left (hL.trans hQP))).trans hg.image_eq.subset
  have hann {L : Set E} {r : ℝ → E} (hr : IsPLHomeomorphOn r (Icc 0 1) L)
      (hL : L ⊆ Q) (hr₀ : r 0 = x) (hr₁ : r 1 = y) :
      IsAnnulusOn ((u ∘ g) '' (L ×ˢ Icc (0 : ℝ) 1))
        ((u ∘ g) '' ({x} ×ˢ Icc (0 : ℝ) 1))
        ((u ∘ g) '' ({y} ×ˢ Icc (0 : ℝ) 1)) := by
    have h := (hg.isAnnulusOn_base_arc hends hr (hL.trans hQP)).image_of_continuousOn_injOn
      (hu.mono (hsub hL)) (hi.mono (hsub hL))
    simpa only [image_comp, hr₀, hr₁] using h
  have hA := hann hδ hAQ hδ₀ hδ₁
  have hB := hann hε hBQ hε₀ hε₁
  have hbandcover : (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) ∪
      (u ∘ g) '' (B ×ˢ Icc (0 : ℝ) 1) = T := by
    rw [← image_union, ← union_prod, hcover, hside]
  have hbandinter : (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) ∩
      (u ∘ g) '' (B ×ˢ Icc (0 : ℝ) 1) =
      (u ∘ g) '' ({x} ×ˢ Icc (0 : ℝ) 1) ∪
        (u ∘ g) '' ({y} ×ˢ Icc (0 : ℝ) 1) := by
    rw [image_comp, image_comp, ← hi.image_inter (hsub hAQ) (hsub hBQ),
      hg.inter_images_base_regions hends (hAQ.trans hQP) (hBQ.trans hQP), hinter,
      ← singleton_union, union_prod, image_union, image_union]
    simp only [image_comp]
  have hFT : F ⊆ T := hfront ▸ subset_union_right
  rcases hF.eq_or_eq_of_annular_cover hA hB hFT hbandcover hbandinter with hFA | hFB
  · refine ⟨A, B, δ, ε, hδ, hε, hδ₀, hδ₁, hε₀, hε₁, hcover, hinter, hFA.symm, ?_⟩
    apply (hB.eq_closed_complement hD ?_ hDF ?_).symm
    · exact hfront.trans (by rw [hFA, union_comm]; exact hbandcover.symm)
    · rw [hFA, inter_comm, hbandinter]
  · refine ⟨B, A, ε, δ, hε, hδ, hε₀, hε₁, hδ₀, hδ₁,
      (union_comm _ _).trans hcover, (inter_comm _ _).trans hinter, hFB.symm, ?_⟩
    apply (hA.eq_closed_complement hD ?_ hDF ?_).symm
    · exact hfront.trans (by rw [hFB]; exact hbandcover.symm)
    · rw [hFB, hbandinter]

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

open Classical in
theorem exists_section34_face_aligned_filling_cylinder
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite B.faces] [Finite R.faces] (hB : IsPLBall 2 B.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hRP : R.space ⊆ P)
    {g : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g B.space R.space)
    (hends : ∀ z ∈ B.space, g (z, 0) = g (z, 1))
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hRT : u '' R.space ⊆ Tp e) (hfront : u '' frontier R.space = D ∪ F)
    (hD : IsClosed D) (hDF : D ∩ F = Pg e i ∪ Pg e j) :
    ∃ (g' : E × ℝ → EuclideanSpace ℝ (Fin 3))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (a : Fin 2 → (boundaryComplex 2 B).space) (A₀ A₁ : Set E) (δ₀ δ₁ : ℝ → E),
      IsCylindricalDiagram g' B.space R.space ∧
      (∀ z ∈ B.space, g' (z, 0) = g' (z, 1)) ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (g' '' (B.space ×ˢ {0})) ∧
      q '' stdSimplexBoundary 2 ⊆ frontier R.space ∧ Function.Injective a ∧
      (u ∘ g') '' ({(a 0 : E)} ×ˢ Icc (0 : ℝ) 1) = Pg e i ∧
      (u ∘ g') '' ({(a 1 : E)} ×ˢ Icc (0 : ℝ) 1) = Pg e j ∧
      IsPLHomeomorphOn δ₀ (Icc 0 1) A₀ ∧ IsPLHomeomorphOn δ₁ (Icc 0 1) A₁ ∧
      δ₀ 0 = a 0 ∧ δ₀ 1 = a 1 ∧ δ₁ 0 = a 0 ∧ δ₁ 1 = a 1 ∧
      A₀ ∪ A₁ = (boundaryComplex 2 B).space ∧
      A₀ ∩ A₁ = {(a 0 : E), (a 1 : E)} ∧
      (u ∘ g') '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g') '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D := by
  obtain ⟨g', q, a, hg', hends', hq, hqfront, hinj, hzero, hone⟩ :=
    exists_section34_aligned_filling_cylinder hprep hpack e hi hj hij hiess hjess
      B R hB hR hu hRP hg hends hF hRT hfront
  have hsolid := hg.isCombinatorialSolidTorus hB (by simp)
  have hfrontR : frontier R.space ⊆ R.space := hsolid.isPolyhedron.isClosed.frontier_subset
  obtain ⟨hchart⟩ := hsolid.isPLTorus_frontier.nonempty_chartedSpace_image
    (hu.continuousOn.mono (hfrontR.trans hRP)) (hu.injOn.mono (hfrontR.trans hRP))
  let _ := hchart
  have hside : (u ∘ g') '' ((boundaryComplex 2 B).space ×ˢ Icc (0 : ℝ) 1) =
      u '' frontier R.space := by
    rw [image_comp, ← hg'.frontier_eq_image_side B R hB hR (by simp)]
  have hbound : IsPLSphere 1 (boundaryComplex 2 B).space := by
    obtain ⟨r, hr⟩ := hB
    rw [← hr.image_stdSimplexBoundary_eq_boundaryComplex B rfl]
    exact hr.isPLSphere_image_stdSimplexBoundary
  have hxy : (a 0 : E) ≠ a 1 := fun heq =>
    (by decide : (0 : Fin 2) ≠ 1) (hinj (Subtype.ext heq))
  obtain ⟨A₀, A₁, δ₀, δ₁, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter,
      hfirst, hsecond⟩ :=
    hg'.exists_base_arcs_of_annulus_pair hends' hbound (boundaryComplex_space_subset 2 B)
      (hu.continuousOn.mono hRP) (hu.injOn.mono hRP) hside (a 0).2 (a 1).2 hxy
      (by simpa only [hzero, hone] using hF) hD hfront.symm
      (by simpa only [hzero, hone] using hDF)
  exact ⟨g', q, a, A₀, A₁, δ₀, δ₁, hg', hends', hq, hqfront, hinj, hzero, hone,
    hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hfirst, hsecond⟩

end DifferentialGeometry.Topology.PiecewiseLinear
