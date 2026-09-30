import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_boundary_product_coordinates_of_carrying_rims
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    {n : ℕ} (L : Fin n → Set M) (hn : 1 < n)
    (hL : ∀ i, IsPolyhedralSphere (n := 3) 1 (L i))
    (hLC : ∀ i, L i ⊆ u '' frontier C) (hdis : Pairwise fun i j => Disjoint (L i) (L j))
    (hgen : ∀ i, CarriesFundamentalGroupOnto (L i) S) :
    ∃ (J Q : Set (EuclideanSpace ℝ (Fin 3)))
      (f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (q : Fin n → EuclideanSpace ℝ (Fin 3)),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier C) ∧
      (∀ i, q i ∈ Q) ∧ Function.Injective q ∧
      ∀ i, L i = (u ∘ f) '' (J ×ˢ {q i}) := by
  let τ := Function.invFunOn u P
  have hfront : frontier C ⊆ C := hC.isPolyhedron.isClosed.frontier_subset
  have hLP (i : Fin n) : L i ⊆ u '' P :=
    (hLC i).trans (image_mono (hfront.trans hCP))
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hback (i : Fin n) : u '' (τ '' L i) = L i := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hLP i hx)).trans (image_id' _)
  have hsphere (i : Fin n) : IsPLSphere 1 (τ '' L i) :=
    hu.isPLSphere_invFunOn_image (hL i) (hLP i)
  have hsub (i : Fin n) : τ '' L i ⊆ frontier C := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hLC i hx
    rw [hleft (hCP (hfront hy))]
    exact hy
  have hdis' : Pairwise fun i j => Disjoint (τ '' L i) (τ '' L j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have heq : y = x := by
      rw [← hright (hLP j hy), ← hright (hLP i hx), hyx]
    exact disjoint_left.mp (hdis hij) hx (heq ▸ hy)
  have hess (i : Fin n) :
      ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
        (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier C ∧
          τ '' L i = r '' stdSimplexBoundary 2 := by
    rintro ⟨D, r, hr, hDC, hbd⟩
    have hD : IsPLBall 2 D := ⟨r, hr⟩
    have hDP := hDC.trans (hfront.trans hCP)
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hD.isPolyhedron hDP).isPLHomeomorphInto_model
        hD.isPolyhedron.isCompact (hu.injOn.mono hDP)
    have hcell : IsPLCellOn 2 (u '' D) (L i) := by
      refine ⟨D, r, u, hr, huD, rfl, ?_⟩
      rw [← hbd, hback]
    have hne : (L i).Nonempty := by
      rw [← hback i]
      exact (hsphere i).nonempty.image u
    exact hS.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hcell
      ((image_mono (hDC.trans hfront)).trans hCS) hne hcell.boundary_subset (hgen i)
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hi, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hC (fun i => τ '' L i)
      hn hsphere hsub hdis' hess
  refine ⟨J, Q, f, q, hJ, hQ, hf, hq, hi, fun i => ?_⟩
  rw [image_comp, ← hfamily i, hback]

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


theorem exists_section34_marked_filling_boundary_coordinates
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    {P C : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    (hCT : u '' C ⊆ Tp e) (hfront : u '' frontier C = D ∪ F) :
    ∃ (J Q : Set (EuclideanSpace ℝ (Fin 3)))
      (f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (q : Fin 2 → EuclideanSpace ℝ (Fin 3)),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier C) ∧
      (∀ k, q k ∈ Q) ∧ Function.Injective q ∧
      Pg e i = (u ∘ f) '' (J ×ˢ {q 0}) ∧ Pg e j = (u ∘ f) '' (J ×ˢ {q 1}) := by
  let L : Fin 2 → Set M₂ := ![Pg e i, Pg e j]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPg, hdis, -⟩ := id hpack
  have hL : ∀ k, IsPolyhedralSphere (n := 3) 1 (L k) := by
    intro k
    fin_cases k
    · exact (hPg e i hi).1
    · exact (hPg e j hj).1
  have hLC : ∀ k, L k ⊆ u '' frontier C := by
    intro k
    rw [hfront]
    fin_cases k
    · exact hF.first_subset.trans subset_union_right
    · exact hF.second_subset.trans subset_union_right
  have hdisL : Pairwise fun k l => Disjoint (L k) (L l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact hdis e i hi j hj hij
    · exact (hdis e i hi j hj hij).symm
    · exact (hkl rfl).elim
  have hgen : ∀ k, CarriesFundamentalGroupOnto (L k) (Sp e) := by
    intro k
    fin_cases k
    · exact (section34_piercing_generators_of_essential_second hprep hpack e hi hiess).1
    · exact (section34_piercing_generators_of_essential_second hprep hpack e hj hjess).1
  have hCS := hCT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    hu.exists_boundary_product_coordinates_of_carrying_rims hC hCP
      (section34_tubes_are_topological_solid_tori hprep hpack e).1 hCS L (by norm_num)
      hL hLC hdisL hgen
  exact ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily 0, hfamily 1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
