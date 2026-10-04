import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedFillingSeamNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentPairedFillingSeamNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCollaredFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualSeamCorrection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingFaceIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredCylinderFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem exists_collared_annular_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j) {D F : Set M₂}
    (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → ℝ × ℝ)
    (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ)
    (hP : IsPLBall 3 P)
    (hu : IsPLHomeomorphInto 3 u P)
    (hcell : u '' P = (G (ends e).1 '' Cc (ends e).1))
    (hRfin : R.faces.Finite)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRP : R.space ⊆ P)
    (hsolid : IsTopologicalSolidTorus R.space)
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space)
    (hends : (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)))
    (hT : u '' R.space ⊆ (Tp e))
    (hfirst : (G (ends e).1 '' CpBd (ends e).1) ∩ u '' R.space = F)
    (hsecond : (G (ends e).2 '' CpBd (ends e).2) ∩ u '' R.space = D)
    (hzero : (u ∘ g) '' ({a 0} ×ˢ Icc (0 : ℝ) 1) = (Pg e i))
    (hone : (u ∘ g) '' ({a 1} ×ˢ Icc (0 : ℝ) 1) = (Pg e j))
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) A₀)
    (hδ₁ : IsPLHomeomorphOn δ₁ (Icc 0 1) A₁)
    (hδ₀₀ : δ₀ 0 = a 0)
    (hδ₀₁ : δ₀ 1 = a 1)
    (hδ₁₀ : δ₁ 0 = a 0)
    (hδ₁₁ : δ₁ 1 = a 1)
    (hcover : A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hinter : A₀ ∩ A₁ = {a 0, a 1})
    (hface₀ : (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F)
    (hface₁ : (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D) :
    ∃ (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
        (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool),
        Disjoint (C 0) (C 1) ∧ Disjoint (u '' C 0) (u '' C 1) ∧ (∀ k,
          IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
          IsCylindricalDiagram (f k) spliceSquare (C k) ∧
          (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
          u '' (f k '' section34MarkedAxis) = ![(Pg e i), (Pg e j)] k ∧
          u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C k ∩ (G (ends e).1 '' CpBd (ends e).1) ∧
          u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C k ∩ (G (ends e).2 '' CpBd (ends e).2) ∧
          (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
            ![(G (ends e).1 '' CpBd (ends e).1) ∩ (G (ends e).2 '' Cp (ends e).2), (G (ends e).2 '' CpBd (ends e).2) ∩ (G (ends e).1 '' Cp (ends e).1), (G (ends e).1 '' CpBd (ends e).1) \ interior (G (ends e).2 '' Cp (ends e).2), (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
          u '' C k ⊆ interior (Sp e) ∧ ![(Pg e i), (Pg e j)] k ⊆ interior (u '' C k) ∧
          f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R.space) ∧
        let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
        let B := fun k => f k '' (section34CornerBase (α k) (β k) ×ˢ Icc (0 : ℝ) 1)
        ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
          (W : Set (EuclideanSpace ℝ (Fin 3)))
          (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
          (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
          let V := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
          let V' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
          IsPLBall 2 V' ∧ IsCylindricalDiagram H V' (R.space ∪ W) ∧
          (∀ z ∈ V', H (z, 0) = H (z, 1)) ∧
          EqOn H g (V ×ˢ Icc (0 : ℝ) 1) ∧
          (∀ p ∈ frontier V, ∀ t ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
            H (section34SquareShellFlatten c (p, t), s) = ρ (g (p, s), t)) ∧
          u '' (R.space ∪ W) ⊆ interior (Sp e) ∧
          0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
          L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
          (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
          J = Function.invFunOn u P '' ((Pg e i) ∪ (Pg e j)) ∧
          IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior (Sp e) ∧
          IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
          (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
          MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
          (∀ k, ∀ p ∈ section34CornerBase (α k) (β k), ∀ s ∈ Icc (0 : ℝ) 1,
            f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
              ρ (f k (p, s), t) = f k (section34CornerExteriorPush (α k) (β k) (p, t), s) ∧
              (u (ρ (f k (p, s), t)) ∈ (G (ends e).1 '' CpBd (ends e).1) ↔
                p.2 = (if β k then t / 2 else -t / 2)) ∧
              (u (ρ (f k (p, s), t)) ∈ (G (ends e).2 '' CpBd (ends e).2) ↔
                p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
            (u (ρ (x, t)) ∈ (G (ends e).1 '' CpBd (ends e).1) ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if β k then t / 2 else -t / 2)) ∧
            (u (ρ (x, t)) ∈ (G (ends e).2 '' CpBd (ends e).2) ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ t ∈ Ioc (0 : ℝ) c,
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ (G (ends e).1 '' CpBd (ends e).1) =
              ⋃ k, (u ∘ f k) ''
                ({((if α k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ (G (ends e).2 '' CpBd (ends e).2) =
              ⋃ k, (u ∘ f k) ''
                ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1)) ∧
          ∃ (Hc : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
            (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (seamRadius : Fin 2 → ℝ)
            (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
            IsPLHomeomorphOn Hc R.space R.space ∧
            IsCylindricalDiagram (Hc ∘ g) V R.space ∧
            (∀ p ∈ V, (Hc ∘ g) (p, 0) = (Hc ∘ g) (p, 1)) ∧
            (u ∘ Hc ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
            (u ∘ Hc ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
            (∀ k, (u ∘ Hc ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![(Pg e i), (Pg e j)] k) ∧
            ∀ k, IsPLHomeomorphOn (θ k) V V ∧ θ k (1 / 2, 0) = a k ∧
              0 < seamRadius k ∧ seamRadius k ≤ 1 / 2 ∧
              IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
              (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (0 : ℝ) (seamRadius k), (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (-seamRadius k) 0, (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q) := by
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hSpP : Sp e ⊆ u '' P := by
    rw [hcell, (htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hRS : u '' R.space ⊆ interior (Sp e) :=
    hT.trans (section34_inner_tube_subset_interior_outer hprep hpack e)
  have hRint : R.space ⊆ interior P := by
    intro x hx
    have hux : u x ∈ interior (u '' P) := interior_mono hSpP (hRS ⟨x, hx, rfl⟩)
    rw [← hu.image_interior] at hux
    obtain ⟨y, hy, hyx⟩ := hux
    exact hu.injOn (interior_subset hy) (hRP hx) hyx ▸ hy
  have hside : frontier R.space =
      g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) :=
    hg.frontier_eq_image_base_frontier isPLBall_unit_square (by simp) (by simp)
  have hfront : u '' frontier R.space = D ∪ F := by
    rw [hside, ← hcover, union_prod, image_union, image_union,
      ← image_comp, ← image_comp, hface₀, hface₁, union_comm]
  have hA₀ : A₀ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_left).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hA₁ : A₁ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_right).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hmodel : g '' ((A₀ ∪ A₁) ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left (union_subset hA₀ hA₁))).trans hg.image_eq.subset).trans hRP
  have hpair := hg.isAnnulusOn_pair_of_base_arcs hends hδ₀ hδ₁
    (hδ₁₀.trans hδ₀₀.symm) (hδ₁₁.trans hδ₀₁.symm) hA₀ hA₁
    (by simpa only [hδ₀₀, hδ₀₁] using hinter)
    (hu.continuousOn.mono hmodel) (hu.injOn.mono hmodel)
  have hfaces : IsAnnulusOn F (Pg e i) (Pg e j) ∧
      IsAnnulusOn D (Pg e i) (Pg e j) ∧ D ∩ F = Pg e i ∪ Pg e j := by
    simpa only [hδ₀₀, hδ₀₁, hzero, hone, hface₀, hface₁] using hpair
  obtain ⟨hF, hD, hDF⟩ := hfaces
  have hseams := hDF.symm.subset
  have hJO : Pg e i ∪ Pg e j ⊆ interior (Sp e) := by
    intro x hx
    exact section34_inner_tube_subset_interior_outer hprep hpack e
      (hT (hsecond.symm.subset (hseams hx).1).2)
  obtain ⟨N, C, f, α, β, hN, -, hCdis, htarget, hcf⟩ :=
    exists_section34_paired_filling_seam_neighborhoods hprep hpack e hi hj hij hP hu
      hcell R hR hsolid hRP hT hfront hfirst hsecond hseams isOpen_interior hJO
  have hfamily : ∀ k,
      IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
      IsCylindricalDiagram (f k) spliceSquare (C k) ∧
      (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
      u '' (f k '' section34MarkedAxis) = ![Pg e i, Pg e j] k ∧
      u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C k ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C k ∩ G (ends e).2 '' CpBd (ends e).2 ∧
      (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
          G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
          G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
      u '' C k ⊆ interior (Sp e) ∧ ![Pg e i, Pg e j] k ⊆ interior (u '' C k) ∧
      f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R.space := by
    intro k
    have hindex : Pg e (![i, j] k) = ![Pg e i, Pg e j] k := by fin_cases k <;> rfl
    obtain ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN, hJC, hquad⟩ := hcf k
    rw [hindex] at haxis hJC
    exact ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN.trans (hN k).2.2, hJC, hquad⟩
  obtain ⟨c, L, W, ρ, H, hcollar⟩ :=
    exists_collared_filling_cylinder_of_cell_contacts hcellA hcellB hP hu R hR
      hsolid hRint hRS hfront hfirst hsecond hseams hF hD hDF
      (fun k => (hfamily k).1) (fun k => (hfamily k).2.1)
      (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.1) α β
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2) hCdis hg hends hside
  have hcorrection := exists_actual_paired_seam_correction hu.injOn R hR hRP hg hends
    hside hfirst hsecond hδ₀ hδ₁ hδ₀₀ hδ₀₁ hδ₁₀ hδ₁₁ hcover hinter hface₀ hface₁
    (by
      intro k
      fin_cases k
      · exact hzero
      · exact hone)
    (fun k => (hfamily k).2.1.trans interior_subset)
    (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.2.2.1) α β
    (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2)
  obtain ⟨hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels⟩ := hcollar
  exact ⟨C, f, α, β, hCdis, htarget, hfamily, c, L, W, ρ, H,
    hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels, hcorrection⟩

theorem exists_collared_annular_filling_of_transported_sheet
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j) {D F : Set M₂}
    (Ψ : M₂ ≃ₜ M₂) (hfix : ∀ x ∈ Pg e i ∪ Pg e j, Ψ =ᶠ[𝓝 x] id)
    (hcellB : IsPLCellOn 3 (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (Ψ '' (G (ends e).2 '' CpBd (ends e).2)))
    (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → ℝ × ℝ)
    (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ)
    (hP : IsPLBall 3 P)
    (hu : IsPLHomeomorphInto 3 u P)
    (hcell : u '' P = (G (ends e).1 '' Cc (ends e).1))
    (hRfin : R.faces.Finite)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRP : R.space ⊆ P)
    (hsolid : IsTopologicalSolidTorus R.space)
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space)
    (hends : (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)))
    (hT : u '' R.space ⊆ (interior (Sp e)))
    (hfirst : (G (ends e).1 '' CpBd (ends e).1) ∩ u '' R.space = F)
    (hsecond : (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) ∩ u '' R.space = D)
    (hzero : (u ∘ g) '' ({a 0} ×ˢ Icc (0 : ℝ) 1) = (Pg e i))
    (hone : (u ∘ g) '' ({a 1} ×ˢ Icc (0 : ℝ) 1) = (Pg e j))
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) A₀)
    (hδ₁ : IsPLHomeomorphOn δ₁ (Icc 0 1) A₁)
    (hδ₀₀ : δ₀ 0 = a 0)
    (hδ₀₁ : δ₀ 1 = a 1)
    (hδ₁₀ : δ₁ 0 = a 0)
    (hδ₁₁ : δ₁ 1 = a 1)
    (hcover : A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hinter : A₀ ∩ A₁ = {a 0, a 1})
    (hface₀ : (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F)
    (hface₁ : (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D) :
    ∃ (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
        (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool),
        Disjoint (C 0) (C 1) ∧ Disjoint (u '' C 0) (u '' C 1) ∧ (∀ k,
          IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
          IsCylindricalDiagram (f k) spliceSquare (C k) ∧
          (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
          u '' (f k '' section34MarkedAxis) = ![(Pg e i), (Pg e j)] k ∧
          u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C k ∩ (G (ends e).1 '' CpBd (ends e).1) ∧
          u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C k ∩ (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) ∧
          (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
            ![(G (ends e).1 '' CpBd (ends e).1) ∩ (Ψ '' (G (ends e).2 '' Cp (ends e).2)), (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) ∩ (G (ends e).1 '' Cp (ends e).1), (G (ends e).1 '' CpBd (ends e).1) \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)), (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
          u '' C k ⊆ interior (Sp e) ∧ ![(Pg e i), (Pg e j)] k ⊆ interior (u '' C k) ∧
          f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R.space) ∧
        let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
        let B := fun k => f k '' (section34CornerBase (α k) (β k) ×ˢ Icc (0 : ℝ) 1)
        ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
          (W : Set (EuclideanSpace ℝ (Fin 3)))
          (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
          (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
          let V := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
          let V' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
          IsPLBall 2 V' ∧ IsCylindricalDiagram H V' (R.space ∪ W) ∧
          (∀ z ∈ V', H (z, 0) = H (z, 1)) ∧
          EqOn H g (V ×ˢ Icc (0 : ℝ) 1) ∧
          (∀ p ∈ frontier V, ∀ t ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
            H (section34SquareShellFlatten c (p, t), s) = ρ (g (p, s), t)) ∧
          u '' (R.space ∪ W) ⊆ interior (Sp e) ∧
          0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
          L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
          (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
          J = Function.invFunOn u P '' ((Pg e i) ∪ (Pg e j)) ∧
          IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior (Sp e) ∧
          IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
          (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
          MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
          (∀ k, ∀ p ∈ section34CornerBase (α k) (β k), ∀ s ∈ Icc (0 : ℝ) 1,
            f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
              ρ (f k (p, s), t) = f k (section34CornerExteriorPush (α k) (β k) (p, t), s) ∧
              (u (ρ (f k (p, s), t)) ∈ (G (ends e).1 '' CpBd (ends e).1) ↔
                p.2 = (if β k then t / 2 else -t / 2)) ∧
              (u (ρ (f k (p, s), t)) ∈ (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) ↔
                p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
            (u (ρ (x, t)) ∈ (G (ends e).1 '' CpBd (ends e).1) ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if β k then t / 2 else -t / 2)) ∧
            (u (ρ (x, t)) ∈ (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ t ∈ Ioc (0 : ℝ) c,
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ (G (ends e).1 '' CpBd (ends e).1) =
              ⋃ k, (u ∘ f k) ''
                ({((if α k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) =
              ⋃ k, (u ∘ f k) ''
                ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1)) ∧
          ∃ (Hc : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
            (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (seamRadius : Fin 2 → ℝ)
            (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
            IsPLHomeomorphOn Hc R.space R.space ∧
            IsCylindricalDiagram (Hc ∘ g) V R.space ∧
            (∀ p ∈ V, (Hc ∘ g) (p, 0) = (Hc ∘ g) (p, 1)) ∧
            (u ∘ Hc ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
            (u ∘ Hc ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
            (∀ k, (u ∘ Hc ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![(Pg e i), (Pg e j)] k) ∧
            ∀ k, IsPLHomeomorphOn (θ k) V V ∧ θ k (1 / 2, 0) = a k ∧
              0 < seamRadius k ∧ seamRadius k ≤ 1 / 2 ∧
              IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
              (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (0 : ℝ) (seamRadius k), (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (-seamRadius k) 0, (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q) := by
  have hside : frontier R.space =
      g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) :=
    hg.frontier_eq_image_base_frontier isPLBall_unit_square (by simp) (by simp)
  have hfront : u '' frontier R.space = D ∪ F := by
    rw [hside, ← hcover, union_prod, image_union, image_union,
      ← image_comp, ← image_comp, hface₀, hface₁, union_comm]
  have hA₀ : A₀ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_left).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hA₁ : A₁ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_right).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hmodel : g '' ((A₀ ∪ A₁) ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left (union_subset hA₀ hA₁))).trans hg.image_eq.subset).trans hRP
  have hpair := hg.isAnnulusOn_pair_of_base_arcs hends hδ₀ hδ₁
    (hδ₁₀.trans hδ₀₀.symm) (hδ₁₁.trans hδ₀₁.symm) hA₀ hA₁
    (by simpa only [hδ₀₀, hδ₀₁] using hinter)
    (hu.continuousOn.mono hmodel) (hu.injOn.mono hmodel)
  have hfaces : IsAnnulusOn F (Pg e i) (Pg e j) ∧
      IsAnnulusOn D (Pg e i) (Pg e j) ∧ D ∩ F = Pg e i ∪ Pg e j := by
    simpa only [hδ₀₀, hδ₀₁, hzero, hone, hface₀, hface₁] using hpair
  obtain ⟨hF, hD, hDF⟩ := hfaces
  have hseams := hDF.symm.subset
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hSpP : Sp e ⊆ u '' P := by
    rw [hcell, (htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hRint : R.space ⊆ interior P := by
    intro x hx
    have hux : u x ∈ interior (u '' P) := interior_mono hSpP (hT ⟨x, hx, rfl⟩)
    rw [← hu.image_interior] at hux
    obtain ⟨y, hy, hyx⟩ := hux
    exact hu.injOn (interior_subset hy) (hRP hx) hyx ▸ hy
  have hclosedR : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hregR : closure (interior R.space) = R.space :=
    (closure_minimal interior_subset hclosedR).antisymm
      (hR.subset_closure_interior_space (by simp))
  have hconnR : IsConnected (interior R.space) :=
    (isConnected_interior_space_and_compl (Set.toFinite R.faces) hR
      (hsolid.isConnected_frontier hclosedR) hsolid.interior_nonempty).1
  have hJO : Pg e i ∪ Pg e j ⊆ interior (Sp e) := by
    intro x hx
    exact hT (hsecond.symm.subset (hseams hx).1).2
  obtain ⟨N, C, f, α, β, hN, -, hCdis, htarget, hcf⟩ :=
    exists_section34_current_paired_filling_seam_neighborhoods hprep hpack e hi hj hij hP hu
      hcell Ψ hfix hcellB hRint hclosedR hregR hconnR hfront hfirst hsecond hseams
      isOpen_interior hJO
  have hfamily : ∀ k,
      IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
      IsCylindricalDiagram (f k) spliceSquare (C k) ∧
      (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
      u '' (f k '' section34MarkedAxis) = ![Pg e i, Pg e j] k ∧
      u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C k ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C k ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∧
      (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' Cp (ends e).2),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
      u '' C k ⊆ interior (Sp e) ∧ ![Pg e i, Pg e j] k ⊆ interior (u '' C k) ∧
      f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R.space := by
    intro k
    have hindex : Pg e (![i, j] k) = ![Pg e i, Pg e j] k := by fin_cases k <;> rfl
    obtain ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN, hJC, hquad⟩ := hcf k
    rw [hindex] at haxis hJC
    exact ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN.trans (hN k).2.2, hJC, hquad⟩
  obtain ⟨c, L, W, ρ, H, hcollar⟩ :=
    exists_collared_filling_cylinder_of_cell_contacts hcellA hcellB hP hu R hR
      hsolid hRint hT hfront hfirst hsecond hseams hF hD hDF
      (fun k => (hfamily k).1) (fun k => (hfamily k).2.1)
      (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.1) α β
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2) hCdis hg hends hside
  have hcorrection := exists_actual_paired_seam_correction hu.injOn R hR hRP hg hends
    hside hfirst hsecond hδ₀ hδ₁ hδ₀₀ hδ₀₁ hδ₁₀ hδ₁₁ hcover hinter hface₀ hface₁
    (by
      intro k
      fin_cases k
      · exact hzero
      · exact hone)
    (fun k => (hfamily k).2.1.trans interior_subset)
    (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.2.2.1) α β
    (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2)
  obtain ⟨hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels⟩ := hcollar
  exact ⟨C, f, α, β, hCdis, htarget, hfamily, c, L, W, ρ, H,
    hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels, hcorrection⟩

end DifferentialGeometry.Topology.PiecewiseLinear
