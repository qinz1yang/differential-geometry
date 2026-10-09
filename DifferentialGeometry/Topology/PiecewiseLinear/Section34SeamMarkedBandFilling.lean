import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedFillingSeamNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCollaredFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualSeamCorrection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def Section34SeamMarkedBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (Cc Cp Cq As Bs S T D F J₀ J₁ : Set M) : Prop :=
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → ℝ × ℝ)
      (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCombinatorialSolidTorus R.space ∧
      IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)) ∧
      frontier R.space = g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ T ∧
      As ∩ u '' R.space = F ∧ Bs ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier T = F ∩ frontier T ∧
      (u '' R.space ⊆ Cp ∨ u '' R.space ∩ Cp = F) ∧
      (∀ k, a k ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) ∧
      Function.Injective a ∧
      (u ∘ g) '' ({a 0} ×ˢ Icc (0 : ℝ) 1) = J₀ ∧
      (u ∘ g) '' ({a 1} ×ˢ Icc (0 : ℝ) 1) = J₁ ∧
      IsPLHomeomorphOn δ₀ (Icc 0 1) A₀ ∧ IsPLHomeomorphOn δ₁ (Icc 0 1) A₁ ∧
      δ₀ 0 = a 0 ∧ δ₀ 1 = a 1 ∧ δ₁ 0 = a 0 ∧ δ₁ 1 = a 1 ∧
      A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      A₀ ∩ A₁ = {a 0, a 1} ∧
      (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
      ∃ (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
        (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool),
        Disjoint (C 0) (C 1) ∧ Disjoint (u '' C 0) (u '' C 1) ∧ (∀ k,
          IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
          IsCylindricalDiagram (f k) spliceSquare (C k) ∧
          (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
          u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k ∧
          u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C k ∩ As ∧
          u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C k ∩ Bs ∧
          (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
            ![As ∩ Cq, Bs ∩ Cp, As \ interior Cq, Bs \ interior Cp] l) ∧
          u '' C k ⊆ interior S ∧ ![J₀, J₁] k ⊆ interior (u '' C k) ∧
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
          u '' (R.space ∪ W) ⊆ interior S ∧
          0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
          L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
          (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
          J = Function.invFunOn u P '' (J₀ ∪ J₁) ∧
          IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior S ∧
          IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
          (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
          MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
          (∀ k, ∀ p ∈ section34CornerBase (α k) (β k), ∀ s ∈ Icc (0 : ℝ) 1,
            f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
              ρ (f k (p, s), t) = f k (section34CornerExteriorPush (α k) (β k) (p, t), s) ∧
              (u (ρ (f k (p, s), t)) ∈ As ↔
                p.2 = (if β k then t / 2 else -t / 2)) ∧
              (u (ρ (f k (p, s), t)) ∈ Bs ↔
                p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
            (u (ρ (x, t)) ∈ As ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if β k then t / 2 else -t / 2)) ∧
            (u (ρ (x, t)) ∈ Bs ↔
              ∃ k p s, p ∈ section34CornerBase (α k) (β k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
                x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if α k then t / 2 else -t / 2))) ∧
          (∀ t ∈ Ioc (0 : ℝ) c,
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ As =
              ⋃ k, (u ∘ f k) ''
                ({((if α k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
            (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ Bs =
              ⋃ k, (u ∘ f k) ''
                ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1)) ∧
          ∃ (Hc : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
            (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (e : Fin 2 → ℝ)
            (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
            IsPLHomeomorphOn Hc R.space R.space ∧
            IsCylindricalDiagram (Hc ∘ g) V R.space ∧
            (∀ p ∈ V, (Hc ∘ g) (p, 0) = (Hc ∘ g) (p, 1)) ∧
            (u ∘ Hc ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
            (u ∘ Hc ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
            (∀ k, (u ∘ Hc ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![J₀, J₁] k) ∧
            ∀ k, IsPLHomeomorphOn (θ k) V V ∧ θ k (1 / 2, 0) = a k ∧
              0 < e k ∧ e k ≤ 1 / 2 ∧
              IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
              (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (0 : ℝ) (e k), (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
                ν k (stdTriangleLoop s) = stdTriangleLoop q →
                ∀ t ∈ Icc (-e k) 0, (Hc ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
                  f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q)

theorem Section34SeamMarkedBandFilling.toFaceAlignedBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    Section34FaceAlignedBandFilling Cc Cp As Bs T D F J₀ J₁ := by
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁, -⟩ := h
  exact ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁⟩

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

theorem section34_seam_marked_band_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j) {D F : Set M₂}
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j)) :
    Section34SeamMarkedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).2 '' Cp (ends e).2)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2)
      (Sp e) (Tp e) D F (Pg e i) (Pg e j) := by
  have hseams := hfill.seams_subset_faces
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁⟩ := id hfill
  let _ : Finite R.faces := hRfin.to_subtype
  have hJO : Pg e i ∪ Pg e j ⊆ interior (Sp e) := by
    intro x hx
    exact section34_inner_tube_subset_interior_outer hprep hpack e
      (hT (hsecond.symm.subset (hseams hx).1).2)
  obtain ⟨N, C, f, α, β, hN, -, hCdis, htarget, hcf⟩ :=
    exists_section34_paired_filling_seam_neighborhoods hprep hpack e hi hj hij hP hu
      hcell R hR hsolid.1 hRP hT hfront hfirst hsecond hseams isOpen_interior hJO
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
    exists_section34_actual_collared_filling_cylinder hprep hpack e hP hu hcell R hR
      hsolid.1 hRP hT hfront hfirst hsecond hseams hfill
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
  exact ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁,
    C, f, α, β, hCdis, htarget, hfamily, c, L, W, ρ, H,
    hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels, hcorrection⟩

end DifferentialGeometry.Topology.PiecewiseLinear
