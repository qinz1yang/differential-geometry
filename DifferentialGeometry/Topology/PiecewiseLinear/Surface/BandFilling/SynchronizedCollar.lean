import DifferentialGeometry.Topology.Map.LevelTraces
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedCollarRadius
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCornerBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedSeamSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollarAvoidance
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredCylinderFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderExpanded
import DifferentialGeometry.Topology.PiecewiseLinear.Annulus.ExteriorShellTraces

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_synchronized_collared_filling_avoiding
    {M : Type*} [TopologicalSpace M]
    {P R L W₀ : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M}
    (hui : InjOn u P) (huc : ContinuousOn u P)
    {g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (p, 0) = g (p, 1))
    (hRP : R ⊆ P) {As Bs S : Set M} {A₀ A₁ : Set (ℝ × ℝ)}
    (hcover : A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfirst : As ∩ u '' R = (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1))
    (hsecond : Bs ∩ u '' R = (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1))
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {α β : Fin 2 → Bool}
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hfirstF : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C k ∩ As)
    (hsecondF : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C k ∩ Bs)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R)
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)} {c₀ : ℝ}
    (hc₀ : 0 < c₀)
    (hρ₀ : IsPLHomeomorphOn ρ (frontier R ×ˢ Icc (0 : ℝ) c₀) W₀)
    (hzero : ∀ x ∈ frontier R, ρ (x, 0) = x)
    (hWR₀ : W₀ ∩ R = frontier R) (hWP₀ : W₀ ⊆ interior P)
    (hsupport₀ : u '' (R ∪ W₀) ⊆ interior S)
    (hL : ∀ k, L ∈ 𝓝ˢ[frontier R] (f k '' section34MarkedAxis))
    (hread : ∀ k, ∀ p ∈ section34CornerBase (α k) (β k), ∀ s ∈ Icc (0 : ℝ) 1,
      f k (p, s) ∈ L → ∀ t ∈ Icc (0 : ℝ) c₀,
        ρ (f k (p, s), t) = f k (section34CornerExteriorPush (α k) (β k) (p, t), s))
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c₀,
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ As =
        ⋃ k, (u ∘ f k) '' ({(if α k then -t / 2 else t / 2, 0)} ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ Bs =
        ⋃ k, (u ∘ f k) '' ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1))
    {γ : Fin 2 → ℝ → ℝ × ℝ} {b : Fin 2 → ℝ}
    {ν : Fin 2 → (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hb : ∀ k, 0 < b k) (hb1 : ∀ k, b k ≤ 1)
    (hγ : ∀ k, MapsTo (γ k) (Icc (-b k) (b k))
      (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hγcore : ∀ k, γ k 0 ∈ A₀ ∩ A₁)
    (hνmap : ∀ k, MapsTo (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hνsurj : ∀ k, SurjOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hpos : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) (b k),
        g (γ k t, s) = f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q))
    (hneg : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-b k) 0,
        g (γ k t, s) = f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q))
    {Z : Set M} (hZ : IsClosed Z) (hRZ : Disjoint (u '' R) Z) :
    ∃ (c : ℝ) (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
      let Q' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
      let W := ρ '' (frontier R ×ˢ Icc (0 : ℝ) c)
      let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
      let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
      0 < c ∧ c ≤ c₀ ∧ c ≤ 1 ∧ (∀ k, c / 2 ≤ b k) ∧ W ⊆ W₀ ∧
      IsPLHomeomorphOn ρ (frontier R ×ˢ Icc (0 : ℝ) c) W ∧
      W ∩ R = frontier R ∧ (R ∪ W) ⊆ interior P ∧ u '' (R ∪ W) ⊆ interior S ∧
      IsCylindricalDiagram H Q' (R ∪ W) ∧
      (∀ p ∈ Q', H (p, 0) = H (p, 1)) ∧ EqOn H g (Q ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ frontier Q, ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, r), s) = ρ (g (p, s), r)) ∧
      (∀ k, γ k '' Icc (0 : ℝ) (b k) ⊆ A₀ ∧ γ k '' Icc (-b k) 0 ⊆ A₁) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        f k ((0, if β k then r / 2 else -r / 2), s) ∈ L ∧
        f k ((if α k then r / 2 else -r / 2, 0), s) ∈ L) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ Icc (0 : ℝ) 1, ν k (stdTriangleLoop s) = stdTriangleLoop q →
          H (η₀ k r, s) = f k ((if α k then -r / 2 else r / 2, 0), q) ∧
          H (η₁ k r, s) = f k ((0, if β k then -r / 2 else r / 2), q)) ∧
      u '' (R ∪ W) ∩ As =
        (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' (R ∪ W) ∩ Bs =
        (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) ∧
      Disjoint (u '' (R ∪ W)) Z := by
  classical
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let F := (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1)
  let D := (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1)
  have hRpoly : IsPolyhedron R := by
    rw [← hg.image_eq]
    exact hg.isPiecewiseAffineOn.isPolyhedron_image
      (isPLBall_unit_square.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
  have hside : frontier R = g '' (frontier Q ×ˢ Icc (0 : ℝ) 1) :=
    hg.frontier_eq_image_base_frontier isPLBall_unit_square (by simp) (by simp)
  have hfront : u '' frontier R = D ∪ F := by
    rw [hside, ← hcover, union_prod, image_union, image_union, ← image_comp, ← image_comp]
    exact union_comm _ _
  have hRclosed : IsClosed R := hRpoly.isClosed
  have hfrontP := hRclosed.frontier_subset.trans hRP
  have hRint : R ⊆ interior P := by
    intro x hx
    by_cases hi : x ∈ interior R
    · exact interior_mono hRP hi
    · have hxfront : x ∈ frontier R := ⟨subset_closure hx, hi⟩
      exact hWP₀ ((hWR₀.symm ▸ hxfront).1)
  have hbase (k : Fin 2) :
      f k '' (section34CornerBase (α k) (β k) ×ˢ Icc (0 : ℝ) 1) ⊆ frontier R :=
    section34_corner_base_subset_frontier_of_target_contacts hui hRP hfrontP
      hfront hfirst hsecond (hfirstF k) (hsecondF k)
      (α k) (β k) (hquad k)
  obtain ⟨c₁, hc₁, hc₁c, hcollarZ⟩ := exists_short_collar_disjoint_of_closed
    hRpoly.frontier.isCompact hc₀ hρ₀.isPiecewiseAffineOn.continuousOn
    (hρ₀.bijOn.mapsTo.mono_right (hWP₀.trans interior_subset)) hzero huc hZ
    (hRZ.mono_left (image_mono hRclosed.frontier_subset))
  obtain ⟨c, hc, hcc₁, hc1, hce, hfeet⟩ := exists_common_seam_collar_radius
    hf α β hbase hL hc₁ b hb
  have hcc := hcc₁.trans hc₁c
  have hsmall : frontier R ×ˢ Icc (0 : ℝ) c ⊆
      frontier R ×ˢ Icc (0 : ℝ) c₀ := prod_mono_right (Icc_subset_Icc le_rfl hcc)
  let W := ρ '' (frontier R ×ˢ Icc (0 : ℝ) c)
  have hρ : IsPLHomeomorphOn ρ (frontier R ×ˢ Icc (0 : ℝ) c) W :=
    hρ₀.restrict (hRpoly.frontier.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hWW : W ⊆ W₀ := (image_mono hsmall).trans hρ₀.image_eq.subset
  have hWZ : Disjoint (u '' W) Z := by
    rw [show W = ρ '' (frontier R ×ˢ Icc (0 : ℝ) c) from rfl, ← image_comp]
    exact hcollarZ.mono_left
      (image_mono (prod_mono_right (Icc_subset_Icc le_rfl hcc₁)))
  have havoid : Disjoint (u '' (R ∪ W)) Z := by
    rw [image_union]
    exact hRZ.union_left hWZ
  have hWR : W ∩ R = frontier R := by
    apply Subset.antisymm ((inter_subset_inter_left _ hWW).trans hWR₀.subset)
    intro x hx
    exact ⟨hzero x hx ▸ hρ.bijOn.mapsTo ⟨hx, by constructor <;> linarith⟩,
      hRclosed.frontier_subset hx⟩
  have hAQ : A₀ ⊆ Q :=
    (subset_union_left.trans hcover.subset).trans
      isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hBQ : A₁ ⊆ Q :=
    (subset_union_right.trans hcover.subset).trans
      isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  obtain ⟨_, H, hH, hHends, hHeq, hshell⟩ :=
    hg.exists_expanded_square_of_outward_collar hends hside hc hρ hzero hWR
  let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
  let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
  have hγsides (k : Fin 2) := hg.image_base_arc_sides_of_signed_seam_formulas hends
    hui hRP hAQ hBQ (show (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F from rfl)
    (show (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D from rfl) hfirst hsecond
    (hfirstF k) (hsecondF k) (hb1 k)
    ((hγ k).mono_right isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset)
    (hνmap k) (hpos k) (hneg k)
  have hshellread (k : Fin 2) := synchronized_exterior_shell_ribbon_formulas hc.le hc1
    (hce k) (α k) (β k) (hγ k) hshell (hpos k) (hneg k) (hfeet k)
      (fun p hp s hs hx r hr => hread k p hp s hs hx r ⟨hr.1, hr.2.trans hcc⟩)
  have hbaseImage {A : Set (ℝ × ℝ)} (hA : A ⊆ Q) :
      (u ∘ H) '' (A ×ˢ Icc (0 : ℝ) 1) = (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) := by
    rw [image_comp, image_comp, (hHeq.mono (prod_mono_left hA)).image_eq]
  have hcore (k : Fin 2) : η₀ k 0 = γ k 0 ∧ η₁ k 0 = γ k 0 := by
    have hγQ := hAQ (hγcore k).1
    constructor <;> simp only [η₀, η₁, neg_zero, zero_div,
      section34_square_shell_flatten_zero hc.le hγQ]
  have hηimage (k : Fin 2) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) c) :
      (u ∘ H) '' ({η₀ k r} ×ˢ Icc (0 : ℝ) 1) =
        (u ∘ f k) '' ({(if α k then -r / 2 else r / 2, 0)} ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ H) '' ({η₁ k r} ×ˢ Icc (0 : ℝ) 1) =
        (u ∘ f k) '' ({(0, if β k then -r / 2 else r / 2)} ×ˢ Icc (0 : ℝ) 1) := by
    constructor
    · have hh := image_cylinder_region_of_circle_reparametrization (F := u ∘ H) (f := u ∘ f k)
        (η := η₀ k) (v := fun r => (if α k then -r / 2 else r / 2, 0))
        (hνmap k) (hνsurj k) (T := {r})
        (fun t ht s hs q hq heq => congrArg u ((hshellread k t (ht.symm ▸ hr) s hs q hq heq).1))
      simpa only [image_singleton] using hh
    · have hh := image_cylinder_region_of_circle_reparametrization (F := u ∘ H) (f := u ∘ f k)
        (η := η₁ k) (v := fun r => (0, if β k then -r / 2 else r / 2))
        (hνmap k) (hνsurj k) (T := {r})
        (fun t ht s hs q hq heq => congrArg u ((hshellread k t (ht.symm ▸ hr) s hs q hq heq).2))
      simpa only [image_singleton] using hh
  have htraceA : u '' (R ∪ W) ∩ As =
      (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
    apply DifferentialGeometry.Topology.image_union_inter_eq_of_level_traces
      (I := Icc (0 : ℝ) c) (J := Icc (0 : ℝ) 1) (t₀ := (0 : ℝ))
      hRclosed.frontier_subset hρ.image_eq (fun _ => hzero)
    · rw [inter_comm, hfirst, hbaseImage hAQ]
    · intro _ k
      rw [(hcore k).1]
      exact (hγcore k).1
    · intro r hr
      have hr' : r ∈ Ioc (0 : ℝ) c :=
        ⟨lt_of_le_of_ne hr.1.1 (Ne.symm hr.2), hr.1.2⟩
      rw [(hlevels r ⟨hr'.1, hr'.2.trans hcc⟩).1]
      exact iUnion_congr fun k => (hηimage k r ⟨hr'.1.le, hr'.2⟩).1.symm
  have htraceB : u '' (R ∪ W) ∩ Bs =
      (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
    apply DifferentialGeometry.Topology.image_union_inter_eq_of_level_traces
      (I := Icc (0 : ℝ) c) (J := Icc (0 : ℝ) 1) (t₀ := (0 : ℝ))
      hRclosed.frontier_subset hρ.image_eq (fun _ => hzero)
    · rw [inter_comm, hsecond, hbaseImage hBQ]
    · intro _ k
      rw [(hcore k).2]
      exact (hγcore k).2
    · intro r hr
      have hr' : r ∈ Ioc (0 : ℝ) c :=
        ⟨lt_of_le_of_ne hr.1.1 (Ne.symm hr.2), hr.1.2⟩
      rw [(hlevels r ⟨hr'.1, hr'.2.trans hcc⟩).2]
      exact iUnion_congr fun k => (hηimage k r ⟨hr'.1.le, hr'.2⟩).2.symm
  exact ⟨c, H, hc, hcc, hc1, hce, hWW, hρ, hWR,
    union_subset hRint (hWW.trans hWP₀),
    (image_mono (union_subset_union_right _ hWW)).trans hsupport₀,
    hH, hHends, hHeq, hshell, hγsides, hfeet, hshellread, htraceA, htraceB, havoid⟩

theorem exists_synchronized_collared_filling
    {M : Type*} [TopologicalSpace M]
    {P R L W₀ : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M}
    (hui : InjOn u P) (huc : ContinuousOn u P)
    {g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (p, 0) = g (p, 1))
    (hRP : R ⊆ P) {As Bs S : Set M} {A₀ A₁ : Set (ℝ × ℝ)}
    (hcover : A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfirst : As ∩ u '' R = (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1))
    (hsecond : Bs ∩ u '' R = (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1))
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {α β : Fin 2 → Bool}
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hfirstF : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C k ∩ As)
    (hsecondF : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C k ∩ Bs)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R)
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)} {c₀ : ℝ}
    (hc₀ : 0 < c₀)
    (hρ₀ : IsPLHomeomorphOn ρ (frontier R ×ˢ Icc (0 : ℝ) c₀) W₀)
    (hzero : ∀ x ∈ frontier R, ρ (x, 0) = x)
    (hWR₀ : W₀ ∩ R = frontier R) (hWP₀ : W₀ ⊆ interior P)
    (hsupport₀ : u '' (R ∪ W₀) ⊆ interior S)
    (hL : ∀ k, L ∈ 𝓝ˢ[frontier R] (f k '' section34MarkedAxis))
    (hread : ∀ k, ∀ p ∈ section34CornerBase (α k) (β k), ∀ s ∈ Icc (0 : ℝ) 1,
      f k (p, s) ∈ L → ∀ t ∈ Icc (0 : ℝ) c₀,
        ρ (f k (p, s), t) = f k (section34CornerExteriorPush (α k) (β k) (p, t), s))
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c₀,
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ As =
        ⋃ k, (u ∘ f k) '' ({(if α k then -t / 2 else t / 2, 0)} ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ Bs =
        ⋃ k, (u ∘ f k) '' ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1))
    {γ : Fin 2 → ℝ → ℝ × ℝ} {b : Fin 2 → ℝ}
    {ν : Fin 2 → (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hb : ∀ k, 0 < b k) (hb1 : ∀ k, b k ≤ 1)
    (hγ : ∀ k, MapsTo (γ k) (Icc (-b k) (b k))
      (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hγcore : ∀ k, γ k 0 ∈ A₀ ∩ A₁)
    (hνmap : ∀ k, MapsTo (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hνsurj : ∀ k, SurjOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hpos : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) (b k),
        g (γ k t, s) = f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q))
    (hneg : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-b k) 0,
        g (γ k t, s) = f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q))
    :
    ∃ (c : ℝ) (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
      let Q' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
      let W := ρ '' (frontier R ×ˢ Icc (0 : ℝ) c)
      let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
      let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
      0 < c ∧ c ≤ c₀ ∧ c ≤ 1 ∧ (∀ k, c / 2 ≤ b k) ∧ W ⊆ W₀ ∧
      IsPLHomeomorphOn ρ (frontier R ×ˢ Icc (0 : ℝ) c) W ∧
      W ∩ R = frontier R ∧ (R ∪ W) ⊆ interior P ∧ u '' (R ∪ W) ⊆ interior S ∧
      IsCylindricalDiagram H Q' (R ∪ W) ∧
      (∀ p ∈ Q', H (p, 0) = H (p, 1)) ∧ EqOn H g (Q ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ frontier Q, ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, r), s) = ρ (g (p, s), r)) ∧
      (∀ k, γ k '' Icc (0 : ℝ) (b k) ⊆ A₀ ∧ γ k '' Icc (-b k) 0 ⊆ A₁) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        f k ((0, if β k then r / 2 else -r / 2), s) ∈ L ∧
        f k ((if α k then r / 2 else -r / 2, 0), s) ∈ L) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ Icc (0 : ℝ) 1, ν k (stdTriangleLoop s) = stdTriangleLoop q →
          H (η₀ k r, s) = f k ((if α k then -r / 2 else r / 2, 0), q) ∧
          H (η₁ k r, s) = f k ((0, if β k then -r / 2 else r / 2), q)) ∧
      u '' (R ∪ W) ∩ As =
        (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' (R ∪ W) ∩ Bs =
        (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨c, H, hc, hcc, hc1, hce, hWW, hρ, hWR, hVP, hVS, hH, hHends,
    hHeq, hshell, hγsides, hfeet, hshellread, htraceA, htraceB, -⟩ :=
    exists_synchronized_collared_filling_avoiding
    hui huc hg hends hRP hcover hfirst hsecond hf hfirstF hsecondF hquad
    hc₀ hρ₀ hzero hWR₀ hWP₀ hsupport₀ hL hread hlevels hb hb1 hγ hγcore
    hνmap hνsurj hpos hneg isClosed_empty (disjoint_empty _)
  exact ⟨c, H, hc, hcc, hc1, hce, hWW, hρ, hWR, hVP, hVS, hH, hHends,
    hHeq, hshell, hγsides, hfeet, hshellread, htraceA, htraceB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
