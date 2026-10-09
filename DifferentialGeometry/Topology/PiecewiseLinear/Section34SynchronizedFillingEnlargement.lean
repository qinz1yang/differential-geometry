import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedCollarRadius
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCollarTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCornerBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedSeamSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollarAvoidance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem Section34SeamMarkedBandFilling.exists_synchronized_enlargement_avoiding
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁)
    {Z : Set M} (hZ : IsClosed Z) (hZsheet : Z ⊆ As ∪ Bs)
    (hZfaces : Disjoint Z (D ∪ F)) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (a : Fin 2 → ℝ × ℝ) (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ)
      (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
      (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool)
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
      (L W : Set (EuclideanSpace ℝ (Fin 3))) (c : ℝ)
      (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (e : Fin 2 → ℝ)
      (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
      let Q' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
      let γ := fun k t => θ k (t / 2 + 1 / 2, 0)
      let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
      let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
      (IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCylindricalDiagram g Q R.space ∧ (∀ p ∈ Q, g (p, 0) = g (p, 1)) ∧
      frontier R.space = g '' (frontier Q ×ˢ Icc (0 : ℝ) 1) ∧
      IsPLHomeomorphOn δ₀ (Icc 0 1) A₀ ∧ IsPLHomeomorphOn δ₁ (Icc 0 1) A₁ ∧
      δ₀ 0 = a 0 ∧ δ₀ 1 = a 1 ∧ δ₁ 0 = a 0 ∧ δ₁ 1 = a 1 ∧
      A₀ ∪ A₁ = frontier Q ∧ A₀ ∩ A₁ = {a 0, a 1} ∧
      (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
      Disjoint (C 0) (C 1) ∧
      (∀ k, IsCylindricalDiagram (f k) spliceSquare (C k) ∧ C k ⊆ P ∧
        (∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) ∧
        u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k) ∧
      0 < c ∧ c ≤ 1 ∧ (R.space ∪ W) ⊆ interior P ∧ u '' (R.space ∪ W) ⊆ interior S ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      IsCylindricalDiagram H Q' (R.space ∪ W) ∧
      (∀ p ∈ Q', H (p, 0) = H (p, 1)) ∧ EqOn H g (Q ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ frontier Q, ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, r), s) = ρ (g (p, s), r)) ∧
      (∀ k, IsPLHomeomorphOn (θ k) Q Q ∧ θ k (1 / 2, 0) = a k ∧
        0 < e k ∧ e k ≤ 1 / 2 ∧ c / 2 ≤ e k ∧
        IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
        MapsTo (γ k) (Icc (-e k) (e k)) (frontier Q) ∧
        γ k '' Icc (0 : ℝ) (e k) ⊆ A₀ ∧ γ k '' Icc (-e k) 0 ⊆ A₁ ∧
        (u ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![J₀, J₁] k ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) (e k),
          g (γ k t, s) = f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e k) 0,
          g (γ k t, s) = f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q)) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        f k ((0, if β k then r / 2 else -r / 2), s) ∈ L ∧
          f k ((if α k then r / 2 else -r / 2, 0), s) ∈ L) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ Icc (0 : ℝ) 1, ν k (stdTriangleLoop s) = stdTriangleLoop q →
          H (η₀ k r, s) = f k ((if α k then -r / 2 else r / 2, 0), q) ∧
          H (η₁ k r, s) = f k ((0, if β k then -r / 2 else r / 2), q)) ∧
      u '' (R.space ∪ W) ∩ As =
        (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' (R.space ∪ W) ∩ Bs =
        (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1)) ∧
      Disjoint (u '' (R.space ∪ W)) Z := by
  obtain ⟨P, u, R, g₀, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, -, -,
    -, -, hfront, -, hfirst, hsecond, -, -, ha, -, -, -, hδ₀, hδ₁, hδ₀₀, hδ₀₁,
    hδ₁₀, hδ₁₁, hcover, hinter, -, -, C, f, α, β, hCdis, -, hfamily,
    c₀, L, W₀, ρ, _, -, -, -, -, -, hsupport₀, hc₀, -, _, _, -, _, hLnhds, _, _, hWP₀,
    _, hρ₀, hzero, hWR₀, _, hread, _, hlevels, Hc, θ, e, ν, -, hg, hends, hface₀,
    hface₁, hPg, hframe⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let g := Hc ∘ g₀
  have hRclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hfrontP := hRclosed.frontier_subset.trans hRP
  have hRint : R.space ⊆ interior P := by
    intro x hx
    by_cases hi : x ∈ interior R.space
    · exact interior_mono hRP hi
    · have hxfront : x ∈ frontier R.space := ⟨subset_closure hx, hi⟩
      exact hWP₀ ((hWR₀.symm ▸ hxfront).1)
  have hbase (k : Fin 2) :
      f k '' (section34CornerBase (α k) (β k) ×ˢ Icc (0 : ℝ) 1) ⊆ frontier R.space :=
    section34_corner_base_subset_frontier_of_target_contacts hu.injOn hRP hfrontP
      hfront hfirst hsecond (hfamily k).2.2.2.2.2.1 (hfamily k).2.2.2.2.2.2.1
      (α k) (β k) (hfamily k).2.2.2.2.2.2.2.2.2.2
  have hLn (k : Fin 2) : L.space ∈ 𝓝ˢ[frontier R.space] (f k '' section34MarkedAxis) := by
    rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
    intro x hx
    apply Filter.mem_inf_principal.mp
    apply hLnhds x
    fin_cases k
    · exact Or.inl hx
    · exact Or.inr hx
  have hRZ : Disjoint (u '' R.space) Z := by
    apply disjoint_left.mpr
    intro x hx hxZ
    apply disjoint_left.mp hZfaces hxZ
    rcases hZsheet hxZ with hA | hB
    · exact Or.inr (hfirst ▸ ⟨hA, hx⟩)
    · exact Or.inl (hsecond ▸ ⟨hB, hx⟩)
  obtain ⟨c₁, hc₁, hc₁c, hcollarZ⟩ := exists_short_collar_disjoint_of_closed
    (isPolyhedron_space R).frontier.isCompact hc₀ hρ₀.isPiecewiseAffineOn.continuousOn
    (hρ₀.bijOn.mapsTo.mono_right (hWP₀.trans interior_subset)) hzero hu.continuousOn hZ
    (hRZ.mono_left (image_mono hRclosed.frontier_subset))
  obtain ⟨c, hc, hcc₁, hc1, hce, hfeet⟩ := exists_common_seam_collar_radius
    (fun k => (hfamily k).2.2.1) α β hbase hLn hc₁ e (fun k => (hframe k).2.2.1)
  have hcc := hcc₁.trans hc₁c
  have hsmall : frontier R.space ×ˢ Icc (0 : ℝ) c ⊆
      frontier R.space ×ˢ Icc (0 : ℝ) c₀ := prod_mono_right (Icc_subset_Icc le_rfl hcc)
  let W := ρ '' (frontier R.space ×ˢ Icc (0 : ℝ) c)
  have hρ : IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W :=
    hρ₀.restrict ((isPolyhedron_space R).frontier.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hWW : W ⊆ W₀ := (image_mono hsmall).trans hρ₀.image_eq.subset
  have hWZ : Disjoint (u '' W) Z := by
    rw [show W = ρ '' (frontier R.space ×ˢ Icc (0 : ℝ) c) from rfl, ← image_comp]
    exact hcollarZ.mono_left
      (image_mono (prod_mono_right (Icc_subset_Icc le_rfl hcc₁)))
  have havoid : Disjoint (u '' (R.space ∪ W)) Z := by
    rw [image_union]
    exact hRZ.union_left hWZ
  have hWR : W ∩ R.space = frontier R.space := by
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
  have hside : frontier R.space = g '' (frontier Q ×ˢ Icc (0 : ℝ) 1) := by
    apply (hu.injOn.image_eq_image_iff hfrontP
      (((image_mono (prod_mono_left
        isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset)).trans
          hg.image_eq.subset).trans hRP)).mp
    rw [hfront, ← hcover, union_prod, image_union, image_union, ← image_comp, ← image_comp,
      hface₀, hface₁, union_comm]
  obtain ⟨_, H, hH, hHends, hHeq, hshell⟩ :=
    hg.exists_expanded_square_of_outward_collar hends hside hc hρ hzero hWR
  let γ := fun k t => θ k (t / 2 + 1 / 2, 0)
  let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
  let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
  have hγ (k : Fin 2) : MapsTo (γ k) (Icc (-e k) (e k)) (frontier Q) := by
    have hθbd : θ k '' frontier Q = frontier Q := by
      obtain ⟨v, hv⟩ := isPLBall_unit_square
      conv_lhs => rw [← hv.image_stdSimplexBoundary_eq_frontier_real_prod, ← image_comp]
      exact (hv.trans (hframe k).1).image_stdSimplexBoundary_eq_frontier_real_prod
    intro t ht
    apply hθbd.subset
    refine ⟨(t / 2 + 1 / 2, 0), ?_, rfl⟩
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
    refine Or.inl ⟨?_, by simp⟩
    constructor <;> linarith [ht.1, ht.2, (hframe k).2.2.2.1]
  have hγsides (k : Fin 2) := hg.image_base_arc_sides_of_signed_seam_formulas hends
    hu.injOn hRP hAQ hBQ hface₀ hface₁ hfirst hsecond
    (hfamily k).2.2.2.2.2.1 (hfamily k).2.2.2.2.2.2.1
    ((hframe k).2.2.2.1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
    ((hγ k).mono_right isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset)
    (hframe k).2.2.2.2.1.bijOn.mapsTo (hframe k).2.2.2.2.2.1 (hframe k).2.2.2.2.2.2
  have hshellread (k : Fin 2) := synchronized_exterior_shell_ribbon_formulas hc.le hc1
    (hce k) (α k) (β k) (hγ k) hshell (hframe k).2.2.2.2.2.1
      (hframe k).2.2.2.2.2.2 (hfeet k)
      (fun p hp s hs hL r hr =>
        (hread k p hp s hs hL r ⟨hr.1, hr.2.trans hcc⟩).1)
  have hbaseImage {A : Set (ℝ × ℝ)} (hA : A ⊆ Q) :
      (u ∘ H) '' (A ×ˢ Icc (0 : ℝ) 1) = (u ∘ g) '' (A ×ˢ Icc (0 : ℝ) 1) := by
    rw [image_comp, image_comp, (hHeq.mono (prod_mono_left hA)).image_eq]
  have hcore (k : Fin 2) : η₀ k 0 = a k ∧ η₁ k 0 = a k := by
    have hγzero : γ k 0 = a k := by simpa only [γ, zero_div, zero_add] using (hframe k).2.1
    have haQ := isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset (ha k)
    constructor <;> simp only [η₀, η₁, neg_zero, zero_div, hγzero,
      section34_square_shell_flatten_zero hc.le haQ]
  have hηimage (k : Fin 2) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) c) :
      (u ∘ H) '' ({η₀ k r} ×ˢ Icc (0 : ℝ) 1) =
        (u ∘ f k) '' ({(if α k then -r / 2 else r / 2, 0)} ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ H) '' ({η₁ k r} ×ˢ Icc (0 : ℝ) 1) =
        (u ∘ f k) '' ({(0, if β k then -r / 2 else r / 2)} ×ˢ Icc (0 : ℝ) 1) := by
    constructor
    · have hh := image_cylinder_region_of_circle_reparametrization (F := u ∘ H) (f := u ∘ f k)
        (η := η₀ k) (v := fun r => (if α k then -r / 2 else r / 2, 0))
        ((hframe k).2.2.2.2.1.bijOn) (T := {r})
        (fun t ht s hs q hq heq => congrArg u ((hshellread k t (ht.symm ▸ hr) s hs q hq heq).1))
      simpa only [image_singleton] using hh
    · have hh := image_cylinder_region_of_circle_reparametrization (F := u ∘ H) (f := u ∘ f k)
        (η := η₁ k) (v := fun r => (0, if β k then -r / 2 else r / 2))
        ((hframe k).2.2.2.2.1.bijOn) (T := {r})
        (fun t ht s hs q hq heq => congrArg u ((hshellread k t (ht.symm ▸ hr) s hs q hq heq).2))
      simpa only [image_singleton] using hh
  have htraceA : u '' (R.space ∪ W) ∩ As =
      (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
    apply cylindrical_trace_of_collar_level_traces hRclosed.frontier_subset hρ.image_eq hzero
    · rw [inter_comm, hfirst, hbaseImage hAQ, hface₀]
    · intro k
      rw [(hcore k).1]
      fin_cases k
      · exact hδ₀₀ ▸ hδ₀.bijOn.mapsTo (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      · exact hδ₀₁ ▸ hδ₀.bijOn.mapsTo (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    · intro r hr
      rw [(hlevels r ⟨hr.1, hr.2.trans hcc⟩).1]
      apply iUnion_congr
      intro k
      exact (hηimage k r ⟨hr.1.le, hr.2⟩).1.symm
  have htraceB : u '' (R.space ∪ W) ∩ Bs =
      (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
    apply cylindrical_trace_of_collar_level_traces hRclosed.frontier_subset hρ.image_eq hzero
    · rw [inter_comm, hsecond, hbaseImage hBQ, hface₁]
    · intro k
      rw [(hcore k).2]
      fin_cases k
      · exact hδ₁₀ ▸ hδ₁.bijOn.mapsTo (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      · exact hδ₁₁ ▸ hδ₁.bijOn.mapsTo (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    · intro r hr
      rw [(hlevels r ⟨hr.1, hr.2.trans hcc⟩).2]
      apply iUnion_congr
      intro k
      exact (hηimage k r ⟨hr.1.le, hr.2⟩).2.symm
  refine ⟨P, u, R, g, H, a, A₀, A₁, δ₀, δ₁, C, f, α, β, ρ, L.space, W, c, θ, e, ν,
    ?_, havoid⟩
  refine ⟨hP, hu, hcell, hRfin, hR, hRP, hg, hends, hside, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁,
    hcover, hinter, hface₀, hface₁, hCdis, ?_, hc, hc1,
    union_subset hRint (hWW.trans hWP₀),
    (image_mono (union_subset_union_right _ hWW)).trans hsupport₀, hρ, hzero, hWR,
    hH, hHends, hHeq, hshell, ?_, hfeet, hshellread, htraceA, htraceB⟩
  · intro k
    exact ⟨(hfamily k).2.2.1, (hfamily k).2.1.trans interior_subset,
      (hfamily k).2.2.2.1, (hfamily k).2.2.2.2.1⟩
  · intro k
    exact ⟨(hframe k).1, (hframe k).2.1, (hframe k).2.2.1, (hframe k).2.2.2.1,
      hce k, (hframe k).2.2.2.2.1, hγ k, (hγsides k).1, (hγsides k).2, hPg k,
      (hframe k).2.2.2.2.2.1, (hframe k).2.2.2.2.2.2⟩

open Classical in
theorem Section34SeamMarkedBandFilling.exists_synchronized_enlargement
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (a : Fin 2 → ℝ × ℝ) (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ)
      (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
      (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool)
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
      (L W : Set (EuclideanSpace ℝ (Fin 3))) (c : ℝ)
      (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (e : Fin 2 → ℝ)
      (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
      let Q' := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
      let γ := fun k t => θ k (t / 2 + 1 / 2, 0)
      let η₀ := fun k r => section34SquareShellFlatten c (γ k (-r / 2), r)
      let η₁ := fun k r => section34SquareShellFlatten c (γ k (r / 2), r)
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCylindricalDiagram g Q R.space ∧ (∀ p ∈ Q, g (p, 0) = g (p, 1)) ∧
      frontier R.space = g '' (frontier Q ×ˢ Icc (0 : ℝ) 1) ∧
      IsPLHomeomorphOn δ₀ (Icc 0 1) A₀ ∧ IsPLHomeomorphOn δ₁ (Icc 0 1) A₁ ∧
      δ₀ 0 = a 0 ∧ δ₀ 1 = a 1 ∧ δ₁ 0 = a 0 ∧ δ₁ 1 = a 1 ∧
      A₀ ∪ A₁ = frontier Q ∧ A₀ ∩ A₁ = {a 0, a 1} ∧
      (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
      Disjoint (C 0) (C 1) ∧
      (∀ k, IsCylindricalDiagram (f k) spliceSquare (C k) ∧ C k ⊆ P ∧
        (∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) ∧
        u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k) ∧
      0 < c ∧ c ≤ 1 ∧ (R.space ∪ W) ⊆ interior P ∧ u '' (R.space ∪ W) ⊆ interior S ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      IsCylindricalDiagram H Q' (R.space ∪ W) ∧
      (∀ p ∈ Q', H (p, 0) = H (p, 1)) ∧ EqOn H g (Q ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ frontier Q, ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, r), s) = ρ (g (p, s), r)) ∧
      (∀ k, IsPLHomeomorphOn (θ k) Q Q ∧ θ k (1 / 2, 0) = a k ∧
        0 < e k ∧ e k ≤ 1 / 2 ∧ c / 2 ≤ e k ∧
        IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
        MapsTo (γ k) (Icc (-e k) (e k)) (frontier Q) ∧
        γ k '' Icc (0 : ℝ) (e k) ⊆ A₀ ∧ γ k '' Icc (-e k) 0 ⊆ A₁ ∧
        (u ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![J₀, J₁] k ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) (e k),
          g (γ k t, s) = f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e k) 0,
          g (γ k t, s) = f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q)) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        f k ((0, if β k then r / 2 else -r / 2), s) ∈ L ∧
          f k ((if α k then r / 2 else -r / 2, 0), s) ∈ L) ∧
      (∀ k r, r ∈ Icc (0 : ℝ) c → ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ Icc (0 : ℝ) 1, ν k (stdTriangleLoop s) = stdTriangleLoop q →
          H (η₀ k r, s) = f k ((if α k then -r / 2 else r / 2, 0), q) ∧
          H (η₁ k r, s) = f k ((0, if β k then -r / 2 else r / 2), q)) ∧
      u '' (R.space ∪ W) ∩ As =
        (u ∘ H) '' ((A₀ ∪ ⋃ k, η₀ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' (R.space ∪ W) ∩ Bs =
        (u ∘ H) '' ((A₁ ∪ ⋃ k, η₁ k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨P, u, R, g, H, a, A₀, A₁, δ₀, δ₁, C, f, α, β, ρ, L, W, c, θ, e, ν,
    hdata, -⟩ := h.exists_synchronized_enlargement_avoiding isClosed_empty
      (empty_subset _) (empty_disjoint _)
  exact ⟨P, u, R, g, H, a, A₀, A₁, δ₀, δ₁, C, f, α, β, ρ, L, W, c, θ, e, ν, hdata⟩

end DifferentialGeometry.Topology.PiecewiseLinear
