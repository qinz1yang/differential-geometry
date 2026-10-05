import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollarSheetLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_collar_sheet_localization_of_annular_contacts
    {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {X Y As Bs D F J₀ J₁ : Set M}
    (hcellA : IsPLCellOn 3 X As) (hcellB : IsPLCellOn 3 Y Bs)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsAnnulusOn D J₀ J₁)
    (hDF : D ∩ F = J₀ ∪ J₁)
    {P R L : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hR : IsCompact R) (hRP : R ⊆ P)
    (hfront : u '' frontier R = D ∪ F)
    (hfirst : As ∩ u '' R = F) (hsecond : Bs ∩ u '' R = D)
    (hL : L ∈ 𝓝ˢ[frontier R] (frontier R ∩ u ⁻¹' (J₀ ∪ J₁)))
    {c : ℝ} (hc : 0 < c)
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : ContinuousOn ρ (frontier R ×ˢ Icc (0 : ℝ) c))
    (hρP : MapsTo ρ (frontier R ×ˢ Icc (0 : ℝ) c) P)
    (hbottom : ∀ x ∈ frontier R, ρ (x, 0) = x)
    (hpositive : MapsTo ρ (frontier R ×ˢ Ioc (0 : ℝ) c) Rᶜ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ c ∧ ∀ x ∈ frontier R, ∀ t ∈ Ioc (0 : ℝ) d,
      u (ρ (x, t)) ∈ As ∪ Bs → x ∈ L := by
  obtain ⟨V, hV, hJV, hVL⟩ := mem_nhdsSetWithin.mp hL
  let K := frontier R \ V
  have hfrontP : frontier R ⊆ P := hR.isClosed.frontier_subset.trans hRP
  have hK : IsCompact K :=
    (hR.of_isClosed_subset isClosed_frontier hR.isClosed.frontier_subset).diff hV
  have hKP : K ⊆ P := sdiff_subset.trans hfrontP
  have huK : IsCompact (u '' K) := hK.image_of_continuousOn (hu.continuousOn.mono hKP)
  have hnoJ : Disjoint (u '' K) (J₀ ∪ J₁) := by
    refine disjoint_left.mpr ?_
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 (hJV ⟨hx.1, hy⟩)
  have hFA : F ⊆ As := fun x hx => (hfirst.symm.subset hx).1
  have hDB : D ⊆ Bs := fun x hx => (hsecond.symm.subset hx).1
  have hdisF : Disjoint (F \ (J₀ ∪ J₁)) Bs := by
    refine disjoint_left.mpr fun x hx hxB => ?_
    exact hx.2 (hDF.subset ⟨hsecond.subset ⟨hxB, (hfirst.symm.subset hx.1).2⟩, hx.1⟩)
  have hdisD : Disjoint (D \ (J₀ ∪ J₁)) As := by
    refine disjoint_left.mpr fun x hx hxA => ?_
    exact hx.2 (hDF.subset ⟨hx.1, hfirst.subset ⟨hxA, (hsecond.symm.subset hx.1).2⟩⟩)
  have hAs : IsClosed As := hcellA.boundary_eq_frontier ▸ isClosed_frontier
  have hBs : IsClosed Bs := hcellB.boundary_eq_frontier ▸ isClosed_frontier
  obtain ⟨hchartA⟩ := hcellA.nonempty_chartedSpace_boundary
  obtain ⟨hchartB⟩ := hcellB.nonempty_chartedSpace_boundary
  let _ := hchartA
  let _ := hchartB
  obtain ⟨O₀, hO₀, hK₀, -, hO₀A, hO₀B⟩ :=
    hF.exists_open_isolation_of_isClosed hFA hBs hdisF
      (huK.inter_right hF.isCompact.isClosed).isClosed
      (fun x hx => ⟨hx.2, fun hj => disjoint_left.mp hnoJ hx.1 hj⟩)
      isOpen_univ (subset_univ _)
  obtain ⟨O₁, hO₁, hK₁, -, hO₁B, hO₁A⟩ :=
    hD.exists_open_isolation_of_isClosed hDB hAs hdisD
      (huK.inter_right hD.isCompact.isClosed).isClosed
      (fun x hx => ⟨hx.2, fun hj => disjoint_left.mp hnoJ hx.1 hj⟩)
      isOpen_univ (subset_univ _)
  have hKO : u '' K ⊆ O₀ ∪ O₁ := by
    rintro y hy
    have hyfront := hfront.subset ((image_mono sdiff_subset) hy)
    rcases hyfront with hyD | hyF
    · exact Or.inr (hK₁ ⟨hy, hyD⟩)
    · exact Or.inl (hK₀ ⟨hy, hyF⟩)
  have hOtrace : (O₀ ∪ O₁) ∩ (As ∪
      Bs) ⊆ D ∪ F := by
    rintro y ⟨hyO | hyO, hyA | hyB⟩
    · exact Or.inr (hO₀A ⟨subset_closure hyO, hyA⟩).1
    · exact (disjoint_left.mp hO₀B (subset_closure hyO) hyB).elim
    · exact (disjoint_left.mp hO₁A (subset_closure hyO) hyA).elim
    · exact Or.inl (hO₁B ⟨subset_closure hyO, hyB⟩).1
  have hprod : K ×ˢ Icc (0 : ℝ) c ⊆ frontier R ×ˢ Icc (0 : ℝ) c :=
    prod_mono_left sdiff_subset
  have hcomp : ContinuousOn (fun z => u (ρ z)) (K ×ˢ Icc (0 : ℝ) c) :=
    hu.continuousOn.comp (hρ.mono hprod) (hρP.mono_left hprod)
  obtain ⟨d, hd, hdc, hshort⟩ := exists_short_product_image_subset_of_compact hK hc hcomp
    (mapsTo_univ _ _) (fun x hx => by rw [hbottom x hx.1]; exact mem_image_of_mem u hx)
    (mem_nhdsSetWithin.mpr ⟨O₀ ∪ O₁, hO₀.union hO₁, hKO, inter_subset_left⟩)
  refine ⟨d, hd, hdc, ?_⟩
  intro x hx t ht hsheet
  by_contra hxL
  have hxK : x ∈ K := ⟨hx, fun hxV => hxL (hVL ⟨hxV, hx⟩)⟩
  have hyO := hshort (mem_image_of_mem (fun z => u (ρ z))
    (show (x, t) ∈ K ×ˢ Icc (0 : ℝ) d from ⟨hxK, ht.1.le, ht.2⟩))
  obtain ⟨z, hz, hzu⟩ := hfront.symm.subset (hOtrace ⟨hyO, hsheet⟩)
  have hzt : z = ρ (x, t) :=
    hu.injOn (hfrontP hz) (hρP ⟨hx, ht.1.le, ht.2.trans hdc⟩) hzu
  exact hpositive ⟨hx, ht.1, ht.2.trans hdc⟩ (hzt ▸ hR.isClosed.frontier_subset hz)


end DifferentialGeometry.Topology.PiecewiseLinear
