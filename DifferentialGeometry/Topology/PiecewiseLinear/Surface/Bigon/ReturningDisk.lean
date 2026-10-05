import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianBigonStrip
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CappedLateralAnnulus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_returning_disk_of_upper_height_arc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S : Set F} {r : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S) (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t))
    {β : ℝ → F} (hβ : IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1))
    (hβside : β '' Icc 0 1 ⊆ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    {g : F → ℝ} (hlift : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ht : β t ∈ S,
      (e ⟨β t, ht⟩).2 = (g (β t) : loopCircle))
    {m : ℤ} (hzero : g (β 0) = m) (hone : g (β 1) = m)
    (hopen : ∀ t ∈ Ioo (0 : ℝ) 1, g (β t) < m) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, (m : ℝ) - δ ≤ g (β t) ∧ g (β t) ≤ m) :
    ∃ (D A : Set F) (q : (Fin 3 → ℝ) → F),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ IsPLBall 1 A ∧
      D ⊆ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 1) ∧
      q '' stdSimplexBoundary 2 = (β '' Icc 0 1) ∪ A ∧
      D ∩ (f '' (P ×ˢ ({0} : Set ℝ))) = A := by
  classical
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hBP : r '' stdSimplexBoundary 2 ⊆ P :=
    (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  obtain ⟨a, γ, ha, ha1, hγ, hγside, hγtop, -, hγimage⟩ :=
    hf.exists_upper_returning_arc_in_strip hP.isPolyhedron hBP e he hβ hβside hlift
      hzero hone hopen hδ hδ1 hbound
  have hγbase : Disjoint (γ '' Icc 0 1) (P ×ˢ ({a} : Set ℝ)) := by
    refine disjoint_left.mpr fun z hz hzbase => ?_
    exact (hγside hz).2.1.ne' hzbase.2
  obtain ⟨D, A, q, hq, hA, hDside, hqbd, hDtop⟩ :=
    exists_disk_of_lateral_returning_arc hr ha1 hγ
      (hγside.trans (prod_mono_right Ioc_subset_Icc_self)) hγtop hγbase
  have hDstrip : D ⊆ P ×ˢ Icc a 1 :=
    hDside.trans (prod_mono hBP Ioc_subset_Icc_self)
  have hAD : A ⊆ D := hDtop ▸ inter_subset_left
  have hAstrip := hAD.trans hDstrip
  have hstrip := hf.isPLHomeomorphOn_strip hP.isPolyhedron ha.le le_rfl (Or.inl ha)
  have hDpoly : IsPolyhedron D := (show IsPLBall 2 D from ⟨q, hq⟩).isPolyhedron
  have hDmap := hstrip.restrict hDpoly hDstrip
  refine ⟨f '' D, f '' A, f ∘ q, hq.trans hDmap,
    hA.of_isPLHomeomorphOn (hstrip.restrict hA.isPolyhedron hAstrip), ?_, ?_, ?_⟩
  · exact image_mono (hDside.trans (prod_mono_right
      (fun _ ht => ⟨ha.le.trans ht.1.le, ht.2⟩)))
  · change (fun x => f (q x)) '' stdSimplexBoundary 2 = _
    rw [← image_image f q, hqbd, image_union, hγimage]
  · rw [← hf.image_top_eq_bottom]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      have hystrip : y ∈ P ×ˢ Icc a 1 := ⟨hy.1, hy.2.symm ▸ ⟨ha1.le, le_rfl⟩⟩
      have hxy := hstrip.bijOn.injOn (hDstrip hx) hystrip hyx.symm
      have hxA : x ∈ A := hDtop ▸ ⟨hx, (hDside hx).1,
        (congrArg Prod.snd hxy).trans hy.2⟩
      exact ⟨x, hxA, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxD : x ∈ D ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) :=
        hDtop.symm ▸ hx
      exact ⟨⟨x, hxD.1, rfl⟩, x, ⟨hBP hxD.2.1, hxD.2.2⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
