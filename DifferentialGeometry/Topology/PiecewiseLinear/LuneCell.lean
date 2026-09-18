import DifferentialGeometry.Topology.PiecewiseLinear.PlanarGraphRegion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideFwd

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def luneModelMap (μ ν : ℝ → ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ × ℝ :=
  (w 0, μ (w 1), ν (w 1))

theorem isPLOn_chart_comp_of_isPiecewiseAffineOn {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {A : Set (EuclideanSpace ℝ (Fin 2))} {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hb : IsPiecewiseAffineOn b A) (hmaps : MapsTo b A ec.target) :
    IsPLOn 2 3 (fun x => ec.symm (b x)) A := by
  have hsrc : MapsTo (fun x => ec.symm (b x)) A ec.source := fun x hx => ec.map_target (hmaps hx)
  refine (isPLOn_iff_isPiecewiseAffineOn_comp_chart ec hec hsrc).mpr (hb.congr ?_)
  intro x hx
  exact ec.right_inv (hmaps hx)

theorem isPiecewiseAffineOn_luneModelMap {μ ν : ℝ → ℝ} {A : Set (EuclideanSpace ℝ (Fin 2))}
    {s t : ℝ} (hA : IsPolyhedron A)
    (hmap : MapsTo (fun w : EuclideanSpace ℝ (Fin 2) => w 1) A (Icc s t))
    (hμ : IsPiecewiseAffineOn μ (Icc s t)) (hν : IsPiecewiseAffineOn ν (Icc s t)) :
    IsPiecewiseAffineOn (luneModelMap μ ν) A := by
  have hproj0 : IsPiecewiseAffineOn (fun w : EuclideanSpace ℝ (Fin 2) => w 0) A :=
    (isPiecewiseAffineOn_of_affine
      (LinearMap.toAffineMap (EuclideanSpace.projₗ (0 : Fin 2))) isOpen_univ).mono_of_isPolyhedron
      hA (subset_univ A)
  have hproj1 : IsPiecewiseAffineOn (fun w : EuclideanSpace ℝ (Fin 2) => w 1) A :=
    (isPiecewiseAffineOn_of_affine
      (LinearMap.toAffineMap (EuclideanSpace.projₗ (1 : Fin 2))) isOpen_univ).mono_of_isPolyhedron
      hA (subset_univ A)
  have hset : A ∩ (fun w : EuclideanSpace ℝ (Fin 2) => w 1) ⁻¹' Icc s t = A :=
    inter_eq_left.mpr hmap
  have hμA : IsPiecewiseAffineOn (fun w : EuclideanSpace ℝ (Fin 2) => μ (w 1)) A := by
    have h := hμ.comp hproj1
    rwa [hset] at h
  have hνA : IsPiecewiseAffineOn (fun w : EuclideanSpace ℝ (Fin 2) => ν (w 1)) A := by
    have h := hν.comp hproj1
    rwa [hset] at h
  exact hproj0.prod_mk (hμA.prod_mk hνA)

theorem mapsTo_luneModelMap_slideSupportLong {μ ν α : ℝ → ℝ} {R s t : ℝ}
    (hμν : ∀ u ∈ Icc s t, |μ u| + |ν u| ≤ 1) (hαR : ∀ u ∈ Icc s t, α u ≤ R) :
    MapsTo (luneModelMap μ ν) (graphRegion α s t) (slideSupportLong R) := by
  rintro w ⟨hw1, hw0, hwa⟩
  refine ⟨hμν (w 1) hw1, ?_⟩
  rw [show (luneModelMap μ ν w).1 = w 0 from rfl, abs_of_nonneg hw0]
  exact hwa.trans (hαR (w 1) hw1)

theorem injOn_luneModelMap {μ ν : ℝ → ℝ} {A : Set (EuclideanSpace ℝ (Fin 2))} {s t : ℝ}
    (hmap : MapsTo (fun w : EuclideanSpace ℝ (Fin 2) => w 1) A (Icc s t))
    (hinj : InjOn (fun u => (μ u, ν u)) (Icc s t)) : InjOn (luneModelMap μ ν) A := by
  intro w hw v hv h
  have h0 : w 0 = v 0 := congrArg Prod.fst h
  have h2 : ((μ (w 1), ν (w 1)) : ℝ × ℝ) = (μ (v 1), ν (v 1)) := congrArg Prod.snd h
  have h1 : w 1 = v 1 := hinj (hmap hw) (hmap hv) h2
  refine PiLp.ext ?_
  rw [Fin.forall_fin_two]
  exact ⟨h0, h1⟩

theorem exists_lune_singularTwoCell {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {BdM : Set M} {Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hei : IsPiecewiseAffineOn e.symm e.target) (hesrc : e.source ⊆ E.target)
    {R : ℝ} (hsupp : slideSupportLong R ⊆ e.target)
    (hBdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hBd₁ : ∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0)
    {α μ ν : ℝ → ℝ} {N : ℕ} {σ : ℕ → ℝ}
    (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hσ : ∀ k ≤ N, σ k < σ (k + 1))
    (haff : ∀ k ≤ N, ∃ p q : ℝ, ∀ u ∈ Icc (σ k) (σ (k + 1)), α u = p * u + q)
    (hpos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < α u) (hα0 : α 0 = 0) (hα1 : α 1 = 0)
    (hαR : ∀ u ∈ Icc (0 : ℝ) 1, α u ≤ R)
    (hμ : IsPiecewiseAffineOn μ (Icc (0 : ℝ) 1)) (hν : IsPiecewiseAffineOn ν (Icc (0 : ℝ) 1))
    (hμν : ∀ u ∈ Icc (0 : ℝ) 1, |μ u| + |ν u| ≤ 1)
    (hinj : InjOn (fun u => (μ u, ν u)) (Icc (0 : ℝ) 1)) :
    ∃ D₂ : SingularTwoCell M, D₂.domain = graphRegion α 0 1 ∧
      (∀ w ∈ D₂.domain, D₂ w = E.symm (e.symm (luneModelMap μ ν w))) ∧
      InjOn D₂ D₂.domain ∧
      D₂ '' D₂.domain ⊆ E.symm '' (e.symm '' slideSupportLong R) ∧
      (∀ z ∈ frontier D₂.domain, z ∉ graphArc α 0 1 → D₂ z ∈ BdM) ∧
      ∀ x ∈ D₂.domain, E (D₂ x) ∈ e.source ∧ e (E (D₂ x)) = luneModelMap μ ν x := by
  have hball : IsPLBall 2 (graphRegion α 0 1) :=
    (isPLBall_two_and_closure_inside_frontier_graphRegion hσ0 hσN hσ haff hpos).1
  have hmap1 : MapsTo (fun w : EuclideanSpace ℝ (Fin 2) => w 1) (graphRegion α 0 1) (Icc 0 1) :=
    fun w hw => hw.1
  have hmapsS : MapsTo (luneModelMap μ ν) (graphRegion α 0 1) (slideSupportLong R) :=
    mapsTo_luneModelMap_slideSupportLong hμν hαR
  have htgt : ∀ w ∈ graphRegion α 0 1, luneModelMap μ ν w ∈ e.target :=
    fun w hw => hsupp (hmapsS hw)
  have hPA : IsPiecewiseAffineOn (luneModelMap μ ν) (graphRegion α 0 1) :=
    isPiecewiseAffineOn_luneModelMap hball.isPolyhedron hmap1 hμ hν
  have hbmaps : MapsTo (fun w => e.symm (luneModelMap μ ν w)) (graphRegion α 0 1) E.target :=
    fun w hw => hesrc (e.map_target (htgt w hw))
  have hbPA : IsPiecewiseAffineOn (fun w => e.symm (luneModelMap μ ν w)) (graphRegion α 0 1) := by
    have hsub : graphRegion α 0 1 ⊆ luneModelMap μ ν ⁻¹' e.target := fun w hw => htgt w hw
    have h := hei.comp hPA
    rwa [inter_eq_left.mpr hsub] at h
  have hPL : IsPLOn 2 3 (fun w => E.symm (e.symm (luneModelMap μ ν w))) (graphRegion α 0 1) :=
    isPLOn_chart_comp_of_isPiecewiseAffineOn E hE hbPA hbmaps
  have hEinj : ∀ y ∈ E.target, ∀ y' ∈ E.target, E.symm y = E.symm y' → y = y' := by
    intro y hy y' hy' h
    rw [← E.right_inv hy, ← E.right_inv hy', h]
  have heinj : ∀ p ∈ e.target, ∀ p' ∈ e.target, e.symm p = e.symm p' → p = p' := by
    intro p hp p' hp' h
    rw [← e.right_inv hp, ← e.right_inv hp', h]
  refine ⟨⟨graphRegion α 0 1, hball, fun w => E.symm (e.symm (luneModelMap μ ν w)), hPL⟩,
    rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    exact injOn_luneModelMap hmap1 hinj hw hv
      (heinj _ (htgt w hw) _ (htgt v hv)
        (hEinj _ (hesrc (e.map_target (htgt w hw))) _ (hesrc (e.map_target (htgt v hv))) h))
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨e.symm (luneModelMap μ ν w), ⟨luneModelMap μ ν w, hmapsS hw, rfl⟩, rfl⟩
  · intro z hz hznot
    have hcont : ContinuousOn α (Icc (0 : ℝ) 1) := by
      have h := continuousOn_of_subdivision hσ haff
      rwa [hσ0, hσN] at h
    have hzR : z ∈ graphRegion α 0 1 := hball.isPolyhedron.isClosed.frontier_subset hz
    have hz0 : z 0 = 0 :=
      (frontier_graphRegion_subset hball.isPolyhedron.isClosed hcont hα0.le hα1.le hz).resolve_right
        hznot
    have hp : luneModelMap μ ν z ∈ e.target := htgt z hzR
    have hy : e.symm (luneModelMap μ ν z) ∈ e.source := e.map_target hp
    have hx : E.symm (e.symm (luneModelMap μ ν z)) ∈ E.source := E.map_target (hesrc hy)
    change E.symm (e.symm (luneModelMap μ ν z)) ∈ BdM
    rw [hBdE _ hx, E.right_inv (hesrc hy), hBd₁ _ hy, e.right_inv hp]
    exact hz0
  · intro x hx
    have hp : luneModelMap μ ν x ∈ e.target := htgt x hx
    have hy : e.symm (luneModelMap μ ν x) ∈ e.source := e.map_target hp
    have hEy : E (E.symm (e.symm (luneModelMap μ ν x))) = e.symm (luneModelMap μ ν x) :=
      E.right_inv (hesrc hy)
    exact ⟨by rw [show E (E.symm (e.symm (luneModelMap μ ν x))) =
        e.symm (luneModelMap μ ν x) from hEy]; exact hy,
      by rw [show E (E.symm (e.symm (luneModelMap μ ν x))) =
        e.symm (luneModelMap μ ν x) from hEy]; exact e.right_inv hp⟩

theorem lune_ne_of_fiber_height {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    {α μ ν : ℝ → ℝ} {D₂ : SingularTwoCell M} (hdom : D₂.domain = graphRegion α 0 1)
    (hchart : ∀ x ∈ D₂.domain, E (D₂ x) ∈ e.source ∧ e (E (D₂ x)) = luneModelMap μ ν x)
    {S : Set M}
    (hfib : ∀ y ∈ S, E y ∈ e.source → ∀ s ∈ Icc (0 : ℝ) 1,
      (e (E y)).2 = (μ s, ν s) → α s ≤ (e (E y)).1) :
    ∀ x ∈ D₂.domain, x ∉ graphArc α 0 1 → ∀ y ∈ S, D₂ x ≠ y := by
  intro x hx hxarc y hy heq
  obtain ⟨hsrc, hval⟩ := hchart x hx
  rw [heq] at hsrc hval
  rw [hdom] at hx
  obtain ⟨hx1, hx0, hxa⟩ := hx
  have hlt : x 0 < α (x 1) := lt_of_le_of_ne hxa fun h => hxarc ⟨hx1, h⟩
  have h2 : (e (E y)).2 = (μ (x 1), ν (x 1)) := by
    rw [hval]
    rfl
  have hge := hfib y hy hsrc (x 1) hx1 h2
  rw [hval] at hge
  exact absurd hge (not_le.mpr hlt)

theorem slideAmountLong_le_slideMapFwd_fst {d R : ℝ} {p : ℝ × ℝ × ℝ} (hp : 0 ≤ p.1) :
    slideAmountLong d R (0, p.2) ≤ (slideMapFwd d R p).1 := by
  have h := slideAmountLong_le_add' (d := d) (R := R) (p := ((0 : ℝ), p.2)) (q := p) rfl hp
  have hfst : (slideMapFwd d R p).1 = p.1 + slideAmountLong d R p := rfl
  rw [hfst]
  have h0 : ((0 : ℝ), p.2).1 = 0 := rfl
  rw [h0] at h
  linarith

theorem lune_base_notMem_graphArc {α : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hα : 0 < α s) :
    planePoint 0 s ∈ graphRegion α 0 1 ∧ planePoint 0 s ∉ graphArc α 0 1 := by
  refine ⟨⟨hs, le_rfl, hα.le⟩, ?_⟩
  rintro ⟨-, h⟩
  exact hα.ne' h.symm

theorem exists_lune_base_off_graphArc {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    {α μ ν : ℝ → ℝ} {D₂ : SingularTwoCell M} (hdom : D₂.domain = graphRegion α 0 1)
    (hval : ∀ w ∈ D₂.domain, D₂ w = E.symm (e.symm (luneModelMap μ ν w)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hα : 0 < α s) :
    ∃ x ∈ D₂.domain, x ∉ graphArc α 0 1 ∧ D₂ x = E.symm (e.symm (0, μ s, ν s)) := by
  obtain ⟨hmem, hoff⟩ := lune_base_notMem_graphArc (α := α) hs hα
  rw [← hdom] at hmem
  exact ⟨planePoint 0 s, hmem, hoff, hval _ hmem⟩

end DifferentialGeometry.Topology.PiecewiseLinear
