import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalCoordinates
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.LocalFlow

open Set Function Topology Filter Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar

theorem exists_inward_manifold_localFlow
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p)
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p)) :
    ∃ O : TopologicalSpace.Opens M, p ∈ O ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Φ : M × ℝ → M,
      ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ Φ
        ((O : Set M) ×ˢ Icc (0 : ℝ) ε) ∧
      (∀ y ∈ O, Φ (y, 0) = y) ∧
      (∀ y ∈ O, IsMIntegralCurveOn (fun t => Φ (y, t)) V (Icc (0 : ℝ) ε)) ∧
      (∀ y ∈ O, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (Φ (y, t))) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, InjOn (fun y => Φ (y, t)) O) ∧
      ∀ y ∈ O, ∀ s ∈ Icc (0 : ℝ) ε, ∀ t : ℝ,
        Φ (Φ (y, s), t) = Φ (y, s + t) := by
  let I := 𝓡∂ (n + 1)
  let e := extChartAt I p
  let A := normalSplit n
  let C : M → ℝ × EuclideanSpace ℝ (Fin n) := fun y => A (e y)
  obtain ⟨U, hU, h0U, hf, htarget, hnormal⟩ := exists_normalChartField_neighborhood hp hV hpos
  obtain ⟨F, hF, hFzero, hFadd, hFinj, W, hW, h0W, _, ε, hε, hflow⟩ :=
    exists_inward_halfSpace_localFlow hU h0U hf hnormal
  have hC : ContMDiffOn I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞ C e.source :=
    A.contDiff.contMDiff.comp_contMDiffOn (by
      simpa only [e, extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := p) (n := ∞)))
  let O : TopologicalSpace.Opens M :=
    ⟨e.source ∩ C ⁻¹' W, hC.continuousOn.isOpen_inter_preimage
      (by simpa only [e, extChartAt_source] using
        (chartAt (EuclideanHalfSpace (n + 1)) p).open_source) hW⟩
  have hpO : p ∈ O := by
    refine ⟨mem_extChartAt_source p, ?_⟩
    change A (e p) ∈ W
    rw [normalSplit_extChartAt_boundary hp]
    exact h0W
  have hCpos (y : M) : 0 ≤ (C y).1 := chartHeight_nonneg (n := n + 1) p y
  let G : M × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun q => A.symm (F (C q.1, q.2))
  let Φ : M × ℝ → M := fun q => e.symm (G q)
  have hGtarget : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) ε, G (y, t) ∈ e.target := by
    intro y hy t ht
    obtain ⟨hu, hn, _, _⟩ := hflow (C y) hy.2 (hCpos y) t ht
    exact htarget _ ⟨⟨hn, mem_univ _⟩, hu⟩
  have hΦsource : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) ε, Φ (y, t) ∈ e.source := by
    intro y hy t ht
    exact e.map_target (hGtarget y hy t ht)
  have hΦcoord : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) ε, e (Φ (y, t)) = G (y, t) := by
    intro y hy t ht
    exact e.right_inv (hGtarget y hy t ht)
  have hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ G
      ((O : Set M) ×ˢ Icc (0 : ℝ) ε) := by
    have hpair := (hC.mono (show (O : Set M) ⊆ e.source from inter_subset_left)).prodMap
      ((contMDiff_id (I := 𝓘(ℝ, ℝ))).contMDiffOn (s := Icc (0 : ℝ) ε))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hpair
    exact A.symm.contDiff.contMDiff.comp_contMDiffOn
      (hF.contMDiff.comp_contMDiffOn hpair)
  have hΦ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Φ
      ((O : Set M) ×ˢ Icc (0 : ℝ) ε) :=
    (contMDiffOn_extChartAt_symm p).comp hG (fun q hq => hGtarget q.1 hq.1 q.2 hq.2)
  refine ⟨O, hpO, ε, hε, Φ, hΦ, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change e.symm (A.symm (F (C y, 0))) = y
    rw [hFzero, A.symm_apply_apply]
    exact e.left_inv hy.1
  · intro y hy
    apply isMIntegralCurveOn_of_chartField I p V (γ := fun t => G (y, t))
      (fun t ht => hGtarget y hy t ht)
    intro t ht
    have hd := (hflow (C y) hy.2 (hCpos y) t ht).2.2.1
    have hh := A.symm.hasFDerivAt.comp_hasDerivAt t hd
    have he : A.symm (normalChartField p V (F (C y, t))) =
        chartField I p V (G (y, t)) := A.symm_apply_apply _
    change HasDerivAt (fun s => G (y, s)) (A.symm (normalChartField p V (F (C y, t)))) t at hh
    rw [he] at hh
    exact hh.hasDerivWithinAt
  · intro y hy t ht
    have hn := (hflow (C y) hy.2 (hCpos y) t ⟨ht.1.le, ht.2⟩).2.2.2 ht.1
    have hc : 0 < chartHeight (n := n + 1) p (Φ (y, t)) := by
      change 0 < (e (Φ (y, t))) 0
      rw [hΦcoord y hy t ⟨ht.1.le, ht.2⟩]
      exact hn
    by_contra hi
    have hb := (I.isBoundaryPoint_iff_not_isInteriorPoint (Φ (y, t))).mpr hi
    have hz := (chartHeight_eq_zero_iff p (by
      simpa only [e, extChartAt_source] using hΦsource y hy t ⟨ht.1.le, ht.2⟩)).mpr hb
    exact hc.ne' hz
  · intro t ht y hy z hz he
    apply e.injOn hy.1 hz.1
    apply A.injective
    apply hFinj t
    have hh := congrArg (fun q => A (e q)) he
    rw [hΦcoord y hy t ht, hΦcoord z hz t ht] at hh
    simpa only [G, A.apply_symm_apply] using hh
  · intro y hy s hs t
    have hc : C (Φ (y, s)) = F (C y, s) := by
      change A (e (Φ (y, s))) = F (C y, s)
      rw [hΦcoord y hy s hs]
      exact A.apply_symm_apply _
    change e.symm (A.symm (F (C (Φ (y, s)), t))) = e.symm (A.symm (F (C y, s + t)))
    rw [hc, hFadd]

end Poincare.Manifold.BoundaryCollar
