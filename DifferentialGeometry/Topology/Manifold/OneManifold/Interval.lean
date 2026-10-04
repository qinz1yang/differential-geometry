import DifferentialGeometry.Topology.Manifold.OneManifold.DoubleEmbedding
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Ehresmann.BoundaryInterval
import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema

/-!
# Compact connected one-manifolds with boundary are closed intervals

Let `M` be a compact connected smooth one-manifold (model `𝓡∂ 1`) with nonempty boundary.

* `exists_injective_noncritical_coordinate`: the double of `M` is a circle (`Double`,
  `nonempty_addCircle_diffeomorph_of_finrank_eq_one`); the upper sheet misses a point of the lower
  sheet, so cutting the circle there gives a smooth injective function `u : M → ℝ` with
  nonvanishing derivative.
* `boundary_value_eq_or_eq`: such a function takes its extreme values at boundary points, and
  only there.
* `nonempty_diffeomorph_Icc_of_boundary_nonempty`: the Ehresmann trivialization
  `exists_boundary_interval_trivialization` over `[min u, max u]` has a one-point fibre, so
  `M ≃ₘ [0, 1]`; `ncard_boundary_eq_two_of_boundary_nonempty`: `M` has exactly two boundary
  points.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M] [T2Space M]

omit [CompactSpace M] [T2Space M] in
/-- A point of the collar of a boundary point that is not a boundary point. -/
theorem exists_notMem_boundary_of_mem_boundary {p : M} (hp : p ∈ (𝓡∂ 1).boundary M) :
    ∃ x : M, x ∉ (𝓡∂ 1).boundary M := by
  let q : Bdry M := ⟨p, hp⟩
  let e := chartAt (EuclideanHalfSpace 1) p
  have hr := bdryRadius_pos q
  have ht : halfPt (bdryRadius q) ∈ e.target := halfPt_mem_target_of_le q hr.le (by linarith)
  refine ⟨e.symm (halfPt (bdryRadius q)), ?_⟩
  have hint : (𝓡∂ 1).IsInteriorPoint (e.symm (halfPt (bdryRadius q))) := by
    rw [isInteriorPoint_iff_coord_pos (chart_mem_atlas _ p) (e.map_target ht)]
    change 0 < chartCoord e (e.symm (halfPt (bdryRadius q)))
    rw [chartCoord_symm_halfPt e hr.le ht]
    exact hr
  exact (𝓡∂ 1).isInteriorPoint_iff_not_isBoundaryPoint _ |>.mp hint

theorem exists_injective_noncritical_coordinate [ConnectedSpace M]
    (hb : ((𝓡∂ 1).boundary M).Nonempty) :
    ∃ u : M → ℝ, ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ u ∧ Function.Injective u ∧
      ∀ x, mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) u x ≠ 0 := by
  have : Nonempty ((𝓡∂ 1).boundary M) := hb.to_subtype
  have := connectedSpace_double (M := M)
  obtain ⟨D⟩ := nonempty_addCircle_diffeomorph_of_finrank_eq_one (E := ℝ) (M := Double M)
    (by simp)
  obtain ⟨x₁, hx₁⟩ := exists_notMem_boundary_of_mem_boundary hb.some_mem
  let φ : M → AddCircle (1 : ℝ) := fun x => D.symm (doubleIncl x)
  have hφ : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ φ := D.symm.contMDiff.comp contMDiff_doubleIncl
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (D.symm (doubleInclNeg x₁))
  have hφne : ∀ x, φ x ≠ (c : AddCircle (1 : ℝ)) := by
    intro x hx
    have hc' : (c : AddCircle (1 : ℝ)) = D.symm (doubleInclNeg x₁) := hc
    rw [hc'] at hx
    exact doubleInclNeg_notMem_range hx₁ ⟨x, D.symm.injective hx⟩
  let u : M → ℝ := fun x => (AddCircle.equivIco 1 c (φ x) : ℝ)
  have hcomp : (fun t : ℝ => (t : AddCircle (1 : ℝ))) ∘ u = φ := by
    funext x
    exact AddCircle.coe_equivIco
  have hucont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    exact continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco (p := (1 : ℝ)) (a := c) (hφne x)).comp
        hφ.continuous.continuousAt)
  have hu : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ u :=
    AddCircle.isLocalDiffeomorph_coe.contMDiff_of_continuous_of_comp hucont
      (by rw [hcomp]; exact hφ) le_rfl
  refine ⟨u, hu, ?_, ?_⟩
  · intro x y hxy
    have h1 : φ x = φ y := by
      rw [← hcomp]
      exact congrArg (fun t : ℝ => (t : AddCircle (1 : ℝ))) hxy
    exact doubleIncl_injective (D.symm.injective h1)
  · intro x hzero
    have hmk : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (u x) :=
      (AddCircle.isLocalDiffeomorph_coe (u x)).contMDiffAt.mdifferentiableAt (by simp)
    have hchain := mfderiv_comp x hmk ((hu x).mdifferentiableAt (by simp))
    rw [hcomp, hzero, ContinuousLinearMap.comp_zero] at hchain
    have hDsymm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D.symm (doubleIncl x) :=
      D.symm.contMDiff.mdifferentiable (by simp) _
    have hchain2 := mfderiv_comp x hDsymm ((contMDiff_doubleIncl x).mdifferentiableAt (by simp))
    have hne := mfderiv_doubleIncl_ne_zero x
    have h3 : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) φ x = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D.symm (doubleIncl x)).comp
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) doubleIncl x) := hchain2
    have h4 := congrArg (fun L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ =>
      L (EuclideanSpace.single 0 1)) (h3.symm.trans hchain)
    apply hne
    apply (D.symm.mfderivToContinuousLinearEquiv (by simp) (doubleIncl x)).injective
    rw [map_zero]
    exact h4

omit [T2Space M] in
/-- A continuous injective function on a compact connected one-manifold takes the values strictly between
its extreme values only at interior points. -/
theorem boundary_value_eq_or_eq [ConnectedSpace M] {u : M → ℝ} (hu : Continuous u) (hinj : Function.Injective u)
    {a b : ℝ} (ha : a ∈ range u) (hb : b ∈ range u) (hab : ∀ x, u x ∈ Icc a b)
    {p : M} (hp : p ∈ (𝓡∂ 1).boundary M) : u p = a ∨ u p = b := by
  by_contra hcon
  push Not at hcon
  have hap : a < u p := lt_of_le_of_ne (hab p).1 hcon.1.symm
  have hpb : u p < b := lt_of_le_of_ne (hab p).2 hcon.2
  let q : Bdry M := ⟨p, hp⟩
  let e := chartAt (EuclideanHalfSpace 1) p
  let r := bdryRadius q
  have hr : 0 < r := bdryRadius_pos q
  let W : Set M := e.source ∩ chartCoord e ⁻¹' Iio r
  have hW : IsOpen W := (continuousOn_chartCoord e).isOpen_inter_preimage e.open_source isOpen_Iio
  have hpW : p ∈ W := ⟨mem_chart_source _ p, by
    change chartCoord e p < r
    rw [chartCoord_self_of_boundary hp]
    exact hr⟩
  let γ : ℝ → M := fun t => e.symm (halfPt t)
  let S : Set M := γ '' Ioo 0 r
  have hS : IsPreconnected S := by
    apply isPreconnected_Ioo.image
    apply e.continuousOn_symm.comp continuous_halfPt.continuousOn
    intro t ht
    exact halfPt_mem_target_of_le q ht.1.le (by linarith [ht.2])
  have hpS : p ∉ S := by
    rintro ⟨t, ht, htp⟩
    have hte : halfPt t ∈ e.target := halfPt_mem_target_of_le q ht.1.le (by linarith [ht.2])
    have h1 : chartCoord e (γ t) = t := chartCoord_symm_halfPt e ht.1.le hte
    rw [htp, chartCoord_self_of_boundary hp] at h1
    linarith [ht.1]
  have hWS : ∀ x ∈ W, x ≠ p → x ∈ S := by
    intro x hx hxp
    refine ⟨chartCoord e x, ⟨?_, hx.2⟩, ?_⟩
    · rcases (chartCoord_nonneg e x).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hxp
        apply e.injOn hx.1 (mem_chart_source _ p)
        rw [← halfPt_chartCoord e x, ← halfPt_chartCoord e p, ← h,
          chartCoord_self_of_boundary hp]
    · change e.symm (halfPt (chartCoord e x)) = x
      rw [halfPt_chartCoord, e.left_inv hx.1]
  have hemb : Topology.IsEmbedding u :=
    hu.isClosedEmbedding hinj |>.isEmbedding
  obtain ⟨O, hO, hOW⟩ := hemb.isInducing.isOpen_iff.mp hW
  have hpO : u p ∈ O := by
    rw [← mem_preimage, hOW]
    exact hpW
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hO (u p) hpO
  have hrange : Icc a b ⊆ range u := by
    have hconn : IsPreconnected (range u) := isPreconnected_range hu
    exact hconn.Icc_subset ha hb
  let y₁ := max a (u p - δ / 2)
  let y₂ := min b (u p + δ / 2)
  have hy₁ : y₁ < u p := max_lt hap (by linarith)
  have hy₂ : u p < y₂ := lt_min hpb (by linarith)
  obtain ⟨x₁, hx₁⟩ := hrange ⟨le_max_left _ _, hy₁.le.trans hpb.le⟩
  obtain ⟨x₂, hx₂⟩ := hrange ⟨hap.le.trans hy₂.le, min_le_left _ _⟩
  have hmemO : ∀ y, u p - δ / 2 ≤ y → y ≤ u p + δ / 2 → y ∈ O := by
    intro y h1 h2
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hx₁S : x₁ ∈ S := by
    apply hWS x₁
    · rw [← hOW, mem_preimage, hx₁]
      exact hmemO _ (le_max_right _ _) (by linarith)
    · rintro rfl
      exact lt_irrefl _ (hx₁ ▸ hy₁)
  have hx₂S : x₂ ∈ S := by
    apply hWS x₂
    · rw [← hOW, mem_preimage, hx₂]
      exact hmemO _ (by linarith) (min_le_right _ _)
    · rintro rfl
      exact lt_irrefl _ (hx₂ ▸ hy₂)
  have hIcc := (hS.image u hu.continuousOn).Icc_subset ⟨x₁, hx₁S, hx₁⟩ ⟨x₂, hx₂S, hx₂⟩
  obtain ⟨s, hs, hsp⟩ := hIcc ⟨hy₁.le, hy₂.le⟩
  exact hpS (hinj hsp ▸ hs)

theorem exists_coordinate_boundary_values [ConnectedSpace M]
    (hb : ((𝓡∂ 1).boundary M).Nonempty) :
    ∃ (u : M → ℝ) (a b : ℝ), a < b ∧ ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ u ∧ Function.Injective u ∧
      (∀ x, mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      (∀ x, (𝓡∂ 1).IsBoundaryPoint x → u x = a ∨ u x = b) ∧ a ∈ range u ∧ b ∈ range u := by
  obtain ⟨u, hu, hinj, hreg⟩ := exists_injective_noncritical_coordinate hb
  obtain ⟨xa, -, hxa⟩ := isCompact_univ.exists_isMinOn univ_nonempty hu.continuous.continuousOn
  obtain ⟨xb, -, hxb⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hu.continuous.continuousOn
  have hIcc : ∀ x, u x ∈ Icc (u xa) (u xb) := fun x => ⟨hxa (mem_univ x), hxb (mem_univ x)⟩
  obtain ⟨x₁, hx₁⟩ := exists_notMem_boundary_of_mem_boundary hb.some_mem
  have hab : u xa < u xb := by
    refine lt_of_le_of_ne ((hIcc xa).2) fun h => ?_
    have h1 : u hb.some = u x₁ := by
      have h2 := hIcc hb.some
      have h3 := hIcc x₁
      rw [h] at h2 h3
      exact (le_antisymm h2.2 h2.1).trans (le_antisymm h3.2 h3.1).symm
    exact hx₁ (hinj h1 ▸ hb.some_mem)
  refine ⟨u, u xa, u xb, hab, hu, hinj, hreg, fun x hx => ?_, mem_range_self xa,
    mem_range_self xb⟩
  exact boundary_value_eq_or_eq hu.continuous hinj (mem_range_self xa) (mem_range_self xb) hIcc hx

/-- A product with a one-point factor is diffeomorphic to the other factor. -/
def prodSubsingletonDiffeomorph {E' H' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace F'] [ChartedSpace H' F'] (J : ModelWithCorners ℝ E' H')
    {E'' H'' X : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [TopologicalSpace X] [ChartedSpace H'' X] (K : ModelWithCorners ℝ E'' H'')
    (f₀ : F') (hsub : ∀ f : F', f = f₀) : (F' × X) ≃ₘ⟮J.prod K, K⟯ X where
  toFun := Prod.snd
  invFun x := (f₀, x)
  left_inv q := Prod.ext (hsub q.1).symm rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_snd
  contMDiff_invFun := contMDiff_const.prodMk contMDiff_id

/-- **Classification of compact one-manifolds with boundary.** A compact connected smooth
one-manifold with nonempty boundary is diffeomorphic to the closed interval `[0, 1]`. -/
theorem nonempty_diffeomorph_Icc_of_boundary_nonempty [ConnectedSpace M]
    (hb : ((𝓡∂ 1).boundary M).Nonempty) : Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) := by
  obtain ⟨u, a, b, hab, hu, hinj, hreg, hbdy, ha, hb'⟩ := exists_coordinate_boundary_values hb
  have : Fact (a < b) := ⟨hab⟩
  obtain ⟨Θ, -, -⟩ := DifferentialGeometry.Topology.Ehresmann.exists_boundary_interval_trivialization
    (I := 𝓡∂ 1) hab hu hreg hbdy ha hb'
  have hx : Nonempty M := ⟨hb.some⟩
  let f₀ := (Θ.symm (Classical.arbitrary M)).1
  have hsub : ∀ f, f = f₀ := by
    intro f
    have h1 : u f.1.1 = a := f.2
    have h2 : u f₀.1.1 = a := f₀.2
    apply Subtype.ext
    apply Subtype.ext
    exact hinj (h1.trans h2.symm)
  exact ⟨(Θ.symm.trans (prodSubsingletonDiffeomorph _ (𝓡∂ 1) f₀ hsub)).trans
    (DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph a b).symm⟩

/-- A compact connected smooth one-manifold with nonempty boundary has exactly two boundary
points. -/
theorem ncard_boundary_eq_two_of_boundary_nonempty [ConnectedSpace M]
    (hb : ((𝓡∂ 1).boundary M).Nonempty) : ((𝓡∂ 1).boundary M).ncard = 2 := by
  obtain ⟨u, a, b, hab, hu, hinj, hreg, hbdy, ⟨xa, hxa⟩, ⟨xb, hxb⟩⟩ :=
    exists_coordinate_boundary_values hb
  have hbd : (𝓡∂ 1).boundary M = {xa, xb} := by
    rw [DifferentialGeometry.Topology.Manifold.boundary_eq_preimage_endpoints_of_boundary_values
      hab.le hreg hbdy]
    ext x
    simp only [mem_union, mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (hinj (h.trans hxa.symm))
      · exact Or.inr (hinj (h.trans hxb.symm))
    · rintro (rfl | rfl)
      · exact Or.inl hxa
      · exact Or.inr hxb
  rw [hbd, ncard_pair]
  intro h
  rw [h] at hxa
  exact hab.ne (hxa.symm.trans hxb)

end DifferentialGeometry.Topology.Manifold.OneManifold
