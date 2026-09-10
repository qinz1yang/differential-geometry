import DifferentialGeometry.Topology.Manifold.BoundaryCollar.HalfSpaceFlowBox
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalCoordinates
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.CurveUniqueness
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SmoothInverse

open Set Function Topology Filter Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_smooth_boundary_flow_rightInverse
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p)
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) {ε : ℝ} (hε : 0 < ε)
    {F : M × ℝ → M}
    (hzero : ∀ q ∈ U, F (q, 0) = q)
    (hcurve : ∀ q ∈ U, IsMIntegralCurveOn (fun t => F (q, t)) V (Icc (0 : ℝ) ε))
    (hi : ∀ q ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (q, t))) :
    ∃ O : TopologicalSpace.Opens M, p ∈ O ∧ ∃ R : M → M × ℝ,
      ContMDiffOn (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) ∞ R O ∧
      ∀ y ∈ O, (R y).1 ∈ U ∧ (𝓡∂ (n + 1)).IsBoundaryPoint (R y).1 ∧
        (R y).2 ∈ Ico (0 : ℝ) ε ∧ F (R y) = y := by
  let I := 𝓡∂ (n + 1)
  let c := extChartAt I p
  let A := normalSplit n
  let C : M → ℝ × EuclideanSpace ℝ (Fin n) := fun y => A (c y)
  let z := (C p).2
  have hCp : C p = (0, z) := normalSplit_extChartAt_boundary hp
  obtain ⟨N, hN, h0N, hf, htarget, hnormal⟩ := exists_normalChartField_neighborhood hp hV hpos
  obtain ⟨Φ, hΦ, hΦzero, _, _, e, he, heq, _, hhalf, _, hpath⟩ :=
    exists_inward_halfSpace_flowBox hN h0N hf hnormal
  have hezero : e (0, z) = (0, z) := by rw [heq]; exact hΦzero (0, z)
  have hztarget : (0, z) ∈ e.target := by
    have hh := e.toPartialEquiv.map_source he
    rwa [hezero] at hh
  have hinvzero : e.symm (0, z) = (0, z) := by
    have hh : e.symm (e (0, z)) = (0, z) := e.toPartialEquiv.left_inv he
    rwa [hezero] at hh
  let D : M → ℝ × EuclideanSpace ℝ (Fin n) := fun y => e.symm (C y)
  have hDp : D p = (0, z) := by change e.symm (C p) = _; rw [hCp, hinvzero]
  have hC : ContinuousAt C p := A.continuous.continuousAt.comp (continuousAt_extChartAt p)
  have hD : ContinuousAt D p := by
    apply (e.symm.toOpenPartialHomeomorph.continuousAt ?_).comp hC
    rwa [hCp]
  let Q : EuclideanSpace ℝ (Fin n) → M := fun w => c.symm (A.symm (0, w))
  have hbase : A.symm (0, z) = c p := by rw [← hCp]; exact A.symm_apply_apply _
  have hQz : Q z = p := by
    change c.symm (A.symm (0, z)) = p
    rw [hbase]
    exact c.left_inv (mem_extChartAt_source p)
  have hQ : ContinuousAt Q z := by
    have hc : ContinuousAt c.symm (A.symm (0, z)) := by
      rw [hbase]
      exact continuousAt_extChartAt_symm p
    exact hc.comp (f := fun w : EuclideanSpace ℝ (Fin n) => A.symm (0, w)) (by fun_prop)
  have hQDp : Q (D p).2 = p := by rw [hDp]; exact hQz
  have hQD : ContinuousAt (fun y => Q (D y).2) p := by
    have hQ' : ContinuousAt Q (D p).2 := by simpa only [hDp] using hQ
    exact hQ'.comp (f := fun y : M => (D y).2) hD.snd
  have hUevent : ∀ᶠ y in 𝓝 p, Q (D y).2 ∈ U := by
    apply hQD.preimage_mem_nhds
    rw [hQDp]
    exact hU.mem_nhds hpU
  have htimeevent : ∀ᶠ y in 𝓝 p, (D y).1 < ε := by
    change (fun y => (D y).1) ⁻¹' Iio ε ∈ 𝓝 p
    apply hD.fst.preimage_mem_nhds
    rw [hDp]
    exact isOpen_Iio.mem_nhds hε
  have htargetevent : ∀ᶠ y in 𝓝 p, C y ∈ e.target := by
    apply hC.preimage_mem_nhds
    rw [hCp]
    exact e.open_target.mem_nhds hztarget
  have hgood : {y | y ∈ c.source ∧ Q (D y).2 ∈ U ∧ (D y).1 < ε ∧ C y ∈ e.target} ∈ 𝓝 p := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) p,
      hUevent, htimeevent, htargetevent] with y hyc hyU hyt hyT
    exact ⟨hyc, hyU, hyt, hyT⟩
  obtain ⟨O, hOg, hO, hpO⟩ := mem_nhds_iff.mp hgood
  have hDsource (y : M) (hy : y ∈ O) : D y ∈ e.source :=
    e.toPartialEquiv.map_target (hOg hy).2.2.2
  have hDcoord (y : M) (hy : y ∈ O) : e (D y) = C y :=
    e.toPartialEquiv.right_inv (hOg hy).2.2.2
  have hDnonneg (y : M) (hy : y ∈ O) : 0 ≤ (D y).1 := by
    apply (hhalf (D y) (hDsource y hy)).mp
    rw [hDcoord y hy]
    exact chartHeight_nonneg (n := n + 1) p y
  have hstart (y : M) (hy : y ∈ O) : A.symm (0, (D y).2) ∈ c.target := by
    have hh := hpath (D y) (hDsource y hy) 0 ⟨le_rfl, hDnonneg y hy⟩
    rw [hΦzero] at hh
    exact htarget _ ⟨⟨hh.2.1, mem_univ _⟩, hh.1⟩
  have hCon : ContMDiffOn I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞ C O :=
    A.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_extChartAt (I := I) (x := p) (n := ∞)).mono
        (fun y hy => by simpa only [c, extChartAt_source] using (hOg hy).1))
  have heforward : ContDiffOn ℝ ∞ e e.source := by
    rw [heq]
    exact (hΦ.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)).contDiffOn
  have hDon : ContMDiffOn I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞ D O :=
    (Poincare.Manifold.PartialDiffeomorph.contDiffOn_symm_of_partialDiffeomorph e heforward).contMDiffOn.comp hCon
      (fun y hy => (hOg hy).2.2.2)
  have hDon' : ContMDiffOn I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ D O := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hDon
  have hDsnd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun y => (D y).2) O :=
    fun y hy => (hDon' y hy).snd
  have hDfst : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => (D y).1) O :=
    fun y hy => (hDon' y hy).fst
  have hsplit := (contMDiffOn_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ)) (s := O)).prodMk hDsnd
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hsplit
  have hQon : ContMDiffOn I I ∞ (fun y => Q (D y).2) O :=
    (contMDiffOn_extChartAt_symm p).comp
      (A.symm.contDiff.contMDiff.comp_contMDiffOn hsplit) hstart
  let R : M → M × ℝ := fun y => (Q (D y).2, (D y).1)
  refine ⟨⟨O, hO⟩, hpO, R, hQon.prodMk hDfst, ?_⟩
  intro y hy
  obtain ⟨hyc, hyU, hyt, hyT⟩ := hOg hy
  have hyD := hDsource y hy
  have heDy := hDcoord y hy
  have ht := hDnonneg y hy
  let t := (D y).1
  let w := (D y).2
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have htraj : ∀ s ∈ Icc (0 : ℝ) t,
      A.symm (Φ ((0, w), s)) ∈ c.target := by
    intro s hs
    have hh := hpath (D y) hyD s hs
    exact htarget _ ⟨⟨hh.2.1, mem_univ _⟩, hh.1⟩
  have hstarttarget : A.symm (0, w) ∈ c.target := by
    simpa only [hΦzero] using htraj 0 h0t
  have hQsource : Q w ∈ c.source := c.map_target hstarttarget
  have hQcoord : c (Q w) = A.symm (0, w) := c.right_inv hstarttarget
  have hQboundary : I.IsBoundaryPoint (Q w) := by
    apply (chartHeight_eq_zero_iff p (by simpa only [c, extChartAt_source] using hQsource)).mp
    change c (Q w) 0 = 0
    rw [hQcoord]
    rfl
  let γ : ℝ → M := fun s => c.symm (A.symm (Φ ((0, w), s)))
  have hγ : IsMIntegralCurveOn γ V (Icc (0 : ℝ) t) := by
    apply isMIntegralCurveOn_of_chartField I p V htraj
    intro s hs
    have hd := A.symm.hasFDerivAt.comp_hasDerivAt s (hpath (D y) hyD s hs).2.2
    have hefield : A.symm (normalChartField p V (Φ ((0, w), s))) =
        chartField I p V (A.symm (Φ ((0, w), s))) := A.symm_apply_apply _
    change HasDerivAt (fun r => A.symm (Φ ((0, w), r)))
      (A.symm (normalChartField p V (Φ ((0, w), s)))) s at hd
    rw [hefield] at hd
    exact hd.hasDerivWithinAt
  have hγzero : γ 0 = Q w := by change c.symm (A.symm (Φ ((0, w), 0))) = _; rw [hΦzero]
  have hγt : γ t = y := by
    change c.symm (A.symm (Φ ((0, w), t))) = y
    have hh : Φ ((0, w), t) = C y := by
      have hh := heDy
      rw [heq] at hh
      exact hh
    rw [hh, A.symm_apply_apply]
    exact c.left_inv hyc
  refine ⟨hyU, hQboundary, ⟨ht, hyt⟩, ?_⟩
  change F (Q w, t) = y
  by_cases ht0 : t = 0
  · rw [ht0, hzero _ hyU]
    exact hγzero.symm.trans (ht0 ▸ hγt)
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have heflow := isMIntegralCurveOn_Icc_unique_of_interior hV htp
      ((hcurve (Q w) hyU).mono (Icc_subset_Icc le_rfl hyt.le)) hγ
      (fun s hs => hi (Q w) hyU s ⟨hs.1, hs.2.le.trans hyt.le⟩)
      ((hzero _ hyU).trans hγzero.symm)
    exact (heflow ⟨ht, le_rfl⟩).trans hγt

end Poincare.Manifold.BoundaryCollar
