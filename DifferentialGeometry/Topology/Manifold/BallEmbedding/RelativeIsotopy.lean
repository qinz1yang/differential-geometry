import DifferentialGeometry.Topology.Manifold.SupportedPointMotion
import DifferentialGeometry.Topology.Manifold.OrientedBallChartTransitionDet
import DifferentialGeometry.Topology.Manifold.ManifoldIsotopyExtension

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
  [IsManifold ThreeModel ∞ U] [T2Space U] [PreconnectedSpace U]

theorem OrientedBallEmbedding.exists_isotopy_eqOn_closedBall_of_isPreconnected_compl
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o)
    (C : Set U) (hC : IsCompact C) (hcomp : IsPreconnected (Cᶜ : Set U))
    (hb : Disjoint (b.chart '' closedBall (0 : ThreeSpace) 1) C)
    (hb' : Disjoint (b'.chart '' closedBall (0 : ThreeSpace) 1) C) :
    ∃ (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
      IsCompact K ∧ Disjoint K C ∧ J 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (J q.1).symm q.2) ∧
      (∀ t, EqOn (J t) (id : U → U) Kᶜ) ∧
      (∀ t, EqOn (J t).symm (id : U → U) Kᶜ) ∧
      ∀ z ∈ closedBall (0 : ThreeSpace) 1, J 1 (b.chart z) = b'.chart z := by
  have h01 : (0 : ThreeSpace) ∈ closedBall (0 : ThreeSpace) 1 := mem_closedBall_self (by norm_num)
  have h02 : (0 : ThreeSpace) ∈ closedBall (0 : ThreeSpace) 2 := mem_closedBall_self (by norm_num)
  have hb0 : b.chart 0 ∈ Cᶜ := disjoint_left.mp hb ⟨0, h01, rfl⟩
  have hb'0 : b'.chart 0 ∈ Cᶜ := disjoint_left.mp hb' ⟨0, h01, rfl⟩
  obtain ⟨F, hF0, hF1, hF, hFi, KF, hKFc, hKFU, hFfix⟩ :=
    DifferentialGeometry.Topology.exists_supported_isotopy_apply_eq_of_isPreconnected
      (E := ThreeSpace) Cᶜ hC.isClosed.isOpen_compl hcomp
      (b.chart 0) (b'.chart 0) hb0 hb'0
  have hFo : (F 1).preservesOrientation o o :=
    preservesOrientation_of_jointlySmooth_isotopy o F hF0 hF 1
  let bF : OrientedBallEmbedding U o := b.comp (F 1) hFo
  have hbF_apply (z : ThreeSpace) : bF.chart z = F 1 (b.chart z) := rfl
  have hbF0 : bF.chart 0 = b'.chart 0 := hF1
  have hbFC : Disjoint (bF.chart '' closedBall (0 : ThreeSpace) 1) C := by
    rw [disjoint_left]
    rintro z ⟨v, hv, rfl⟩ hzC
    have hzK : bF.chart v ∉ KF := fun h => (hKFU h) hzC
    have he := (hFfix 1 (bF.chart v) hzK).2
    change (F 1).symm (F 1 (b.chart v)) = F 1 (b.chart v) at he
    rw [Diffeomorph.symm_apply_apply] at he
    have hbC : F 1 (b.chart v) ∈ C := hzC
    exact disjoint_left.mp hb ⟨v, hv, rfl⟩ (he.symm ▸ hbC)
  have hb'0s : (0 : ThreeSpace) ∈ b'.chart.source := b'.closedBall_subset_source h02
  have hcenter : bF.chart 0 ∈ b'.chart.target := by
    rw [hbF0]
    exact b'.chart.map_source hb'0s
  have hdet : 0 < (fderiv ℝ (fun z : ThreeSpace => b'.chart.symm (bF.chart z)) 0).det :=
    bF.transition_fderiv_det_pos b' hcenter
  have htube : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (b'.chart.symm (bF.chart 0)) + t • (0 : ThreeSpace)
        ∈ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ := by
    intro t _
    have hcenter_inv : b'.chart.symm (bF.chart 0) = 0 := by
      rw [hbF0]
      exact PartialDiffeomorph.symm_apply_apply b'.chart hb'0s
    rw [hcenter_inv, smul_zero, smul_zero, zero_add]
    exact ⟨hb'0s, hb'0⟩
  obtain ⟨G, KG, hKGc, hKGC, hG0, hG, hGi, hGfix, hGifix, hGmatch⟩ :=
    orientedBallChartIsotopicAwayFromCompact_of_centerComparison_and_tube
      o bF b' C hC hbFC hb' hcenter hdet htube
  have hKFC : Disjoint KF C := disjoint_left.mpr fun _ hz hzC => (hKFU hz) hzC
  have hKunion : Disjoint (KF ∪ KG) C := by
    rw [disjoint_left]
    rintro z (hzF | hzG) hzC
    · exact disjoint_left.mp hKFC hzF hzC
    · exact disjoint_left.mp hKGC hzG hzC
  refine ⟨fun t => (F t).trans (G t), KF ∪ KG, hKFc.union hKGc,
    hKunion, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro z
    change G 0 (F 0 z) = z
    simp only [hF0, hG0, Diffeomorph.coe_refl, id_eq]
  · change ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => G q.1 (F q.1 q.2))
    exact hG.comp (contMDiff_fst.prodMk hF)
  · change ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (F q.1).symm ((G q.1).symm q.2))
    exact hFi.comp (contMDiff_fst.prodMk hGi)
  · intro t z hz
    have hzF : z ∉ KF := fun h => hz (Or.inl h)
    have hzG : z ∉ KG := fun h => hz (Or.inr h)
    change G t (F t z) = z
    have hGz : G t z = z := hGfix t hzG
    rw [(hFfix t z hzF).1, hGz]
  · intro t z hz
    have hzF : z ∉ KF := fun h => hz (Or.inl h)
    have hzG : z ∉ KG := fun h => hz (Or.inr h)
    change (F t).symm ((G t).symm z) = z
    have hGiz : (G t).symm z = z := hGifix t hzG
    rw [hGiz, (hFfix t z hzF).2]
  · intro z hz
    change G 1 (F 1 (b.chart z)) = b'.chart z
    rw [← hbF_apply]
    exact hGmatch z hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
