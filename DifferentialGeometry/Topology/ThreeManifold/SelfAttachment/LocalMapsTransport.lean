import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Transport
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace E3 N] [T2Space N]
  (c d : BallChart 3 (𝓡 3) M) (c' d' : BallChart 3 (𝓡 3) N)
  (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x)

omit [T2Space M] [T2Space N] in
private theorem chart_image_closedBall_one_eq
    (e : BallChart 3 (𝓡 3) M) (e' : BallChart 3 (𝓡 3) N)
    (he : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (e.chart x) = e'.chart x) :
    F '' (e.chart '' Metric.closedBall 0 1) = e'.chart '' Metric.closedBall 0 1 := by
  rw [Set.image_image]
  exact Set.image_congr (fun x hx => he x
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx))

include hc hd in
private theorem mem_coreInterior_iff : ∀ x : M,
    x ∈ coreInterior c d ↔ F x ∈ coreInterior c' d' := by
  intro x
  have himg : F '' (c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) =
      c'.chart '' Metric.closedBall 0 1 ∪ d'.chart '' Metric.closedBall 0 1 := by
    rw [Set.image_union, chart_image_closedBall_one_eq F c c' hc,
      chart_image_closedBall_one_eq F d d' hd]
  change x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1 ↔
    F x ∉ c'.chart '' Metric.closedBall 0 1 ∪ d'.chart '' Metric.closedBall 0 1
  rw [← himg]
  apply not_congr
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact F.injective he ▸ hy

def coreInteriorDiffeomorphOfChartTransport :
    Diffeomorph (𝓡 3) (𝓡 3) (coreInterior c d) (coreInterior c' d') ∞ where
  toEquiv := (F.toHomeomorph.subtype (mem_coreInterior_iff c d c' d' F hc hd)).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (coreInterior c' d') _).mp
    exact F.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (coreInterior c d) _).mp
    exact F.symm.contMDiff.comp contMDiff_subtype_val

@[simp] theorem coreInteriorDiffeomorphOfChartTransport_apply_val (x : coreInterior c d) :
    (coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd x).val = F x.val := rfl

@[simp] theorem coreInteriorDiffeomorphOfChartTransport_symm_apply_val (x : coreInterior c' d') :
    ((coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd).symm x).val =
      F.symm x.val := rfl

variable
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

theorem homeomorphOfChartTransport_coreInterior
    (x : coreInterior c d) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F.toHomeomorph hc hd a
        (coreInteriorInclusion c d hcd a x) =
      coreInteriorInclusion c' d' hcd' a
        (coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd x) := rfl

omit [T2Space M] [T2Space N] in
theorem homeomorphOfChartTransport_bandInterior
    (x : bandInterior) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F.toHomeomorph hc hd a
        (bandInteriorInclusion c d hcd a x) =
      bandInteriorInclusion c' d' hcd' a x := rfl

variable [ChartedSpace E3 (Quotient c' d' hcd' a)]
  [IsManifold (𝓡 3) ∞ (Quotient c' d' hcd' a)]

theorem local_maps_of_chart_transport
    (hcore : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreInteriorInclusion c' d' hcd' a))
    (hband : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (bandInteriorInclusion c' d' hcd' a))
    (hlower : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (lowerCollar c' d' hcd' a) (collarZero z))
    (hupper : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (upperCollar c' d' hcd' a) (collarZero z)) :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3)
      (homeomorphOfChartTransport c d c' d' hcd hcd' F.toHomeomorph hc hd a)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreInteriorInclusion c d hcd a) ∧
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (bandInteriorInclusion c d hcd a) ∧
      (∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (lowerCollar c d hcd a) (collarZero z)) ∧
      ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (upperCollar c d hcd a) (collarZero z) := by
  let Hq := homeomorphOfChartTransport c d c' d' hcd hcd' F.toHomeomorph hc hd a
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) Hq
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := 𝓡 3) (n := ∞) Hq
  let C := coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd
  have heCore : coreInteriorInclusion c d hcd a =
      G.symm ∘ (coreInteriorInclusion c' d' hcd' a) ∘ C := by
    funext x
    apply G.injective
    change Hq (coreInteriorInclusion c d hcd a x) =
      Hq (Hq.symm (coreInteriorInclusion c' d' hcd' a (C x)))
    rw [Hq.apply_symm_apply]
    exact homeomorphOfChartTransport_coreInterior c d c' d' F hc hd hcd hcd' a x
  have heBand : bandInteriorInclusion c d hcd a =
      G.symm ∘ bandInteriorInclusion c' d' hcd' a := by
    funext x
    apply G.injective
    change Hq (bandInteriorInclusion c d hcd a x) =
      Hq (Hq.symm (bandInteriorInclusion c' d' hcd' a x))
    rw [Hq.apply_symm_apply]
    exact homeomorphOfChartTransport_bandInterior c d c' d' F hc hd hcd hcd' a x
  have heLower : lowerCollar c d hcd a = G.symm ∘ lowerCollar c' d' hcd' a := by
    funext x
    apply G.injective
    change Hq (lowerCollar c d hcd a x) = Hq (Hq.symm (lowerCollar c' d' hcd' a x))
    rw [Hq.apply_symm_apply]
    exact homeomorphOfChartTransport_lowerCollar c d c' d' hcd hcd'
      F.toHomeomorph hc hd a x
  have heUpper : upperCollar c d hcd a = G.symm ∘ upperCollar c' d' hcd' a := by
    funext x
    apply G.injective
    change Hq (upperCollar c d hcd a x) = Hq (Hq.symm (upperCollar c' d' hcd' a x))
    rw [Hq.apply_symm_apply]
    exact homeomorphOfChartTransport_upperCollar c d c' d' hcd hcd'
      F.toHomeomorph hc hd a x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heCore]
    exact DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph
      (DifferentialGeometry.isLocalDiffeomorph_comp hcore C.isLocalDiffeomorph)
  · rw [heBand]
    exact DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph hband
  · intro z
    rw [heLower]
    exact (hlower z).comp (𝓡 3) _ (G.symm.isLocalDiffeomorph _)
  · intro z
    rw [heUpper]
    exact (hupper z).comp (𝓡 3) _ (G.symm.isLocalDiffeomorph _)

end DifferentialGeometry.Topology.SelfAttachment
