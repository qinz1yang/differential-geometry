import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierSum
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeamOrientation

/-!
One actual positive collar point transports boundary reversal in both directions.
The physical torus matching is unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem reversalTrans_source {C D : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (τ : PartialDiffeomorph C.model D.model C.Carrier D.Carrier ∞)
    (hr : r.source = halfCollarSource) (ht : r.target ⊆ τ.source) :
    (r.trans τ).source = halfCollarSource := by
  ext p
  change (p ∈ r.source ∧ r p ∈ τ.source) ↔ p ∈ halfCollarSource
  rw [hr]
  exact ⟨And.left, fun hp => ⟨hp, ht (r.map_source' (hr.symm ▸ hp))⟩⟩

private theorem reversalPullback_trans {C D : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (τ : PartialDiffeomorph C.model D.model C.Carrier D.Carrier ∞)
    (hr : r.source = halfCollarSource) (ht : r.target ⊆ τ.source)
    (p0 : surgeryHalfDomain)
    (hpos : ∃ A : TangentSpace C.model (r p0.val) ≃ₗ[ℝ]
        TangentSpace D.model (τ (r p0.val)),
      (∀ v, A v = mfderiv C.model D.model τ (r p0.val) v) ∧
        Orientation.map (Fin 3) A (C.orientation.orientation (r p0.val)) =
          D.orientation.orientation (τ (r p0.val))) :
    ∀ p (hp : p ∈ halfCollarSource),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ hp)).symm
        (C.orientation.orientation (r p)) =
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (r.trans τ)
        ((reversalTrans_source r τ hr ht).symm ▸ hp)).symm
        (D.orientation.orientation ((r.trans τ) p)) := by
  have hs := reversalTrans_source r τ hr ht
  obtain ⟨O, hO⟩ := exists_surgeryHalfCollarOrientation r hr
  obtain ⟨O', hO'⟩ := exists_surgeryHalfCollarOrientation (r.trans τ) hs
  obtain ⟨A, hA, hAo⟩ := hpos
  let L : TangentSpace halfCollarModel p0.val ≃ₗ[ℝ] TangentSpace C.model (r p0.val) :=
    carrierSurgeryPatchTangentEquiv r
      (hr.symm ▸ (show p0.val ∈ halfCollarSource from p0.property))
  let R : TangentSpace halfCollarModel p0.val ≃ₗ[ℝ]
      TangentSpace D.model ((r.trans τ) p0.val) :=
    carrierSurgeryPatchTangentEquiv (r.trans τ)
      (hs.symm ▸ (show p0.val ∈ halfCollarSource from p0.property))
  have hder : R = L.trans A := by
    apply LinearEquiv.ext
    intro v
    change mfderiv halfCollarModel D.model (τ ∘ r) p0.val v = A (L v)
    have hp : p0.val ∈ r.source := hr.symm ▸
      (show p0.val ∈ halfCollarSource from p0.property)
    have hd := mfderiv_comp_apply p0.val
      (τ.mdifferentiableAt (by simp) (ht (r.map_source' hp)))
      (r.mdifferentiableAt (by simp) hp) v
    exact hd.trans (hA (L v)).symm
  have hpoint : O.orientation p0 = O'.orientation p0 := by
    apply (Orientation.map (Fin 3) R).injective
    have hL0 := hO p0
    have hR0 := hO' p0
    change Orientation.map (Fin 3) L (O.orientation p0) = _ at hL0
    change Orientation.map (Fin 3) R (O'.orientation p0) = _ at hR0
    have hmap := DifferentialGeometry.orientation_map_trans L A (O.orientation p0)
    have he : Orientation.map (Fin 3) R (O.orientation p0) =
        Orientation.map (Fin 3) A (Orientation.map (Fin 3) L (O.orientation p0)) := by
      exact (congrArg (fun B : TangentSpace halfCollarModel p0.val ≃ₗ[ℝ]
        TangentSpace D.model (τ (r p0.val)) =>
          Orientation.map (Fin 3) B (O.orientation p0)) hder).trans hmap
    exact he.trans ((congrArg (Orientation.map (Fin 3) A) hL0).trans (hAo.trans hR0.symm))
  have hsame : O = O' := O.eq_of_eq_at O' p0 hpoint
  intro p hp
  let q : surgeryHalfDomain := ⟨p, hp⟩
  have hL := hO q
  have hR := hO' q
  rw [← hL, ← hR, hsame]
  exact (Orientation.map (Fin 3)
    (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ hp))).symm_apply_apply
    (O'.orientation q) |>.trans
      ((Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (r.trans τ)
        (hs.symm ▸ hp))).symm_apply_apply (O'.orientation q)).symm

private def reversalMatched {C : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans r

private theorem reversalMatched_source {C : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞) (hr : r.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (reversalMatched r f).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (f p.1, p.2) ∈ r.source) ↔ p ∈ halfCollarSource
  rw [hr]
  simp only [mem_univ, true_and]
  rfl

private def reversalPoint (t : Torus) : surgeryHalfDomain :=
  ⟨(t, halfPoint (1 / 2) (by norm_num)), by change (1 / 2 : ℝ) < 1; norm_num⟩

private theorem reversal_iff {C : CompactCarrier.{u}}
    {l r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞}
    {hl : l.source = halfCollarSource} {hr : r.source = halfCollarSource} :
    ReversesBoundaryOrientation C l r ↔ ∀ t : Torus,
      Orientation.map (Fin 3)
        (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t)).symm
        (C.orientation.orientation (l (t, halfZero))) =
      -Orientation.map (Fin 3)
        (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t)).symm
        (C.orientation.orientation (r (t, halfZero))) := by
  constructor
  · intro h t
    obtain ⟨L, R, hL, hR, hO⟩ := h t
    have heL : L = carrierSurgeryPatchTangentEquiv l
        (hl.symm ▸ zero_mem_halfCollarSource t) := LinearEquiv.ext hL
    have heR : R = carrierSurgeryPatchTangentEquiv r
        (hr.symm ▸ zero_mem_halfCollarSource t) := LinearEquiv.ext hR
    rw [heL, heR] at hO
    exact hO
  · intro h t
    exact ⟨carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t),
      carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t),
      fun v => rfl, fun v => rfl, h t⟩

theorem boundaryCollarReversalTransport
    {C1 C2 D : CompactCarrier.{u}}
    {hC1 : C1.kind = .withBoundary} {hC2 : C2.kind = .withBoundary}
    {hD : D.kind = .withBoundary}
    [Nonempty C1.Carrier] [Nonempty C2.Carrier] [Nonempty D.Carrier]
    {l : PartialDiffeomorph halfCollarModel C1.model
      (Torus × EuclideanHalfSpace 1) C1.Carrier ∞}
    {r : PartialDiffeomorph halfCollarModel C2.model
      (Torus × EuclideanHalfSpace 1) C2.Carrier ∞}
    {hl : l.source = halfCollarSource} {hr : r.source = halfCollarSource}
    {τ : PartialDiffeomorph C2.model D.model C2.Carrier D.Carrier ∞}
    {ht : r.target ⊆ τ.source}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    {hpos : ∃ A : TangentSpace C2.model
        (r (torusBase, halfPoint (1 / 2) (by norm_num))) ≃ₗ[ℝ]
        TangentSpace D.model (τ (r (torusBase, halfPoint (1 / 2) (by norm_num)))),
      (∀ v, A v = mfderiv C2.model D.model τ
        (r (torusBase, halfPoint (1 / 2) (by norm_num))) v) ∧
        Orientation.map (Fin 3) A
          (C2.orientation.orientation (r (torusBase, halfPoint (1 / 2) (by norm_num)))) =
        D.orientation.orientation (τ (r (torusBase, halfPoint (1 / 2) (by norm_num))))} :
    ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2)
      (l.trans (withBoundarySumLeft C1 C2 hC1 hC2))
      (fun p => (r.trans (withBoundarySumRight C1 C2 hC1 hC2)) (f p.1, p.2)) ↔
    ReversesBoundaryOrientation (withBoundarySum C1 D hC1 hD)
      (l.trans (withBoundarySumLeft C1 D hC1 hD))
      (fun p => ((r.trans τ).trans (withBoundarySumRight C1 D hC1 hD)) (f p.1, p.2)) := by
  let L0 := l.trans (withBoundarySumLeft C1 C2 hC1 hC2)
  let L1 := l.trans (withBoundarySumLeft C1 D hC1 hD)
  let R := reversalMatched r f
  let R0 := R.trans (withBoundarySumRight C1 C2 hC1 hC2)
  let R1 := (R.trans τ).trans (withBoundarySumRight C1 D hC1 hD)
  have hR := reversalMatched_source r hr f
  have hL0 := reversalTrans_source l (withBoundarySumLeft C1 C2 hC1 hC2) hl
    (by rw [withBoundarySumLeft_source]; exact subset_univ _)
  have hL1 := reversalTrans_source l (withBoundarySumLeft C1 D hC1 hD) hl
    (by rw [withBoundarySumLeft_source]; exact subset_univ _)
  have hRt : R.target ⊆ τ.source := by
    intro x hx
    obtain ⟨p, hp, he⟩ := (reversalMatched r f).image_source_eq_target.symm ▸ hx
    rw [← he]
    exact ht (r.map_source' (by
      change (f p.1, p.2) ∈ r.source
      exact hp.2))
  have hRT := reversalTrans_source R τ hR hRt
  have hR0 := reversalTrans_source R (withBoundarySumRight C1 C2 hC1 hC2) hR
    (by rw [withBoundarySumRight_source]; exact subset_univ _)
  have hR1 := reversalTrans_source (R.trans τ) (withBoundarySumRight C1 D hC1 hD) hRT
    (by rw [withBoundarySumRight_source]; exact subset_univ _)
  have hposR : ∃ A : TangentSpace C2.model (R (reversalPoint (f.symm torusBase)).val) ≃ₗ[ℝ]
        TangentSpace D.model (τ (R (reversalPoint (f.symm torusBase)).val)),
      (∀ v, A v = mfderiv C2.model D.model τ
        (R (reversalPoint (f.symm torusBase)).val) v) ∧
        Orientation.map (Fin 3) A
          (C2.orientation.orientation (R (reversalPoint (f.symm torusBase)).val)) =
        D.orientation.orientation (τ (R (reversalPoint (f.symm torusBase)).val)) := by
    change ∃ A : TangentSpace C2.model
        (r (f (f.symm torusBase), halfPoint (1 / 2) (by norm_num))) ≃ₗ[ℝ]
        TangentSpace D.model (τ (r (f (f.symm torusBase),
          halfPoint (1 / 2) (by norm_num)))),
      (∀ v, A v = mfderiv C2.model D.model τ
        (r (f (f.symm torusBase), halfPoint (1 / 2) (by norm_num))) v) ∧
        Orientation.map (Fin 3) A (C2.orientation.orientation
          (r (f (f.symm torusBase), halfPoint (1 / 2) (by norm_num)))) =
        D.orientation.orientation (τ (r (f (f.symm torusBase),
          halfPoint (1 / 2) (by norm_num))))
    rw [f.apply_symm_apply]
    exact hpos
  change ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2) L0 R0 ↔
    ReversesBoundaryOrientation (withBoundarySum C1 D hC1 hD) L1 R1
  rw [reversal_iff (hl := hL0) (hr := hR0), reversal_iff (hl := hL1) (hr := hR1)]
  have heL : ∀ p (hp : p ∈ halfCollarSource),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv L0 (hL0.symm ▸ hp)).symm
        ((withBoundarySum C1 C2 hC1 hC2).orientation.orientation (L0 p)) =
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv L1 (hL1.symm ▸ hp)).symm
        ((withBoundarySum C1 D hC1 hD).orientation.orientation (L1 p)) := by
    intro p hp
    exact (reversalPullback_trans l (withBoundarySumLeft C1 C2 hC1 hC2) hl
      (by rw [withBoundarySumLeft_source]; exact subset_univ _) (reversalPoint torusBase)
      (withBoundarySumLeft_positive C1 C2 hC1 hC2 _) p hp).symm.trans
      (reversalPullback_trans l (withBoundarySumLeft C1 D hC1 hD) hl
        (by rw [withBoundarySumLeft_source]; exact subset_univ _) (reversalPoint torusBase)
        (withBoundarySumLeft_positive C1 D hC1 hD _) p hp)
  have heR : ∀ p (hp : p ∈ halfCollarSource),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv R0 (hR0.symm ▸ hp)).symm
        ((withBoundarySum C1 C2 hC1 hC2).orientation.orientation (R0 p)) =
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv R1 (hR1.symm ▸ hp)).symm
        ((withBoundarySum C1 D hC1 hD).orientation.orientation (R1 p)) := by
    intro p hp
    exact (reversalPullback_trans R (withBoundarySumRight C1 C2 hC1 hC2) hR
      (by rw [withBoundarySumRight_source]; exact subset_univ _) (reversalPoint torusBase)
      (withBoundarySumRight_positive C1 C2 hC1 hC2 _) p hp).symm.trans
      ((reversalPullback_trans R τ hR hRt (reversalPoint (f.symm torusBase)) hposR p hp).trans
        (reversalPullback_trans (R.trans τ) (withBoundarySumRight C1 D hC1 hD) hRT
          (by rw [withBoundarySumRight_source]; exact subset_univ _) (reversalPoint torusBase)
          (withBoundarySumRight_positive C1 D hC1 hD _) p hp))
  exact forall_congr' fun t => by rw [heL (t, halfZero) (zero_mem_halfCollarSource t),
    heR (t, halfZero) (zero_mem_halfCollarSource t)]

end GC.GraphManifold
