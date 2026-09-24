import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapCollarSide
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRestriction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem exists_discardedCapCollar
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) :
    ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 => (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall y)),
      ∃ hwidth : c.radius ≤ cuttingCollarWidth (G.delta b.1),
      ∃ capSide : C({q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
          q.2.val ≤ 0}, ThreeBall),
        (∀ q (hq : 0 ≤ q.2.val), c.toFun q = G.discardedCoreCollar b hb
          ((H.event i).transition.trace.capping.attaching b q.1,
            ⟨q.2.val, hq, q.2.property.2.trans_le hwidth⟩)) ∧
        (∀ q (hq : q.2.val ≤ 0), c.toFun q =
          (H.event i).transition.trace.discardedCap b hb (capSide ⟨q, hq⟩)) := by
  classical
  obtain ⟨d, hdwidth, hd⟩ := G.exists_discardedTwoSidedCollar b hb
  let a := (H.event i).transition.trace.capping.attaching b
  let A := a.symm.prodCongr (Homeomorph.refl (Ioo (-d.radius) d.radius))
  let f := d.toFun ∘ A
  have hmatch : ∀ (s : Sphere 2) (t : Ioo (-d.radius) d.radius) (ht : 0 ≤ t.val)
      (htw : t.val < cuttingCollarWidth (G.delta b.1)),
      f (s, t) = G.discardedCoreCollar b hb (s, ⟨t.val, ht, htw⟩) := by
    intro s t ht htw
    have h := hd (a.symm s, t) ht
    change d.toFun (a.symm s, t) = _
    change d.toFun (a.symm s, t) = G.discardedCoreCollar b hb
      (a (a.symm s), ⟨t.val, ht, t.property.2.trans_le hdwidth⟩) at h
    simpa only [a.apply_symm_apply] using h
  obtain ⟨ε, hε, hεr, hside⟩ := G.exists_pos_negative_half_collar_mem_discardedCap b hb
    d.radius_pos (d.isOpenEmbedding_toFun.continuous.comp A.continuous)
    (d.isOpenEmbedding_toFun.injective.comp A.injective) hmatch
  let c := d.restrictRadius ε hε hεr
  have hwidth : c.radius ≤ cuttingCollarWidth (G.delta b.1) := hεr.trans hdwidth
  have hcore : ∀ q (hq : 0 ≤ q.2.val), c.toFun q = G.discardedCoreCollar b hb
      ((H.event i).transition.trace.capping.attaching b q.1,
        ⟨q.2.val, hq, q.2.property.2.trans_le hwidth⟩) := by
    intro q hq
    change d.toFun (q.1, ⟨q.2.val,
      (Ioo_subset_Ioo (neg_le_neg hεr) hεr) q.2.property⟩) = _
    exact hd _ hq
  have hcap : ∀ q : {q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
      q.2.val ≤ 0}, c.toFun q.val ∈ range ((H.event i).transition.trace.discardedCap b hb) := by
    rintro ⟨q, hq⟩
    by_cases ht : q.2.val = 0
    · have hqt : q.2 = ⟨0, neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩ := Subtype.ext ht
      refine ⟨sphereToThreeBall q.1, ?_⟩
      change (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall q.1) = c.toFun q
      rw [show q = (q.1, ⟨0, neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩) from Prod.ext rfl hqt,
        c.toFun_zero]
    · have htn : q.2.val < 0 := lt_of_le_of_ne hq ht
      let t : Ioo (-d.radius) d.radius :=
        ⟨q.2.val, (Ioo_subset_Ioo (neg_le_neg hεr) hεr) q.2.property⟩
      have h := (hside (a q.1) t q.2.property.1 htn).1
      change d.toFun (a.symm (a q.1), t) ∈ _ at h
      have hdmem : d.toFun (q.1, t) ∈
          range ((H.event i).transition.trace.discardedCap b hb) := by
        simpa only [a.symm_apply_apply] using h
      exact hdmem
  let g : {q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
      q.2.val ≤ 0} → ThreeBall := fun q => Classical.choose (hcap q)
  have hg : ∀ q, (H.event i).transition.trace.discardedCap b hb (g q) = c.toFun q.val :=
    fun q => Classical.choose_spec (hcap q)
  have hgcont : Continuous g := by
    apply ((H.event i).transition.trace.discardedCap_isEmbedding b hb).isInducing.continuous_iff.mpr
    exact (c.isOpenEmbedding_toFun.continuous.comp continuous_subtype_val).congr
      fun q => (hg q).symm
  refine ⟨c, hwidth, ⟨g, hgcont⟩, hcore, ?_⟩
  intro q hq
  exact (hg ⟨q, hq⟩).symm

theorem exists_discardedCapCollars :
    ∃ c : ∀ b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b},
      DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 => (H.event i).transition.trace.discardedCap b.1 b.2
          (sphereToThreeBall y)),
      ∃ hwidth : ∀ b, (c b).radius ≤ cuttingCollarWidth (G.delta b.1.1),
      ∃ capSide : ∀ b, C({q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval
          (c b).radius // q.2.val ≤ 0}, ThreeBall),
        (∀ b q (hq : 0 ≤ q.2.val), (c b).toFun q = G.discardedCoreCollar b.1 b.2
          ((H.event i).transition.trace.capping.attaching b.1 q.1,
            ⟨q.2.val, hq, q.2.property.2.trans_le (hwidth b)⟩)) ∧
        (∀ b q (hq : q.2.val ≤ 0), (c b).toFun q =
          (H.event i).transition.trace.discardedCap b.1 b.2 (capSide b ⟨q, hq⟩)) := by
  classical
  choose c hwidth capSide hcore hcap using fun b : {b : (H.event i).transition.trace.tubes.Boundary //
      (H.event i).transition.trace.capDiscarded b} =>
    G.exists_discardedCapCollar b.1 b.2
  exact ⟨c, hwidth, capSide, hcore, hcap⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
