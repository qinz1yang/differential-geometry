import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E H F G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def restrictRadius (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ c.radius) :
    SmoothTwoSidedCollar I J e := by
  let incl : symmetricOpenInterval ε → symmetricOpenInterval c.radius :=
    fun t => ⟨t.val, (Ioo_subset_Ioo (neg_le_neg hle) hle) t.property⟩
  let U : TopologicalSpace.Opens (S × symmetricOpenInterval c.radius) :=
    ⟨{q | q.2.val ∈ Ioo (-ε) ε},
      isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_snd)⟩
  let d : Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (S × symmetricOpenInterval ε) U ∞ := {
    toEquiv := {
      toFun := fun q => ⟨(q.1, incl q.2), q.2.property⟩
      invFun := fun q => (q.val.1, ⟨q.val.2.val, q.property⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      apply ContMDiff.prodMk contMDiff_fst
      apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval c.radius) _).mp
      change ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
        (fun q : S × symmetricOpenInterval ε => q.2.val)
      exact contMDiff_subtype_val.comp contMDiff_snd
    contMDiff_invFun := by
      apply ContMDiff.prodMk
      · exact contMDiff_fst.comp contMDiff_subtype_val
      · apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval ε) _).mp
        change ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : U => q.val.2.val)
        exact contMDiff_subtype_val.comp
          (contMDiff_snd.comp contMDiff_subtype_val) }
  have hc : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ c.toFun :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val c.neighborhood)
      c.toDiffeomorph.isLocalDiffeomorph
  have hU : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ (fun q : U => c.toFun q.val) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U
      (hc.isLocalDiffeomorphOn U)
  let f : S × symmetricOpenInterval ε → M := fun q => c.toFun (q.1, incl q.2)
  have hf : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ f := by
    intro q
    exact (d.isLocalDiffeomorph q).comp J M (hU (d q))
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := c.isOpenEmbedding_toFun.injective hpq
    apply Prod.ext
    · exact congrArg (fun z : S × symmetricOpenInterval c.radius => z.1) h
    · apply Subtype.ext
      exact congrArg (fun z : S × symmetricOpenInterval c.radius => z.2.val) h
  exact {
    radius := ε
    radius_pos := hε
    neighborhood := hf.image
    toDiffeomorph := diffeomorphRangeOfInjective hf hinj
    zero_eq := fun s => c.toFun_zero s }

@[simp] theorem restrictRadius_radius (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ c.radius) :
    (c.restrictRadius ε hε hle).radius = ε := rfl

@[simp] theorem restrictRadius_toFun (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ c.radius)
    (q : S × symmetricOpenInterval ε) :
    (c.restrictRadius ε hε hle).toFun q = c.toFun
      (q.1, ⟨q.2.val, (Ioo_subset_Ioo (neg_le_neg hle) hle) q.2.property⟩) := rfl

@[simp] theorem restrictRadius_neighborhood (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ c.radius) :
    ((c.restrictRadius ε hε hle).neighborhood : Set M) =
      range (fun q : S × symmetricOpenInterval ε => c.toFun
        (q.1, ⟨q.2.val, (Ioo_subset_Ioo (neg_le_neg hle) hle) q.2.property⟩)) := rfl

theorem restrictRadius_neighborhood_le (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ c.radius) :
    (c.restrictRadius ε hε hle).neighborhood ≤ c.neighborhood := by
  rintro y ⟨q, rfl⟩
  exact (c.toDiffeomorph
    (q.1, ⟨q.2.val, (Ioo_subset_Ioo (neg_le_neg hle) hle) q.2.property⟩)).property

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
