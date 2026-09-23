import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalDiffeomorphism
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

universe u v

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

def connectingCylinder (q : S2 × unitInterval) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  collarMap c.toBallChart d.toBallChart a.val
    (q.1, ⟨(1 - 2 * q.2.val) / 4, by
      constructor <;> linarith [q.2.property.1, q.2.property.2]⟩)

theorem continuous_connectingCylinder : Continuous (connectingCylinder c d a) := by
  apply (continuous_collarMap c.toBallChart d.toBallChart a.val).comp
  exact continuous_fst.prodMk
    ((by fun_prop : Continuous (fun q : S2 × unitInterval => (1 - 2 * q.2.val) / 4)).subtype_mk _)

theorem connectingCylinder_injective : Injective (connectingCylinder c d a) := by
  intro p q hpq
  have he := congrArg (collarInv c.toBallChart d.toBallChart a.val) hpq
  rw [connectingCylinder, connectingCylinder, collarInv_collarMap, collarInv_collarMap] at he
  apply Prod.ext
  · exact congrArg (fun q : CollarDomain => q.1) he
  · apply Subtype.ext
    have ht := congrArg (fun q : CollarDomain => q.2.val) he
    change (1 - 2 * p.2.val) / 4 = (1 - 2 * q.2.val) / 4 at ht
    linarith

theorem isClosedEmbedding_connectingCylinder :
    _root_.Topology.IsClosedEmbedding (connectingCylinder c d a) :=
  (continuous_connectingCylinder c d a).isClosedEmbedding (connectingCylinder_injective c d a)

theorem connectingCylinder_zero (z : S2) :
    connectingCylinder c d a (z, 0) =
      inl c.toBallChart d.toBallChart a.val.toHomeomorph
        (c.toBallChart.radialMap z (5 / 4) (by constructor <;> norm_num)) := by
  unfold connectingCylinder
  rw [collarMap_of_nonneg _ _ _ _ (by norm_num)]
  apply congrArg (inl c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change c.chart ((1 + (1 - 2 * (0 : ℝ)) / 4) • z.val) = _
  congr 2
  norm_num

theorem connectingCylinder_one (z : S2) :
    connectingCylinder c d a (z, 1) =
      inr c.toBallChart d.toBallChart a.val.toHomeomorph
        (d.toBallChart.radialMap (a.val z) (5 / 4) (by constructor <;> norm_num)) := by
  unfold connectingCylinder
  rw [collarMap_of_neg _ _ _ _ (by norm_num)]
  apply congrArg (inr c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change d.chart ((1 - (1 - 2 * (1 : ℝ)) / 4) • (a.val z).val) = _
  congr 2
  norm_num

theorem connectingCylinder_half (z : S2) :
    connectingCylinder c d a (z, ⟨1 / 2, by constructor <;> norm_num⟩) =
      inl c.toBallChart d.toBallChart a.val.toHomeomorph (c.toBallChart.boundaryMap z) := by
  have heq : (⟨(1 - 2 * (1 / 2 : ℝ)) / 4, by constructor <;> norm_num⟩ : collarInterval) =
      ⟨0, by constructor <;> norm_num [collarInterval]⟩ := Subtype.ext (by norm_num)
  change collarMap c.toBallChart d.toBallChart a.val (z, _) = _
  rw [heq]
  exact collarMap_zero_left _ _ _ z

def connectingCylinderDomain : TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨univ ×ˢ Ioo (-(1 / 2 : ℝ)) (3 / 2), isOpen_univ.prod isOpen_Ioo⟩

def connectingCylinderOpen (q : connectingCylinderDomain) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  collarMap c.toBallChart d.toBallChart a.val
    (q.val.1, ⟨(1 - 2 * q.val.2) / 4, by
      constructor <;> linarith [q.property.2.1, q.property.2.2]⟩)

theorem isLocalDiffeomorph_connectingCylinderOpen :
    IsLocalDiffeomorph CI (𝓡 3) ∞ (connectingCylinderOpen c d a) := by
  let Q := (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold
  let F : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ) :=
    Diffeomorph.fiberwiseAffine (fun _ => (1 / 4 : ℝ)) (fun _ => (-(1 / 2) : ℝ))
      contMDiff_const contMDiff_const (by intro; norm_num)
  have hF (q : S2 × ℝ) : F q = (q.1, (1 - 2 * q.2) / 4) := by
    change (q.1, 1 / 4 + -(1 / 2) * q.2) = _
    congr 1
    ring
  let phi : connectingCylinderDomain → CollarDomain := fun q =>
    (q.val.1, ⟨(1 - 2 * q.val.2) / 4, by
      constructor <;> linarith [q.property.2.1, q.property.2.2]⟩)
  let U : TopologicalSpace.Opens (S2 × ℝ) :=
    ⟨univ ×ˢ (collarInterval : Set ℝ), isOpen_univ.prod collarInterval.isOpen⟩
  have hloc : IsLocalDiffeomorph CI CI ∞ (fun q : connectingCylinderDomain => F q.val) := by
    intro q
    exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val connectingCylinderDomain q).comp
      CI (S2 × ℝ) (F.isLocalDiffeomorph q.val)
  have hmem : ∀ q : connectingCylinderDomain, F q.val ∈ U := by
    intro q
    rw [hF]
    exact ⟨mem_univ _, (phi q).2.property⟩
  have hlocU := fun q : connectingCylinderDomain =>
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem (hloc q)
  let e : U ≃ₘ⟮CI, CI⟯ CollarDomain :=
    { toFun q := (q.val.1, ⟨q.val.2, q.property.2⟩)
      invFun q := ⟨(q.1, q.2.val), mem_univ _, q.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      contMDiff_toFun := by
        apply ContMDiff.prodMk
        · exact contMDiff_fst.comp contMDiff_subtype_val
        · apply (ContMDiff.subtypeVal_comp_iff collarInterval _).mp
          change ContMDiff CI 𝓘(ℝ) ∞ (fun q : U => q.val.2)
          exact contMDiff_snd.comp contMDiff_subtype_val
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff U _).mp
        exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd) }
  have hphi : IsLocalDiffeomorph CI CI ∞ phi := by
    intro q
    have h := (hlocU q).comp CI CollarDomain (e.isLocalDiffeomorph _)
    have heq : (fun q : connectingCylinderDomain => e ⟨F q.val, hmem q⟩) = phi := by
      funext q
      apply Prod.ext
      · change (F q.val).1 = q.val.1
        rw [hF]
      · apply Subtype.ext
        change (F q.val).2 = (1 - 2 * q.val.2) / 4
        rw [hF]
    exact heq ▸ h
  intro q
  exact (hphi q).comp (𝓡 3) Q.Carrier
    ((smoothConnectedSum M N c d a).collar_localDiffeomorph (phi q))

theorem connectingCylinderOpen_restrict (q : S2 × unitInterval) :
    connectingCylinderOpen c d a ⟨(q.1, q.2.val), mem_univ _, by
      constructor <;> linarith [q.2.property.1, q.2.property.2]⟩ =
      connectingCylinder c d a q := rfl


end DifferentialGeometry.Topology.ConnectedSumQuotient
