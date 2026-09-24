import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TransportDiffeomorphism
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingSmooth

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v

theorem boundaryAttachment_toHomeomorph_symm :
    (boundaryAttachment.1.toHomeomorph).symm = boundaryAttachment.1.toHomeomorph := by
  rw [← Diffeomorph.symm_toHomeomorph, boundaryAttachment_symm]

theorem boundaryAttachment_involutive (z : ConnectedSumQuotient.csSphere) :
    boundaryAttachment.1.toHomeomorph (boundaryAttachment.1.toHomeomorph z) = z := by
  have h2 : (boundaryAttachment.1.toHomeomorph : ConnectedSumQuotient.csSphere →
        ConnectedSumQuotient.csSphere) =
      ((boundaryAttachment.1.toHomeomorph).symm : ConnectedSumQuotient.csSphere →
        ConnectedSumQuotient.csSphere) :=
    congrArg (fun f : ConnectedSumQuotient.csSphere ≃ₜ ConnectedSumQuotient.csSphere =>
      (f : ConnectedSumQuotient.csSphere → ConnectedSumQuotient.csSphere))
      boundaryAttachment_toHomeomorph_symm
  calc boundaryAttachment.1.toHomeomorph (boundaryAttachment.1.toHomeomorph z)
      = boundaryAttachment.1.toHomeomorph
          ((boundaryAttachment.1.toHomeomorph).symm z) := by
        rw [congrFun h2 z]
    _ = z := (boundaryAttachment.1.toHomeomorph).apply_symm_apply z

namespace ConnectedSumQuotient

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

theorem commHomeomorph_inl (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (y : c.Punctured) :
    commHomeomorph c d a (inl c d a y) = inr d c a.symm y := rfl

theorem commHomeomorph_inr (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (y : d.Punctured) :
    commHomeomorph c d a (inr c d a y) = inl d c a.symm y := rfl

theorem commHomeomorph_interiorLeft [T2Space M] [T2Space N]
    (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N) (x : c.interior) :
    commHomeomorph c d boundaryAttachment.1.toHomeomorph
        (interiorLeft c d boundaryAttachment.1 x)
      = interiorRight d c boundaryAttachment.1 x := by
  rw [interiorLeft, Function.comp_apply, commHomeomorph_inl]
  rw [interiorRight, Function.comp_apply]
  rfl

theorem commHomeomorph_interiorRight [T2Space M] [T2Space N]
    (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N) (x : d.interior) :
    commHomeomorph c d boundaryAttachment.1.toHomeomorph
        (interiorRight c d boundaryAttachment.1 x)
      = interiorLeft d c boundaryAttachment.1 x := by
  rw [interiorRight, Function.comp_apply, commHomeomorph_inr]
  rw [interiorLeft, Function.comp_apply]
  rfl

private theorem collarNeg_mem (t : collarInterval) : (-(t : ℝ)) ∈ collarInterval := by
  change (-(t : ℝ)) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  exact ⟨by linarith [t.2.1, t.2.2], by linarith [t.2.1, t.2.2]⟩

private theorem contMDiff_collarNeg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
    (fun t : collarInterval => (⟨-(t : ℝ), collarNeg_mem t⟩ : collarInterval)) := by
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : collarInterval => -(t : ℝ)) := by
    intro t
    exact (contMDiffAt_subtype_iff (U := collarInterval)
      (f := fun s : ℝ => -s)).mpr (contMDiff_neg 𝓘(ℝ, ℝ) ∞).contMDiffAt
  exact (ContMDiff.subtypeVal_comp_iff collarInterval _).mp h

private def collarNeg :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) collarInterval collarInterval ∞ where
  toEquiv :=
    { toFun := fun t => ⟨-(t : ℝ), collarNeg_mem t⟩
      invFun := fun t => ⟨-(t : ℝ), collarNeg_mem t⟩
      left_inv := fun t => Subtype.ext (by simp)
      right_inv := fun t => Subtype.ext (by simp) }
  contMDiff_toFun := contMDiff_collarNeg
  contMDiff_invFun := contMDiff_collarNeg

private def collarZero : collarInterval :=
  ⟨0, by constructor <;> norm_num [collarInterval]⟩

private theorem collarNeg_val (t : collarInterval) :
    ((collarNeg t : collarInterval) : ℝ) = -(t : ℝ) := rfl

private theorem collarZero_val : ((collarZero : collarInterval) : ℝ) = 0 := rfl

private theorem collarMap_zero (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (z : csSphere) :
    collarMap c d boundaryAttachment.1 (z, collarZero) =
      inl c d boundaryAttachment.1.toHomeomorph (c.boundaryMap z) := by
  rw [collarMap_of_nonneg c d boundaryAttachment.1 (z, collarZero) collarZero_val.ge]
  refine congrArg (inl c d boundaryAttachment.1.toHomeomorph) ?_
  change c.radialMap z (1 + ((collarZero : collarInterval) : ℝ)) _ = c.boundaryMap z
  exact (radialMap_congr (c := c) rfl (by rw [collarZero_val]; norm_num)
      (by rw [collarZero_val]; norm_num) (by norm_num)).trans
    (BallChart.radialMap_one c z (by norm_num))

private def collarReflect : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
    ((𝓡 2).prod 𝓘(ℝ, ℝ)) CollarDomain CollarDomain ∞ :=
  boundaryAttachment.1.prodCongr collarNeg

private theorem collarReflect_pair (z : csSphere) (t : collarInterval) :
    collarReflect (z, t) = (boundaryAttachment.1.toHomeomorph z, collarNeg t) := by
  rw [collarReflect, Diffeomorph.coe_prodCongr]
  rfl

theorem commHomeomorph_collarMap (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (p : CollarDomain) :
    commHomeomorph c d boundaryAttachment.1.toHomeomorph (collarMap c d boundaryAttachment.1 p)
      = collarMap d c boundaryAttachment.1 (collarReflect p) := by
  obtain ⟨z, t⟩ := p
  rw [collarReflect_pair z t]
  rcases lt_trichotomy (t : ℝ) 0 with hneg | hzero | hpos
  · have hle : 0 ≤ ((collarNeg t : collarInterval) : ℝ) := by
      rw [collarNeg_val]; linarith
    rw [collarMap_of_neg c d boundaryAttachment.1 (z, t) hneg, commHomeomorph_inr,
      collarMap_of_nonneg d c boundaryAttachment.1
        (boundaryAttachment.1.toHomeomorph z, collarNeg t) hle]
    refine congrArg (inl d c boundaryAttachment.1.toHomeomorph) ?_
    refine radialMap_congr rfl ?_ _ _
    rw [collarNeg_val]; ring
  · have ht : t = collarZero := Subtype.ext hzero
    have hcz : collarNeg collarZero = collarZero :=
      Subtype.ext (by rw [collarNeg_val, collarZero_val, neg_zero])
    rw [ht, hcz, collarMap_zero c d z, commHomeomorph_inl,
      collarMap_zero d c (boundaryAttachment.1.toHomeomorph z)]
    conv_lhs => rw [← boundaryAttachment_involutive z]
    exact (boundary_eq d c boundaryAttachment.1.toHomeomorph
      (boundaryAttachment.1.toHomeomorph z)).symm
  · have hle : ((collarNeg t : collarInterval) : ℝ) < 0 := by
      rw [collarNeg_val]; linarith
    rw [collarMap_of_nonneg c d boundaryAttachment.1 (z, t) (le_of_lt hpos),
      commHomeomorph_inl, collarMap_of_neg d c boundaryAttachment.1
        (boundaryAttachment.1.toHomeomorph z, collarNeg t) hle]
    refine congrArg (inr d c boundaryAttachment.1.toHomeomorph) ?_
    refine radialMap_congr (boundaryAttachment_involutive z).symm ?_ _ _
    rw [collarNeg_val]; ring

end ConnectedSumQuotient

theorem commHomeomorph_isLocalDiffeomorph (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    letI := ConnectedSumQuotient.csChartedSpace (orientedBallChart M).toBallChart
      (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold (orientedBallChart M).toBallChart
      (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
    letI := ConnectedSumQuotient.csChartedSpace (orientedBallChart N).toBallChart
      (orientedBallChart M).toBallChart boundaryAttachment.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold (orientedBallChart N).toBallChart
      (orientedBallChart M).toBallChart boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
    letI := ConnectedSumQuotient.csChartedSpace (orientedBallChart N).toBallChart
      (orientedBallChart M).toBallChart (boundaryAttachment.1.toHomeomorph).symm
    letI := ConnectedSumQuotient.csIsManifold (orientedBallChart N).toBallChart
      (orientedBallChart M).toBallChart (boundaryAttachment.1.toHomeomorph).symm
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (ConnectedSumQuotient.commHomeomorph (orientedBallChart M).toBallChart
        (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph) := by
  let c := (orientedBallChart M).toBallChart
  let d := (orientedBallChart N).toBallChart
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (ConnectedSumQuotient c d boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c d boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c d boundaryAttachment.1.toHomeomorph
    (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
    (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (ConnectedSumQuotient d c boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace d c boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient d c boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold d c boundaryAttachment.1.toHomeomorph
    (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
    (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) :=
    ConnectedSumQuotient.csChartedSpace d c (boundaryAttachment.1.toHomeomorph).symm
  let _ : IsManifold (𝓡 3) ∞
        (ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) :=
    ConnectedSumQuotient.csIsManifold d c (boundaryAttachment.1.toHomeomorph).symm
    (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
    (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  intro z
  rcases ConnectedSumQuotient.interior_collar_cover c d boundaryAttachment.1 z with
    ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨p, rfl⟩
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1) u :=
      (smoothConnectedSum M N (orientedBallChart M) (orientedBallChart N)
        boundaryAttachment).interiorLeft_localDiffeomorph u
    have hright : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorRight d c boundaryAttachment.1) u :=
      (smoothConnectedSum N M (orientedBallChart N) (orientedBallChart M)
        boundaryAttachment).interiorRight_localDiffeomorph u
    have hEq : (fun x : c.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 x)) =
        fun x : c.interior =>
          ConnectedSumQuotient.interiorRight d c boundaryAttachment.1 x :=
      funext fun x => ConnectedSumQuotient.commHomeomorph_interiorLeft c d x
    have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 x)) u := by
      rw [hEq]; exact hright
    have hpt : hg.localInverse (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 u)
        = u := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 u)) := by
      rw [hpt]; exact hcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.interiorLeft c d boundaryAttachment.1 u) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact (congrArg (ConnectedSumQuotient.commHomeomorph c d
      boundaryAttachment.1.toHomeomorph) hy).symm
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1) v :=
      (smoothConnectedSum M N (orientedBallChart M) (orientedBallChart N)
        boundaryAttachment).interiorRight_localDiffeomorph v
    have hleft : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (ConnectedSumQuotient.interiorLeft d c boundaryAttachment.1) v :=
      (smoothConnectedSum N M (orientedBallChart N) (orientedBallChart M)
        boundaryAttachment).interiorLeft_localDiffeomorph v
    have hEq : (fun x : d.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 x)) =
        fun x : d.interior =>
          ConnectedSumQuotient.interiorLeft d c boundaryAttachment.1 x :=
      funext fun x => ConnectedSumQuotient.commHomeomorph_interiorRight c d x
    have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 x)) v := by
      rw [hEq]; exact hleft
    have hpt : hg.localInverse (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 v)
        = v := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.interior => ConnectedSumQuotient.commHomeomorph c d
          boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 v)) := by
      rw [hpt]; exact hcomp
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.interiorRight c d boundaryAttachment.1 v) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact (congrArg (ConnectedSumQuotient.commHomeomorph c d
      boundaryAttachment.1.toHomeomorph) hy).symm
  · have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (ConnectedSumQuotient.collarMap c d boundaryAttachment.1) p :=
      (smoothConnectedSum M N (orientedBallChart M) (orientedBallChart N)
        boundaryAttachment).collar_localDiffeomorph p
    have hreflect : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (⇑(ConnectedSumQuotient.collarReflect)) p :=
      (ConnectedSumQuotient.collarReflect).isLocalDiffeomorph p
    have htarget : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (ConnectedSumQuotient.collarMap d c boundaryAttachment.1)
        (ConnectedSumQuotient.collarReflect p) :=
      (smoothConnectedSum N M (orientedBallChart N) (orientedBallChart M)
        boundaryAttachment).collar_localDiffeomorph (ConnectedSumQuotient.collarReflect p)
    have hcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => ConnectedSumQuotient.collarMap d c boundaryAttachment.1
          (ConnectedSumQuotient.collarReflect x)) p :=
      hreflect.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) htarget
    have hEq : (fun x : ConnectedSumQuotient.CollarDomain =>
          ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
            (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 x)) =
        fun x => ConnectedSumQuotient.collarMap d c boundaryAttachment.1
          (ConnectedSumQuotient.collarReflect x) :=
      funext fun x => ConnectedSumQuotient.commHomeomorph_collarMap c d x
    have hcomp' : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 x)) p := by
      rw [hEq]; exact hcomp
    have hpt : hg.localInverse (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 p)
        = p := hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 x))
        (hg.localInverse (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 p)) := by
      rw [hpt]; exact hcomp'
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph
          (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 (hg.localInverse y)))
        (ConnectedSumQuotient.collarMap c d boundaryAttachment.1 p) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    exact (congrArg (ConnectedSumQuotient.commHomeomorph c d
      boundaryAttachment.1.toHomeomorph) hy).symm

def connectedSumCommDiffeomorph (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum N M).Carrier := by
  let c := (orientedBallChart M).toBallChart
  let d := (orientedBallChart N).toBallChart
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c d boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c d boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c d boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient d c boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace d c boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient d c boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold d c boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) :=
    ConnectedSumQuotient.csChartedSpace d c (boundaryAttachment.1.toHomeomorph).symm
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient d c (boundaryAttachment.1.toHomeomorph).symm) :=
    ConnectedSumQuotient.csIsManifold d c (boundaryAttachment.1.toHomeomorph).symm
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  exact IsLocalDiffeomorph.diffeomorphOfBijective (commHomeomorph_isLocalDiffeomorph M N)
    (ConnectedSumQuotient.commHomeomorph c d boundaryAttachment.1.toHomeomorph).bijective

theorem nonempty_diffeomorph_connectedSum_comm (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    Nonempty ((connectedSum M N).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum N M).Carrier) :=
  ⟨connectedSumCommDiffeomorph M N⟩

theorem nonempty_diffeomorph_connectedSum_sphere_left
    (X : ConnectedClosedOrientedManifold.{u} 3) (P : SphereUnitFilling.S3)
    (h : ∃ d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold,
      ∀ u : csE3, ULift.down (d.toBallChart.chart u)
        = (SphereUnitFilling.sphereBallChart P).chart u) :
    Nonempty ((connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) := by
  obtain ⟨e₁⟩ := nonempty_diffeomorph_connectedSum_comm standardThreeSphereLift.{u} X
  obtain ⟨e₂⟩ := ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right X P h
  exact ⟨e₁.trans e₂⟩

end DifferentialGeometry.Topology
