import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.SmoothCollarAbsorption
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CollarAbsorption
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Pullback
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OrientationComposition
import DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.RetainedChart
import DifferentialGeometry.Topology.Manifold.OrientedBallChartMap

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

def directSeamDomain : TopologicalSpace.Opens (Sphere (n := 3) × ℝ) :=
  ⟨univ ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2), isOpen_univ.prod isOpen_Ioo⟩

def directSeam (p : directSeamDomain) : DirectQuotient c d hcd a :=
  if ht : 0 ≤ p.val.2 then
    Quot.mk _ (c.firstRadialMap d hcd p.val.1 (1 + p.val.2)
      ⟨by linarith, by linarith [p.property.2.2]⟩)
  else
    Quot.mk _ (c.secondRadialMap d hcd (a p.val.1) (1 - p.val.2)
      ⟨by linarith, by linarith [p.property.2.1]⟩)

theorem directSeam_zero (z : Sphere (n := 3)) :
    directSeam c d hcd a ⟨(z, 0), mem_univ _, by norm_num⟩ =
      Quot.mk _ (c.firstBoundaryMap d hcd z) := by
  rw [directSeam, dite_eq_left le_rfl]
  congr 1
  apply Subtype.ext
  change c.chart ((1 + 0 : ℝ) • z.val) = c.chart z.val
  simp only [add_zero, one_smul]

private def seamBandParameter (p : directSeamDomain) : bandInterior :=
  ⟨(p.val.1, 1 / 2 - p.val.2), mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

private def seamBandAffine : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (Sphere (n := 3) × ℝ) (Sphere (n := 3) × ℝ) ∞ where
  toFun p := (p.1, 1 / 2 - p.2)
  invFun p := (p.1, 1 / 2 - p.2)
  left_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)

private theorem seamBandParameter_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ seamBandParameter := by
  have h := DifferentialGeometry.isLocalDiffeomorph_restrict_open directSeamDomain
    (seamBandAffine.isLocalDiffeomorph.isLocalDiffeomorphOn directSeamDomain)
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := bandInterior) (fun q : directSeamDomain => (seamBandParameter q).property) (h p)

theorem directToBand_directSeam (p : directSeamDomain) :
    directToBand c d hcd a (directSeam c d hcd a p) =
      bandInteriorInclusion c d hcd a
        ⟨(p.val.1, 1 / 2 - p.val.2), mem_univ _,
          by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩ := by
  by_cases ht : 0 ≤ p.val.2
  · rw [directSeam, dite_eq_left ht]
    change coreToBand c d hcd a
      (c.firstClosedRadial d hcd (p.val.1, ⟨1 + p.val.2, by constructor <;> linarith [p.property.2.2]⟩)) = _
    rw [coreToBand_first, stretchedLowerCollar_of_radius_le_three_halves c d hcd a _
      (by dsimp; linarith [p.property.2.2])]
    apply congrArg (bandInclusion c d hcd a)
    refine Prod.ext rfl (Subtype.ext ?_)
    change 3 / 2 - (1 + p.val.2) = 1 / 2 - p.val.2
    ring
  · rw [directSeam, dite_eq_right ht]
    change coreToBand c d hcd a
      (c.secondClosedRadial d hcd (a p.val.1, ⟨1 - p.val.2, by constructor <;> linarith [p.property.2.1]⟩)) = _
    rw [coreToBand_second, stretchedUpperCollar_of_radius_le_three_halves c d hcd a _
      (by dsimp; linarith [p.property.2.1])]
    apply congrArg (bandInclusion c d hcd a)
    refine Prod.ext (a.symm_apply_apply _) (Subtype.ext ?_)
    change 1 - p.val.2 - 1 / 2 = 1 / 2 - p.val.2
    ring

variable [T2Space M]

def directCoreInteriorInclusion : coreInterior c d → DirectQuotient c d hcd a :=
  fun x => Quot.mk _ (coreInteriorToCore c d x)

theorem directToBand_directCoreInteriorInclusion (x : coreInterior c d) :
    directToBand c d hcd a (directCoreInteriorInclusion c d hcd a x) =
      coreToBand c d hcd a (coreInteriorToCore c d x) := rfl

theorem direct_local_maps_cover (q : DirectQuotient c d hcd a) :
    (∃ x, directCoreInteriorInclusion c d hcd a x = q) ∨
      ∃ z, directSeam c d hcd a ⟨(z, 0), mem_univ _, by norm_num [directSeamDomain]⟩ = q := by
  induction q using Quot.inductionOn with
  | h x =>
    by_cases hc : x.val ∈ c.chart '' Metric.closedBall 0 1
    · right
      obtain ⟨v, hv, hvx⟩ := hc
      have hvl : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
      have hvg : 1 ≤ ‖v‖ := by
        by_contra h
        exact x.property (Or.inl ⟨v, mem_ball_zero_iff.mpr (not_le.mp h), hvx⟩)
      let z : Sphere (n := 3) := ⟨v, mem_sphere_zero_iff_norm.mpr (le_antisymm hvl hvg)⟩
      refine ⟨z, ?_⟩
      rw [directSeam_zero]
      exact congrArg (Quot.mk (directRel c d hcd a)) (Subtype.ext hvx)
    · by_cases hd : x.val ∈ d.chart '' Metric.closedBall 0 1
      · right
        obtain ⟨v, hv, hvx⟩ := hd
        have hvl : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
        have hvg : 1 ≤ ‖v‖ := by
          by_contra h
          exact x.property (Or.inr ⟨v, mem_ball_zero_iff.mpr (not_le.mp h), hvx⟩)
        let z : Sphere (n := 3) := ⟨v, mem_sphere_zero_iff_norm.mpr (le_antisymm hvl hvg)⟩
        refine ⟨a.symm z, ?_⟩
        rw [directSeam_zero]
        apply Quot.sound
        refine ⟨a.symm z, Or.inl ⟨rfl, ?_⟩⟩
        apply Subtype.ext
        change x.val = d.chart (a (a.symm z)).val
        rw [a.apply_symm_apply]
        exact hvx.symm
      · left
        exact ⟨⟨x.val, not_or.mpr ⟨hc, hd⟩⟩, rfl⟩

end DifferentialGeometry.Topology.SelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment} (s : SmoothSelfAttachment c d hcd a)

theorem directToBand_comp_directSeam_isLocalDiffeomorph :
    let _ := s.charts
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (SelfAttachment.directToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := by
  let _ := s.charts
  have heq : SelfAttachment.directToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
      SelfAttachment.directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph =
      SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.seamBandParameter := by
    funext p
    exact SelfAttachment.directToBand_directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph p
  rw [heq]
  exact DifferentialGeometry.isLocalDiffeomorph_comp s.band_localDiffeomorph
    SelfAttachment.seamBandParameter_isLocalDiffeomorph

end DifferentialGeometry.Topology.SmoothSelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment} (s : SmoothSelfAttachment c d hcd a)

def directManifold : ConnectedClosedOrientedManifold.{u} 3 :=
  s.toConnectedClosedOrientedManifold.pullback
    (SelfAttachment.directBandHomeomorph c.toBallChart d.toBallChart hcd a.val.toHomeomorph)

def directBandOrientedDiffeomorph : ClosedOrientedManifold.OrientedDiffeomorph
    s.directManifold.toClosedOrientedManifold s.toConnectedClosedOrientedManifold.toClosedOrientedManifold :=
  s.toConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph
    (SelfAttachment.directBandHomeomorph c.toBallChart d.toBallChart hcd a.val.toHomeomorph)

theorem directBandOrientedDiffeomorph_mk (x : c.toBallChart.DoublePunctured d.toBallChart) :
    s.directBandOrientedDiffeomorph.val (Quot.mk _ x) =
      SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph x := rfl

theorem directBandOrientedDiffeomorph_seam (z : SelfAttachment.Sphere (n := 3)) :
    s.directBandOrientedDiffeomorph.val (Quot.mk _ (c.toBallChart.firstBoundaryMap d.toBallChart hcd z)) =
      SelfAttachment.bandInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (z, ⟨1 / 2, by norm_num⟩) :=
  SelfAttachment.directToBand_seam c.toBallChart d.toBallChart hcd a.val.toHomeomorph z

theorem exists_directManifold_orientedBallChart (e : OrientedBallChart M.toClosedOrientedManifold)
    (hc : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
    (hd : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ e' : OrientedBallChart s.directManifold.toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : E3) 2,
        ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
          e'.chart x = Quot.mk (SelfAttachment.directRel c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
            ⟨e.chart x, hx⟩ := by
  have havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1 := by
    intro x hx h
    rcases h with h | h
    · exact Set.disjoint_left.mp hc ⟨x, hx, rfl⟩
        (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) h)
    · exact Set.disjoint_left.mp hd ⟨x, hx, rfl⟩
        (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) h)
  obtain ⟨e₀, he₀⟩ := s.exists_orientedBallChart_core e havoid
  let F := s.directBandOrientedDiffeomorph
  refine ⟨e₀.map F.symm, ?_⟩
  intro x hx
  obtain ⟨hx', hmap⟩ := he₀ x hx
  refine ⟨hx', ?_⟩
  apply F.val.injective
  change F.val (F.val.symm (e₀.chart x)) = _
  rw [F.val.apply_symm_apply, hmap]
  exact (SelfAttachment.directBandHomeomorph_survivor c.toBallChart d.toBallChart hcd a.val.toHomeomorph
    e.toBallChart hc hd x hx hx').symm

theorem exists_directManifold_orientedBallChart_family {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (hc : ∀ i, Disjoint ((e i).chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
    (hd : ∀ i, Disjoint ((e i).chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ e' : ι → OrientedBallChart s.directManifold.toClosedOrientedManifold,
      ∀ i x, x ∈ Metric.closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
          (e' i).chart x = Quot.mk (SelfAttachment.directRel c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
            ⟨(e i).chart x, hx⟩ := by
  choose e' he' using fun i => s.exists_directManifold_orientedBallChart (e i) (hc i) (hd i)
  exact ⟨e', he'⟩

theorem directSeam_isLocalDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.charts
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (SelfAttachment.directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.smooth
  dsimp only
  exact isLocalDiffeomorph_pullback_of_comp (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := 𝓡 3)
    (Y := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    (SelfAttachment.directBandHomeomorph c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    (SelfAttachment.directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    s.directToBand_comp_directSeam_isLocalDiffeomorph

theorem directCoreInteriorInclusion_isLocalDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.charts
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.directCoreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.smooth
  dsimp only
  exact isLocalDiffeomorph_pullback_of_comp (I := 𝓡 3) (J := 𝓡 3)
    (Y := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    (SelfAttachment.directBandHomeomorph c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    (SelfAttachment.directCoreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    s.coreToBand_isLocalDiffeomorph

theorem directCoreInteriorInclusion_preserves_orientation :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.charts
    let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.smooth
    let _ : ChartedSpace E3 (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.charts
    let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.smooth
    ∀ x : SelfAttachment.coreInterior c.toBallChart d.toBallChart,
      let L : E3 ≃L[ℝ] E3 := s.directCoreInteriorInclusion_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x
      Orientation.map (Fin 3) L.toLinearEquiv
        (M.orientation.orientation x.val) = s.directManifold.orientation.orientation
          (SelfAttachment.directCoreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph x) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.smooth
  let _ : ChartedSpace E3 (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.DirectQuotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := s.directManifold.smooth
  dsimp only
  exact Manifold.local_orientation_of_comp
    (SelfAttachment.directCoreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
    s.directBandOrientedDiffeomorph.val
    (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
      SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart)
    s.directCoreInteriorInclusion_isLocalDiffeomorph s.directBandOrientedDiffeomorph.val.isLocalDiffeomorph
    s.coreToBand_isLocalDiffeomorph rfl
    (M.orientation.restrictOpen (SelfAttachment.coreInterior c.toBallChart d.toBallChart))
    s.directManifold.orientation s.orientation
    s.directBandOrientedDiffeomorph.property s.coreToBand_preserves_orientation

end DifferentialGeometry.Topology.SmoothSelfAttachment
