import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CollarAbsorption
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumLocalMaps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def stretchedCollarInterior : TopologicalSpace.Opens (Sphere (n := 3) × ℝ) :=
  ⟨univ ×ˢ Ioo (1 : ℝ) 2, isOpen_univ.prod isOpen_Ioo⟩

private def radialClosed (p : stretchedCollarInterior) : Sphere (n := 3) × Icc (1 : ℝ) 2 :=
  (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

private theorem profile_mem (p : stretchedCollarInterior) :
    collarStretch p.val.2 ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hm : StrictMono collarStretch :=
    strictMono_of_deriv_pos collarStretch_deriv_pos
  have h1 : collarStretch 1 = 1 / 2 := by norm_num [collarStretch, Real.smoothTransition.zero_of_nonpos]
  have h2 : collarStretch 2 = 2 := by norm_num [collarStretch, Real.smoothTransition.one_of_one_le]
  exact ⟨h1 ▸ hm p.property.2.1, h2 ▸ hm p.property.2.2⟩

private theorem local_comp_open
    {E F G H H' H'' X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {K : ModelWithCorners ℝ G H''}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [TopologicalSpace Z] [ChartedSpace H'' Z]
    (f : X → Z) (φ : X → Y) (U : TopologicalSpace.Opens Y) (g : U → Z) (x : X)
    (hx : φ x ∈ U) (hφ : IsLocalDiffeomorphAt I J ∞ φ x)
    (hg : IsLocalDiffeomorphAt J K ∞ g ⟨φ x, hx⟩)
    (he : ∀ y (hy : φ y ∈ U), f y = g ⟨φ y, hy⟩) :
    IsLocalDiffeomorphAt I K ∞ f x := by
  let e : Y → Z := Function.extend (Subtype.val : U → Y) g (fun _ => f x)
  have hext : (fun y : U => e y.val) = g := by
    funext y
    exact Subtype.val_injective.extend_apply _ _ y
  have hl : IsLocalDiffeomorphAt J K ∞ e (φ x) := by
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
      (I := J) (J := J) (K := K) (f := (Subtype.val : U → Y)) (g := e) (x := ⟨φ x, hx⟩)
      (by simpa only [Function.comp_def, hext] using hg) (DifferentialGeometry.isLocalDiffeomorph_subtype_val U ⟨φ x, hx⟩)
  have h := hφ.comp K Z hl
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ h
  filter_upwards [hφ.contMDiffAt.continuousAt (U.isOpen.mem_nhds hx)] with y hy
  exact (he y hy).trans (congrFun hext ⟨φ y, hy⟩).symm

private def profileCylinder : Diffeomorph IC IC (Sphere (n := 3) × ℝ)
    (Sphere (n := 3) × ℝ) ∞ :=
  (Diffeomorph.refl (𝓡 2) (Sphere (n := 3)) ∞).prodCongr collarStretchDiffeomorph

private def reflectionOne : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := 1 - r
  invFun r := 1 - r
  left_inv r := by ring
  right_inv r := by ring
  contMDiff_toFun := (contDiff_const.sub contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.sub contDiff_id).contMDiff

private def lowerCylinder : Diffeomorph IC IC (Sphere (n := 3) × ℝ)
    (Sphere (n := 3) × ℝ) ∞ :=
  profileCylinder.trans ((Diffeomorph.refl (𝓡 2) (Sphere (n := 3)) ∞).prodCongr reflectionOne)

private theorem local_lowerCylinder (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC IC ∞ (fun p : stretchedCollarInterior =>
      (p.val.1, 1 - collarStretch p.val.2)) p :=
  (DifferentialGeometry.isLocalDiffeomorph_subtype_val stretchedCollarInterior p).comp IC _
    (lowerCylinder.isLocalDiffeomorph p.val)

private theorem local_profileCylinder (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC IC ∞ (fun p : stretchedCollarInterior =>
      (p.val.1, collarStretch p.val.2)) p :=
  (DifferentialGeometry.isLocalDiffeomorph_subtype_val stretchedCollarInterior p).comp IC _
    (profileCylinder.isLocalDiffeomorph p.val)

private theorem local_radialChart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (c : BallChart 3 (𝓡 3) M) (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => c.chart (collarStretch q.val.2 • q.val.1.val)) p := by
  have hp : 0 < collarStretch p.val.2 := lt_trans (by norm_num) (profile_mem p).1
  have hpolar := (Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2)).isLocalDiffeomorphAt
    IC (𝓡 3) ∞ (x := (p.val.1, collarStretch p.val.2)) hp
  have hcsrc : collarStretch p.val.2 • p.val.1.val ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial p.val.1 (by linarith : 0 ≤ collarStretch p.val.2)]
    exact (profile_mem p).2.le
  exact ((local_profileCylinder p).comp (𝓡 3) _ hpolar).comp (𝓡 3) _
    (c.chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hcsrc)

universe u
variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment} (s : SmoothSelfAttachment c d hcd a)

include hcd in
private theorem radial_first_core_mem (p : stretchedCollarInterior) (hp : 1 < collarStretch p.val.2) :
    c.chart (collarStretch p.val.2 • p.val.1.val) ∈ coreInterior c.toBallChart d.toBallChart := by
  intro h
  rcases h with ⟨x, hx, he⟩ | ⟨x, hx, he⟩
  · have hsrc : collarStretch p.val.2 • p.val.1.val ∈ c.chart.source := by
      apply c.closedBall_subset_source
      rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial p.val.1 (by linarith : 0 ≤ collarStretch p.val.2)]
      exact (profile_mem p).2.le
    have hxs := c.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx)
    have hxval := c.chart.injOn hxs hsrc he
    have hnorm := mem_closedBall_zero_iff.mp hx
    rw [hxval, BallChart.norm_radial p.val.1 (by linarith : 0 ≤ collarStretch p.val.2)] at hnorm
    linarith
  · exact Set.disjoint_left.mp hcd
      ⟨collarStretch p.val.2 • p.val.1.val, by
        rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial p.val.1 (by linarith : 0 ≤ collarStretch p.val.2)]
        exact (profile_mem p).2.le, rfl⟩
      ⟨x, Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx, he⟩

private theorem lower_local_of_lt (p : stretchedCollarInterior) (hp : collarStretch p.val.2 < 1) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  apply local_comp_open _ (fun q => (q.val.1, 1 - collarStretch q.val.2)) bandInterior
    (bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph) p
    (show (p.val.1, 1 - collarStretch p.val.2) ∈ bandInterior from
      ⟨mem_univ _, by constructor <;> linarith [(profile_mem p).1]⟩)
    (local_lowerCylinder p) (s.band_localDiffeomorph _)
  intro q hq
  rw [stretchedLowerCollar_of_le _ _ _ _ (radialClosed q)
    (show collarStretch (radialClosed q).2 ≤ 1 from by
      change collarStretch q.val.2 ≤ 1
      have hq0 : 0 < 1 - collarStretch q.val.2 := hq.2.1
      linarith)]
  rfl

private theorem lower_local_of_gt (p : stretchedCollarInterior) (hp : 1 < collarStretch p.val.2) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  let U : TopologicalSpace.Opens (stretchedCollarInterior) :=
    ⟨{q | 1 < collarStretch q.val.2}, isOpen_lt continuous_const
      (collarStretch_contDiff.continuous.comp (continuous_snd.comp continuous_subtype_val))⟩
  let g : U → coreInterior c.toBallChart d.toBallChart := fun q =>
    ⟨c.chart (collarStretch q.val.val.2 • q.val.val.1.val), radial_first_core_mem (hcd := hcd) q.val q.property⟩
  have hg : IsLocalDiffeomorph IC (𝓡 3) ∞ g := by
    intro q
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun q : U => radial_first_core_mem (hcd := hcd) q.val q.property)
      ((DifferentialGeometry.isLocalDiffeomorph_subtype_val U q).comp (𝓡 3) _ (local_radialChart c.toBallChart q.val))
  have heq : (fun q : U => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q.val)) =
      coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘ g := by
    funext q
    rw [stretchedLowerCollar_of_gt _ _ _ _ (radialClosed q.val) q.property]
    rfl
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (by
      have h := (hg ⟨p, hp⟩).comp (𝓡 3) _ (s.core_localDiffeomorph _)
      rw [← heq] at h
      exact h)
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val U ⟨p, hp⟩)

private def collarOpen : TopologicalSpace.Opens (Sphere (n := 3) × ℝ) :=
  ⟨univ ×ˢ (ConnectedSumQuotient.collarInterval : Set ℝ),
    isOpen_univ.prod ConnectedSumQuotient.collarInterval.isOpen⟩

private def collarOpenDiffeomorph : Diffeomorph IC IC collarOpen CollarDomain ∞ where
  toFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1, p.2.val), mem_univ _, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      ((ContMDiff.subtypeVal_comp_iff ConnectedSumQuotient.collarInterval _).mp
        (contMDiff_snd.comp contMDiff_subtype_val))
  contMDiff_invFun := by
    exact (ContMDiff.subtypeVal_comp_iff collarOpen _).mp
      (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd))

private theorem lower_local_of_eq (p : stretchedCollarInterior) (hp : collarStretch p.val.2 = 1) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  have hmem : (p.val.1, 1 - collarStretch p.val.2) ∈ collarOpen := by
    rw [hp]
    exact ⟨mem_univ _, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩
  apply local_comp_open _ (fun q => (q.val.1, 1 - collarStretch q.val.2)) collarOpen
    (lowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘ collarOpenDiffeomorph) p
    hmem (local_lowerCylinder p)
  · have he : collarOpenDiffeomorph ⟨(p.val.1, 1 - collarStretch p.val.2), hmem⟩ = collarZero p.val.1 := by
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      change 1 - collarStretch p.val.2 = 0
      rw [hp, sub_self]
    apply (collarOpenDiffeomorph.isLocalDiffeomorph _).comp (𝓡 3) _
    rw [he]
    exact s.lower_localDiffeomorph _
  · intro q hq
    change stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q) =
      lowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (q.val.1, ⟨1 - collarStretch q.val.2, hq.2⟩)
    by_cases h : collarStretch q.val.2 < 1
    · rw [stretchedLowerCollar_of_le _ _ _ _ (radialClosed q) h.le,
        lowerCollar_of_pos _ _ _ _ _ (by change 0 < 1 - collarStretch q.val.2; linarith)]
      rfl
    · have hn : 1 ≤ collarStretch q.val.2 := not_lt.mp h
      rw [lowerCollar_of_nonpos _ _ _ _ _ (by change 1 - collarStretch q.val.2 ≤ 0; linarith)]
      rcases eq_or_lt_of_le hn with he | hg
      · rw [stretchedLowerCollar_of_le _ _ _ _ (radialClosed q) he.symm.le]
        have hs0 : 1 - collarStretch (radialClosed q).2 = 0 := by
          change 1 - collarStretch q.val.2 = 0
          rw [← he, sub_self]
        convert (seam_eq c.toBallChart d.toBallChart hcd a.val.toHomeomorph (false, q.val.1)) using 1
        · apply congrArg (bandInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
          refine Prod.ext (by rfl) ?_
          apply Subtype.ext
          exact hs0
        · symm
          apply congrArg (coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
          apply Subtype.ext
          change c.chart q.val.1.val = c.chart ((1 - (1 - collarStretch q.val.2)) • q.val.1.val)
          rw [← he]
          simp
      · rw [stretchedLowerCollar_of_gt _ _ _ _ (radialClosed q) hg]
        apply congrArg (coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
        apply Subtype.ext
        change c.chart (collarStretch q.val.2 • q.val.1.val) =
          c.chart ((1 - (1 - collarStretch q.val.2)) • q.val.1.val)
        congr 2
        ring

theorem stretchedLowerCollar_isLocalDiffeomorph :
    let _ := s.charts
    IsLocalDiffeomorph IC (𝓡 3) ∞
      (fun p : stretchedCollarInterior => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)) := by
  let _ := s.charts
  change IsLocalDiffeomorph IC (𝓡 3) ∞
    (fun p : stretchedCollarInterior => stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed p))
  intro p
  rcases lt_trichotomy (collarStretch p.val.2) 1 with hp | hp | hp
  · exact lower_local_of_lt s p hp
  · exact lower_local_of_eq s p hp
  · exact lower_local_of_gt s p hp

private def shiftMinusOne : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := r - 1
  invFun r := r + 1
  left_inv r := by ring
  right_inv r := by ring
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

private theorem local_upperBand (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC IC ∞ (fun p : stretchedCollarInterior =>
      (a.val.symm p.val.1, collarStretch p.val.2)) p :=
  (DifferentialGeometry.isLocalDiffeomorph_subtype_val stretchedCollarInterior p).comp IC _
    ((a.val.symm.prodCongr collarStretchDiffeomorph).isLocalDiffeomorph p.val)

private theorem local_upperCylinder (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC IC ∞ (fun p : stretchedCollarInterior =>
      (a.val.symm p.val.1, collarStretch p.val.2 - 1)) p :=
  (DifferentialGeometry.isLocalDiffeomorph_subtype_val stretchedCollarInterior p).comp IC _
    ((a.val.symm.prodCongr (collarStretchDiffeomorph.trans shiftMinusOne)).isLocalDiffeomorph p.val)

include hcd in
private theorem radial_second_core_mem (p : stretchedCollarInterior) (hp : 1 < collarStretch p.val.2) :
    d.chart (collarStretch p.val.2 • p.val.1.val) ∈ coreInterior c.toBallChart d.toBallChart := by
  have hm := radial_first_core_mem (c := d) (d := c) (hcd := hcd.symm) p hp
  exact fun h => hm h.symm

private theorem upper_local_of_lt (p : stretchedCollarInterior) (hp : collarStretch p.val.2 < 1) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  apply local_comp_open _ (fun q => (a.val.symm q.val.1, collarStretch q.val.2)) bandInterior
    (bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph) p
    (show (a.val.symm p.val.1, collarStretch p.val.2) ∈ bandInterior from
      ⟨mem_univ _, by constructor <;> linarith [(profile_mem p).1]⟩)
    (local_upperBand p) (s.band_localDiffeomorph _)
  intro q hq
  rw [stretchedUpperCollar_of_le _ _ _ _ (radialClosed q)
    (show collarStretch (radialClosed q).2 ≤ 1 from hq.2.2.le)]
  rfl

private theorem upper_local_of_gt (p : stretchedCollarInterior) (hp : 1 < collarStretch p.val.2) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  let U : TopologicalSpace.Opens (stretchedCollarInterior) :=
    ⟨{q | 1 < collarStretch q.val.2}, isOpen_lt continuous_const
      (collarStretch_contDiff.continuous.comp (continuous_snd.comp continuous_subtype_val))⟩
  let g : U → coreInterior c.toBallChart d.toBallChart := fun q =>
    ⟨d.chart (collarStretch q.val.val.2 • q.val.val.1.val), radial_second_core_mem (hcd := hcd) q.val q.property⟩
  have hg : IsLocalDiffeomorph IC (𝓡 3) ∞ g := by
    intro q
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun q : U => radial_second_core_mem (hcd := hcd) q.val q.property)
      ((DifferentialGeometry.isLocalDiffeomorph_subtype_val U q).comp (𝓡 3) _ (local_radialChart d.toBallChart q.val))
  have heq : (fun q : U => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q.val)) =
      coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘ g := by
    funext q
    rw [stretchedUpperCollar_of_gt _ _ _ _ (radialClosed q.val) q.property]
    rfl
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (by
      have h := (hg ⟨p, hp⟩).comp (𝓡 3) _ (s.core_localDiffeomorph _)
      rw [← heq] at h
      exact h)
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val U ⟨p, hp⟩)

private theorem upper_local_of_eq (p : stretchedCollarInterior) (hp : collarStretch p.val.2 = 1) :
    let _ := s.charts
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q)) p := by
  let _ := s.charts
  have hmem : (a.val.symm p.val.1, collarStretch p.val.2 - 1) ∈ collarOpen := by
    rw [hp]
    exact ⟨mem_univ _, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩
  apply local_comp_open _ (fun q => (a.val.symm q.val.1, collarStretch q.val.2 - 1)) collarOpen
    (upperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘ collarOpenDiffeomorph) p
    hmem (local_upperCylinder p)
  · have he : collarOpenDiffeomorph ⟨(a.val.symm p.val.1, collarStretch p.val.2 - 1), hmem⟩ =
        collarZero (a.val.symm p.val.1) := by
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      change collarStretch p.val.2 - 1 = 0
      rw [hp, sub_self]
    apply (collarOpenDiffeomorph.isLocalDiffeomorph _).comp (𝓡 3) _
    rw [he]
    exact s.upper_localDiffeomorph _
  · intro q hq
    change stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed q) =
      upperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (a.val.symm q.val.1, ⟨collarStretch q.val.2 - 1, hq.2⟩)
    by_cases h : collarStretch q.val.2 < 1
    · rw [stretchedUpperCollar_of_le _ _ _ _ (radialClosed q) h.le,
        upperCollar_of_neg _ _ _ _ _ (by change collarStretch q.val.2 - 1 < 0; linarith)]
      apply congrArg (bandInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
      refine Prod.ext (by rfl) ?_
      apply Subtype.ext
      change collarStretch q.val.2 = 1 + (collarStretch q.val.2 - 1)
      ring
    · have hn : 1 ≤ collarStretch q.val.2 := not_lt.mp h
      rw [upperCollar_of_nonneg _ _ _ _ _ (by change 0 ≤ collarStretch q.val.2 - 1; linarith)]
      rcases eq_or_lt_of_le hn with he | hg
      · rw [stretchedUpperCollar_of_le _ _ _ _ (radialClosed q) he.symm.le]
        have hs1 : collarStretch (radialClosed q).2 = 1 := he.symm
        convert (seam_eq c.toBallChart d.toBallChart hcd a.val.toHomeomorph (true, a.val.symm q.val.1)) using 1
        · apply congrArg (bandInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
          refine Prod.ext (by rfl) ?_
          apply Subtype.ext
          exact hs1
        · symm
          apply congrArg (coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
          apply Subtype.ext
          change d.chart (a.val (a.val.symm q.val.1)).val =
            d.chart ((1 + (collarStretch q.val.2 - 1)) • (a.val (a.val.symm q.val.1)).val)
          rw [← he]
          simp
      · rw [stretchedUpperCollar_of_gt _ _ _ _ (radialClosed q) hg]
        apply congrArg (coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
        apply Subtype.ext
        change d.chart (collarStretch q.val.2 • q.val.1.val) =
          d.chart ((1 + (collarStretch q.val.2 - 1)) • (a.val (a.val.symm q.val.1)).val)
        rw [a.val.apply_symm_apply]
        congr 2
        ring

theorem stretchedUpperCollar_isLocalDiffeomorph :
    let _ := s.charts
    IsLocalDiffeomorph IC (𝓡 3) ∞
      (fun p : stretchedCollarInterior => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)) := by
  let _ := s.charts
  change IsLocalDiffeomorph IC (𝓡 3) ∞
    (fun p : stretchedCollarInterior => stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph (radialClosed p))
  intro p
  rcases lt_trichotomy (collarStretch p.val.2) 1 with hp | hp | hp
  · exact upper_local_of_lt s p hp
  · exact upper_local_of_eq s p hp
  · exact upper_local_of_gt s p hp

end DifferentialGeometry.Topology.SelfAttachment

namespace DifferentialGeometry.Topology.SelfAttachment

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

include hcd in
private theorem radial_chart_mem_coreInterior (p : stretchedCollarInterior) :
    c.chart (p.val.2 • p.val.1.val) ∈ coreInterior c d := by
  have hr : 0 ≤ p.val.2 := le_trans zero_le_one p.property.2.1.le
  have hball : p.val.2 • p.val.1.val ∈ Metric.closedBall (0 : E3) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial p.val.1 hr]
    exact p.property.2.2.le
  intro h
  rcases h with ⟨x, hx, he⟩ | ⟨x, hx, he⟩
  · have hxs := c.closedBall_subset_source
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx)
    have hxval := c.chart.injOn hxs (c.closedBall_subset_source hball) he
    have hnorm := mem_closedBall_zero_iff.mp hx
    rw [hxval, BallChart.norm_radial p.val.1 hr] at hnorm
    exact (not_le.mpr p.property.2.1) hnorm
  · exact Set.disjoint_left.mp hcd ⟨_, hball, rfl⟩
      ⟨x, Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx, he⟩

def firstRadialInteriorMap (p : stretchedCollarInterior) : coreInterior c d :=
  ⟨c.chart (p.val.2 • p.val.1.val), radial_chart_mem_coreInterior c d hcd p⟩

def secondRadialInteriorMap (p : stretchedCollarInterior) : coreInterior c d :=
  ⟨d.chart (p.val.2 • p.val.1.val), fun h =>
    radial_chart_mem_coreInterior d c hcd.symm p h.symm⟩

@[simp] theorem firstRadialInteriorMap_val (p : stretchedCollarInterior) :
    (firstRadialInteriorMap c d hcd p).val = c.chart (p.val.2 • p.val.1.val) := rfl

@[simp] theorem secondRadialInteriorMap_val (p : stretchedCollarInterior) :
    (secondRadialInteriorMap c d hcd p).val = d.chart (p.val.2 • p.val.1.val) := rfl

omit [T2Space M] in
private theorem radial_chart_isLocalDiffeomorph (p : stretchedCollarInterior) :
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (fun q : stretchedCollarInterior => c.chart (q.val.2 • q.val.1.val)) p := by
  have hpolar := (Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2)).isLocalDiffeomorphAt
    IC (𝓡 3) ∞ (x := p.val) (lt_trans zero_lt_one p.property.2.1)
  have hsrc : p.val.2 • p.val.1.val ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right,
      BallChart.norm_radial p.val.1 (le_trans zero_le_one p.property.2.1.le)]
    exact p.property.2.2.le
  exact ((DifferentialGeometry.isLocalDiffeomorph_subtype_val stretchedCollarInterior p).comp
    (𝓡 3) _ hpolar).comp (𝓡 3) _
      (c.chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hsrc)

theorem firstRadialInteriorMap_isLocalDiffeomorph :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (firstRadialInteriorMap c d hcd) := by
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (radial_chart_mem_coreInterior c d hcd) (radial_chart_isLocalDiffeomorph c p)

theorem secondRadialInteriorMap_isLocalDiffeomorph :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (secondRadialInteriorMap c d hcd) := by
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := coreInterior c d)
    (f := fun q : stretchedCollarInterior => d.chart (q.val.2 • q.val.1.val))
    (fun q h => radial_chart_mem_coreInterior d c hcd.symm q h.symm)
    (radial_chart_isLocalDiffeomorph d p)

omit [T2Space M] in
private theorem exists_radial_preimage {x : M}
    (hx : x ∈ c.chart '' Metric.ball 0 2) (hx1 : x ∉ c.chart '' Metric.closedBall 0 1) :
    ∃ p : stretchedCollarInterior, c.chart (p.val.2 • p.val.1.val) = x := by
  obtain ⟨v, hv, rfl⟩ := hx
  have hv1 : 1 < ‖v‖ := by
    by_contra h
    exact hx1 ⟨v, mem_closedBall_zero_iff.mpr (not_lt.mp h), rfl⟩
  have hv0 : v ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hv1)
  let e := Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2)
  have he : (e.symm v).2 = ‖v‖ :=
    Geometry.Riemannian.euclideanPolarDiffeomorph_symm_snd hv0
  have hp : e.symm v ∈ stretchedCollarInterior := by
    refine ⟨mem_univ _, ?_⟩
    change (e.symm v).2 ∈ Ioo (1 : ℝ) 2
    rw [he]
    exact ⟨hv1, mem_ball_zero_iff.mp hv⟩
  refine ⟨⟨e.symm v, hp⟩, ?_⟩
  apply congrArg c.chart
  exact e.right_inv' hv0

theorem exists_firstRadialInteriorMap (x : coreInterior c d)
    (hx : x.val ∈ c.chart '' Metric.ball 0 2) :
    ∃ p, firstRadialInteriorMap c d hcd p = x := by
  obtain ⟨p, hp⟩ := exists_radial_preimage c hx (fun h => x.property (Or.inl h))
  exact ⟨p, Subtype.ext hp⟩

theorem exists_secondRadialInteriorMap (x : coreInterior c d)
    (hx : x.val ∈ d.chart '' Metric.ball 0 2) :
    ∃ p, secondRadialInteriorMap c d hcd p = x := by
  obtain ⟨p, hp⟩ := exists_radial_preimage d hx (fun h => x.property (Or.inr h))
  exact ⟨p, Subtype.ext hp⟩

end DifferentialGeometry.Topology.SelfAttachment

namespace DifferentialGeometry.Topology.SelfAttachment

variable {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X] [T2Space X]
  {c d : BallChart 3 (𝓡 3) X}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : Sphere (n := 3) ≃ₜ Sphere (n := 3)}

theorem coreToBand_eventually_eq_coreInteriorInclusion
    (x : coreInterior c d)
    (hc : x.val ∉ c.chart '' Metric.closedBall 0 (7 / 4))
    (hd : x.val ∉ d.chart '' Metric.closedBall 0 (7 / 4)) :
    (coreToBand c d hcd a ∘
      coreInteriorToCore c d) =ᶠ[𝓝 x]
        coreInteriorInclusion c d hcd a := by
  have hclosed (e : BallChart 3 (𝓡 3) X) :
      IsClosed (e.chart '' Metric.closedBall 0 (7 / 4)) :=
    ((isCompact_closedBall (0 : E3) (7 / 4)).image_of_continuousOn
      (e.chart.contMDiffOn_toFun.continuousOn.mono (fun y hy =>
        e.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hy)))).isClosed
  have he : ∀ᶠ y : coreInterior c d in 𝓝 x,
      y.val ∈ (c.chart '' Metric.closedBall 0 (7 / 4) ∪
        d.chart '' Metric.closedBall 0 (7 / 4))ᶜ :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hclosed c |>.union (hclosed d)).isOpen_compl.mem_nhds (not_or.mpr ⟨hc, hd⟩))
  filter_upwards [he] with y hy
  exact coreToBand_of_not_mem_ball_image_seven_fourths
    c d hcd a
    (coreInteriorToCore c d y)
    (fun h => hy (Or.inl (Set.image_mono Metric.ball_subset_closedBall h)))
    (fun h => hy (Or.inr (Set.image_mono Metric.ball_subset_closedBall h)))

end DifferentialGeometry.Topology.SelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment}

include hcd in
private theorem exists_coreInterior_exterior :
    ∃ x : SelfAttachment.coreInterior c.toBallChart d.toBallChart,
      x.val ∉ c.chart '' Metric.closedBall 0 (7 / 4) ∧
      x.val ∉ d.chart '' Metric.closedBall 0 (7 / 4) := by
  let z : SelfAttachment.Sphere (n := 3) := Classical.choice (ConnectedSumQuotient.nonempty_sphere_of_neZero (n := 3))
  have hz : (2 : ℝ) • z.val ∈ Metric.closedBall (0 : E3) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by norm_num)]
  have hc : c.chart ((2 : ℝ) • z.val) ∉ c.chart '' Metric.closedBall 0 (7 / 4) := by
    rintro ⟨w, hw, heq⟩
    have hw2 := Metric.closedBall_subset_closedBall (by norm_num : (7 / 4 : ℝ) ≤ 2) hw
    have hweq := c.chart.toPartialEquiv.injOn (c.closedBall_subset_source hw2)
      (c.closedBall_subset_source hz) heq
    rw [hweq, Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by norm_num)] at hw
    norm_num at hw
  have hd : c.chart ((2 : ℝ) • z.val) ∉ d.chart '' Metric.closedBall 0 (7 / 4) := by
    intro h
    exact Set.disjoint_left.mp hcd ⟨_, hz, rfl⟩
      (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num)) h)
  refine ⟨⟨c.chart ((2 : ℝ) • z.val), ?_⟩, hc, hd⟩
  rintro (h | h)
  · exact hc (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num)) h)
  · exact hd (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num)) h)

variable (s : SmoothSelfAttachment c d hcd a)

theorem coreToBand_isLocalDiffeomorph :
    let _ := s.charts
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart) := by
  let _ := s.charts
  dsimp only
  intro x
  by_cases hc : x.val ∈ c.chart '' Metric.ball 0 2
  · obtain ⟨p, rfl⟩ := SelfAttachment.exists_firstRadialInteriorMap c.toBallChart d.toBallChart hcd x hc
    have heq : (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart) ∘
        SelfAttachment.firstRadialInteriorMap c.toBallChart d.toBallChart hcd =
        (fun q : SelfAttachment.stretchedCollarInterior =>
          SelfAttachment.stretchedLowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
            (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩)) := by
      funext q
      change SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (c.toBallChart.firstClosedRadial d.toBallChart hcd (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩)) = _
      exact SelfAttachment.coreToBand_first c.toBallChart d.toBallChart hcd a.val.toHomeomorph _
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
      (by rw [heq]; exact SelfAttachment.stretchedLowerCollar_isLocalDiffeomorph s p)
      (SelfAttachment.firstRadialInteriorMap_isLocalDiffeomorph c.toBallChart d.toBallChart hcd p)
  · by_cases hd : x.val ∈ d.chart '' Metric.ball 0 2
    · obtain ⟨p, rfl⟩ := SelfAttachment.exists_secondRadialInteriorMap c.toBallChart d.toBallChart hcd x hd
      have heq : (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
          SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart) ∘
          SelfAttachment.secondRadialInteriorMap c.toBallChart d.toBallChart hcd =
          (fun q : SelfAttachment.stretchedCollarInterior =>
            SelfAttachment.stretchedUpperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph
              (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩)) := by
        funext q
        change SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
          (c.toBallChart.secondClosedRadial d.toBallChart hcd (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩)) = _
        exact SelfAttachment.coreToBand_second c.toBallChart d.toBallChart hcd a.val.toHomeomorph _
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (by rw [heq]; exact SelfAttachment.stretchedUpperCollar_isLocalDiffeomorph s p)
        (SelfAttachment.secondRadialInteriorMap_isLocalDiffeomorph c.toBallChart d.toBallChart hcd p)
    · have heq := SelfAttachment.coreToBand_eventually_eq_coreInteriorInclusion
        (hcd := hcd) (a := a.val.toHomeomorph) x
        (fun h => hc (Set.image_mono (Metric.closedBall_subset_ball (by norm_num)) h))
        (fun h => hd (Set.image_mono (Metric.closedBall_subset_ball (by norm_num)) h))
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq (s.core_localDiffeomorph x)

private theorem coreToBand_preserves_orientation_of_isLocalDiffeomorph :
    let _ := s.charts
    let _ := s.smooth
    ∀ (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart))
    (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart),
    Orientation.map (Fin 3) ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (M.orientation.orientation x.val) = s.orientation.orientation
        (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
          (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart x)) := by
  let _ := s.charts
  let _ := s.smooth
  dsimp only
  intro hf x
  let _ := SelfAttachment.coreInterior_connected c d hcd
  have hloc := hf.orientation_agreement_isLocallyConstant
    (M.orientation.restrictOpen (SelfAttachment.coreInterior c.toBallChart d.toBallChart)) s.orientation
  obtain ⟨x₀, hc, hd⟩ := exists_coreInterior_exterior (hcd := hcd)
  have heq := SelfAttachment.coreToBand_eventually_eq_coreInteriorInclusion (hcd := hcd) (a := a.val.toHomeomorph) x₀ hc hd
  have hder : ((hf x₀).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv =
      ((s.core_localDiffeomorph x₀).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : E3 →L[ℝ] E3 => L v) heq.mfderiv_eq
  have hbase : Orientation.map (Fin 3) ((hf x₀).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (M.orientation.orientation x₀.val) = s.orientation.orientation
        (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
          (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart x₀)) := by
    rw [hder]
    have hpoint : SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart x₀) =
        SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph x₀ :=
      heq.eq_of_nhds
    rw [hpoint]
    exact s.core_preserves_orientation x₀
  exact Eq.mpr (hloc.apply_eq_of_preconnectedSpace x x₀) hbase

end DifferentialGeometry.Topology.SmoothSelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u
variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment} (s : SmoothSelfAttachment c d hcd a)

theorem coreToBand_preserves_orientation :
    let _ := s.charts
    let _ := s.smooth
    ∀ x : SelfAttachment.coreInterior c.toBallChart d.toBallChart,
      Orientation.map (Fin 3)
        ((s.coreToBand_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (M.orientation.orientation x.val) = s.orientation.orientation
          (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph
            (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart x)) := by
  let _ := s.charts
  let _ := s.smooth
  exact coreToBand_preserves_orientation_of_isLocalDiffeomorph s s.coreToBand_isLocalDiffeomorph

end DifferentialGeometry.Topology.SmoothSelfAttachment
