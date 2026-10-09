/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.DiskUnion
import DifferentialGeometry.Topology.PlanarJordan.Transport
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Geometry.Manifold.ChartedSpace

open Set Metric Topology Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.PlanarJordan

theorem exists_homeomorph_extending_closedBall_embedding
    (g : closedBall (0 : Plane) 1 → Plane) (hg : Continuous g) (hginj : Function.Injective g) :
    ∃ Φ : Plane ≃ₜ Plane, ∀ x : closedBall (0 : Plane) 1, Φ x = g x := by
  classical
  have hBc : CompactSpace (closedBall (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hSc : CompactSpace (sphere (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hemb : IsClosedEmbedding g := hg.isClosedEmbedding hginj
  let gs : sphere (0 : Plane) 1 → Plane := fun s => g ⟨s.1, sphere_subset_closedBall s.2⟩
  have hgsc : Continuous gs := hg.comp (continuous_subtype_val.subtype_mk _)
  have hgsinj : Function.Injective gs := by
    intro s t h
    have h1 := hginj h
    exact Subtype.ext (congrArg (fun x : closedBall (0 : Plane) 1 => x.val) h1)
  obtain ⟨F, hF⟩ := exists_homeomorph_extending_circle_embedding
    (hgsc.isClosedEmbedding hgsinj).isEmbedding
  let φC : range g ≃ₜ closedBall (0 : Plane) 1 := hemb.isEmbedding.toHomeomorph.symm
  have hfr : frontier (range g) = range gs := by
    rw [frontier_eq_image_sphere_of_homeomorphClosedBall φC]
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b.val, hb⟩, ?_⟩
      change g ⟨b.val, _⟩ = closedBallParam φC b
      change g ⟨b.val, _⟩ = (φC.symm b : Plane)
      rfl
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.1, sphere_subset_closedBall s.2⟩, s.2, rfl⟩
  have hball : closure (inside (sphere (0 : Plane) 1)) = closedBall 0 1 := by
    have h := closure_inside_frontier_eq_of_homeomorphClosedBall
      (Homeomorph.refl (closedBall (0 : Plane) 1))
    rwa [frontier_closedBall (0 : Plane) one_ne_zero] at h
  have hFS : F '' sphere (0 : Plane) 1 = range gs := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hF ⟨x, hx⟩).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, hF s⟩
  have hFB : F '' closedBall (0 : Plane) 1 = range g := by
    have h1 : F '' closure (inside (sphere (0 : Plane) 1)) = range g := by
      rw [F.image_closure, image_inside, hFS, ← hfr,
        closure_inside_frontier_eq_of_homeomorphClosedBall φC]
    rw [← h1, hball]
  have hFnot : ∀ z, z ∉ closedBall (0 : Plane) 1 → F z ∉ range g := by
    intro z hz hFz
    rw [← hFB] at hFz
    obtain ⟨w, hw, hwz⟩ := hFz
    exact hz (F.injective hwz ▸ hw)
  have hFsymm : ∀ w, w ∉ range g → F.symm w ∉ closedBall (0 : Plane) 1 := by
    intro w hw hFw
    apply hw
    rw [← hFB]
    exact ⟨F.symm w, hFw, F.apply_symm_apply w⟩
  let ginv : range g ≃ₜ closedBall (0 : Plane) 1 := φC
  have hginv : ∀ x : closedBall (0 : Plane) 1, ginv ⟨g x, x, rfl⟩ = x := by
    intro x
    exact hemb.isEmbedding.toHomeomorph_symm_apply x
  have hgginv : ∀ w : range g, g (ginv w) = w.val := by
    intro w
    have h := hemb.isEmbedding.toHomeomorph.apply_symm_apply w
    exact congrArg Subtype.val h
  let Φf : Plane → Plane := fun z => if hz : z ∈ closedBall (0 : Plane) 1 then g ⟨z, hz⟩ else F z
  let Ψf : Plane → Plane := fun w => if hw : w ∈ range g then (ginv ⟨w, hw⟩ : Plane) else F.symm w
  have hΦin : ∀ x : closedBall (0 : Plane) 1, Φf x = g x := fun x => dite_eq_left x.2
  have hΦout : ∀ z, z ∉ closedBall (0 : Plane) 1 → Φf z = F z := fun z hz => dite_eq_right hz
  have hΨin : ∀ w (hw : w ∈ range g), Ψf w = (ginv ⟨w, hw⟩ : Plane) := fun w hw => dite_eq_left hw
  have hΨout : ∀ w, w ∉ range g → Ψf w = F.symm w := fun w hw => dite_eq_right hw
  have hfrontB : ∀ z ∈ frontier (closedBall (0 : Plane) 1), Φf z = F z := by
    intro z hz
    rw [frontier_closedBall (0 : Plane) one_ne_zero] at hz
    rw [hΦin ⟨z, sphere_subset_closedBall hz⟩]
    exact (hF ⟨z, hz⟩).symm
  have hΦc : Continuous Φf := by
    have h1 : ContinuousOn Φf (closedBall (0 : Plane) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine hg.congr fun x => ?_
      exact (hΦin x).symm
    have h2 : ContinuousOn Φf (closure (closedBall (0 : Plane) 1)ᶜ) := by
      refine F.continuous.continuousOn.congr fun z hz => ?_
      by_cases hzB : z ∈ closedBall (0 : Plane) 1
      · refine hfrontB z ?_
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hzB, hz⟩
      · exact hΦout z hzB
    have h := h1.union_of_isClosed h2 isClosed_closedBall isClosed_closure
    have hcov : closedBall (0 : Plane) 1 ∪ closure (closedBall (0 : Plane) 1)ᶜ = univ := by
      refine eq_univ_of_forall fun z => ?_
      by_cases hz : z ∈ closedBall (0 : Plane) 1
      · exact Or.inl hz
      · exact Or.inr (subset_closure hz)
    rw [hcov] at h
    exact continuousOn_univ.mp h
  have hRc : IsClosed (range g) := hemb.isClosed_range
  have hfrontR : ∀ w ∈ frontier (range g), Ψf w = F.symm w := by
    intro w hw
    rw [hfr] at hw
    obtain ⟨s, rfl⟩ := hw
    have hmem : gs s ∈ range g := ⟨_, rfl⟩
    rw [hΨin _ hmem]
    have h1 : ginv ⟨gs s, hmem⟩ = ⟨s.1, sphere_subset_closedBall s.2⟩ :=
      hginv ⟨s.1, sphere_subset_closedBall s.2⟩
    rw [h1, ← hF s, F.symm_apply_apply]
  have hΨc : Continuous Ψf := by
    have h1 : ContinuousOn Ψf (range g) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_subtype_val.comp ginv.continuous).congr fun w => ?_
      exact (hΨin w.val w.2).symm
    have h2 : ContinuousOn Ψf (closure (range g)ᶜ) := by
      refine F.symm.continuous.continuousOn.congr fun w hw => ?_
      by_cases hwR : w ∈ range g
      · refine hfrontR w ?_
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hwR, hw⟩
      · exact hΨout w hwR
    have h := h1.union_of_isClosed h2 hRc isClosed_closure
    have hcov : range g ∪ closure (range g)ᶜ = univ := by
      refine eq_univ_of_forall fun w => ?_
      by_cases hw : w ∈ range g
      · exact Or.inl hw
      · exact Or.inr (subset_closure hw)
    rw [hcov] at h
    exact continuousOn_univ.mp h
  have hleft : ∀ z, Ψf (Φf z) = z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : Plane) 1
    · rw [hΦin ⟨z, hz⟩, hΨin _ ⟨⟨z, hz⟩, rfl⟩, hginv]
    · rw [hΦout z hz, hΨout _ (hFnot z hz), F.symm_apply_apply]
  have hright : ∀ w, Φf (Ψf w) = w := by
    intro w
    by_cases hw : w ∈ range g
    · rw [hΨin w hw]
      have h := hΦin (ginv ⟨w, hw⟩)
      rw [h, hgginv]
    · rw [hΨout w hw, hΦout _ (hFsymm w hw), F.apply_symm_apply]
  let Φ : Plane ≃ₜ Plane :=
    { toFun := Φf
      invFun := Ψf
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hΦc
      continuous_invFun := hΨc }
  exact ⟨Φ, fun x => hΦin x⟩

theorem exists_localExtension_of_closedBall_embedding
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : closedBall (0 : Plane) 1 → S) (he : Continuous e) (hinj : Function.Injective e)
    {W : Set S} (hW : IsOpen W) (hDW : range e ⊆ W) (u : Plane) (hu : ‖u‖ = 1) :
    ∃ κ : OpenPartialHomeomorph Plane S, u ∈ κ.source ∧ κ.target ⊆ W ∧
      (∀ v : closedBall (0 : Plane) 1, v.val ∈ κ.source → κ v.val = e v) ∧
      ∀ v : closedBall (0 : Plane) 1, e v ∈ κ.target → v.val ∈ κ.source := by
  classical
  have hBc : CompactSpace (closedBall (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hemb : IsEmbedding e := (he.isClosedEmbedding hinj).isEmbedding
  have hu1 : u ∈ closedBall (0 : Plane) 1 := mem_closedBall_zero_iff.mpr hu.le
  let u' : closedBall (0 : Plane) 1 := ⟨u, hu1⟩
  let φ := chartAt Plane (e u')
  obtain ⟨r₀, hr₀, hr₀sub⟩ : ∃ r₀ > 0, ∀ v : closedBall (0 : Plane) 1,
      dist v.val u < r₀ → e v ∈ φ.source := by
    have hopen : IsOpen (e ⁻¹' φ.source) := φ.open_source.preimage he
    have hmem : u' ∈ e ⁻¹' φ.source := mem_chart_source Plane (e u')
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u' hmem
    exact ⟨ε, hε, fun v hv => hball (by rw [mem_ball, Subtype.dist_eq]; exact hv)⟩
  let r : ℝ := min (r₀ / 2) (1 / 2)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_right _ _
  let Q : Set Plane := closedBall (0 : Plane) 1 ∩ closedBall u r
  have hQc : Convex ℝ Q := (convex_closedBall 0 1).inter (convex_closedBall u r)
  have hQb : Bornology.IsBounded Q := isBounded_closedBall.subset inter_subset_left
  have hQcl : IsClosed Q := isClosed_closedBall.inter isClosed_closedBall
  have hQi : (interior Q).Nonempty := by
    refine ⟨(1 - r / 2) • u, ?_⟩
    rw [interior_inter, interior_closedBall _ one_ne_zero, interior_closedBall _ hr.ne']
    constructor
    · rw [mem_ball_zero_iff, norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
    · rw [mem_ball, dist_eq_norm, show (1 - r / 2) • u - u = -((r / 2) • u) by
        rw [sub_smul, one_smul]; abel, norm_neg, norm_smul, hu, mul_one,
        Real.norm_of_nonneg (by linarith)]
      linarith
  obtain ⟨R, -, hRQ, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hQc hQi hQb
  rw [hQcl.closure_eq] at hRQ
  have hRsQ : ∀ x : closedBall (0 : Plane) 1, R.symm x ∈ Q := by
    intro x
    have hx : x.val ∈ R '' Q := by
      rw [hRQ]
      exact x.2
    obtain ⟨q, hq, hqx⟩ := hx
    rw [← hqx, R.symm_apply_apply]
    exact hq
  have hQB : ∀ q ∈ Q, q ∈ closedBall (0 : Plane) 1 := fun q hq => hq.1
  have hQsrc : ∀ q (hq : q ∈ Q), e ⟨q, hQB q hq⟩ ∈ φ.source := by
    intro q hq
    apply hr₀sub
    exact lt_of_le_of_lt (mem_closedBall.mp hq.2) hrr₀
  let g : closedBall (0 : Plane) 1 → Plane := fun x => φ (e ⟨R.symm x, hQB _ (hRsQ x)⟩)
  have hgin : Continuous (fun x : closedBall (0 : Plane) 1 =>
      e ⟨R.symm x, hQB _ (hRsQ x)⟩) :=
    he.comp ((R.symm.continuous.comp continuous_subtype_val).subtype_mk _)
  have hgc : Continuous g :=
    φ.continuousOn.comp_continuous hgin fun x => hQsrc _ (hRsQ x)
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 := φ.injOn (hQsrc _ (hRsQ x)) (hQsrc _ (hRsQ y)) hxy
    have h2 := hinj h1
    have h3 : R.symm x = R.symm y := congrArg (fun w : closedBall (0 : Plane) 1 => w.val) h2
    exact Subtype.ext (R.symm.injective h3)
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_extending_closedBall_embedding g hgc hginj
  let Ψ : Plane ≃ₜ Plane := R.trans Φ
  have hΨQ : ∀ q (hq : q ∈ Q), Ψ q = φ (e ⟨q, hQB q hq⟩) := by
    intro q hq
    have hRq : R q ∈ closedBall (0 : Plane) 1 := by
      rw [← hRQ]
      exact mem_image_of_mem R hq
    change Φ (R q) = _
    rw [hΦ ⟨R q, hRq⟩]
    change φ (e ⟨R.symm (R q), _⟩) = _
    congr 2
    exact Subtype.ext (R.symm_apply_apply q)
  let κ₀ : OpenPartialHomeomorph Plane S := Ψ.toOpenPartialHomeomorph.trans φ.symm
  have hκ₀Q : ∀ q (hq : q ∈ Q), q ∈ κ₀.source ∧ κ₀ q = e ⟨q, hQB q hq⟩ := by
    intro q hq
    have hmap : Ψ q ∈ φ.target := by
      rw [hΨQ q hq]
      exact φ.map_source (hQsrc q hq)
    refine ⟨⟨mem_univ _, hmap⟩, ?_⟩
    change φ.symm (Ψ q) = _
    rw [hΨQ q hq, φ.left_inv (hQsrc q hq)]
  obtain ⟨O, hO, hOe⟩ : ∃ O : Set S, IsOpen O ∧
      e ⁻¹' O = {v : closedBall (0 : Plane) 1 | dist v.val u < r} := by
    have hop : IsOpen {v : closedBall (0 : Plane) 1 | dist v.val u < r} :=
      isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
    exact hemb.isInducing.isOpen_iff.mp hop
  have huQ : u ∈ Q := ⟨hu1, mem_closedBall_self hr.le⟩
  obtain ⟨hu_src, hκ₀u⟩ := hκ₀Q u huQ
  have hWO : κ₀ u ∈ W ∩ O := by
    rw [hκ₀u]
    refine ⟨hDW ⟨_, rfl⟩, ?_⟩
    have h : (⟨u, hQB u huQ⟩ : closedBall (0 : Plane) 1) ∈ e ⁻¹' O := by
      rw [hOe]
      change dist u u < r
      rw [dist_self]
      exact hr
    exact h
  have hnb : κ₀ ⁻¹' (W ∩ O) ∩ κ₀.source ∈ 𝓝 u :=
    Filter.inter_mem ((κ₀.continuousAt hu_src).preimage_mem_nhds ((hW.inter hO).mem_nhds hWO))
      (κ₀.open_source.mem_nhds hu_src)
  obtain ⟨r', hr', hr'sub⟩ := Metric.mem_nhds_iff.mp hnb
  let r'' : ℝ := min r' r
  have hr'' : 0 < r'' := lt_min hr' hr
  have hballsub : ball u r'' ⊆ κ₀ ⁻¹' (W ∩ O) ∩ κ₀.source :=
    (ball_subset_ball (min_le_left _ _)).trans hr'sub
  let κ := κ₀.restrOpen (ball u r'') isOpen_ball
  have hκs : κ.source = κ₀.source ∩ ball u r'' := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hκapp : ∀ x, κ x = κ₀ x := fun x => rfl
  have hsrcQ : ∀ v : closedBall (0 : Plane) 1, v.val ∈ ball u r'' → v.val ∈ Q := by
    intro v hv
    refine ⟨v.2, ?_⟩
    exact mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le (mem_ball.mp hv) (min_le_right _ _)))
  have htarget : ∀ y ∈ κ.target, y ∈ W ∩ O := by
    intro y hy
    have hs := κ.map_target hy
    have hy' : κ (κ.symm y) = y := κ.right_inv hy
    rw [hκs] at hs
    have h := (hballsub hs.2).1
    rw [← hy', hκapp]
    exact h
  refine ⟨κ, ?_, fun y hy => (htarget y hy).1, fun v hv => ?_, fun v hv => ?_⟩
  · rw [hκs]
    exact ⟨hu_src, mem_ball_self hr''⟩
  · rw [hκs] at hv
    rw [hκapp]
    have hvQ := hsrcQ v hv.2
    rw [(hκ₀Q v.val hvQ).2]
  · have hO' := (htarget _ hv).2
    have hvO : v ∈ e ⁻¹' O := hO'
    rw [hOe] at hvO
    have hvQ : v.val ∈ Q := ⟨v.2, mem_closedBall.mpr (le_of_lt hvO)⟩
    obtain ⟨hvs, hκv⟩ := hκ₀Q v.val hvQ
    have hw := κ.map_target hv
    have hκw : κ (κ.symm (e v)) = e v := κ.right_inv hv
    rw [hκs] at hw ⊢
    have heq : κ₀ v.val = κ₀ (κ.symm (e v)) := by
      rw [hκv, ← hκapp (κ.symm (e v)), hκw]
    have hveq := κ₀.injOn hvs hw.1 heq
    rw [hveq]
    exact hw

end DifferentialGeometry.Topology.PiecewiseLinear
