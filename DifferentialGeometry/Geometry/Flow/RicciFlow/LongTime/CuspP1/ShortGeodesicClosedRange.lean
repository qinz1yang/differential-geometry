import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepFun
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepShift

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- Invariance of domain on the model space of `T² × ℝ`. -/
instance hasInvarianceOfDomain_signedCollar_CPA2 :
    DifferentialGeometry.Topology.HasInvarianceOfDomain
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) :=
  hasInvarianceOfDomain_of_equiv_CPA2
    (ContinuousLinearEquiv.ofFinrankEq (F := EuclideanSpace ℝ (Fin 3)) (by simp [Module.finrank_prod]))

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- Core-side collar of the `k`-th boundary torus, as a point of the core. -/
theorem collar_interior_CPA2 (k : Fin T.count) {q : Torus × EuclideanHalfSpace 1}
    (hq : q.2.val 0 < 1) (h0 : 0 < q.2.val 0) :
    T.core.model.IsInteriorPoint ((T.boundary.collar k) q) := by
  have hs : q ∈ (T.boundary.collar k).source := by rw [T.boundary.source_eq]; exact hq
  have hloc := PartialDiffeomorph.isLocalDiffeomorphAt halfCollarModel T.core.model ∞
    (T.boundary.collar k) hs
  exact (hloc.isInteriorPoint_iff (by simp)).mp ((isInteriorPoint_halfCollar_iff_CPA2 q).mpr h0)

/-- The open slab `|t| < 1` of `T² × ℝ`. -/
def thetaDom_CPA2 : TopologicalSpace.Opens (Torus × ℝ) :=
  ⟨{y | -1 < y.2 ∧ y.2 < 1}, (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)⟩

/-- A bicollar of the `k`-th boundary torus: the cusp on the side `t ≥ 0`, the core collar on the
side `t ≤ 0`. -/
def theta_CPA2 (k : Fin T.count) (y : Torus × ℝ) : H.Carrier :=
  open Classical in
  if 0 ≤ y.2 then T.cuspMap k (y.1, halfSpaceOneLift y.2)
  else T.inclusion (T.boundary.collar k (y.1, halfSpaceOneLift (-y.2)))

theorem theta_zero_CPA2 (k : Fin T.count) (x : Torus) :
    theta_CPA2 T k (x, 0) = T.cuspMap k (x, halfZero) := by
  classical
  have h : halfSpaceOneLift 0 = halfZero := by
    apply Subtype.ext; ext j; rw [Subsingleton.elim j 0]
    change max (0 : ℝ) 0 = 0
    exact max_self 0
  simp [theta_CPA2, h]

theorem theta_of_nonneg_CPA2 (k : Fin T.count) {y : Torus × ℝ} (hy : 0 ≤ y.2) :
    theta_CPA2 T k y = T.cuspMap k (y.1, halfSpaceOneLift y.2) := by
  classical
  simp [theta_CPA2, hy]

theorem theta_of_neg_CPA2 (k : Fin T.count) {y : Torus × ℝ} (hy : y.2 < 0) :
    theta_CPA2 T k y = T.inclusion (T.boundary.collar k (y.1, halfSpaceOneLift (-y.2))) := by
  classical
  simp [theta_CPA2, not_le.mpr hy]

theorem continuous_theta_CPA2 (k : Fin T.count) :
    Continuous fun z : thetaDom_CPA2 => theta_CPA2 T k z.val := by
  classical
  have hpos : Continuous fun z : thetaDom_CPA2 =>
      T.cuspMap k (z.val.1, halfSpaceOneLift z.val.2) :=
    (T.cuspEmbedding k).contMDiff.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_halfSpaceOneLift_CPA2.comp (continuous_snd.comp continuous_subtype_val)))
  have hneg : Continuous fun z : thetaDom_CPA2 =>
      T.inclusion (T.boundary.collar k (z.val.1, halfSpaceOneLift (-z.val.2))) := by
    refine T.inclusion.continuous.comp ?_
    have hc : ContinuousOn (T.boundary.collar k) (T.boundary.collar k).source :=
      (T.boundary.collar k).contMDiffOn.continuousOn
    refine hc.comp_continuous
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_halfSpaceOneLift_CPA2.comp (continuous_snd.comp continuous_subtype_val).neg))
      fun z => ?_
    rw [T.boundary.source_eq]
    have h1 : z.val.2 < 1 := z.2.2
    have h2 : -1 < z.val.2 := z.2.1
    change max (-z.val.2) 0 < 1
    exact max_lt (by linarith) one_pos
  have h := Continuous.if_le (f := fun _ : thetaDom_CPA2 => (0 : ℝ)) (g := fun z => z.val.2)
    (f' := fun z : thetaDom_CPA2 => T.cuspMap k (z.val.1, halfSpaceOneLift z.val.2))
    (g' := fun z : thetaDom_CPA2 =>
      T.inclusion (T.boundary.collar k (z.val.1, halfSpaceOneLift (-z.val.2))))
    hpos hneg continuous_const (continuous_snd.comp continuous_subtype_val) (fun z hz => by
      have h0 : z.val.2 = 0 := hz.symm
      have hl : halfSpaceOneLift z.val.2 = halfZero := by
        rw [h0]
        apply Subtype.ext; ext j; rw [Subsingleton.elim j 0]
        change max (0 : ℝ) 0 = 0
        exact max_self 0
      have hl' : halfSpaceOneLift (-z.val.2) = halfZero := by
        rw [h0, neg_zero]
        apply Subtype.ext; ext j; rw [Subsingleton.elim j 0]
        change max (0 : ℝ) 0 = 0
        exact max_self 0
      change T.cuspMap k (z.val.1, halfSpaceOneLift z.val.2) =
        T.inclusion (T.boundary.collar k (z.val.1, halfSpaceOneLift (-z.val.2)))
      rw [hl, hl', T.cusp_zero]
      rfl)
  convert h using 2 with z
  classical
  by_cases hz : 0 ≤ z.val.2
  · simp [theta_CPA2, hz]
  · simp [theta_CPA2, hz]

theorem lift_height_pos_CPA2 {t : ℝ} (ht : 0 < t) : 0 < (halfSpaceOneLift t).val 0 := by
  change 0 < max t 0
  exact lt_max_of_lt_left ht

theorem lift_height_CPA2 {t : ℝ} (ht : 0 ≤ t) : (halfSpaceOneLift t).val 0 = t := by
  change max t 0 = t
  exact max_eq_left ht

/-- The core side of the bicollar misses the cusp. -/
theorem inclusion_collar_not_mem_range_CPA2 (k i : Fin T.count) {u : EuclideanHalfSpace 1}
    (hu1 : u.val 0 < 1) (hu0 : 0 < u.val 0) (x : Torus) :
    T.inclusion (T.boundary.collar k (x, u)) ∉ range (T.cuspMap i) := by
  rintro ⟨q, hq⟩
  have hmem : T.inclusion (T.boundary.collar k (x, u)) ∈
      range T.inclusion ∩ range (T.cuspMap i) := ⟨⟨_, rfl⟩, ⟨q, hq⟩⟩
  rw [T.intersection i] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  have hx₀' : T.cuspMap i (x₀, halfZero) = T.inclusion (T.boundary.collar k (x, u)) := hx₀
  rw [T.cusp_zero] at hx₀'
  have hc : T.boundary.collar k (x, u) = T.boundary.torusMap i x₀ :=
    T.embedding.isEmbedding.injective hx₀'.symm
  have hbd : T.core.model.IsBoundaryPoint (T.boundary.collar k (x, u)) := by
    rw [hc]; exact T.boundary.boundary_zero i x₀
  exact Set.disjoint_left.mp (T.core.model.disjoint_interior_boundary (M := T.core.Carrier))
    (collar_interior_CPA2 T k hu1 hu0) hbd

theorem injective_theta_CPA2 (k : Fin T.count) :
    Injective fun z : thetaDom_CPA2 => theta_CPA2 T k z.val := by
  classical
  have hsrc : ∀ {t : ℝ}, t < 0 → -1 < t → (halfSpaceOneLift (-t)).val 0 < 1 := by
    intro t ht h1
    rw [lift_height_CPA2 (by linarith)]; linarith
  intro z z' h
  obtain ⟨⟨y1, y2⟩, hz1, hz2⟩ := z
  obtain ⟨⟨y1', y2'⟩, hz1', hz2'⟩ := z'
  simp only at hz1 hz2 hz1' hz2' h
  apply Subtype.ext
  by_cases h0 : 0 ≤ y2 <;> by_cases h0' : 0 ≤ y2'
  · rw [theta_of_nonneg_CPA2 T k (by exact h0), theta_of_nonneg_CPA2 T k (by exact h0')] at h
    have := (T.cuspEmbedding k).isEmbedding.injective h
    have e1 : y1 = y1' := congrArg Prod.fst this
    have e2 := congrArg (fun u : EuclideanHalfSpace 1 => u.val 0) (congrArg Prod.snd this)
    change (halfSpaceOneLift y2).val 0 = (halfSpaceOneLift y2').val 0 at e2
    rw [lift_height_CPA2 h0, lift_height_CPA2 h0'] at e2
    exact Prod.ext e1 e2
  · exfalso
    rw [theta_of_nonneg_CPA2 T k (by exact h0), theta_of_neg_CPA2 T k (by exact not_le.mp h0')] at h
    exact inclusion_collar_not_mem_range_CPA2 T k k (hsrc (not_le.mp h0') hz1')
      (lift_height_pos_CPA2 (by linarith [not_le.mp h0'])) y1' ⟨_, h⟩
  · exfalso
    rw [theta_of_neg_CPA2 T k (by exact not_le.mp h0), theta_of_nonneg_CPA2 T k (by exact h0')] at h
    exact inclusion_collar_not_mem_range_CPA2 T k k (hsrc (not_le.mp h0) hz1)
      (lift_height_pos_CPA2 (by linarith [not_le.mp h0])) y1 ⟨_, h.symm⟩
  · rw [theta_of_neg_CPA2 T k (by exact not_le.mp h0), theta_of_neg_CPA2 T k (by exact not_le.mp h0')] at h
    have hc := T.embedding.isEmbedding.injective h
    have hsa : (y1, halfSpaceOneLift (-y2)) ∈ (T.boundary.collar k).source := by
      rw [T.boundary.source_eq]; exact hsrc (not_le.mp h0) hz1
    have hsb : (y1', halfSpaceOneLift (-y2')) ∈ (T.boundary.collar k).source := by
      rw [T.boundary.source_eq]; exact hsrc (not_le.mp h0') hz1'
    have := (T.boundary.collar k).toPartialEquiv.injOn hsa hsb hc
    have e1 : y1 = y1' := congrArg Prod.fst this
    have e2 := congrArg (fun u : EuclideanHalfSpace 1 => u.val 0) (congrArg Prod.snd this)
    change (halfSpaceOneLift (-y2)).val 0 = (halfSpaceOneLift (-y2')).val 0 at e2
    rw [lift_height_CPA2 (by linarith [not_le.mp h0]), lift_height_CPA2 (by linarith [not_le.mp h0'])] at e2
    exact Prod.ext e1 (by linarith)

theorem exists_nhds_disjoint_boundary_CPA2 (k i : Fin T.count) (hik : i ≠ k) (x : Torus) :
    ∃ V ∈ 𝓝 (T.cuspMap k (x, halfZero)), Disjoint V (range (T.cuspMap i)) := by
  classical
  have hsrc : ∀ {t : ℝ}, t < 0 → -1 < t → (halfSpaceOneLift (-t)).val 0 < 1 := by
    intro t ht h1
    rw [lift_height_CPA2 (by linarith)]; linarith
  let z₀ : thetaDom_CPA2 := ⟨(x, 0), by constructor <;> norm_num⟩
  have hz₀ : signedCollarModel.IsInteriorPoint z₀ := BoundarylessManifold.isInteriorPoint
  have hnhds := image_interior_mem_nhds_CPA2 (N := H.Carrier) signedCollarModel
    (by simp [Module.finrank_prod]) (e := fun z : thetaDom_CPA2 => theta_CPA2 T k z.val)
    (continuous_theta_CPA2 T k) (injective_theta_CPA2 T k) hz₀
  have hval : theta_CPA2 T k z₀.val = T.cuspMap k (x, halfZero) := theta_zero_CPA2 T k x
  refine ⟨range fun z : thetaDom_CPA2 => theta_CPA2 T k z.val, ?_, ?_⟩
  · rw [← hval]
    exact Filter.mem_of_superset hnhds (image_subset_range _ _)
  · rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨q, hq⟩
    obtain ⟨⟨y1, y2⟩, hz1, hz2⟩ := z
    by_cases h0 : 0 ≤ y2
    · have h := hq
      change T.cuspMap i q = theta_CPA2 T k (y1, y2) at h
      rw [theta_of_nonneg_CPA2 T k (by exact h0)] at h
      exact Set.disjoint_left.mp (T.cusp_disjoint hik) ⟨q, h⟩ ⟨_, rfl⟩
    · have h := hq
      change T.cuspMap i q = theta_CPA2 T k (y1, y2) at h
      rw [theta_of_neg_CPA2 T k (by exact not_le.mp h0)] at h
      exact inclusion_collar_not_mem_range_CPA2 T k i (hsrc (not_le.mp h0) hz1)
        (lift_height_pos_CPA2 (by linarith [not_le.mp h0])) y1 ⟨q, h⟩

theorem halfZero_of_height_zero'_CPA2 {u : EuclideanHalfSpace 1} (h : u.val 0 = 0) : u = halfZero := by
  apply Subtype.ext
  ext j
  rw [Subsingleton.elim j 0]
  exact h

/-- The core minus its boundary misses every cusp range. -/
theorem inclusion_not_mem_range_of_interior_CPA2 (i : Fin T.count) {c : T.core.Carrier}
    (hc : T.core.model.IsInteriorPoint c) : T.inclusion c ∉ range (T.cuspMap i) := by
  rintro ⟨q, hq⟩
  have hmem : T.inclusion c ∈ range T.inclusion ∩ range (T.cuspMap i) := ⟨⟨c, rfl⟩, ⟨q, hq⟩⟩
  rw [T.intersection i] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  have hx₀' : T.cuspMap i (x₀, halfZero) = T.inclusion c := hx₀
  rw [T.cusp_zero] at hx₀'
  have hcc : c = T.boundary.torusMap i x₀ := T.embedding.isEmbedding.injective hx₀'.symm
  have hbd : T.core.model.IsBoundaryPoint c := by
    rw [hcc]; exact T.boundary.boundary_zero i x₀
  exact Set.disjoint_left.mp (T.core.model.disjoint_interior_boundary (M := T.core.Carrier)) hc hbd

/-- **The cusp ranges are closed.** (Properness of the cusp ends, from the structure axioms.) -/
theorem isClosed_range_cuspMap_CPA2 (i : Fin T.count) : IsClosed (range (T.cuspMap i)) := by
  classical
  refine isClosed_of_closure_subset fun p hp => ?_
  by_contra hpi
  have hV : ∃ V ∈ 𝓝 p, Disjoint V (range (T.cuspMap i)) := by
    have hex : p ∈ range T.inclusion ∪ ⋃ k, range (T.cuspMap k) := by rw [T.exhausts]; trivial
    rcases hex with ⟨c, rfl⟩ | hk
    · by_cases hc : T.core.model.IsInteriorPoint c
      · refine ⟨T.inclusion '' (T.core.interior : Set T.core.Carrier),
          T.interior_image.mem_nhds ⟨c, hc, rfl⟩, ?_⟩
        rw [Set.disjoint_left]
        rintro _ ⟨c', hc', rfl⟩
        exact inclusion_not_mem_range_of_interior_CPA2 T i hc'
      · have hbd : T.core.model.IsBoundaryPoint c :=
          (T.core.model.isInteriorPoint_or_isBoundaryPoint c).resolve_left hc
        have hb : c ∈ T.boundary.image := by
          rw [← T.boundary_exhausted]; exact hbd
        obtain ⟨k, x, rfl⟩ := mem_iUnion.mp hb
        have hpk : T.inclusion (T.boundary.torusMap k x) = T.cuspMap k (x, halfZero) :=
          (T.cusp_zero k x).symm
        have hki : i ≠ k := by
          rintro rfl
          exact hpi ⟨(x, halfZero), hpk.symm⟩
        rw [hpk]
        exact exists_nhds_disjoint_boundary_CPA2 T k i hki x
    · obtain ⟨k, q, rfl⟩ := mem_iUnion.mp hk
      have hki : i ≠ k := by
        rintro rfl
        exact hpi ⟨q, rfl⟩
      rcases q.2.2.eq_or_lt with h0 | hpos
      · have hq : q = (q.1, halfZero) :=
          Prod.ext rfl (halfZero_of_height_zero'_CPA2 h0.symm)
        rw [hq]
        exact exists_nhds_disjoint_boundary_CPA2 T k i hki q.1
      · refine ⟨cuspW_CPA2 T k, (isOpen_cuspW_CPA2 T k).mem_nhds ⟨q, hpos, rfl⟩, ?_⟩
        rw [Set.disjoint_left]
        rintro _ ⟨q', -, rfl⟩ ⟨q'', hq''⟩
        exact Set.disjoint_left.mp (T.cusp_disjoint hki) ⟨q'', hq''⟩ ⟨q', rfl⟩
  obtain ⟨V, hVn, hVd⟩ := hV
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hp V hVn
  exact Set.disjoint_left.mp hVd hy1 hy2

end GC.LongTime.CuspP1
