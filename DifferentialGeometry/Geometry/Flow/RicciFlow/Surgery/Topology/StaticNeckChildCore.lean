import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace D]
  [TopologicalSpace N]

theorem isClopen_retainedCore (E : CutCapTopology M Q D N) : IsClopen E.retainedCore := by
  have hcont : Continuous
      (fun x : E.tubes.core => E.presentation (E.capping.coreInclusion x)) :=
    E.presentation.continuous.comp E.capping.coreInclusion.continuous
  have hset : E.retainedCore =
      (fun x : E.tubes.core => E.presentation (E.capping.coreInclusion x)) ⁻¹'
        Set.range (Sum.inl : Q → Q ⊕ D) := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
  rw [hset]
  exact isClopen_range_inl.preimage hcont

theorem connectedComponent_subset_compl_retainedCore (E : CutCapTopology M Q D N)
    (x : E.tubes.core) (hx : x ∉ E.retainedCore) :
    connectedComponent x ⊆ E.retainedCoreᶜ :=
  (isClopen_retainedCore E).compl.connectedComponent_subset hx

end CutCapTopology

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem staticNeckChart_eq_neckChart (b : (H.event i).RetainedBoundaryIndex)
    (x : neckBuffer (G.static b).delta) :
    ((G.static b).neck.chart x).1 =
      ((G.neck b.1.1).chart ⟨(x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)),
        G.recenter_in_buffer b x⟩).1 :=
  congrArg Subtype.val (G.recenter_chart b x (G.recenter_in_buffer b x))

theorem staticNeck_delta_inv_le_delta_inv (b : (H.event i).RetainedBoundaryIndex) :
    ((G.static b).delta)⁻¹ ≤ (G.delta b.1.1)⁻¹ := by
  have hα : 0 < G.delta b.1.1 := G.delta_pos b.1.1
  have hc4 : (4 : ℝ) ≤ parameters.recenterConstant := parameters.recenterConstant_ge_four
  have hle : G.delta b.1.1 ≤ (G.static b).delta := by
    rw [G.recenter_delta b]
    nlinarith
  exact inv_anti₀ hα hle

theorem mem_removedBand_of_neckChart_abs_lt_one
    (α : (H.event i).transition.trace.tubes.Index) (z : neckBuffer (G.delta α))
    (hz : |z.1.2| < 1) :
    ((G.neck α).chart z).1 ∈ (H.event i).transition.trace.tubes.removedBand α := by
  obtain ⟨hz1, hz2⟩ := abs_lt.mp hz
  let w : TubeDomain := (z.1.1, ⟨z.1.2, ⟨by linarith, by linarith⟩⟩)
  have hw : (w.1, ↑w.2) ∈ neckBuffer (G.delta α) := G.tube_in_buffer α w
  have hwz : (⟨(w.1, ↑w.2), hw⟩ : neckBuffer (G.delta α)) = z :=
    Subtype.ext (Prod.ext rfl rfl)
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · rw [G.tube_eq α w hw, hwz]

theorem mem_core_of_neckChart_one_le_abs
    (α : (H.event i).transition.trace.tubes.Index) (z : neckBuffer (G.delta α))
    (hz : 1 ≤ |z.1.2|) :
    ((G.neck α).chart z).1 ∈ (H.event i).transition.trace.tubes.core := by
  rw [TubeSystem.core, mem_compl_iff, mem_iUnion]
  rintro ⟨β, hβ⟩
  rw [TubeSystem.removedBand, mem_image] at hβ
  obtain ⟨w, ⟨hw1, hw2⟩, hweq⟩ := hβ
  have hβeq : β = α := by
    by_contra hne
    have h1 : ((H.event i).transition.trace.tubes.tube β) w =
        ((G.neck β).chart ⟨(w.1, ↑w.2), G.tube_in_buffer β w⟩).1 :=
      G.tube_eq β w (G.tube_in_buffer β w)
    have h2 : (G.neck β).chart ⟨(w.1, ↑w.2), G.tube_in_buffer β w⟩ = (G.neck α).chart z :=
      Subtype.ext (h1.symm.trans hweq)
    have hmemα : (G.neck α).chart z ∈ Set.range (G.neck α).chart := Set.mem_range_self _
    exact Set.disjoint_left.mp (G.buffer_disjoint (Ne.symm hne)) hmemα
      ⟨⟨(w.1, ↑w.2), G.tube_in_buffer β w⟩, h2⟩
  subst β
  have h1 : ((H.event i).transition.trace.tubes.tube α) w =
      ((G.neck α).chart ⟨(w.1, ↑w.2), G.tube_in_buffer α w⟩).1 :=
    G.tube_eq α w (G.tube_in_buffer α w)
  have h2 : (G.neck α).chart ⟨(w.1, ↑w.2), G.tube_in_buffer α w⟩ = (G.neck α).chart z :=
    Subtype.ext (h1.symm.trans hweq)
  have h3 := (G.neck α).chart_smooth.isEmbedding.injective h2
  have h4 : (w.2 : ℝ) = z.1.2 := congrArg (fun t : neckBuffer (G.delta α) => t.1.2) h3
  rw [h4] at hw1 hw2
  have := abs_lt.mpr ⟨hw1, hw2⟩
  linarith [hz]

theorem staticNeckChart_notMem_retainedCore_of_coordinate_le_neg_two
    (b : (H.event i).RetainedBoundaryIndex)
    (hret : (H.event i).RetainedBoundary (b.1.1, b.1.2))
    (x : neckBuffer (G.static b).delta) (hx2 : x.1.2 ≤ -2)
    (q : (H.event i).transition.trace.tubes.core)
    (hq : (q : (H.stage i.castSucc).Carrier) = ((G.static b).neck.chart x).1) :
    q ∉ (H.event i).transition.trace.retainedCore := by
  classical
  set u : ℝ := x.1.2 with hu
  have hu2 : u ≤ -2 := hx2
  have hu_upper : u < ((G.static b).delta)⁻¹ + 1 := x.2.2
  have hu_lower : -(((G.static b).delta)⁻¹ + 1) < u := by linarith [x.2.1]
  set s₀ : ℝ := (if b.1.2 then (1 : ℝ) else -1) * (1 + u) with hs₀
  have hsign1 : |(if b.1.2 then (1 : ℝ) else -1)| = 1 := by cases b.1.2 <;> norm_num
  have hs₀_abs : 1 ≤ |s₀| := by
    rw [hs₀, abs_mul, hsign1, one_mul, abs_of_nonpos (by linarith : 1 + u ≤ 0)]
    linarith
  have hs₀pos_iff : (0 < s₀) ↔ b.1.2 = false := by
    rcases hb : b.1.2
    · rw [hs₀, hb]
      simp
      linarith
    · rw [hs₀, hb]
      simp
      linarith
  set c₀ : ℝ := if 0 < s₀ then 1 else -1 with hc₀
  have hc₀_abs : |c₀| = 1 := by rw [hc₀]; split <;> norm_num
  set side' : Bool := decide (0 < s₀) with hside'
  have hbL : ((TubeSystem.boundaryLevel side' : Icc (-2 : ℝ) 2) : ℝ) = c₀ := by
    rw [hc₀, hside']
    by_cases h : 0 < s₀ <;> simp [TubeSystem.boundaryLevel, h]
  have hnret : ¬ (H.event i).RetainedBoundary (b.1.1, side') := by
    have hone := G.one_retained_side b.1.1
    rcases hb : b.1.2
    · rw [hb] at hret
      have hs₀pos : 0 < s₀ := hs₀pos_iff.mpr hb
      have hside't : side' = true := by rw [hside', decide_eq_true hs₀pos]
      rw [hside't]
      intro h
      exact (hone.mp h) hret
    · rw [hb] at hret
      have hs₀neg : ¬ (0 < s₀) := fun h => by
        rw [hs₀pos_iff] at h
        simp [hb] at h
      have hside'f : side' = false := by rw [hside', decide_eq_false hs₀neg]
      rw [hside'f]
      exact hone.mp hret
  obtain ⟨y₀, hy₀⟩ := not_forall.mp hnret
  let J : Set ℝ := Icc (min s₀ c₀) (max s₀ c₀)
  have hs₀J : s₀ ∈ J := ⟨min_le_left _ _, le_max_left _ _⟩
  have hc₀J : c₀ ∈ J := ⟨min_le_right _ _, le_max_right _ _⟩
  have hJ : ∀ h ∈ J, 1 ≤ |h| := by
    intro h hh
    have hh' : h ∈ Icc (min s₀ c₀) (max s₀ c₀) := hh
    by_cases hpos : 0 < s₀
    · have hc₀one : c₀ = 1 := by rw [hc₀]; exact if_pos hpos
      have hs₀one : 1 ≤ s₀ := by
        have := abs_of_pos hpos
        linarith [hs₀_abs, this]
      have hmin : min s₀ c₀ = 1 := by rw [hc₀one]; exact min_eq_right hs₀one
      rw [hmin] at hh'
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one hh'.1)]
      exact hh'.1
    · have hc₀neg : c₀ = -1 := by rw [hc₀]; exact if_neg hpos
      have hs₀neg : s₀ ≤ -1 := by
        have := abs_of_nonpos (le_of_not_gt hpos)
        linarith [hs₀_abs, this]
      have hmax : max s₀ c₀ = -1 := by rw [hc₀neg]; exact max_eq_right hs₀neg
      rw [hmax] at hh'
      rw [abs_of_nonpos (le_trans hh'.2 (by norm_num : (-1 : ℝ) ≤ 0))]
      simpa using neg_le_neg_iff.mpr hh'.2
  have hbuf : ∀ h ∈ J, (x.1.1, h) ∈ neckBuffer (G.delta b.1.1) := by
    intro h hh
    have hh' : h ∈ Icc (min s₀ c₀) (max s₀ c₀) := hh
    have h1 : |h| ≤ |s₀| := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have hlow : -|s₀| ≤ min s₀ c₀ := by
          refine le_min (neg_abs_le s₀) ?_
          linarith [neg_abs_le c₀, hc₀_abs]
        linarith [hh'.1]
      · have hhigh : max s₀ c₀ ≤ |s₀| := by
          refine max_le (le_abs_self s₀) ?_
          linarith [le_abs_self c₀, hc₀_abs]
        linarith [hh'.2]
    have h2 : |s₀| = |1 + u| := by rw [hs₀, abs_mul, hsign1, one_mul]
    have h5 : ((G.static b).delta)⁻¹ ≤ ((G.delta b.1.1))⁻¹ := G.staticNeck_delta_inv_le_delta_inv b
    have h3 : |1 + u| < ((G.delta b.1.1))⁻¹ + 1 := by
      rw [abs_of_neg (by linarith : 1 + u < 0)]
      linarith
    have h6 := abs_lt.mp (lt_of_le_of_lt (le_trans h1 (le_of_eq h2)) h3)
    exact ⟨by linarith [h6.1], h6.2⟩
  let φ : ↑J × Sphere 2 → (H.event i).transition.trace.tubes.core :=
    fun w => ⟨((G.neck b.1.1).chart ⟨(w.2, w.1.1), hbuf w.1.1 w.1.2⟩).1,
      G.mem_core_of_neckChart_one_le_abs b.1.1 _ (hJ w.1.1 w.1.2)⟩
  have hmemc : Continuous (fun w : ↑J × Sphere 2 =>
      (⟨(w.2, w.1.1), hbuf w.1.1 w.1.2⟩ : neckBuffer (G.delta b.1.1))) := by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hφ : Continuous φ :=
    Continuous.subtype_mk (continuous_subtype_val.comp
      ((G.neck b.1.1).chart.continuous.comp hmemc))
      (fun w => G.mem_core_of_neckChart_one_le_abs b.1.1 _ (hJ w.1.1 w.1.2))
  have hJpre : PreconnectedSpace ↑J :=
    isPreconnected_iff_preconnectedSpace.mp
      (isPreconnected_Icc (a := min s₀ c₀) (b := max s₀ c₀))
  have hSpre : PreconnectedSpace (Sphere 2) :=
    isPreconnected_iff_preconnectedSpace.mp
      ((isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
        (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one).isPreconnected)
  have hdom : IsPreconnected (Set.univ : Set (↑J × Sphere 2)) := by
    have h3 : IsPreconnected ((Set.univ : Set ↑J) ×ˢ (Set.univ : Set (Sphere 2))) :=
      hJpre.isPreconnected_univ.prod hSpre.isPreconnected_univ
    simpa using h3
  have hpre : IsPreconnected (Set.range φ) := by
    have h4 : IsPreconnected (φ '' (Set.univ : Set (↑J × Sphere 2))) :=
      IsPreconnected.image (f := φ) hdom hφ.continuousOn
    simpa using h4
  have hq'mem : (φ ⟨⟨c₀, hc₀J⟩, y₀⟩) ∈ Set.range φ := Set.mem_range_self _
  have hp'mem : (φ ⟨⟨s₀, hs₀J⟩, x.1.1⟩) ∈ Set.range φ := Set.mem_range_self _
  have hq'not : (φ ⟨⟨c₀, hc₀J⟩, y₀⟩) ∉ (H.event i).transition.trace.retainedCore := by
    have hEq : (φ ⟨⟨c₀, hc₀J⟩, y₀⟩) =
        (H.event i).transition.trace.tubes.coreBoundarySphere (b.1.1, side') y₀ := by
      apply Subtype.ext
      have hstep : ((H.event i).transition.trace.tubes.coreBoundarySphere
          (b.1.1, side') y₀ : (H.stage i.castSucc).Carrier) =
          ((G.neck b.1.1).chart ⟨(y₀, c₀), hbuf c₀ hc₀J⟩).1 := by
        have h1 : (((H.event i).transition.trace.tubes.coreBoundarySphere
            (b.1.1, side') y₀ : (H.event i).transition.trace.tubes.core) :
              (H.stage i.castSucc).Carrier) =
            (((H.event i).transition.trace.tubes.tube b.1.1)
              (y₀, TubeSystem.boundaryLevel side') : (H.stage i.castSucc).Carrier) := rfl
        have h2 := G.tube_eq b.1.1 (y₀, TubeSystem.boundaryLevel side')
          (G.tube_in_buffer b.1.1 (y₀, TubeSystem.boundaryLevel side'))
        have h3 : (⟨(y₀, (TubeSystem.boundaryLevel side' : ℝ)),
              G.tube_in_buffer b.1.1 (y₀, TubeSystem.boundaryLevel side')⟩ :
                neckBuffer (G.delta b.1.1)) = ⟨(y₀, c₀), hbuf c₀ hc₀J⟩ :=
          Subtype.ext (Prod.ext rfl hbL)
        rw [h1, h2, h3]
      exact hstep.symm
    rw [hEq]
    exact hy₀
  have hp'not : (φ ⟨⟨s₀, hs₀J⟩, x.1.1⟩) ∉ (H.event i).transition.trace.retainedCore :=
    (CutCapTopology.connectedComponent_subset_compl_retainedCore _ _ hq'not)
      (hpre.subset_connectedComponent hq'mem hp'mem)
  have hqeq : q = φ ⟨⟨s₀, hs₀J⟩, x.1.1⟩ := by
    apply Subtype.ext
    rw [hq, G.staticNeckChart_eq_neckChart b x]
  rw [hqeq]
  exact hp'not

theorem staticNeckChart_notMem_retainedCore_of_coordinate_negative
    (b : (H.event i).RetainedBoundaryIndex)
    (hret : (H.event i).RetainedBoundary (b.1.1, b.1.2))
    (x : neckBuffer (G.static b).delta) (hx : x.1.2 < 0)
    (q : (H.event i).transition.trace.tubes.core)
    (hq : (q : (H.stage i.castSucc).Carrier) = ((G.static b).neck.chart x).1) :
    q ∉ (H.event i).transition.trace.retainedCore := by
  by_cases h2 : x.1.2 ≤ -2
  · exact G.staticNeckChart_notMem_retainedCore_of_coordinate_le_neg_two b hret x h2 q hq
  · exfalso
    have h1 : |(if b.1.2 then (1 : ℝ) else -1)| = 1 := by cases b.1.2 <;> norm_num
    have hband : |(if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)| < 1 := by
      rw [abs_mul, h1, one_mul, abs_lt]
      exact ⟨by linarith [not_le.mp h2], by linarith⟩
    have hmem : ((G.static b).neck.chart x).1 ∈
        (H.event i).transition.trace.tubes.removedBand b.1.1 := by
      rw [G.staticNeckChart_eq_neckChart b x]
      exact G.mem_removedBand_of_neckChart_abs_lt_one b.1.1
        ⟨(x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)),
          G.recenter_in_buffer b x⟩ hband
    have hcore : ((G.static b).neck.chart x).1 ∈
        (H.event i).transition.trace.tubes.core := by
      rw [← hq]
      exact q.2
    rw [TubeSystem.core, mem_compl_iff, mem_iUnion] at hcore
    exact hcore ⟨b.1.1, hmem⟩

theorem staticNeckChart_ne_childCore_of_coordinate_negative
    (b : (H.event i).RetainedBoundaryIndex)
    (c : ConnectedComponents (H.stage i.succ).Carrier)
    (hc : ∀ y : Sphere 2, ConnectedComponents.mk
      ((H.event i).transition.trace.tubes.coreBoundarySphere b y) =
      (H.event i).transition.childCoreComponent c)
    (x : neckBuffer (G.static b).delta) (hx : x.1.2 < 0) :
    ∀ z : (H.event i).transition.ChildCore c,
      ((G.static b).neck.chart x).1 ≠ (z.1.1 : (H.stage i.castSucc).Carrier) := by
  intro z hz
  have hcoreCompact : CompactSpace (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.core_compact
  have hcoreConnected : LocallyConnectedSpace (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.core_locallyConnected
  have hmem : z.1 ∈ (H.event i).transition.trace.retainedCore :=
    CutCapTopology.childCore_subset_retainedCore (E := (H.event i).transition.trace) c z.2
  have hret : (H.event i).RetainedBoundary (b.1.1, b.1.2) := fun y =>
    CutCapTopology.childCore_subset_retainedCore (E := (H.event i).transition.trace) c (hc y)
  exact G.staticNeckChart_notMem_retainedCore_of_coordinate_negative b hret x hx z.1 hz.symm hmem

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
