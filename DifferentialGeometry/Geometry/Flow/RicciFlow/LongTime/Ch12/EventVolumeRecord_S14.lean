import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeTopology_S14
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeCap_S14

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (R : GeometricCutoffRecord H i parameters)

/-- The point of the incoming stage with neck coordinates `(y, z)` in the neck of the tube `α`. -/
def chartPt_S14 (α : (H.event i).transition.trace.tubes.Index) (y : Sphere 2) (z : ℝ)
    (h : (y, z) ∈ neckBuffer (R.delta α)) : (H.stage i.castSucc).Carrier :=
  ((R.neck α).chart ⟨(y, z), h⟩).1

theorem tube_eq_chartPt_S14 (α : (H.event i).transition.trace.tubes.Index) (y : Sphere 2)
    (z : ℝ) (hz : z ∈ Icc (-2 : ℝ) 2) :
    (H.event i).transition.trace.tubes.tube α (y, ⟨z, hz⟩) =
      chartPt_S14 R α y z (R.tube_in_buffer α (y, ⟨z, hz⟩)) :=
  R.tube_eq α _ _

theorem chartPt_injective_S14 (α : (H.event i).transition.trace.tubes.Index) {y y' : Sphere 2}
    {z z' : ℝ} {h : (y, z) ∈ neckBuffer (R.delta α)} {h' : (y', z') ∈ neckBuffer (R.delta α)}
    (he : chartPt_S14 R α y z h = chartPt_S14 R α y' z' h') : y = y' ∧ z = z' := by
  have h1 : (R.neck α).chart ⟨(y, z), h⟩ = (R.neck α).chart ⟨(y', z'), h'⟩ := Subtype.ext he
  have h2 := (R.neck α).chart_smooth.isEmbedding.injective h1
  have h3 := congrArg Subtype.val h2
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

theorem chartPt_ne_of_ne_S14 {α β : (H.event i).transition.trace.tubes.Index} (hαβ : α ≠ β)
    {y y' : Sphere 2} {z z' : ℝ} {h : (y, z) ∈ neckBuffer (R.delta α)}
    {h' : (y', z') ∈ neckBuffer (R.delta β)} :
    chartPt_S14 R α y z h ≠ chartPt_S14 R β y' z' h' := by
  intro he
  have h1 : (R.neck α).chart ⟨(y, z), h⟩ = (R.neck β).chart ⟨(y', z'), h'⟩ := Subtype.ext he
  exact Set.disjoint_left.mp (R.buffer_disjoint hαβ) ⟨_, rfl⟩ ⟨_, h1.symm⟩

/-- A neck point with `1 ≤ |z|` lies in the core. -/
theorem chartPt_mem_core_S14 (α : (H.event i).transition.trace.tubes.Index) (y : Sphere 2)
    (z : ℝ) (h : (y, z) ∈ neckBuffer (R.delta α)) (hz : 1 ≤ |z|) :
    chartPt_S14 R α y z h ∈ (H.event i).transition.trace.tubes.core := by
  intro hmem
  have hmem' := mem_iUnion.mp hmem
  obtain ⟨β, x, hx, hxe⟩ := hmem'
  have hxe' : chartPt_S14 R β x.1 x.2.1 (R.tube_in_buffer β x) =
      chartPt_S14 R α y z h := by
    rw [← hxe]
    exact (R.tube_eq β x (R.tube_in_buffer β x)).symm
  by_cases hβα : β = α
  · subst hβα
    obtain ⟨_, hzz⟩ := chartPt_injective_S14 R β hxe'
    have h1 : -1 < z := hzz ▸ hx.1
    have h2 : z < 1 := hzz ▸ hx.2
    rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0] at hz; linarith
    · rw [abs_of_neg hz0] at hz; linarith
  · exact chartPt_ne_of_ne_S14 R hβα hxe'

/-- Segment lemma: the cylinder segment from the cutting level `±1` to `z` (on the side of `σ`)
lies in the core, and if one of its points is retained then the boundary `(α, σ)` is retained. -/
theorem seg_S14 (α : (H.event i).transition.trace.tubes.Index) (σ : Bool) (y : Sphere 2)
    (z : ℝ) (h : (y, z) ∈ neckBuffer (R.delta α))
    (hσ : σ = true → 1 ≤ z) (hσ' : σ = false → z ≤ -1) :
    chartPt_S14 R α y z h ∈ (H.event i).transition.trace.tubes.core ∧
    (chartPt_S14 R α y z h ∈ retainedPts_S14 (H.event i) →
      (H.event i).RetainedBoundary (α, σ)) := by
  have hδ := inv_pos.mpr (R.delta_pos α)
  let lvl : ℝ := if σ then 1 else -1
  have hseg : ∀ w ∈ uIcc lvl z, 1 ≤ |w| ∧ (σ = true → 1 ≤ w) ∧ (σ = false → w ≤ -1) := by
    intro w hw
    cases σ
    · have h1 := hσ' rfl
      have : lvl = -1 := by simp [lvl]
      rw [this, mem_uIcc] at hw
      have hw' : w ≤ -1 := by rcases hw with hw | hw <;> linarith [hw.1, hw.2]
      exact ⟨by rw [abs_of_neg (by linarith)]; linarith, by simp, fun _ => hw'⟩
    · have h1 := hσ rfl
      have : lvl = 1 := by simp [lvl]
      rw [this, mem_uIcc] at hw
      have hw' : 1 ≤ w := by rcases hw with hw | hw <;> linarith [hw.1, hw.2]
      exact ⟨by rw [abs_of_pos (by linarith)]; exact hw', fun _ => hw', by simp⟩
  have hbuf : ∀ w ∈ uIcc lvl z, (y, w) ∈ neckBuffer (R.delta α) := by
    intro w hw
    have hl : |lvl| = 1 := by by_cases hs : σ <;> simp [lvl, hs]
    have h1 : -(R.delta α)⁻¹ - 1 < z := h.1
    have h2 : z < (R.delta α)⁻¹ + 1 := h.2
    have hl1 : -1 ≤ lvl := by by_cases hs : σ <;> simp [lvl, hs]
    have hl2 : lvl ≤ 1 := by by_cases hs : σ <;> simp [lvl, hs]
    rw [mem_uIcc] at hw
    constructor <;> rcases hw with hw | hw <;> linarith [hw.1, hw.2]
  let φ : Sphere 2 × uIcc lvl z → (H.stage i.castSucc).Carrier := fun w =>
    chartPt_S14 R α w.1 w.2.1 (hbuf w.2.1 w.2.2)
  have hφ : Continuous φ := by
    have : Continuous fun w : Sphere 2 × uIcc lvl z =>
        (⟨(w.1, w.2.1), hbuf w.2.1 w.2.2⟩ : neckBuffer (R.delta α)) :=
      Continuous.subtype_mk (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _
    exact continuous_subtype_val.comp ((R.neck α).chart.continuous.comp this)
  have : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  have : PreconnectedSpace (uIcc lvl z) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_uIcc
  have hT : IsPreconnected (range φ) := isPreconnected_range hφ
  have hTc : range φ ⊆ (H.event i).transition.trace.tubes.core := by
    rintro _ ⟨w, rfl⟩
    exact chartPt_mem_core_S14 R α w.1 w.2.1 _ (hseg w.2.1 w.2.2).1
  have hzmem : z ∈ uIcc lvl z := right_mem_uIcc
  have hx0 : chartPt_S14 R α y z h = φ (y, ⟨z, hzmem⟩) := rfl
  refine ⟨hTc ⟨(y, ⟨z, hzmem⟩), hx0.symm⟩, fun hret y' => ?_⟩
  have hlmem : lvl ∈ uIcc lvl z := left_mem_uIcc
  have hb : ((H.event i).transition.trace.tubes.coreBoundarySphere (α, σ) y').1 =
      φ (y', ⟨lvl, hlmem⟩) := by
    have hlev : ((TubeSystem.boundaryLevel σ : Icc (-2 : ℝ) 2) : ℝ) = lvl := by
      cases σ <;> simp [TubeSystem.boundaryLevel, lvl]
    change (H.event i).transition.trace.tubes.tube α (y', TubeSystem.boundaryLevel σ) = _
    rw [tube_eq_chartPt_S14 R α y' _ (TubeSystem.boundaryLevel σ).2]
    simp only [φ, hlev]
  have hrt := conn_retained_S14 (H.event i) hT hTc (x := chartPt_S14 R α y z h)
    (y := φ (y', ⟨lvl, hlmem⟩)) ⟨(y, ⟨z, hzmem⟩), hx0.symm⟩ ⟨(y', ⟨lvl, hlmem⟩), rfl⟩ hret
  obtain ⟨xx, hxx, hxe⟩ := hrt
  have : xx = (H.event i).transition.trace.tubes.coreBoundarySphere (α, σ) y' :=
    Subtype.ext (hxe.trans hb.symm)
  rw [← this]
  exact hxx

/-- The sign `±1` of the retained side of a retained boundary. -/
def lvl_S14 (b : (H.event i).RetainedBoundaryIndex) : ℝ := if b.1.2 then 1 else -1

theorem lvl_sq_S14 (b : (H.event i).RetainedBoundaryIndex) : lvl_S14 b * lvl_S14 b = 1 := by
  unfold lvl_S14; split_ifs <;> norm_num

theorem abs_lvl_S14 (b : (H.event i).RetainedBoundaryIndex) : |lvl_S14 b| = 1 := by
  unfold lvl_S14; split_ifs <;> norm_num

theorem inv_static_delta_S14 (b : (H.event i).RetainedBoundaryIndex) :
    (R.delta b.1.1)⁻¹ ≥ ((R.static b).delta)⁻¹ + 3 := by
  have hc := parameters.recenterConstant_ge_four
  have hd := R.recenter_delta b
  have hα := R.delta_pos b.1.1
  have hb1 := (R.static b).neck.delta_lt_one
  have hbpos := (R.static b).neck.delta_pos
  have h1 : 1 < ((R.static b).delta)⁻¹ := by
    rw [lt_inv_comm₀ one_pos hbpos]; simpa using hb1
  have hm : (R.delta b.1.1)⁻¹ = parameters.recenterConstant * ((R.static b).delta)⁻¹ := by
    rw [hd, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]
  rw [hm]
  nlinarith

theorem recenter_buf_S14 (b : (H.event i).RetainedBoundaryIndex)
    (q : neckBuffer (R.static b).delta) :
    (q.1.1, lvl_S14 b * (1 + q.1.2)) ∈ neckBuffer (R.delta b.1.1) := by
  have h3 := inv_static_delta_S14 R b
  have h1 : -((R.static b).delta)⁻¹ - 1 < q.1.2 := q.2.1
  have h2 : q.1.2 < ((R.static b).delta)⁻¹ + 1 := q.2.2
  have hl : |lvl_S14 b| = 1 := abs_lvl_S14 b
  have hab : |lvl_S14 b * (1 + q.1.2)| < ((R.static b).delta)⁻¹ + 2 := by
    rw [abs_mul, hl, one_mul]
    rw [abs_lt]; constructor <;> linarith
  rw [abs_lt] at hab
  constructor <;> linarith [hab.1, hab.2]

theorem static_chart_eq_S14 (b : (H.event i).RetainedBoundaryIndex)
    (q : neckBuffer (R.static b).delta) :
    (((R.static b).neck.chart q) : (H.event i).incoming.terminalRegularOpen).1 =
      chartPt_S14 R b.1.1 q.1.1 (lvl_S14 b * (1 + q.1.2)) (recenter_buf_S14 R b q) := by
  have := R.recenter_chart b q (recenter_buf_S14 R b q)
  unfold chartPt_S14
  rw [this]
  rfl

/-- Band points of a static cap are not off-tube retained points. -/
theorem band_not_offTube_S14 (b : (H.event i).RetainedBoundaryIndex)
    (q : neckBuffer (R.static b).delta) (hq : q ∈ capBandBuf_S14 (R.static b)) :
    ((R.static b).neck.chart q : (H.event i).incoming.terminalRegularOpen).1 ∉
      offTubeRetained_S14 (H.event i) := by
  rintro ⟨hnt, hret⟩
  rw [static_chart_eq_S14 R b q] at hnt hret
  set za : ℝ := lvl_S14 b * (1 + q.1.2) with hza
  have hq1 : q.1.2 ≤ 1 := hq.2
  have hbq := b.2
  have hb' : (H.event i).RetainedBoundary (b.1.1, b.1.2) := b.2
  have hos := R.one_retained_side b.1.1
  have hxbuf := recenter_buf_S14 R b q
  by_cases h2 : |za| ≤ 2
  · apply hnt
    have hz : za ∈ Icc (-2 : ℝ) 2 := abs_le.mp h2
    exact mem_iUnion.mpr ⟨b.1.1, ⟨(q.1.1, ⟨za, hz⟩), tube_eq_chartPt_S14 R b.1.1 q.1.1 za hz⟩⟩
  · rw [not_le] at h2
    cases hσ : b.1.2
    · have hl : lvl_S14 b = -1 := by simp [lvl_S14, hσ]
      have hza2 : 2 < za := by
        rcases lt_abs.mp h2 with h | h
        · exact h
        · exfalso; rw [hza, hl] at h; linarith
      have := (seg_S14 R b.1.1 true q.1.1 za hxbuf (fun _ => by linarith) (by simp)).2 hret
      rw [hσ] at hb'
      exact (hos.mp this) hb'
    · have hl : lvl_S14 b = 1 := by simp [lvl_S14, hσ]
      have hza2 : za < -2 := by
        rcases lt_abs.mp h2 with h | h
        · exfalso; rw [hza, hl] at h; linarith
        · linarith
      have := (seg_S14 R b.1.1 false q.1.1 za hxbuf (by simp) (fun _ => by linarith)).2 hret
      rw [hσ] at hb'
      exact (hos.mp hb') this

/-- The terminal-region band replaced by the static cap of the retained boundary `b`. -/
def band_S14 (b : (H.event i).RetainedBoundaryIndex) :
    Set (H.event i).incoming.terminalRegularOpen :=
  (R.static b).neck.chart '' capBandBuf_S14 (R.static b)

include R in
theorem retained_boundary_unique_S14 (b b' : (H.event i).RetainedBoundaryIndex)
    (h : b.1.1 = b'.1.1) : b = b' := by
  obtain ⟨⟨α, σ⟩, hb⟩ := b
  obtain ⟨⟨α', σ'⟩, hb'⟩ := b'
  simp only at h
  subst h
  have hos := R.one_retained_side α
  have : σ = σ' := by
    cases σ <;> cases σ'
    · rfl
    · exact absurd hb (hos.mp hb')
    · exact absurd hb' (hos.mp hb)
    · rfl
  subst this
  rfl

theorem band_disjoint_S14 {b b' : (H.event i).RetainedBoundaryIndex} (hne : b ≠ b') :
    Disjoint (band_S14 R b) (band_S14 R b') := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, _, rfl⟩ ⟨q', _, he⟩
  have hv := congrArg Subtype.val he
  rw [static_chart_eq_S14 R b q, static_chart_eq_S14 R b' q'] at hv
  by_cases hα : b.1.1 = b'.1.1
  · exact hne (retained_boundary_unique_S14 R b b' hα)
  · exact chartPt_ne_of_ne_S14 R hα hv.symm

theorem isCompact_band_S14 (b : (H.event i).RetainedBoundaryIndex) :
    IsCompact (band_S14 R b) :=
  (isCompact_capBandBuf_S14 (R.static b)).image (R.static b).neck.chart.continuous

theorem chartPt_congr_S14 (α : (H.event i).transition.trace.tubes.Index) (y : Sphere 2) {z z' : ℝ}
    (h : (y, z) ∈ neckBuffer (R.delta α)) (h' : (y, z') ∈ neckBuffer (R.delta α)) (hz : z = z') :
    chartPt_S14 R α y z h = chartPt_S14 R α y z' h' := by
  subst hz; rfl

/-- Cover of the output stage: every output point is the image of an old point off the tubes, or
lies in the image of the collapse of a static cap band. -/
theorem cover_S14 (q : (H.stage i.succ).Carrier) :
    (∃ z : (H.event i).old, z.1.1 ∉ tubeClosure_S14 (H.event i) ∧ (H.event i).oldOutput z = q) ∨
    ∃ b : (H.event i).RetainedBoundaryIndex,
      q ∈ (R.static b).inclusion '' ((R.static b).witness.collapse '' capBandDom_S14 (R.static b)) := by
  classical
  let tr := (H.event i).transition.trace
  have hex := tr.capping.exhaustive
  have hn : tr.capping.coreInclusion.1 = tr.capping.coreInclusion.1 := rfl
  have hmem : tr.presentation.symm (Sum.inl q) ∈ range tr.capping.coreInclusion ∪
      ⋃ b, range (tr.capping.cap b) := by rw [hex]; trivial
  have hpres : ∀ n, tr.presentation.symm (Sum.inl q) = n → tr.presentation n = Sum.inl q := by
    rintro n rfl; exact tr.presentation.apply_symm_apply _
  rcases hmem with ⟨x, hx⟩ | hmem
  · have hxq : tr.presentation (tr.capping.coreInclusion x) = Sum.inl q := hpres _ hx.symm
    have hxret : x ∈ tr.retainedCore := ⟨q, hxq⟩
    by_cases ht : x.1 ∈ tubeClosure_S14 (H.event i)
    · right
      obtain ⟨α, ⟨y, ⟨zz, hz⟩⟩, hxe⟩ := mem_iUnion.mp ht
      have hxe' : x.1 = chartPt_S14 R α y zz (R.tube_in_buffer α (y, ⟨zz, hz⟩)) := by
        rw [← tube_eq_chartPt_S14 R α y zz hz]; exact hxe.symm
      have h1 : 1 ≤ |zz| := by
        by_contra hlt
        rw [not_le, abs_lt] at hlt
        apply x.2
        exact mem_iUnion.mpr ⟨α, ⟨(y, ⟨zz, hz⟩), hlt, hxe⟩⟩
      have hretP : x.1 ∈ retainedPts_S14 (H.event i) := ⟨x, hxret, rfl⟩
      let σ : Bool := decide (1 ≤ zz)
      have hσ1 : σ = true → 1 ≤ zz := fun h => by simpa [σ] using h
      have hσ2 : σ = false → zz ≤ -1 := by
        intro h
        have : ¬ 1 ≤ zz := by simpa [σ] using h
        rcases le_or_gt 0 zz with h0 | h0
        · rw [abs_of_nonneg h0] at h1; exact absurd h1 this
        · rw [abs_of_neg h0] at h1; linarith
      have hseg := seg_S14 R α σ y zz (R.tube_in_buffer α (y, ⟨zz, hz⟩)) hσ1 hσ2
      have hb : (H.event i).RetainedBoundary (α, σ) := hseg.2 (hxe' ▸ hretP)
      let b : (H.event i).RetainedBoundaryIndex := ⟨(α, σ), hb⟩
      have hlvl : lvl_S14 b * zz ≥ 1 := by
        by_cases hs : σ = true
        · have : lvl_S14 b = 1 := by simp [lvl_S14, b, hs]
          rw [this]; linarith [hσ1 hs]
        · have hs' : σ = false := by simpa using hs
          have : lvl_S14 b = -1 := by simp [lvl_S14, b, hs']
          rw [this]; linarith [hσ2 hs']
      have hlvl2 : lvl_S14 b * zz ≤ 2 := by
        have habs : |lvl_S14 b * zz| = |zz| := by rw [abs_mul, abs_lvl_S14, one_mul]
        have : |zz| ≤ 2 := abs_le.mpr hz
        rw [← habs] at this
        exact (abs_le.mp this).2
      have hδ1 := one_lt_inv_delta_S14 (R.static b)
      let x' : neckRetainedCollar (R.static b).delta :=
        ⟨(y, lvl_S14 b * zz - 1), by linarith, by linarith⟩
      have hx'buf : x'.1 ∈ neckBuffer (R.static b).delta := by
        have := inv_pos.mpr (R.static b).neck.delta_pos
        exact ⟨by have := x'.2.1; linarith, by have := x'.2.2; linarith⟩
      have hpt : ((R.static b).retainedPoint x').1.1 = x.1 := by
        rw [(R.static b).retained_point_eq x' hx'buf]
        have := static_chart_eq_S14 R b ⟨x'.1, hx'buf⟩
        rw [this, hxe']
        apply chartPt_congr_S14
        have := lvl_sq_S14 b
        change lvl_S14 b * (1 + (lvl_S14 b * zz - 1)) = zz
        calc lvl_S14 b * (1 + (lvl_S14 b * zz - 1)) = (lvl_S14 b * lvl_S14 b) * zz := by ring
          _ = zz := by rw [this, one_mul]
      have hxx : ((R.static b).retainedPoint x').1 = x := Subtype.ext hpt
      have hre := (R.static b).retained_eq x'
      rw [hxx, hxq] at hre
      have hqe : q = (R.static b).inclusion ((R.static b).witness.retained x') :=
        Sum.inl.inj hre
      refine ⟨b, ?_⟩
      rw [hqe]
      exact ⟨_, retained_mem_collapse_image_S14 (R.static b) x' (by
        change lvl_S14 b * zz - 1 ≤ 1; linarith), rfl⟩
    · left
      have hxold : x ∈ (H.event i).old := (H.event i).old_contains_outside x hxret (fun α hα => by
        obtain ⟨w, _, hw⟩ := hα
        exact ht (mem_iUnion.mpr ⟨α, w, hw⟩))
      refine ⟨⟨x, hxold⟩, ht, ?_⟩
      have := (H.event i).oldOutput_eq ⟨x, hxold⟩
      rw [hxq] at this
      exact (Sum.inl.inj this).symm
  · obtain ⟨b', hb'⟩ := mem_iUnion.mp hmem
    obtain ⟨p, hp⟩ := hb'
    have hpq : tr.presentation (tr.capping.cap b' p) = Sum.inl q := hpres _ hp.symm
    have : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
    have hpc : IsPreconnected (tr.presentation '' range (tr.capping.cap b')) :=
      (isPreconnected_range (tr.capping.cap b').continuous).image _
        tr.presentation.continuous.continuousOn
    have hcases := hpc.subset_or_subset isOpen_range_inl isOpen_range_inr
      (Set.disjoint_left.mpr (by rintro _ ⟨a, rfl⟩ ⟨b, hb⟩; cases hb))
      (by rw [Set.range_inl_union_range_inr]; exact subset_univ _)
    have hleft : tr.presentation '' range (tr.capping.cap b') ⊆ range (Sum.inl : _ → _ ⊕ _) := by
      rcases hcases with h | h
      · exact h
      · exfalso
        obtain ⟨q', hq'⟩ := h ⟨_, ⟨p, rfl⟩, rfl⟩
        rw [hpq] at hq'; cases hq'
    have hb : (H.event i).RetainedBoundary b' := by
      intro y
      have hbd := tr.capping.boundary_eq b' ((tr.capping.attaching b').symm y)
      rw [Homeomorph.apply_symm_apply] at hbd
      have hm : tr.presentation (tr.capping.cap b'
          (sphereToThreeBall ((tr.capping.attaching b').symm y))) ∈
          tr.presentation '' range (tr.capping.cap b') := ⟨_, mem_range_self _, rfl⟩
      obtain ⟨q', hq'⟩ := hleft hm
      exact ⟨q', by rw [← hbd]; exact hq'.symm⟩
    right
    refine ⟨⟨b', hb⟩, ?_⟩
    have hcap := (R.static ⟨b', hb⟩).cap_eq p
    change tr.presentation (tr.capping.cap b' p) = _ at hcap
    rw [hpq] at hcap
    have hqe : q = (R.static ⟨b', hb⟩).inclusion ((R.static ⟨b', hb⟩).witness.cap p) :=
      Sum.inl.inj hcap
    rw [hqe]
    exact ⟨_, range_cap_subset_collapse_image_S14 (R.static ⟨b', hb⟩) (mem_range_self p), rfl⟩

end GC.LongTime.Ch12
