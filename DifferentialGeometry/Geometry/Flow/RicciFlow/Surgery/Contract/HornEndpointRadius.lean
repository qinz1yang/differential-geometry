import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCylinderEscape
import DifferentialGeometry.Geometry.Metric.Distance.ConnectedLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCoordinates
import DifferentialGeometry.Topology.SphereSeparation.ComplementPair

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.SphereSeparation

universe u
variable {D : OneStepIncoming.{u}} {eps Lambda : ℝ} (P : TerminalCorePresentation D eps Lambda)

theorem exists_outer_horn_point_at_distance_in_side
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (U : Set positiveHornDomain) (hU : IsPreconnected U)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ closure U)
    {A : ℝ} (hA : 0 < A)
    (hcompact : IsCompact (riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) A))
    (T : ℝ) (htail : ∀ z : positiveHornDomain, T < z.val.2 → z ∈ U) :
    ∃ z ∈ U, riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.positiveHornMap c e z) = ENNReal.ofReal A := by
  obtain ⟨t, ht, hT, hfar, _⟩ := P.exists_horn_point_distance_gt_of_isCompact_closedBall
    c e y hs.le A (max T 0) hcompact
  have htpos : 0 < t := (le_max_right T 0).trans_lt hT
  let b : positiveHornDomain := ⟨(y, t), mem_univ _, htpos⟩
  have hb : b ∈ U := htail b ((le_max_left T 0).trans_lt hT)
  have hmap : Continuous (P.positiveHornMap c e) :=
    (P.positiveHornMap_local c e).contMDiff.continuous
  have hnear : riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.positiveHornMap c e ⟨(y, s), mem_univ _, hs⟩) < ENNReal.ofReal A := by
    change riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.horn c e (y, s)) < ENNReal.ofReal A
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hA
  have haimage : P.positiveHornMap c e ⟨(y, s), mem_univ _, hs⟩ ∈
      closure (P.positiveHornMap c e '' U) :=
    hmap.continuousOn.image_closure ⟨_, hcenter, rfl⟩
  obtain ⟨z, ⟨w, hw, rfl⟩, hdist⟩ :=
    exists_riemannianEDistOf_eq_of_isPreconnected_of_closure D.terminal.metric
      (P.horn c e (y, s)) (hU.image (P.positiveHornMap c e) hmap.continuousOn)
      haimage (mem_image_of_mem _ hb) hnear hfar.le
  exact ⟨w, hw, hdist⟩

theorem exists_inner_horn_point_at_distance_in_side
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (U : Set positiveHornDomain) (hU : IsPreconnected U)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ closure U)
    {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (hbase : ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, 0)))
    (hside : ∀ z : positiveHornDomain, z.val.2 < T → z ∈ U) :
    ∃ z ∈ U, riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.positiveHornMap c e z) = ENNReal.ofReal A := by
  have hdist : Continuous (fun z => riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) z) := continuous_riemannianEDist D.terminal.metric _
  have hhorn : ContinuousWithinAt (fun t : ℝ => P.horn c e (y, t)) (Ici 0) 0 :=
    ((P.horn_smooth c e).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨mem_univ _, ht⟩)) 0 (by simp)
  have hfar : {t : ℝ | ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, t))} ∈ 𝓝[Ici 0] 0 :=
    (hdist.continuousAt.comp_continuousWithinAt hhorn)
      (isOpen_Ioi.mem_nhds hbase)
  have hfarPos : {t : ℝ | ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, t))} ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_mono _ Ioi_subset_Ici_self hfar
  have hfarEvent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
        (P.horn c e (y, s)) (P.horn c e (y, t)) := hfarPos
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hbelow : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  obtain ⟨t, hfarT, htpos, htT⟩ := (hfarEvent.and (hpositive.and hbelow)).exists
  let b : positiveHornDomain := ⟨(y, t), mem_univ _, htpos⟩
  have hb : b ∈ U := hside b htT
  have hmap : Continuous (P.positiveHornMap c e) :=
    (P.positiveHornMap_local c e).contMDiff.continuous
  have hnear : riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.positiveHornMap c e ⟨(y, s), mem_univ _, hs⟩) < ENNReal.ofReal A := by
    change riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
      (P.horn c e (y, s)) < ENNReal.ofReal A
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hA
  have haimage : P.positiveHornMap c e ⟨(y, s), mem_univ _, hs⟩ ∈
      closure (P.positiveHornMap c e '' U) :=
    hmap.continuousOn.image_closure ⟨_, hcenter, rfl⟩
  obtain ⟨z, ⟨w, hw, rfl⟩, hlevel⟩ :=
    exists_riemannianEDistOf_eq_of_isPreconnected_of_closure D.terminal.metric
      (P.horn c e (y, s)) (hU.image (P.positiveHornMap c e) hmap.continuousOn)
      haimage (mem_image_of_mem _ hb) hnear hfarT.le
  exact ⟨w, hw, hlevel⟩

theorem exists_horn_side_points_at_distance
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set positiveHornDomain} (d : ComplementPair S)
    (hleft : S ⊆ closure d.left) (hright : S ⊆ closure d.right)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ S)
    {A Tlo Thi : ℝ} (hA : 0 < A) (hTlo : 0 < Tlo)
    (hcompact : IsCompact (riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) A))
    (hbase : ENNReal.ofReal A < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, 0)))
    (hlow : ∀ z : positiveHornDomain, z.val.2 < Tlo → z ∈ d.left)
    (hhigh : ∀ z : positiveHornDomain, Thi < z.val.2 → z ∈ d.right) :
    ∃ a b : positiveHornDomain, a ∈ d.left ∧ b ∈ d.right ∧
      riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
        (P.positiveHornMap c e a) = ENNReal.ofReal A ∧
      riemannianEDistOf D.terminal.metric (P.horn c e (y, s))
        (P.positiveHornMap c e b) = ENNReal.ofReal A := by
  obtain ⟨a, ha, hdistA⟩ := P.exists_inner_horn_point_at_distance_in_side c e d.left
    d.isConnected_left.isPreconnected y hs (hleft hcenter) hA hTlo hbase hlow
  obtain ⟨b, hb, hdistB⟩ := P.exists_outer_horn_point_at_distance_in_side c e d.right
    d.isConnected_right.isPreconnected y hs (hright hcenter) hA hcompact Thi hhigh
  exact ⟨a, b, ha, hb, hdistA, hdistB⟩

theorem exists_horn_side_points_at_scaled_distance
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {S : Set positiveHornDomain} (d : ComplementPair S)
    (hleft : S ⊆ closure d.left) (hright : S ⊆ closure d.right)
    (y : Sphere 2) {s : ℝ} (hs : 0 < s)
    (hcenter : (⟨(y, s), mem_univ _, hs⟩ : positiveHornDomain) ∈ S)
    (Q : ℝ) (hQ : 0 < Q) {A Tlo Thi : ℝ} (hA : 0 < A) (hTlo : 0 < Tlo)
    (hcompact : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) A))
    (hbase : ENNReal.ofReal A < riemannianEDistOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) (P.horn c e (y, 0)))
    (hlow : ∀ z : positiveHornDomain, z.val.2 < Tlo → z ∈ d.left)
    (hhigh : ∀ z : positiveHornDomain, Thi < z.val.2 → z ∈ d.right) :
    ∃ a b : positiveHornDomain, a ∈ d.left ∧ b ∈ d.right ∧
      riemannianEDistOf (scaleMetric Q hQ D.terminal.metric) (P.horn c e (y, s))
        (P.positiveHornMap c e a) = ENNReal.ofReal A ∧
      riemannianEDistOf (scaleMetric Q hQ D.terminal.metric) (P.horn c e (y, s))
        (P.positiveHornMap c e b) = ENNReal.ofReal A := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hmul : Real.sqrt Q * (A / Real.sqrt Q) = A := mul_div_cancel₀ _ hsqrt.ne'
  have hball : riemannianClosedBallOf (scaleMetric Q hQ D.terminal.metric)
      (P.horn c e (y, s)) A =
      riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) (A / Real.sqrt Q) := by
    simpa only [hmul] using
      riemannianClosedBallOf_scaleMetric Q hQ D.terminal.metric (P.horn c e (y, s))
        (A / Real.sqrt Q)
  have hbasePhysical : ENNReal.ofReal (A / Real.sqrt Q) < riemannianEDistOf D.terminal.metric
      (P.horn c e (y, s)) (P.horn c e (y, 0)) := by
    have hzero : ENNReal.ofReal (Real.sqrt Q) ≠ 0 := (ENNReal.ofReal_pos.mpr hsqrt).ne'
    apply (ENNReal.mul_lt_mul_iff_right hzero ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.ofReal_mul hsqrt.le, hmul, ← edistOf_scale]
    exact hbase
  obtain ⟨a, b, ha, hb, hdistA, hdistB⟩ := P.exists_horn_side_points_at_distance
    c e d hleft hright y hs hcenter (div_pos hA hsqrt) hTlo (hball ▸ hcompact)
      hbasePhysical hlow hhigh
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [edistOf_scale, hdistA, ← ENNReal.ofReal_mul hsqrt.le, hmul]
  · rw [edistOf_scale, hdistB, ← ENNReal.ofReal_mul hsqrt.le, hmul]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
