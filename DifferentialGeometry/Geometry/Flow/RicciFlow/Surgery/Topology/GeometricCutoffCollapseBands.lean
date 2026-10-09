import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace StaticCapWitness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
  {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck h δ k} {fixed : StaticCapScaffold}
  {D : ℝ} {m : ℕ} {ε : ℝ} (w : StaticCapWitness neck fixed D m ε)

theorem tipCoordinate_neg : w.tipCoordinate < 0 := by
  have htip := w.tipCoordinate_upper
  have hcollar := fixed.collar_pos
  have hL := standardCapL_pos
  linarith

/-- The closed parameter band of the supplied collapse, including its tip and seam. -/
abbrev CollapseBandDomain := Sphere 2 × Icc w.tipCoordinate 0

private theorem collapseBandParameter_mem (x : w.CollapseBandDomain) :
    -δ⁻¹ < (x.2 : ℝ) ∧ (x.2 : ℝ) < δ⁻¹ :=
  ⟨lt_of_lt_of_le w.tipCoordinate_lower x.2.2.1,
    lt_of_le_of_lt x.2.2.2 (inv_pos.mpr neck.delta_pos)⟩

def collapseBandParameter : C(w.CollapseBandDomain, neckCentralDomain δ) where
  toFun x := ⟨⟨(x.1, x.2.1), by
    obtain ⟨hl, hr⟩ := w.collapseBandParameter_mem x
    exact ⟨by linarith, by linarith⟩⟩, w.collapseBandParameter_mem x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

@[simp] theorem collapseBandParameter_coe (x : w.CollapseBandDomain) :
    (w.collapseBandParameter x).1.1 = (x.1, x.2.1) := rfl

def collapseBandSource : C(w.CollapseBandDomain, M) :=
  neck.chart.comp ⟨fun x => (w.collapseBandParameter x).1,
    continuous_subtype_val.comp w.collapseBandParameter.continuous⟩

/-- The attaching seam is omitted from the source pieces used in volume sums. -/
def negativeBandParameters : Set w.CollapseBandDomain := {x | (x.2 : ℝ) < 0}

def negativeCollapseBand : Set M := w.collapseBandSource '' w.negativeBandParameters

/-- Compact parameter pieces; early pieces may be empty. -/
def compactBandParameters (n : ℕ) : Set w.CollapseBandDomain :=
  {x | (x.2 : ℝ) ≤ -(1 / ((n : ℝ) + 1))}

theorem isCompact_compactBandParameters (n : ℕ) : IsCompact (w.compactBandParameters n) :=
  (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact

theorem compactBandParameters_mono : Monotone w.compactBandParameters := by
  intro n j hnj x hx
  have hden : (n : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnj 1
  exact hx.trans (neg_le_neg (one_div_le_one_div_of_le (by positivity) hden))

theorem iUnion_compactBandParameters :
    (⋃ n : ℕ, w.compactBandParameters n) = w.negativeBandParameters := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    change (x.2 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) at hn
    change (x.2 : ℝ) < 0
    linarith
  · intro hx
    change (x.2 : ℝ) < 0 at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (show (0 : ℝ) < -(x.2 : ℝ) from neg_pos.mpr hx)
    exact mem_iUnion.mpr ⟨n, by change (x.2 : ℝ) ≤ -(1 / ((n : ℝ) + 1)); linarith⟩

theorem isCompact_collapseBandSource_range : IsCompact (range w.collapseBandSource) :=
  isCompact_range w.collapseBandSource.continuous

theorem isCompact_collapseBandSource_piece (n : ℕ) :
    IsCompact (w.collapseBandSource '' w.compactBandParameters n) :=
  (w.isCompact_compactBandParameters n).image w.collapseBandSource.continuous

theorem negativeCollapseBand_eq_iUnion :
    w.negativeCollapseBand = ⋃ n : ℕ, w.collapseBandSource '' w.compactBandParameters n := by
  rw [negativeCollapseBand, ← w.iUnion_compactBandParameters, image_iUnion]

/-- Radial surjectivity uses only the actual static witness, without a comparison support. -/
theorem exists_collapseBandParameter_collapse_eq_cap (x : ThreeBall) :
    ∃ y : w.CollapseBandDomain, w.collapse (w.collapseBandParameter y) = w.cap x := by
  have hmem : w.cap x ∈ range w.capChart := by
    rw [w.capChart_range]
    exact mem_range_self x
  obtain ⟨x₀, hx₀⟩ := hmem
  have hnorm : ‖x₀.1‖ ≤ standardCapL := by
    simpa [standardCapClosedCore, Metric.mem_closedBall, dist_eq_norm] using x₀.2
  by_cases hzero : x₀.1 = 0
  · refine ⟨(neck.sphereMark, ⟨w.tipCoordinate, le_rfl, w.tipCoordinate_neg.le⟩), ?_⟩
    have hcap : w.cap x = w.tip := by
      rw [← hx₀]
      have heq : x₀ = (⟨0, by simpa [hzero] using x₀.2⟩ : standardCapClosedCore) :=
        Subtype.ext hzero
      rw [heq]
      exact w.capChart_tip _
    rw [hcap]
    exact w.collapse_tip _ le_rfl
  · have hpos : 0 < ‖x₀.1‖ := norm_pos_iff.mpr hzero
    let y : Sphere 2 := ⟨(‖x₀.1‖⁻¹ : ℝ) • x₀.1, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x₀.1))]
      exact inv_mul_cancel₀ (ne_of_gt hpos)⟩
    obtain ⟨z, hz, hrad⟩ : ∃ z ∈ Icc w.tipCoordinate 0, w.radial z = ‖x₀.1‖ := by
      apply intermediate_value_Icc w.tipCoordinate_neg.le w.radial_continuous
      rw [w.radial_tip, w.radial_boundary]
      exact ⟨norm_nonneg _, hnorm⟩
    have hztip : w.tipCoordinate < z := by
      apply lt_of_le_of_ne hz.1
      intro heq
      rw [← heq, w.radial_tip] at hrad
      exact (ne_of_gt hpos) hrad.symm
    have hsmul : w.radial z • y.1 = x₀.1 := by
      rw [hrad]
      exact smul_inv_smul₀ (ne_of_gt hpos) x₀.1
    have hcore : w.radial z • y.1 ∈ standardCapClosedCore := by
      rw [hsmul]
      exact x₀.2
    refine ⟨(y, ⟨z, hz⟩), ?_⟩
    have hcollapse :
        w.collapse (w.collapseBandParameter (y, ⟨z, hz⟩)) =
          w.capChart ⟨w.radial z • y.1, hcore⟩ :=
      w.collapse_radial (w.collapseBandParameter (y, ⟨z, hz⟩)) hztip hz.2 hcore
    exact hcollapse.trans ((congrArg w.capChart (Subtype.ext hsmul)).trans hx₀)

end StaticCapWitness

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

/-- The collapse into the original event output, with its original static inclusion. -/
def collapseBandOutput (b : (H.event i).RetainedBoundaryIndex) :
    C((G.static b).witness.CollapseBandDomain, (H.stage i.succ).Carrier) :=
  (G.static b).inclusion.comp
    ((G.static b).witness.collapse.comp (G.static b).witness.collapseBandParameter)

def negativeCollapseImage (b : (H.event i).RetainedBoundaryIndex) :
    Set (H.stage i.succ).Carrier :=
  G.collapseBandOutput b '' (G.static b).witness.negativeBandParameters

theorem isCompact_collapseBandOutput_piece (b : (H.event i).RetainedBoundaryIndex) (n : ℕ) :
    IsCompact (G.collapseBandOutput b '' (G.static b).witness.compactBandParameters n) :=
  ((G.static b).witness.isCompact_compactBandParameters n).image
    (G.collapseBandOutput b).continuous

theorem negativeCollapseImage_eq_iUnion (b : (H.event i).RetainedBoundaryIndex) :
    G.negativeCollapseImage b =
      ⋃ n : ℕ, G.collapseBandOutput b '' (G.static b).witness.compactBandParameters n := by
  rw [negativeCollapseImage, ← (G.static b).witness.iUnion_compactBandParameters, image_iUnion]

theorem cap_range_subset_oldOutput_union_negativeCollapseImage
    (b : (H.event i).RetainedBoundaryIndex) :
    range (fun x : ThreeBall => (G.static b).inclusion ((G.static b).witness.cap x)) ⊆
      range (H.event i).oldOutput ∪ G.negativeCollapseImage b := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (G.static b).witness.exists_collapseBandParameter_collapse_eq_cap x
  by_cases hneg : (y.2 : ℝ) < 0
  · exact Or.inr ⟨y, hneg, congrArg (G.static b).inclusion hy⟩
  · have hnonneg : 0 ≤ (y.2 : ℝ) := le_of_not_gt hneg
    let r : neckRetainedCollar (G.static b).delta :=
      ⟨(y.1, y.2.1), hnonneg,
        lt_of_le_of_lt y.2.2.2 (inv_pos.mpr (G.static b).neck.delta_pos)⟩
    let a : (H.event i).old := ⟨(G.static b).retainedPoint r,
      by rw [G.old_eq_retained]; exact ((G.static b).retainedPoint r).2⟩
    have heq : (H.event i).oldOutput a =
        (G.static b).inclusion ((G.static b).witness.retained r) :=
      Sum.inl.inj (((H.event i).oldOutput_eq a).symm.trans ((G.static b).retained_eq r))
    refine Or.inl ⟨a, heq.trans ?_⟩
    apply congrArg (G.static b).inclusion
    exact ((G.static b).witness.collapse_retained
      ((G.static b).witness.collapseBandParameter y) hnonneg).symm.trans hy

theorem disjoint_negativeCollapseBand_oldTerminal (b : (H.event i).RetainedBoundaryIndex) :
    Disjoint (G.static b).witness.negativeCollapseBand (range (H.event i).oldTerminal) := by
  refine disjoint_left.mpr ?_
  rintro q ⟨x, hx, hxq⟩ ⟨a, haq⟩
  have hcoord : ((G.static b).witness.collapseBandParameter x).1.1.2 < 0 := hx
  have hpoint : (a.1.1 : (H.stage i.castSucc).Carrier) =
      ((G.static b).neck.chart ((G.static b).witness.collapseBandParameter x).1).1 :=
    ((H.event i).oldTerminal_eq a).symm.trans
      (congrArg Subtype.val (haq.trans hxq.symm))
  have hret : a.1 ∈ (H.event i).transition.trace.retainedCore :=
    (H.event i).old_retained a.2
  exact G.staticNeckChart_notMem_retainedCore_of_coordinate_negative b b.2
    ((G.static b).witness.collapseBandParameter x).1 hcoord a.1 hpoint hret

private theorem collapseBandSource_mem_original_neck (b : (H.event i).RetainedBoundaryIndex)
    (x : (G.static b).witness.CollapseBandDomain) :
    (G.static b).witness.collapseBandSource x ∈ range (G.neck b.1.1).chart := by
  let z := ((G.static b).witness.collapseBandParameter x).1
  refine ⟨⟨(z.1.1, (if b.1.2 then 1 else -1) * (1 + z.1.2)),
    G.recenter_in_buffer b z⟩, ?_⟩
  exact (G.recenter_chart b z (G.recenter_in_buffer b z)).symm

theorem pairwise_disjoint_negativeCollapseBand :
    Pairwise fun b d : (H.event i).RetainedBoundaryIndex =>
      Disjoint (G.static b).witness.negativeCollapseBand
        (G.static d).witness.negativeCollapseBand := by
  intro b d hbd
  have hidx : b.1.1 ≠ d.1.1 := by
    intro heq
    apply hbd
    apply Subtype.ext
    exact Prod.ext heq (retainedBoundary_side_eq G b.2 (heq.symm ▸ d.2))
  refine disjoint_left.mpr ?_
  rintro q ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hb := G.collapseBandSource_mem_original_neck b x
  have hd := G.collapseBandSource_mem_original_neck d y
  rw [hx] at hb
  rw [hy] at hd
  exact disjoint_left.mp (G.buffer_disjoint hidx) hb hd

/-- A compact subset of the actual terminal regular region containing every source piece. -/
def collapseBandHull : Set (H.event i).incoming.terminalRegularOpen :=
  range (H.event i).oldTerminal ∪
    ⋃ b : (H.event i).RetainedBoundaryIndex, range (G.static b).witness.collapseBandSource

theorem isCompact_collapseBandHull : IsCompact G.collapseBandHull := by
  let : CompactSpace (H.event i).old := isCompact_iff_compactSpace.mp (H.event i).old_compact
  exact (isCompact_range (H.event i).oldTerminal.continuous).union
    (isCompact_iUnion fun b => (G.static b).witness.isCompact_collapseBandSource_range)

theorem oldTerminal_subset_collapseBandHull : range (H.event i).oldTerminal ⊆ G.collapseBandHull :=
  subset_union_left

theorem negativeCollapseBand_subset_collapseBandHull (b : (H.event i).RetainedBoundaryIndex) :
    (G.static b).witness.negativeCollapseBand ⊆ G.collapseBandHull := by
  rintro _ ⟨x, _, rfl⟩
  exact Or.inr (mem_iUnion.mpr ⟨b, mem_range_self x⟩)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
