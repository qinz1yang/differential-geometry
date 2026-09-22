import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar
import DifferentialGeometry.Topology.ContinuousMap.ClosedEmbeddingExtension
import DifferentialGeometry.Topology.Homeomorph.QuotientDescent
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
noncomputable section
open Set Metric Function
open scoped ContDiff

section

namespace DifferentialGeometry.Topology.SelfAttachment

private def collarStretch (r : ℝ) : ℝ :=
  r - (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.smoothTransition (4 * (r - 3 / 2))

private theorem collarStretch_of_le {r : ℝ} (h : r ≤ 3 / 2) : collarStretch r = r - 1 / 2 := by
  rw [collarStretch, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

private theorem collarStretch_of_ge {r : ℝ} (h : 7 / 4 ≤ r) : collarStretch r = r := by
  rw [collarStretch, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

private theorem collarStretch_strictMono : StrictMono collarStretch := by
  intro x y hxy
  have h := Real.smoothTransition.monotone (show 4 * (x - 3 / 2) ≤ 4 * (y - 3 / 2) by linarith)
  dsimp [collarStretch]
  linarith

private theorem collarStretch_contDiff : ContDiff ℝ ∞ collarStretch := by
  unfold collarStretch
  exact (contDiff_id.sub contDiff_const).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))))

private theorem collarStretch_continuous : Continuous collarStretch :=
    collarStretch_contDiff.continuous

@[simp] private theorem collarStretch_one : collarStretch 1 = 1 / 2 := by
  rw [collarStretch_of_le (by norm_num)]
  norm_num

@[simp] private theorem collarStretch_two : collarStretch 2 = 2 := collarStretch_of_ge (by norm_num)

private theorem collarStretch_mem_Icc {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) :
    collarStretch r ∈ Icc (1 / 2 : ℝ) 2 := by
  have h1 := collarStretch_strictMono.monotone hr.1
  have h2 := collarStretch_strictMono.monotone hr.2
  exact ⟨collarStretch_one ▸ h1, collarStretch_two ▸ h2⟩

private def collarStretchHomeomorph : Icc (1 : ℝ) 2 ≃ₜ Icc (1 / 2 : ℝ) 2 := by
  let f : Icc (1 : ℝ) 2 → Icc (1 / 2 : ℝ) 2 :=
    fun r => ⟨collarStretch r, collarStretch_mem_Icc r.property⟩
  have hf : Continuous f :=
    (collarStretch_continuous.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (collarStretch_strictMono.injective (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    intro y
    have himage := collarStretch_continuous.image_Icc_of_strictMono collarStretch_strictMono
      (a := (1 : ℝ)) (b := 2)
    have hy : y.val ∈ collarStretch '' Icc (1 : ℝ) 2 := by
      rw [himage, collarStretch_one, collarStretch_two]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact IsHomeomorph.homeomorph f (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hi, hs⟩)

@[simp] private theorem collarStretchHomeomorph_apply (r : Icc (1 : ℝ) 2) :
    (collarStretchHomeomorph r).val = collarStretch r := rfl

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev BandCollarMapsModel := EuclideanSpace ℝ (Fin 3)
private abbrev BandCollarMapsDomain := Sphere (n := 3) × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private def stretchedFirstCore (p : BandCollarMapsDomain) : c.DoublePunctured d :=
  c.firstRadialMap d hdisj p.1 (max 1 (collarStretch p.2))
    ⟨le_max_left _ _, max_le (by norm_num) (collarStretch_mem_Icc p.2.property).2⟩

private def stretchedSecondCore (p : BandCollarMapsDomain) : c.DoublePunctured d :=
  c.secondRadialMap d hdisj p.1 (max 1 (collarStretch p.2))
    ⟨le_max_left _ _, max_le (by norm_num) (collarStretch_mem_Icc p.2.property).2⟩

private def stretchedLowerBand (p : BandCollarMapsDomain) : Band (n := 3) :=
  (p.1, ⟨max 0 (1 - collarStretch p.2), le_max_left _ _,
    max_le (by norm_num) (by linarith [(collarStretch_mem_Icc p.2.property).1])⟩)

private def stretchedUpperBand (p : BandCollarMapsDomain) : Band (n := 3) :=
  (a.symm p.1, ⟨min 1 (collarStretch p.2),
    le_min (by norm_num) (by linarith [(collarStretch_mem_Icc p.2.property).1]), min_le_left _ _⟩)

def stretchedLowerCollar (p : BandCollarMapsDomain) : Quotient c d hdisj a :=
  if collarStretch p.2 ≤ 1 then bandInclusion c d hdisj a (stretchedLowerBand p)
  else coreInclusion c d hdisj a (stretchedFirstCore c d hdisj p)

def stretchedUpperCollar (p : BandCollarMapsDomain) : Quotient c d hdisj a :=
  if collarStretch p.2 ≤ 1 then bandInclusion c d hdisj a (stretchedUpperBand a p)
  else coreInclusion c d hdisj a (stretchedSecondCore c d hdisj p)

theorem continuous_stretchedLowerCollar : Continuous (stretchedLowerCollar c d hdisj a) := by
  have ht : Continuous (fun p : BandCollarMapsDomain => collarStretch p.2) :=
    collarStretch_continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hcore : Continuous (stretchedFirstCore c d hdisj) :=
    c.continuous_firstRadialMap d hdisj Prod.fst _ continuous_fst (continuous_const.max ht) _
  have hband : Continuous stretchedLowerBand :=
    continuous_fst.prodMk ((continuous_const.max (continuous_const.sub ht)).subtype_mk _)
  apply continuous_if_le ht continuous_const
    ((continuous_bandInclusion c d hdisj a).comp hband).continuousOn
    ((continuous_coreInclusion c d hdisj a).comp hcore).continuousOn
  intro p hp
  have hc : stretchedFirstCore c d hdisj p = c.firstBoundaryMap d hdisj p.1 := by
    apply Subtype.ext
    simp only [stretchedFirstCore, BallChart.firstRadialMap_val, BallChart.firstBoundaryMap_val,
      hp, max_self, one_smul]
  have hb : stretchedLowerBand p = boundaryInclusion (false, p.1) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    simp only [stretchedLowerBand, boundaryInclusion, hp]
    norm_num
  exact (congrArg (bandInclusion c d hdisj a) hb).trans
    ((seam_eq c d hdisj a (false, p.1)).trans
      (congrArg (coreInclusion c d hdisj a) hc.symm))

theorem continuous_stretchedUpperCollar : Continuous (stretchedUpperCollar c d hdisj a) := by
  have ht : Continuous (fun p : BandCollarMapsDomain => collarStretch p.2) :=
    collarStretch_continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hcore : Continuous (stretchedSecondCore c d hdisj) :=
    c.continuous_secondRadialMap d hdisj Prod.fst _ continuous_fst (continuous_const.max ht) _
  have hband : Continuous (stretchedUpperBand a) :=
    (a.symm.continuous.comp continuous_fst).prodMk
      ((continuous_const.min ht).subtype_mk _)
  apply continuous_if_le ht continuous_const
    ((continuous_bandInclusion c d hdisj a).comp hband).continuousOn
    ((continuous_coreInclusion c d hdisj a).comp hcore).continuousOn
  intro p hp
  have hc : stretchedSecondCore c d hdisj p = c.secondBoundaryMap d hdisj p.1 := by
    apply Subtype.ext
    simp only [stretchedSecondCore, BallChart.secondRadialMap_val, BallChart.secondBoundaryMap_val,
      hp, max_self, one_smul]
  have hb : stretchedUpperBand a p = boundaryInclusion (true, a.symm p.1) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    simp only [stretchedUpperBand, boundaryInclusion, hp, min_self]
  have hs := seam_eq c d hdisj a (true, a.symm p.1)
  change bandInclusion c d hdisj a (boundaryInclusion (true, a.symm p.1)) =
    coreInclusion c d hdisj a (c.secondBoundaryMap d hdisj (a (a.symm p.1))) at hs
  rw [a.apply_symm_apply] at hs
  exact (congrArg (bandInclusion c d hdisj a) hb).trans
    (hs.trans (congrArg (coreInclusion c d hdisj a) hc.symm))

theorem stretchedLowerCollar_one (z : Sphere (n := 3)) :
    stretchedLowerCollar c d hdisj a (z, ⟨1, by norm_num⟩) =
      bandInclusion c d hdisj a (z, ⟨1 / 2, by norm_num⟩) := by
  simp only [stretchedLowerCollar, collarStretch_one]
  rw [if_pos (by norm_num)]
  apply congrArg (bandInclusion c d hdisj a)
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  norm_num [stretchedLowerBand]

theorem stretchedUpperCollar_one (z : Sphere (n := 3)) :
    stretchedUpperCollar c d hdisj a (a z, ⟨1, by norm_num⟩) =
      bandInclusion c d hdisj a (z, ⟨1 / 2, by norm_num⟩) := by
  simp only [stretchedUpperCollar, collarStretch_one]
  rw [if_pos (by norm_num)]
  apply congrArg (bandInclusion c d hdisj a)
  apply Prod.ext (a.symm_apply_apply z)
  apply Subtype.ext
  norm_num [stretchedUpperBand]

theorem stretchedLowerCollar_of_ge (p : BandCollarMapsDomain) (hp : 7 / 4 ≤ (p.2 : ℝ)) :
    stretchedLowerCollar c d hdisj a p =
      coreInclusion c d hdisj a (c.firstRadialMap d hdisj p.1 p.2 p.2.property) := by
  rw [stretchedLowerCollar, collarStretch_of_ge hp, if_neg (by linarith)]
  apply congrArg (coreInclusion c d hdisj a)
  apply Subtype.ext
  simp only [stretchedFirstCore, BallChart.firstRadialMap_val, collarStretch_of_ge hp,
    max_eq_right p.2.property.1]

theorem stretchedUpperCollar_of_ge (p : BandCollarMapsDomain) (hp : 7 / 4 ≤ (p.2 : ℝ)) :
    stretchedUpperCollar c d hdisj a p =
      coreInclusion c d hdisj a (c.secondRadialMap d hdisj p.1 p.2 p.2.property) := by
  rw [stretchedUpperCollar, collarStretch_of_ge hp, if_neg (by linarith)]
  apply congrArg (coreInclusion c d hdisj a)
  apply Subtype.ext
  simp only [stretchedSecondCore, BallChart.secondRadialMap_val, collarStretch_of_ge hp,
    max_eq_right p.2.property.1]

theorem stretchedLowerCollar_of_le (p : BandCollarMapsDomain) (hp : collarStretch p.2 ≤ 1) :
    stretchedLowerCollar c d hdisj a p = bandInclusion c d hdisj a
      (p.1, ⟨1 - collarStretch p.2, by constructor <;>
        linarith [(collarStretch_mem_Icc p.2.property).1]⟩) := by
  rw [stretchedLowerCollar, if_pos hp]
  apply congrArg (bandInclusion c d hdisj a)
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  exact max_eq_right (by linarith)

theorem stretchedUpperCollar_of_le (p : BandCollarMapsDomain) (hp : collarStretch p.2 ≤ 1) :
    stretchedUpperCollar c d hdisj a p = bandInclusion c d hdisj a
      (a.symm p.1, ⟨collarStretch p.2,
        le_trans (by norm_num) (collarStretch_mem_Icc p.2.property).1, hp⟩) := by
  rw [stretchedUpperCollar, if_pos hp]
  apply congrArg (bandInclusion c d hdisj a)
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  exact min_eq_right hp

theorem stretchedLowerCollar_of_gt (p : BandCollarMapsDomain) (hp : 1 < collarStretch p.2) :
    stretchedLowerCollar c d hdisj a p = coreInclusion c d hdisj a
      (c.firstRadialMap d hdisj p.1 (collarStretch p.2)
        ⟨hp.le, (collarStretch_mem_Icc p.2.property).2⟩) := by
  rw [stretchedLowerCollar, if_neg (not_le.mpr hp)]
  apply congrArg (coreInclusion c d hdisj a)
  apply Subtype.ext
  exact congrArg (fun r => c.chart (r • p.1.val)) (max_eq_right hp.le)

theorem stretchedUpperCollar_of_gt (p : BandCollarMapsDomain) (hp : 1 < collarStretch p.2) :
    stretchedUpperCollar c d hdisj a p = coreInclusion c d hdisj a
      (c.secondRadialMap d hdisj p.1 (collarStretch p.2)
        ⟨hp.le, (collarStretch_mem_Icc p.2.property).2⟩) := by
  rw [stretchedUpperCollar, if_neg (not_le.mpr hp)]
  apply congrArg (coreInclusion c d hdisj a)
  apply Subtype.ext
  exact congrArg (fun r => d.chart (r • p.1.val)) (max_eq_right hp.le)

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.BallChart

private abbrev RadialEmbeddingModel := EuclideanSpace ℝ (Fin 3)
private abbrev RadialEmbeddingDomain := sphere (0 : RadialEmbeddingModel) 1 × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' closedBall 0 2) (d.chart '' closedBall 0 2))

def firstClosedRadial (p : RadialEmbeddingDomain) : c.DoublePunctured d :=
  c.firstRadialMap d hdisj p.1 p.2 p.2.property

def secondClosedRadial (p : RadialEmbeddingDomain) : c.DoublePunctured d :=
  c.secondRadialMap d hdisj p.1 p.2 p.2.property

theorem continuous_firstClosedRadial : Continuous (c.firstClosedRadial d hdisj) :=
  c.continuous_firstRadialMap d hdisj Prod.fst _ continuous_fst
    (continuous_subtype_val.comp continuous_snd) _

theorem continuous_secondClosedRadial : Continuous (c.secondClosedRadial d hdisj) :=
  c.continuous_secondRadialMap d hdisj Prod.fst _ continuous_fst
    (continuous_subtype_val.comp continuous_snd) _

theorem firstClosedRadial_injective : Injective (c.firstClosedRadial d hdisj) := by
  intro p q h
  obtain ⟨hz, hr⟩ := (c.firstRadialMap_eq_iff d hdisj p.1 q.1 p.2 q.2
    p.2.property q.2.property).mp h
  exact Prod.ext hz (Subtype.ext hr)

theorem secondClosedRadial_injective : Injective (c.secondClosedRadial d hdisj) := by
  intro p q h
  have hv : d.firstClosedRadial c hdisj.symm p = d.firstClosedRadial c hdisj.symm q :=
    Subtype.ext (congrArg (fun x : c.DoublePunctured d => x.val) h)
  exact d.firstClosedRadial_injective c hdisj.symm hv

theorem disjoint_range_closedRadial :
    Disjoint (range (c.firstClosedRadial d hdisj)) (range (c.secondClosedRadial d hdisj)) := by
  rw [disjoint_left]
  rintro z ⟨p, hp⟩ ⟨q, hq⟩
  have heq := congrArg Subtype.val (hp.trans hq.symm)
  exact disjoint_left.mp hdisj
    ⟨(p.2 : ℝ) • (p.1 : RadialEmbeddingModel), by
      rw [mem_closedBall, dist_zero_right, norm_radial p.1 (by linarith [p.2.property.1])]
      exact p.2.property.2, heq⟩
    ⟨(q.2 : ℝ) • (q.1 : RadialEmbeddingModel), by
      rw [mem_closedBall, dist_zero_right, norm_radial q.1 (by linarith [q.2.property.1])]
      exact q.2.property.2, rfl⟩

theorem firstClosedRadial_image_lt :
    c.firstClosedRadial d hdisj '' {p : RadialEmbeddingDomain | (p.2 : ℝ) < 2} =
      (Subtype.val : c.DoublePunctured d → M) ⁻¹' (c.chart '' ball (0 : RadialEmbeddingModel)
          2) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(p.2 : ℝ) • (p.1 : RadialEmbeddingModel), ?_, rfl⟩
    rw [mem_ball, dist_zero_right, norm_radial p.1 (by linarith [p.2.property.1])]
    exact hp
  · rintro ⟨x, hx, hxy⟩
    have hr1 : 1 ≤ ‖x‖ := by
      by_contra h
      apply y.property
      exact Or.inl ⟨x, by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge h, hxy⟩
    have hr2 : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hx
    have hx0 : 0 < ‖x‖ := by linarith
    let z : sphere (0 : RadialEmbeddingModel) 1 := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx0), inv_mul_cancel₀ hx0.ne']⟩
    refine ⟨(z, ⟨‖x‖, hr1, hr2.le⟩), hr2, ?_⟩
    apply Subtype.ext
    change c.chart (‖x‖ • (‖x‖⁻¹ • x)) = y.val
    rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
    exact hxy

theorem secondClosedRadial_image_lt :
    c.secondClosedRadial d hdisj '' {p : RadialEmbeddingDomain | (p.2 : ℝ) < 2} =
      (Subtype.val : c.DoublePunctured d → M) ⁻¹' (d.chart '' ball (0 : RadialEmbeddingModel)
          2) := by
  ext y
  let y' : d.DoublePunctured c := ⟨y.val, fun h => y.property h.symm⟩
  have h := Set.ext_iff.mp (d.firstClosedRadial_image_lt c hdisj.symm) y'
  constructor
  · rintro ⟨p, hp, hpy⟩
    exact h.mp ⟨p, hp, Subtype.ext (congrArg (fun x : c.DoublePunctured d => x.val) hpy)⟩
  · intro hy
    obtain ⟨p, hp, hpy⟩ := h.mpr hy
    exact ⟨p, hp, Subtype.ext (congrArg (fun x : d.DoublePunctured c => x.val) hpy)⟩

theorem isOpen_firstClosedRadial_image_lt :
    IsOpen (c.firstClosedRadial d hdisj '' {p : RadialEmbeddingDomain | (p.2 : ℝ) < 2}) := by
  rw [firstClosedRadial_image_lt]
  exact (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
    (fun x hx => c.closedBall_subset_source (ball_subset_closedBall hx))).preimage
      continuous_subtype_val

theorem isOpen_secondClosedRadial_image_lt :
    IsOpen (c.secondClosedRadial d hdisj '' {p : RadialEmbeddingDomain | (p.2 : ℝ) < 2}) := by
  rw [secondClosedRadial_image_lt]
  exact (d.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
    (fun x hx => d.closedBall_subset_source (ball_subset_closedBall hx))).preimage
      continuous_subtype_val

theorem isClosedEmbedding_firstClosedRadial [T2Space M] :
    _root_.Topology.IsClosedEmbedding (c.firstClosedRadial d hdisj) :=
  (c.continuous_firstClosedRadial d hdisj).isClosedEmbedding
    (c.firstClosedRadial_injective d hdisj)

theorem isClosedEmbedding_secondClosedRadial [T2Space M] :
    _root_.Topology.IsClosedEmbedding (c.secondClosedRadial d hdisj) :=
  (c.continuous_secondClosedRadial d hdisj).isClosedEmbedding
    (c.secondClosedRadial_injective d hdisj)

end DifferentialGeometry.Topology.BallChart

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev CoreToBandDomain := Sphere (n := 3) × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private def firstCollarExtension : c.DoublePunctured d → Quotient c d hdisj a :=
  Function.extend (c.firstClosedRadial d hdisj) (stretchedLowerCollar c d hdisj a)
    (coreInclusion c d hdisj a)

private theorem continuous_firstCollarExtension :
    Continuous (firstCollarExtension c d hdisj a) := by
  apply (c.isClosedEmbedding_firstClosedRadial d hdisj).continuous_extend_of_isOpen_image
    (c.isOpen_firstClosedRadial_image_lt d hdisj) (continuous_stretchedLowerCollar c d hdisj a)
    (continuous_coreInclusion c d hdisj a)
  intro p hp
  exact stretchedLowerCollar_of_ge c d hdisj a p (by dsimp at hp; linarith)

omit [T2Space M] in
private theorem firstCollarExtension_second (p : CoreToBandDomain) :
    firstCollarExtension c d hdisj a (c.secondClosedRadial d hdisj p) =
      coreInclusion c d hdisj a (c.secondClosedRadial d hdisj p) := by
  apply Function.extend_apply'
  intro hp
  exact disjoint_left.mp (c.disjoint_range_closedRadial d hdisj) hp (mem_range_self p)

def coreToBand : c.DoublePunctured d → Quotient c d hdisj a :=
  Function.extend (c.secondClosedRadial d hdisj) (stretchedUpperCollar c d hdisj a)
    (firstCollarExtension c d hdisj a)

theorem continuous_coreToBand : Continuous (coreToBand c d hdisj a) := by
  apply (c.isClosedEmbedding_secondClosedRadial d hdisj).continuous_extend_of_isOpen_image
    (c.isOpen_secondClosedRadial_image_lt d hdisj) (continuous_stretchedUpperCollar c d hdisj a)
    (continuous_firstCollarExtension c d hdisj a)
  intro p hp
  exact (stretchedUpperCollar_of_ge c d hdisj a p (by dsimp at hp; linarith)).trans
    (firstCollarExtension_second c d hdisj a p).symm

omit [T2Space M] in
theorem coreToBand_first (p : CoreToBandDomain) :
    coreToBand c d hdisj a (c.firstClosedRadial d hdisj p) =
      stretchedLowerCollar c d hdisj a p := by
  have hp : c.firstClosedRadial d hdisj p ∉ range (c.secondClosedRadial d hdisj) :=
    fun hp => disjoint_left.mp (c.disjoint_range_closedRadial d hdisj) (mem_range_self p) hp
  change Function.extend _ _ _ _ = _
  rw [Function.extend_apply' _ _ _ hp]
  exact (c.firstClosedRadial_injective d hdisj).extend_apply _ _ p

omit [T2Space M] in
theorem coreToBand_second (p : CoreToBandDomain) :
    coreToBand c d hdisj a (c.secondClosedRadial d hdisj p) =
      stretchedUpperCollar c d hdisj a p :=
  (c.secondClosedRadial_injective d hdisj).extend_apply _ _ p

omit [T2Space M] in
theorem coreToBand_of_not_mem_range (x : c.DoublePunctured d)
    (hc : x ∉ range (c.firstClosedRadial d hdisj))
    (hd : x ∉ range (c.secondClosedRadial d hdisj)) :
    coreToBand c d hdisj a x = coreInclusion c d hdisj a x := by
  change Function.extend _ _ _ _ = _
  rw [Function.extend_apply' _ _ _ hd]
  exact Function.extend_apply' _ _ _ hc

omit [T2Space M] in
omit [T2Space M] in
theorem coreToBand_firstBoundary (z : Sphere (n := 3)) :
    coreToBand c d hdisj a (c.firstBoundaryMap d hdisj z) =
      bandInclusion c d hdisj a (z, ⟨1 / 2, by norm_num⟩) := by
  have hp : c.firstClosedRadial d hdisj (z, ⟨1, by norm_num⟩) =
      c.firstBoundaryMap d hdisj z := c.firstRadialMap_one d hdisj z _
  rw [← hp, coreToBand_first, stretchedLowerCollar_one]

omit [T2Space M] in
omit [T2Space M] in
theorem coreToBand_secondBoundary (z : Sphere (n := 3)) :
    coreToBand c d hdisj a (c.secondBoundaryMap d hdisj (a z)) =
      bandInclusion c d hdisj a (z, ⟨1 / 2, by norm_num⟩) := by
  have hp : c.secondClosedRadial d hdisj (a z, ⟨1, by norm_num⟩) =
      c.secondBoundaryMap d hdisj (a z) := c.secondRadialMap_one d hdisj (a z) _
  rw [← hp, coreToBand_second, stretchedUpperCollar_one]

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

def directRel (x y : c.DoublePunctured d) : Prop :=
  ∃ z, (x = c.firstBoundaryMap d hdisj z ∧ y = c.secondBoundaryMap d hdisj (a z)) ∨
    (y = c.firstBoundaryMap d hdisj z ∧ x = c.secondBoundaryMap d hdisj (a z))

abbrev DirectQuotient := Quot (directRel c d hdisj a)

def directToBand : DirectQuotient c d hdisj a → Quotient c d hdisj a :=
  Quot.lift (coreToBand c d hdisj a) (by
    rintro x y ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (coreToBand_firstBoundary c d hdisj a z).trans
        (coreToBand_secondBoundary c d hdisj a z).symm
    · exact (coreToBand_secondBoundary c d hdisj a z).trans
        (coreToBand_firstBoundary c d hdisj a z).symm)

@[simp] theorem directToBand_mk (x : c.DoublePunctured d) :
    directToBand c d hdisj a (Quot.mk _ x) = coreToBand c d hdisj a x := rfl

theorem continuous_directToBand [T2Space M] : Continuous (directToBand c d hdisj a) :=
  continuous_quot_lift _ (continuous_coreToBand c d hdisj a)

theorem directToBand_seam (z : Sphere (n := 3)) :
    directToBand c d hdisj a (Quot.mk _ (c.firstBoundaryMap d hdisj z)) =
      bandInclusion c d hdisj a (z, ⟨1 / 2, by norm_num⟩) :=
  coreToBand_firstBoundary c d hdisj a z

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev BandCollarFibersDomain := Sphere (n := 3) × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private theorem first_ne_second_radial (p q : BandCollarFibersDomain) :
    c.firstRadialMap d hdisj p.1 p.2 p.2.property ≠
      c.secondRadialMap d hdisj q.1 q.2 q.2.property := by
  intro h
  exact disjoint_left.mp (c.disjoint_range_closedRadial d hdisj)
    ⟨p, rfl⟩ ⟨q, h.symm⟩

private theorem second_radial_eq (p q : BandCollarFibersDomain)
    (h : c.secondRadialMap d hdisj p.1 p.2 p.2.property =
      c.secondRadialMap d hdisj q.1 q.2 q.2.property) : p = q :=
  c.secondClosedRadial_injective d hdisj h

private theorem band_ne_first_radial (b : Band (n := 3)) (p : BandCollarFibersDomain) (hp : 1
    < (p.2 : ℝ)) :
    bandInclusion c d hdisj a b ≠
      coreInclusion c d hdisj a (c.firstRadialMap d hdisj p.1 p.2 p.2.property) := by
  intro h
  obtain ⟨⟨t, z⟩, _, hz⟩ := (bandInclusion_eq_coreInclusion_iff c d hdisj a _ _).mp h
  cases t with
  | false =>
    have hrad : c.firstRadialMap d hdisj z 1 (by norm_num) =
        c.firstRadialMap d hdisj p.1 p.2 p.2.property :=
      (c.firstRadialMap_one d hdisj z _).trans hz
    have hr := ((c.firstRadialMap_eq_iff d hdisj z p.1 1 p.2
      (by norm_num) p.2.property).mp hrad).2
    linarith
  | true =>
    have hrad : c.secondRadialMap d hdisj (a z) 1 (by norm_num) =
        c.firstRadialMap d hdisj p.1 p.2 p.2.property :=
      (c.secondRadialMap_one d hdisj (a z) _).trans hz
    exact first_ne_second_radial c d hdisj p (a z, ⟨1, by norm_num⟩) hrad.symm

private theorem band_ne_second_radial (b : Band (n := 3)) (p : BandCollarFibersDomain) (hp : 1
    < (p.2 : ℝ)) :
    bandInclusion c d hdisj a b ≠
      coreInclusion c d hdisj a (c.secondRadialMap d hdisj p.1 p.2 p.2.property) := by
  intro h
  obtain ⟨⟨t, z⟩, _, hz⟩ := (bandInclusion_eq_coreInclusion_iff c d hdisj a _ _).mp h
  cases t with
  | false =>
    have hrad : c.firstRadialMap d hdisj z 1 (by norm_num) =
        c.secondRadialMap d hdisj p.1 p.2 p.2.property :=
      (c.firstRadialMap_one d hdisj z _).trans hz
    exact first_ne_second_radial c d hdisj (z, ⟨1, by norm_num⟩) p hrad
  | true =>
    have hrad : c.secondRadialMap d hdisj (a z) 1 (by norm_num) =
        c.secondRadialMap d hdisj p.1 p.2 p.2.property :=
      (c.secondRadialMap_one d hdisj (a z) _).trans hz
    have hr := congrArg (fun p : BandCollarFibersDomain => p.2.val)
      (second_radial_eq c d hdisj (a z, ⟨1, by norm_num⟩) p hrad)
    dsimp at hr
    linarith

theorem stretchedLowerCollar_injective : Injective (stretchedLowerCollar c d hdisj a) := by
  intro p q h
  by_cases hp : collarStretch p.2 ≤ 1 <;> by_cases hq : collarStretch q.2 ≤ 1
  · rw [stretchedLowerCollar_of_le c d hdisj a p hp,
      stretchedLowerCollar_of_le c d hdisj a q hq] at h
    have hh := bandInclusion_injective c d hdisj a h
    have hz : p.1 = q.1 := congrArg (fun z : Band (n := 3) => z.1) hh
    have hr := congrArg (fun z : Band (n := 3) => z.2.val) hh
    apply Prod.ext hz
    apply Subtype.ext
    apply collarStretch_strictMono.injective
    dsimp at hr
    linarith
  · rw [stretchedLowerCollar_of_le c d hdisj a p hp,
      stretchedLowerCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
    exact (band_ne_first_radial c d hdisj a _
      (q.1, ⟨collarStretch q.2, (lt_of_not_ge hq).le,
        (collarStretch_mem_Icc q.2.property).2⟩) (lt_of_not_ge hq) h).elim
  · rw [stretchedLowerCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
      stretchedLowerCollar_of_le c d hdisj a q hq] at h
    exact (band_ne_first_radial c d hdisj a _
      (p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
        (collarStretch_mem_Icc p.2.property).2⟩) (lt_of_not_ge hp) h.symm).elim
  · rw [stretchedLowerCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
      stretchedLowerCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
    have hh := coreInclusion_injective c d hdisj a h
    have hh' := (c.firstRadialMap_eq_iff d hdisj _ _ _ _ _ _).mp hh
    exact Prod.ext hh'.1 (Subtype.ext (collarStretch_strictMono.injective hh'.2))

theorem stretchedUpperCollar_injective : Injective (stretchedUpperCollar c d hdisj a) := by
  intro p q h
  by_cases hp : collarStretch p.2 ≤ 1 <;> by_cases hq : collarStretch q.2 ≤ 1
  · rw [stretchedUpperCollar_of_le c d hdisj a p hp,
      stretchedUpperCollar_of_le c d hdisj a q hq] at h
    have hh := bandInclusion_injective c d hdisj a h
    have hz : p.1 = q.1 := a.symm.injective (congrArg (fun z : Band (n := 3) => z.1) hh)
    have hr : collarStretch p.2 = collarStretch q.2 :=
      congrArg (fun z : Band (n := 3) => z.2.val) hh
    exact Prod.ext hz (Subtype.ext (collarStretch_strictMono.injective hr))
  · rw [stretchedUpperCollar_of_le c d hdisj a p hp,
      stretchedUpperCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
    exact (band_ne_second_radial c d hdisj a _
      (q.1, ⟨collarStretch q.2, (lt_of_not_ge hq).le,
        (collarStretch_mem_Icc q.2.property).2⟩) (lt_of_not_ge hq) h).elim
  · rw [stretchedUpperCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
      stretchedUpperCollar_of_le c d hdisj a q hq] at h
    exact (band_ne_second_radial c d hdisj a _
      (p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
        (collarStretch_mem_Icc p.2.property).2⟩) (lt_of_not_ge hp) h.symm).elim
  · rw [stretchedUpperCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
      stretchedUpperCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
    have hh := coreInclusion_injective c d hdisj a h
    have hh' := second_radial_eq c d hdisj
      (p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
        (collarStretch_mem_Icc p.2.property).2⟩)
      (q.1, ⟨collarStretch q.2, (lt_of_not_ge hq).le,
        (collarStretch_mem_Icc q.2.property).2⟩) hh
    have hz := congrArg (fun z : BandCollarFibersDomain => z.1) hh'
    have hr : collarStretch p.2 = collarStretch q.2 := congrArg (fun z :
        BandCollarFibersDomain => z.2.val) hh'
    exact Prod.ext hz (Subtype.ext (collarStretch_strictMono.injective hr))

theorem stretchedLowerCollar_eq_upper_iff (p q : BandCollarFibersDomain) :
    stretchedLowerCollar c d hdisj a p = stretchedUpperCollar c d hdisj a q ↔
      p.2.val = 1 ∧ q.2.val = 1 ∧ a p.1 = q.1 := by
  constructor
  · intro h
    by_cases hp : collarStretch p.2 ≤ 1 <;> by_cases hq : collarStretch q.2 ≤ 1
    · rw [stretchedLowerCollar_of_le c d hdisj a p hp,
        stretchedUpperCollar_of_le c d hdisj a q hq] at h
      have hh := bandInclusion_injective c d hdisj a h
      have hz : p.1 = a.symm q.1 := congrArg (fun z : Band (n := 3) => z.1) hh
      have hr : 1 - collarStretch p.2 = collarStretch q.2 :=
        congrArg (fun z : Band (n := 3) => z.2.val) hh
      have hpl := (collarStretch_mem_Icc p.2.property).1
      have hql := (collarStretch_mem_Icc q.2.property).1
      have hp1 : collarStretch p.2 = collarStretch 1 := by rw [collarStretch_one]; linarith
      have hq1 : collarStretch q.2 = collarStretch 1 := by rw [collarStretch_one]; linarith
      exact ⟨collarStretch_strictMono.injective hp1, collarStretch_strictMono.injective hq1,
        (congrArg a hz).trans (a.apply_symm_apply q.1)⟩
    · rw [stretchedLowerCollar_of_le c d hdisj a p hp,
        stretchedUpperCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
      exact (band_ne_second_radial c d hdisj a _
        (q.1, ⟨collarStretch q.2, (lt_of_not_ge hq).le,
          (collarStretch_mem_Icc q.2.property).2⟩) (lt_of_not_ge hq) h).elim
    · rw [stretchedLowerCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
        stretchedUpperCollar_of_le c d hdisj a q hq] at h
      exact (band_ne_first_radial c d hdisj a _
        (p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
          (collarStretch_mem_Icc p.2.property).2⟩) (lt_of_not_ge hp) h.symm).elim
    · rw [stretchedLowerCollar_of_gt c d hdisj a p (lt_of_not_ge hp),
        stretchedUpperCollar_of_gt c d hdisj a q (lt_of_not_ge hq)] at h
      exact (first_ne_second_radial c d hdisj
        (p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
          (collarStretch_mem_Icc p.2.property).2⟩)
        (q.1, ⟨collarStretch q.2, (lt_of_not_ge hq).le,
          (collarStretch_mem_Icc q.2.property).2⟩)
        (coreInclusion_injective c d hdisj a h)).elim
  · rintro ⟨hp, hq, hz⟩
    have hpp : p = (p.1, ⟨1, by norm_num⟩) := Prod.ext rfl (Subtype.ext hp)
    have hqq : q = (a p.1, ⟨1, by norm_num⟩) := Prod.ext hz.symm (Subtype.ext hq)
    rw [hpp, hqq, stretchedLowerCollar_one, stretchedUpperCollar_one]

private theorem band_ne_core_of_not_mem_range (b : Band (n := 3)) (x : c.DoublePunctured d)
    (hc : x ∉ range (c.firstClosedRadial d hdisj))
    (hd : x ∉ range (c.secondClosedRadial d hdisj)) :
    bandInclusion c d hdisj a b ≠ coreInclusion c d hdisj a x := by
  intro h
  obtain ⟨⟨t, z⟩, _, hz⟩ := (bandInclusion_eq_coreInclusion_iff c d hdisj a _ _).mp h
  cases t with
  | false => exact hc ⟨(z, ⟨1, by norm_num⟩), (c.firstRadialMap_one d hdisj z _).trans hz⟩
  | true => exact hd ⟨(a z, ⟨1, by norm_num⟩),
      (c.secondRadialMap_one d hdisj (a z) _).trans hz⟩

theorem stretchedLowerCollar_ne_core_of_not_mem_range (p : BandCollarFibersDomain) (x :
    c.DoublePunctured d)
    (hc : x ∉ range (c.firstClosedRadial d hdisj))
    (hd : x ∉ range (c.secondClosedRadial d hdisj)) :
    stretchedLowerCollar c d hdisj a p ≠ coreInclusion c d hdisj a x := by
  intro h
  by_cases hp : collarStretch p.2 ≤ 1
  · rw [stretchedLowerCollar_of_le c d hdisj a p hp] at h
    exact band_ne_core_of_not_mem_range c d hdisj a _ x hc hd h
  · rw [stretchedLowerCollar_of_gt c d hdisj a p (lt_of_not_ge hp)] at h
    exact hc ⟨(p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
      (collarStretch_mem_Icc p.2.property).2⟩), coreInclusion_injective c d hdisj a h⟩

theorem stretchedUpperCollar_ne_core_of_not_mem_range (p : BandCollarFibersDomain) (x :
    c.DoublePunctured d)
    (hc : x ∉ range (c.firstClosedRadial d hdisj))
    (hd : x ∉ range (c.secondClosedRadial d hdisj)) :
    stretchedUpperCollar c d hdisj a p ≠ coreInclusion c d hdisj a x := by
  intro h
  by_cases hp : collarStretch p.2 ≤ 1
  · rw [stretchedUpperCollar_of_le c d hdisj a p hp] at h
    exact band_ne_core_of_not_mem_range c d hdisj a _ x hc hd h
  · rw [stretchedUpperCollar_of_gt c d hdisj a p (lt_of_not_ge hp)] at h
    exact hd ⟨(p.1, ⟨collarStretch p.2, (lt_of_not_ge hp).le,
      (collarStretch_mem_Icc p.2.property).2⟩), coreInclusion_injective c d hdisj a h⟩

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev DirectBandFibersDomain := Sphere (n := 3) × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private theorem mk_first_eq_second_of_stretched_eq (p q : DirectBandFibersDomain)
    (h : stretchedLowerCollar c d hdisj a p = stretchedUpperCollar c d hdisj a q) :
    Quot.mk (directRel c d hdisj a) (c.firstClosedRadial d hdisj p) =
      Quot.mk (directRel c d hdisj a) (c.secondClosedRadial d hdisj q) := by
  obtain ⟨hp, hq, hz⟩ := (stretchedLowerCollar_eq_upper_iff c d hdisj a p q).mp h
  have hfirst : c.firstClosedRadial d hdisj p = c.firstBoundaryMap d hdisj p.1 := by
    apply Subtype.ext
    change c.chart (p.2.val • p.1.val) = c.chart p.1.val
    rw [hp, one_smul]
  have hsecond : c.secondClosedRadial d hdisj q = c.secondBoundaryMap d hdisj (a p.1) := by
    apply Subtype.ext
    change d.chart (q.2.val • q.1.val) = d.chart (a p.1).val
    rw [hq, one_smul, hz]
  rw [hfirst, hsecond]
  exact Quot.sound ⟨p.1, Or.inl ⟨rfl, rfl⟩⟩

theorem directToBand_injective : Injective (directToBand c d hdisj a) := by
  intro q q' h
  obtain ⟨x, rfl⟩ := Quot.exists_rep q
  obtain ⟨y, rfl⟩ := Quot.exists_rep q'
  change coreToBand c d hdisj a x = coreToBand c d hdisj a y at h
  by_cases hxc : x ∈ range (c.firstClosedRadial d hdisj)
  · obtain ⟨p, rfl⟩ := hxc
    rw [coreToBand_first] at h
    by_cases hyc : y ∈ range (c.firstClosedRadial d hdisj)
    · obtain ⟨q, rfl⟩ := hyc
      rw [coreToBand_first] at h
      rw [(stretchedLowerCollar_injective c d hdisj a) h]
    · by_cases hyd : y ∈ range (c.secondClosedRadial d hdisj)
      · obtain ⟨q, rfl⟩ := hyd
        rw [coreToBand_second] at h
        exact mk_first_eq_second_of_stretched_eq c d hdisj a p q h
      · rw [coreToBand_of_not_mem_range c d hdisj a y hyc hyd] at h
        exact (stretchedLowerCollar_ne_core_of_not_mem_range c d hdisj a p y hyc hyd h).elim
  · by_cases hxd : x ∈ range (c.secondClosedRadial d hdisj)
    · obtain ⟨p, rfl⟩ := hxd
      rw [coreToBand_second] at h
      by_cases hyc : y ∈ range (c.firstClosedRadial d hdisj)
      · obtain ⟨q, rfl⟩ := hyc
        rw [coreToBand_first] at h
        exact (mk_first_eq_second_of_stretched_eq c d hdisj a q p h.symm).symm
      · by_cases hyd : y ∈ range (c.secondClosedRadial d hdisj)
        · obtain ⟨q, rfl⟩ := hyd
          rw [coreToBand_second] at h
          rw [(stretchedUpperCollar_injective c d hdisj a) h]
        · rw [coreToBand_of_not_mem_range c d hdisj a y hyc hyd] at h
          exact (stretchedUpperCollar_ne_core_of_not_mem_range c d hdisj a p y hyc hyd h).elim
    · rw [coreToBand_of_not_mem_range c d hdisj a x hxc hxd] at h
      by_cases hyc : y ∈ range (c.firstClosedRadial d hdisj)
      · obtain ⟨q, rfl⟩ := hyc
        rw [coreToBand_first] at h
        exact (stretchedLowerCollar_ne_core_of_not_mem_range c d hdisj a q x hxc hxd h.symm).elim
      · by_cases hyd : y ∈ range (c.secondClosedRadial d hdisj)
        · obtain ⟨q, rfl⟩ := hyd
          rw [coreToBand_second] at h
          exact (stretchedUpperCollar_ne_core_of_not_mem_range c d hdisj a q x hxc hxd h.symm).elim
        · rw [coreToBand_of_not_mem_range c d hdisj a y hyc hyd] at h
          exact congrArg (Quot.mk (directRel c d hdisj a)) (coreInclusion_injective c d hdisj a h)

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev DirectBandHomeomorphDomain := Sphere (n := 3) × Icc (1 : ℝ) 2

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private theorem exists_stretchedLowerCollar_core (p : DirectBandHomeomorphDomain) :
    ∃ q : DirectBandHomeomorphDomain, stretchedLowerCollar c d hdisj a q =
      coreInclusion c d hdisj a (c.firstClosedRadial d hdisj p) := by
  let r : Icc (1 / 2 : ℝ) 2 := ⟨p.2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩
  let t := collarStretchHomeomorph.symm r
  have ht : collarStretch t = p.2 :=
    congrArg Subtype.val (collarStretchHomeomorph.apply_symm_apply r)
  refine ⟨(p.1, t), ?_⟩
  by_cases hp : p.2.val = 1
  · rw [stretchedLowerCollar_of_le c d hdisj a _ (by rw [ht, hp])]
    have hband : (p.1, (⟨1 - collarStretch t, by constructor <;>
        linarith [(collarStretch_mem_Icc t.property).1, ht, p.2.property.1]⟩ : Icc (0 : ℝ) 1)) =
        boundaryInclusion (false, p.1) := by
      refine Prod.ext (by rfl) (Subtype.ext ?_)
      simp only [ht, hp, sub_self, boundaryInclusion]
    have hcore : c.firstClosedRadial d hdisj p = c.firstBoundaryMap d hdisj p.1 := by
      apply Subtype.ext
      change c.chart (p.2.val • p.1.val) = c.chart p.1.val
      rw [hp, one_smul]
    rw [hband, hcore]
    exact seam_eq c d hdisj a (false, p.1)
  · have hgt : 1 < collarStretch t := by rw [ht]; exact lt_of_le_of_ne p.2.property.1 (Ne.symm hp)
    rw [stretchedLowerCollar_of_gt c d hdisj a _ hgt]
    apply congrArg (coreInclusion c d hdisj a)
    apply Subtype.ext
    exact congrArg (fun r => c.chart (r • p.1.val)) ht

private theorem exists_stretchedUpperCollar_core (p : DirectBandHomeomorphDomain) :
    ∃ q : DirectBandHomeomorphDomain, stretchedUpperCollar c d hdisj a q =
      coreInclusion c d hdisj a (c.secondClosedRadial d hdisj p) := by
  let r : Icc (1 / 2 : ℝ) 2 := ⟨p.2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩
  let t := collarStretchHomeomorph.symm r
  have ht : collarStretch t = p.2 :=
    congrArg Subtype.val (collarStretchHomeomorph.apply_symm_apply r)
  refine ⟨(p.1, t), ?_⟩
  by_cases hp : p.2.val = 1
  · rw [stretchedUpperCollar_of_le c d hdisj a _ (by rw [ht, hp])]
    have hband : (a.symm p.1, (⟨collarStretch t,
        le_trans (by norm_num) (collarStretch_mem_Icc t.property).1, by rw [ht, hp]⟩ :
        Icc (0 : ℝ) 1)) = boundaryInclusion (true, a.symm p.1) := by
      refine Prod.ext (by rfl) (Subtype.ext ?_)
      exact ht.trans hp
    have hcore : c.secondClosedRadial d hdisj p = c.secondBoundaryMap d hdisj p.1 := by
      apply Subtype.ext
      change d.chart (p.2.val • p.1.val) = d.chart p.1.val
      rw [hp, one_smul]
    rw [hband, hcore]
    have hs := seam_eq c d hdisj a (true, a.symm p.1)
    change bandInclusion c d hdisj a (boundaryInclusion (true, a.symm p.1)) =
      coreInclusion c d hdisj a (c.secondBoundaryMap d hdisj (a (a.symm p.1))) at hs
    simpa only [a.apply_symm_apply] using hs
  · have hgt : 1 < collarStretch t := by rw [ht]; exact lt_of_le_of_ne p.2.property.1 (Ne.symm hp)
    rw [stretchedUpperCollar_of_gt c d hdisj a _ hgt]
    apply congrArg (coreInclusion c d hdisj a)
    apply Subtype.ext
    exact congrArg (fun r => d.chart (r • p.1.val)) ht

private theorem exists_coreToBand_band (q : Band (n := 3)) :
    ∃ x, coreToBand c d hdisj a x = bandInclusion c d hdisj a q := by
  by_cases hq : q.2.val ≤ 1 / 2
  · let r : Icc (1 / 2 : ℝ) 2 := ⟨1 - q.2.val, by
      constructor <;> linarith [q.2.property.1]⟩
    let t := collarStretchHomeomorph.symm r
    have ht : collarStretch t = 1 - q.2.val :=
      congrArg Subtype.val (collarStretchHomeomorph.apply_symm_apply r)
    refine ⟨c.firstClosedRadial d hdisj (q.1, t), ?_⟩
    rw [coreToBand_first, stretchedLowerCollar_of_le c d hdisj a _
      (by rw [ht]; linarith [q.2.property.1])]
    apply congrArg (bandInclusion c d hdisj a)
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change 1 - collarStretch t = q.2.val
    rw [ht]
    ring
  · let r : Icc (1 / 2 : ℝ) 2 := ⟨q.2.val, by
      constructor <;> linarith [q.2.property.2]⟩
    let t := collarStretchHomeomorph.symm r
    have ht : collarStretch t = q.2.val :=
      congrArg Subtype.val (collarStretchHomeomorph.apply_symm_apply r)
    refine ⟨c.secondClosedRadial d hdisj (a q.1, t), ?_⟩
    rw [coreToBand_second, stretchedUpperCollar_of_le c d hdisj a _
      (by rw [ht]; exact q.2.property.2)]
    apply congrArg (bandInclusion c d hdisj a)
    exact Prod.ext (a.symm_apply_apply q.1) (Subtype.ext ht)

theorem directToBand_surjective : Surjective (directToBand c d hdisj a) := by
  intro q
  have hq : q ∈ range (bandInclusion c d hdisj a) ∪ range (coreInclusion c d hdisj a) :=
    (inclusions_cover c d hdisj a).symm ▸ mem_univ q
  rcases hq with ⟨p, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := exists_coreToBand_band c d hdisj a p
    exact ⟨Quot.mk _ x, hx⟩
  · by_cases hxc : x ∈ range (c.firstClosedRadial d hdisj)
    · obtain ⟨p, rfl⟩ := hxc
      obtain ⟨p', hp'⟩ := exists_stretchedLowerCollar_core c d hdisj a p
      exact ⟨Quot.mk _ (c.firstClosedRadial d hdisj p'),
        (coreToBand_first c d hdisj a p').trans hp'⟩
    · by_cases hxd : x ∈ range (c.secondClosedRadial d hdisj)
      · obtain ⟨p, rfl⟩ := hxd
        obtain ⟨p', hp'⟩ := exists_stretchedUpperCollar_core c d hdisj a p
        exact ⟨Quot.mk _ (c.secondClosedRadial d hdisj p'),
          (coreToBand_second c d hdisj a p').trans hp'⟩
      · exact ⟨Quot.mk _ x, coreToBand_of_not_mem_range c d hdisj a x hxc hxd⟩

def directBandHomeomorph [T2Space M] [CompactSpace M] :
    DirectQuotient c d hdisj a ≃ₜ Quotient c d hdisj a :=
  IsHomeomorph.homeomorph (directToBand c d hdisj a)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_directToBand c d hdisj a, directToBand_injective c d hdisj a,
        directToBand_surjective c d hdisj a⟩)

@[simp] theorem directBandHomeomorph_mk [T2Space M] [CompactSpace M]
    (x : c.DoublePunctured d) :
    directBandHomeomorph c d hdisj a (Quot.mk _ x) = coreToBand c d hdisj a x := rfl

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev SurvivorFixedModel := EuclideanSpace ℝ (Fin 3)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

theorem coreToBand_of_not_mem_chart_image (x : c.DoublePunctured d)
    (hc : x.val ∉ c.chart '' Metric.closedBall (0 : SurvivorFixedModel) 2)
    (hd : x.val ∉ d.chart '' Metric.closedBall (0 : SurvivorFixedModel) 2) :
    coreToBand c d hdisj a x = coreInclusion c d hdisj a x := by
  apply coreToBand_of_not_mem_range
  · rintro ⟨p, hp⟩
    apply hc
    refine ⟨p.2.val • p.1.val, ?_, congrArg Subtype.val hp⟩
    rw [Metric.mem_closedBall, dist_zero_right,
      BallChart.norm_radial p.1 (by linarith [p.2.property.1])]
    exact p.2.property.2
  · rintro ⟨p, hp⟩
    apply hd
    refine ⟨p.2.val • p.1.val, ?_, congrArg Subtype.val hp⟩
    rw [Metric.mem_closedBall, dist_zero_right,
      BallChart.norm_radial p.1 (by linarith [p.2.property.1])]
    exact p.2.property.2

theorem directBandHomeomorph_survivor [T2Space M] [CompactSpace M]
    (e : BallChart 3 I M)
    (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
    (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (x : SurvivorFixedModel) (hx : x ∈ Metric.closedBall (0 : SurvivorFixedModel) 2)
    (hp : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ) :
    directBandHomeomorph c d hdisj a (Quot.mk _ ⟨e.chart x, hp⟩) =
      coreInclusion c d hdisj a ⟨e.chart x, hp⟩ := by
  exact coreToBand_of_not_mem_chart_image c d hdisj a ⟨e.chart x, hp⟩
    (fun h => disjoint_left.mp hec ⟨x, hx, rfl⟩ h)
    (fun h => disjoint_left.mp hed ⟨x, hx, rfl⟩ h)

theorem coreToBand_mem_core_image_iff
    (U : Set (c.DoublePunctured d))
    (hUc : ∀ x ∈ U, x.val ∉ c.chart '' Metric.closedBall (0 : SurvivorFixedModel) 2)
    (hUd : ∀ x ∈ U, x.val ∉ d.chart '' Metric.closedBall (0 : SurvivorFixedModel) 2)
    (x : c.DoublePunctured d) :
    coreToBand c d hdisj a x ∈ coreInclusion c d hdisj a '' U ↔ x ∈ U := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hc : y ∉ range (c.firstClosedRadial d hdisj) := by
      rintro ⟨p, hp⟩
      apply hUc y hy
      refine ⟨p.2.val • p.1.val, ?_, congrArg Subtype.val hp⟩
      rw [Metric.mem_closedBall, dist_zero_right,
        BallChart.norm_radial p.1 (by linarith [p.2.property.1])]
      exact p.2.property.2
    have hd : y ∉ range (c.secondClosedRadial d hdisj) := by
      rintro ⟨p, hp⟩
      apply hUd y hy
      refine ⟨p.2.val • p.1.val, ?_, congrArg Subtype.val hp⟩
      rw [Metric.mem_closedBall, dist_zero_right,
        BallChart.norm_radial p.1 (by linarith [p.2.property.1])]
      exact p.2.property.2
    by_cases hxc : x ∈ range (c.firstClosedRadial d hdisj)
    · obtain ⟨p, rfl⟩ := hxc
      rw [coreToBand_first] at hyx
      exact (stretchedLowerCollar_ne_core_of_not_mem_range c d hdisj a p y hc hd hyx.symm).elim
    · by_cases hxd : x ∈ range (c.secondClosedRadial d hdisj)
      · obtain ⟨p, rfl⟩ := hxd
        rw [coreToBand_second] at hyx
        exact (stretchedUpperCollar_ne_core_of_not_mem_range c d hdisj a p y hc hd hyx.symm).elim
      · rw [coreToBand_of_not_mem_range c d hdisj a x hxc hxd] at hyx
        exact (coreInclusion_injective c d hdisj a hyx) ▸ hy
  · intro hx
    exact ⟨x, hx, (coreToBand_of_not_mem_chart_image c d hdisj a x (hUc x hx) (hUd x hx)).symm⟩

end DifferentialGeometry.Topology.SelfAttachment

end

section

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev RestrictedModel := EuclideanSpace ℝ (Fin 3)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

omit [T2Space M] [CompactSpace M] in
private theorem directRel_not_mem
    (U : Set (c.DoublePunctured d))
    (hUc : ∀ x ∈ U, x.val ∉ c.chart '' Metric.closedBall (0 : RestrictedModel) 2)
    (hUd : ∀ x ∈ U, x.val ∉ d.chart '' Metric.closedBall (0 : RestrictedModel) 2)
    {x y : c.DoublePunctured d} (hxy : directRel c d hdisj a x y) : x ∉ U ∧ y ∉ U := by
  have hfirst (z : Sphere (n := 3)) : c.firstBoundaryMap d hdisj z ∉ U := by
    intro h
    exact hUc _ h ⟨z, Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by norm_num)) z.property, rfl⟩
  have hsecond (z : Sphere (n := 3)) : c.secondBoundaryMap d hdisj z ∉ U := by
    intro h
    exact hUd _ h ⟨z, Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by norm_num)) z.property, rfl⟩
  rcases hxy with ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨hfirst z, hsecond (a z)⟩
  · exact ⟨hsecond (a z), hfirst z⟩

omit [T2Space M] [CompactSpace M] in
private theorem eqvGen_restrict_compl
    (U : Set (c.DoublePunctured d))
    (hUc : ∀ x ∈ U, x.val ∉ c.chart '' Metric.closedBall (0 : RestrictedModel) 2)
    (hUd : ∀ x ∈ U, x.val ∉ d.chart '' Metric.closedBall (0 : RestrictedModel) 2) :
    ∀ {x y : c.DoublePunctured d}, Relation.EqvGen (directRel c d hdisj a) x y →
      ∀ (hx : x ∉ U) (hy : y ∉ U),
      Relation.EqvGen (fun p q : ↥(Uᶜ) => directRel c d hdisj a p.val q.val) ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x y hxy
  induction hxy with
  | rel x y h => intro hx hy; exact Relation.EqvGen.rel _ _ h
  | refl x => intro hx hy; exact Relation.EqvGen.refl _
  | symm x y h ih => intro hx hy; exact Relation.EqvGen.symm _ _ (ih hy hx)
  | trans x y z hxy hyz ih ih' =>
    intro hx hz
    have hy : y ∉ U := by
      intro hy
      have hmem : ∀ p q : c.DoublePunctured d,
          Relation.EqvGen (directRel c d hdisj a) p q → (p ∈ U ↔ q ∈ U) := by
        intro p q h
        induction h with
        | rel p q h =>
          obtain ⟨hp, hq⟩ := directRel_not_mem c d hdisj a U hUc hUd h
          exact iff_of_false hp hq
        | refl p => exact Iff.rfl
        | symm p q h ih => exact ih.symm
        | trans p q r h h' ih ih' => exact ih.trans ih'
      exact hx ((hmem x y hxy).mpr hy)
    exact Relation.EqvGen.trans _ _ _ (ih hx hy) (ih' hy hz)

def directBandComplementHomeomorph
    (U : Set (c.DoublePunctured d)) (hU : IsOpen U)
    (hUc : ∀ x ∈ U, x.val ∉ c.chart '' Metric.closedBall (0 : RestrictedModel) 2)
    (hUd : ∀ x ∈ U, x.val ∉ d.chart '' Metric.closedBall (0 : RestrictedModel) 2) :
    Quot (fun p q : ↥(Uᶜ) => directRel c d hdisj a p.val q.val) ≃ₜ
      {q : Quotient c d hdisj a // q ∉ coreInclusion c d hdisj a '' U} := by
  let X := ↥(Uᶜ)
  let Y := {q : Quotient c d hdisj a // q ∉ coreInclusion c d hdisj a '' U}
  let r := fun p q : X => directRel c d hdisj a p.val q.val
  have hfmem (x : X) : coreToBand c d hdisj a x.val ∉ coreInclusion c d hdisj a '' U :=
    fun h => x.property ((coreToBand_mem_core_image_iff c d hdisj a U hUc hUd x.val).mp h)
  let F : X → Y := fun x => ⟨coreToBand c d hdisj a x.val, hfmem x⟩
  have hf : Continuous F := ((continuous_coreToBand c d hdisj a).comp
    continuous_subtype_val).subtype_mk hfmem
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hU.isClosed_compl.isCompact
  have hsurj : Surjective F := by
    intro y
    obtain ⟨q, hq⟩ := directToBand_surjective c d hdisj a y.val
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    have hx : x ∉ U := by
      intro hx
      exact y.property (hq ▸ (coreToBand_mem_core_image_iff c d hdisj a U hUc hUd x).mpr hx)
    exact ⟨⟨x, hx⟩, Subtype.ext hq⟩
  have hquot : _root_.Topology.IsQuotientMap F := hf.isClosedMap.isQuotientMap hf hsurj
  have hkernel (x y : X) (h : F x = F y) : Relation.EqvGen r x y := by
    have h' : Quot.mk (directRel c d hdisj a) x.val = Quot.mk _ y.val :=
      directToBand_injective c d hdisj a (congrArg Subtype.val h)
    exact eqvGen_restrict_compl c d hdisj a U hUc hUd (Quot.eqvGen_exact h') x.property y.property
  let H := quotientHomeomorphOfRelations F hquot r Eq
    (fun x y h => Relation.EqvGen.rel _ _ (Subtype.ext
      (congrArg (directToBand c d hdisj a) (Quot.sound h))))
    (fun x y h => hkernel x y h) hkernel
  exact H.trans Homeomorph.quotientBot

@[simp] theorem directBandComplementHomeomorph_mk
    (U : Set (c.DoublePunctured d)) (hU : IsOpen U)
    (hUc : ∀ x ∈ U, x.val ∉ c.chart '' Metric.closedBall (0 : RestrictedModel) 2)
    (hUd : ∀ x ∈ U, x.val ∉ d.chart '' Metric.closedBall (0 : RestrictedModel) 2) (x : ↥(Uᶜ)) :
    (directBandComplementHomeomorph c d hdisj a U hU hUc hUd (Quot.mk _ x)).val =
      coreToBand c d hdisj a x.val := rfl

end DifferentialGeometry.Topology.SelfAttachment

end
