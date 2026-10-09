import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickRadiusTransfer_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverRegular_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow

set_option autoImplicit false

/-! CH12-O27 G3 (part c) — **R4 at regular times**: `Done` + per-model S4 fields ⇒ the frozen O21
COV clause (radius `w'⁻¹`) for every late regular slice.  `cover_regular_of_done_O27` (radius `N`)
+ `hpi07_thick_transfer_O27` (radius `w'⁻¹`), thickness moved across `sliceCast_CX4`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- Thickness at a post-stage point is thickness of its slice cast. -/
theorem thick_cast_of_post_O27 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {Q : OrientedThreeStage.{u}} (t : ℝ)
    (h : postStage F.observation t = Q) (m : Q.Metric) (hm : HEq (postMetric F.observation t) m)
    (hp : 0 < t⁻¹) (p : (postStage F.observation t).Carrier) (w r : ℝ)
    (hcr : curvatureRadius (scaleMetric t⁻¹ hp (postMetric F.observation t)) p = ENNReal.ofReal r)
    (hth : ENNReal.ofReal (w * r ^ 3) ≤
      ballVolume (scaleMetric t⁻¹ hp (postMetric F.observation t)) p r) :
    curvatureRadius (scaleMetric t⁻¹ hp m)
        (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h) p) = ENNReal.ofReal r ∧
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹ hp m)
        (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h) p) r := by
  subst h
  obtain rfl := eq_of_heq hm
  exact ⟨hcr, hth⟩

/-- **R4, regular times.** -/
theorem cover_regular_O27 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K count : ℕ)
    (model : Fin count → FiniteVolumeHyperbolicModel.{u}) (Tr : ∀ i, HyperbolicTruncation (model i))
    (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
    (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (hstart : ∀ i, 0 < start i) (hpos : ∀ i t, start i ≤ t → 0 < α i t)
    (hdecay : ∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε)
    (hsmooth : ∀ i t (ht : start i ≤ t),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t))
    (hemb : ∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x))
    (hball : ∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
      (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t)
    (hck : ∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
        ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t)
    (hDone : ∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R)) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ w' : ℝ, w ≤ w' → w' ≤ w0 →
        ∀ (p : (postStage F.observation s.time).Carrier) (r : ℝ), 0 < r →
          curvatureRadius (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive)
            (postMetric F.observation s.time)) p = ENNReal.ofReal r →
          ENNReal.ofReal (w' * r ^ 3) ≤ ballVolume (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive)
            (postMetric F.observation s.time)) p r →
          ∃ (i : Fin count) (hi : start i ≤ s.time),
            p ∈ map i s.time hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹ := by
  choose w0 hw0 Tg hG using fun i => hpi07_thick_transfer_O27 F K (model i) (Tr i) (start i)
    (hstart i) (α i) (Ω i) (map i) (hpos i) (hdecay i) (hemb i) (hsmooth i) (hball i) (hck i)
  have hsum0 : 0 ≤ ∑ i, (w0 i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hw0 i)).le
  refine ⟨(1 + ∑ i, (w0 i)⁻¹)⁻¹, by positivity, fun w hw => ?_⟩
  have hw0le : ∀ i, (1 + ∑ i, (w0 i)⁻¹)⁻¹ ≤ w0 i := fun i => by
    have h1 : (w0 i)⁻¹ ≤ 1 + ∑ i, (w0 i)⁻¹ := by
      have := Finset.single_le_sum (f := fun i => (w0 i)⁻¹)
        (fun j _ => (inv_pos.mpr (hw0 j)).le) (Finset.mem_univ i)
      linarith
    simpa using inv_anti₀ (inv_pos.mpr (hw0 i)) h1
  obtain ⟨N, T₀, hcov⟩ := cover_regular_of_done_O27 F count model start map w (hDone w hw)
  choose Td hTd using fun i => hdecay i (1 / ((N : ℝ) + 1)) (by positivity)
  refine ⟨max T₀ (∑ i, (|Tg i| + |Td i|)), fun s hs w' hww' hw'0 p r hr hcr hth => ?_⟩
  have hTi : ∀ i, |Tg i| + |Td i| ≤ s.time := fun i =>
    (Finset.single_le_sum (f := fun i => |Tg i| + |Td i|) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hs)
  obtain ⟨hcr', hth'⟩ := thick_cast_of_post_O27 F s.time (postStage_eq_sliceStage_CX4 s) s.metric
    (postMetric_regularSlice F.observation s) (inv_pos.mpr s.positive) p w' r hcr hth
  have hthw : ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric (sliceCast_CX4 s p) r :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hww' (by positivity))).trans hth'
  obtain ⟨i, hi, x, ⟨y, hy, rfl⟩, hx⟩ :=
    hcov s ((le_max_left _ _).trans hs) (sliceCast_CX4 s p) r hr hcr' hthw
  have hxp : map i s.time hi y = p := by
    unfold sliceCast_CX4 at hx
    have h2 := congrArg (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier)
      (postStage_eq_sliceStage_CX4 s)).symm) hx
    simpa only [cast_cast, cast_eq] using h2
  subst hxp
  have hαN : (N : ℝ) < (α i s.time)⁻¹ := by
    have hαt := hpos i s.time hi
    have h1 : α i s.time < 1 / ((N : ℝ) + 1) :=
      hTd i s.time ((le_abs_self _).trans (by linarith [abs_nonneg (Tg i), hTi i]))
    have h2 : (N : ℝ) + 1 < (α i s.time)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hαt]; simpa [one_div] using h1
    linarith
  refine ⟨i, hi, y, hG i s.time hi ((le_abs_self _).trans (by linarith [abs_nonneg (Td i), hTi i]))
    w' (hw.trans_le hww') (hw'0.trans (hw0le i)) y (riemannianBallOf_mono _ _ hαN.le hy) r hr hcr hth,
    rfl⟩

end GC.LongTime.Ch12
