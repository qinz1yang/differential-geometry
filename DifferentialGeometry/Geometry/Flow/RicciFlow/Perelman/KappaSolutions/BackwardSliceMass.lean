import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Mathlib.Topology.Order.MonotoneConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

open Filter Set
open scoped Topology ENNReal

private theorem tendsto_antitoneOn_mul_atTop {V : ℝ → ℝ≥0∞}
    (hV : AntitoneOn V (Ioi 0)) {tau : ℕ → ℝ}
    (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => V (tau i * a)) atTop (𝓝 (⨅ t : Ioi (0 : ℝ), V t)) := by
  have hm : Antitone (fun t : Ioi (0 : ℝ) => V t) :=
    fun x y hxy => hV x.property y.property hxy
  have hesc : Tendsto (fun i => (⟨tau i * a, mul_pos (htau i) ha⟩ : Ioi (0 : ℝ)))
      atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(hescape.atTop_mul_const ha).eventually_ge_atTop (b : ℝ)] with i hi
    exact hi
  exact (tendsto_atTop_iInf hm).comp hesc

private theorem eventually_antitoneOn_mul_le {V : ℝ → ℝ≥0∞}
    (hV : AntitoneOn V (Ioi 0)) {tau : ℕ → ℝ}
    (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    {a : ℝ} (ha : 0 < a) {b : ℝ≥0∞}
    (hb : (⨅ t : Ioi (0 : ℝ), V t) < b) :
    ∀ᶠ i in atTop, ∀ θ ∈ Ici a,
      (⨅ t : Ioi (0 : ℝ), V t) ≤ V (tau i * θ) ∧ V (tau i * θ) < b := by
  have hlim := tendsto_antitoneOn_mul_atTop hV htau hescape ha
  filter_upwards [hlim.eventually (gt_mem_nhds hb)] with i hi
  intro θ hθ
  have hp : 0 < tau i * θ := mul_pos (htau i) (ha.trans_le hθ)
  exact ⟨iInf_le (fun t : Ioi (0 : ℝ) => V t) ⟨tau i * θ, hp⟩,
    (hV (mul_pos (htau i) ha) hp (mul_le_mul_of_nonneg_left hθ (htau i).le)).trans_lt hi⟩

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem normalizedShrinkerMass_scaleMetric (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) {c : ℝ} (hc : 0 < c) :
    normalizedShrinkerMass (scaleMetric c hc g) f =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank ℝ E * normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [volume_scaleMetric, lintegral_smul_measure, smul_eq_mul]

theorem normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    normalizedShrinkerMass
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (T - tau)))
      (fun x => lCost S T p x tau / (2 * Real.sqrt tau)) =
        intrinsicReducedVolume S T p tau := by
  rw [normalizedShrinkerMass_scaleMetric]
  have hfactor : (Real.sqrt tau⁻¹) ^ Module.finrank ℝ E =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau) := by
    rw [← Real.exp_log (pow_pos (Real.sqrt_pos.mpr (inv_pos.mpr htau)) _),
      Real.log_pow, Real.log_sqrt (inv_nonneg.mpr htau.le), Real.log_inv]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) _, hfactor]
  unfold normalizedShrinkerMass intrinsicReducedVolume
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

def asymptoticReducedVolume {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) : ℝ≥0∞ :=
  ⨅ tau : Ioi (0 : ℝ), intrinsicReducedVolume S T p tau

theorem intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => intrinsicReducedVolume S T p (tau i * a))
      atTop (𝓝 (asymptoticReducedVolume S T p)) :=
  tendsto_antitoneOn_mul_atTop hmono htau hescape ha

theorem eventually_intrinsicReducedVolume_mul_lt_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    {a : ℝ} (ha : 0 < a) {b : ℝ≥0∞} (hb : asymptoticReducedVolume S T p < b) :
    ∀ᶠ i in atTop, ∀ θ ∈ Ici a,
      asymptoticReducedVolume S T p ≤ intrinsicReducedVolume S T p (tau i * θ) ∧
      intrinsicReducedVolume S T p (tau i * θ) < b :=
  eventually_antitoneOn_mul_le hmono htau hescape ha hb

theorem intrinsicReducedVolume_sub_tendsto_zero_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun i => intrinsicReducedVolume S T p (tau i * a) -
      intrinsicReducedVolume S T p (tau i * b)) atTop (𝓝 0) := by
  by_cases htop : asymptoticReducedVolume S T p = ⊤
  · have hval (r : ℝ) (hr : 0 < r) : intrinsicReducedVolume S T p r = ⊤ := by
      apply top_unique
      rw [← htop]
      exact iInf_le (fun t : Ioi (0 : ℝ) => intrinsicReducedVolume S T p t) ⟨r, hr⟩
    simpa only [hval _ (mul_pos (htau _) ha), hval _ (mul_pos (htau _) hb), tsub_self]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · have h := ENNReal.Tendsto.sub
      (intrinsicReducedVolume_tendsto_mul_atTop_of_antitone S T p hmono htau hescape ha)
      (intrinsicReducedVolume_tendsto_mul_atTop_of_antitone S T p hmono htau hescape hb)
      (Or.inl htop)
    simpa only [tsub_self] using h

section BackwardSlice

variable [CompleteSpace E]
  {D : RealTimeInterval} (F : CheegerGromovCompactness.PointedFlowData (I := I) D)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem backwardSliceSequence_normalizedShrinkerMass_tendsto
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hescape : Tendsto tau atTop atTop)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0)) :
    Tendsto (fun i => normalizedShrinkerMass
      ((backwardSliceSequence F tau htau q).obj i).metric
      (fun x => lCost F.S 0 p x (tau i) / (2 * Real.sqrt (tau i))))
      atTop (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
  have heq (i : ℕ) : normalizedShrinkerMass
      ((backwardSliceSequence F tau htau q).obj i).metric
      (fun x => lCost F.S 0 p x (tau i) / (2 * Real.sqrt (tau i))) =
        intrinsicReducedVolume F.S 0 p (tau i) := by
    simpa only [zero_sub] using
      normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume F.S 0 p (htau i)
  simp_rw [heq]
  simpa only [mul_one] using intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
    F.S 0 p hmono htau hescape (a := 1) zero_lt_one

end BackwardSlice

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
