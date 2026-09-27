import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientDistanceRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import DifferentialGeometry.Geometry.Metric.Family.DistanceContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData (I := I) ancientTimeInterval)

local instance terminalDistanceTopology : TopologicalSpace F.M := F.topology
local instance terminalDistanceCharted : ChartedSpace H F.M := F.charted
local instance terminalDistanceSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalDistanceT2 : T2Space F.M := F.t2

theorem continuousWithinAt_moving_distance_zero
    (x y : ℝ → F.M) (hx : ContinuousAt x 0) (hy : ContinuousAt y 0)
    (hxy : x 0 = y 0) :
    ContinuousWithinAt
      (fun t => (riemannianEDistOf (F.S.base.metric (-t)) (x t) (y t)).toReal)
      (Ici 0) 0 := by
  let g : ℝ → SmoothRiemannianMetric I F.M := fun t => F.S.base.metric (-|t|)
  have hquad : Continuous (metricTimeBundleQuad g (univ : Set ℝ)) := by
    have hb := metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      F.S.family.metric F.isSolution.smoothMetric (Subset.refl ancientTimeInterval.carrier)
    let f : {t : ℝ // t ∈ (univ : Set ℝ)} × TangentBundle I F.M →
        ancientTimeInterval.carrier × TangentBundle I F.M :=
      fun q => (⟨-|q.1.1|, by
        rw [ancientTimeInterval_carrier]
        exact neg_nonpos.mpr (abs_nonneg (q.1.1 : ℝ))⟩, q.2)
    have hf : Continuous f := by
      apply Continuous.prodMk _ continuous_snd
      apply Continuous.subtype_mk
      exact (continuous_abs.comp (continuous_subtype_val.comp continuous_fst)).neg
    exact hb.comp hf
  let p := x 0
  have hx0 : Tendsto (fun t : ℝ => riemannianEDistOf (g t) p (x t)) (𝓝 0) (𝓝 0) := by
    have hh := (continuousAt_riemannianEDistOf_center g (Filter.univ_mem) hquad p).tendsto.comp
      (continuousAt_id.prodMk hx).tendsto
    simpa only [p, Function.comp_def, id_eq, riemannianEDistOf_self] using hh
  have hy0 : Tendsto (fun t : ℝ => riemannianEDistOf (g t) p (y t)) (𝓝 0) (𝓝 0) := by
    have hpair : Tendsto (fun t : ℝ => (t, y t)) (𝓝 0) (𝓝 (0, p)) := by
      simpa only [id_eq, p, hxy] using (continuousAt_id.prodMk hy).tendsto
    have hh := (continuousAt_riemannianEDistOf_center g (Filter.univ_mem) hquad p).tendsto.comp hpair
    simpa only [Function.comp_def, riemannianEDistOf_self] using hh
  have hsum : Tendsto (fun t : ℝ => riemannianEDistOf (g t) p (x t) +
      riemannianEDistOf (g t) p (y t)) (𝓝 0) (𝓝 0) := by simpa using hx0.add hy0
  have hed : Tendsto (fun t : ℝ => riemannianEDistOf (g t) (x t) (y t)) (𝓝 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro t
    simpa only [riemannianEDistOf_comm (g t) (x t) p] using
      riemannianEDistOf_triangle (g t) (x t) p (y t)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hed
  change Tendsto _ (𝓝[Ici 0] 0) _
  simp only [neg_zero, hxy, riemannianEDistOf_self, ENNReal.toReal_zero]
  apply (hreal.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_def, g, abs_of_nonneg (mem_Ici.mp ht)]

theorem continuousOn_moving_distance_from_common_initial_point
    [I.Boundaryless] {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (x y : ℝ → F.M)
    (hx0 : ContinuousAt x 0) (hy0 : ContinuousAt y 0) (hxy : x 0 = y 0)
    (hx : ∀ s ∈ Ioc 0 tau, ContMDiffAt 𝓘(ℝ, ℝ) I 1 x s)
    (hy : ∀ s ∈ Ioc 0 tau, ContMDiffAt 𝓘(ℝ, ℝ) I 1 y s) :
    ContinuousOn
      (fun t => (riemannianEDistOf (F.S.base.metric (-t)) (x t) (y t)).toReal)
      (Icc 0 tau) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact (continuousWithinAt_moving_distance_zero F x y hx0 hy0 hxy).mono Icc_subset_Ici_self
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hhalf : 0 < t / 2 := half_pos htpos
  have hhalf_le : t / 2 ≤ tau := (half_le_self htpos.le).trans ht.2
  have hac := KappaSolutions.IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance
    F hF hhalf hhalf_le x y
    (fun s hs => (hx s ⟨hhalf.trans_le hs.1, hs.2⟩).contMDiffWithinAt)
    (fun s hs => (hy s ⟨hhalf.trans_le hs.1, hs.2⟩).contMDiffWithinAt)
  have hc := hac.continuousOn t (by simpa only [uIcc_of_le hhalf_le] using
    (show t ∈ Icc (t / 2) tau from ⟨half_le_self htpos.le, ht.2⟩))
  apply hc.mono_of_mem_nhdsWithin
  rw [uIcc_of_le hhalf_le]
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds (half_lt_self htpos))]
    with s hs hsleft
  exact ⟨hsleft, hs.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
