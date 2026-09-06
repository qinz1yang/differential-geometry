import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact

noncomputable section

open Bundle Filter Set
open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

theorem IsCompact.bundle_norm_le {C : Set B} (hC : IsCompact C) (R : ℝ) :
    IsCompact {z : TotalSpace F V | z.proj ∈ C ∧ ‖z.2‖ ≤ R} := by
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro f hf
  have hfC : C ∈ f.map TotalSpace.proj := by
    change {z : TotalSpace F V | z.proj ∈ C} ∈ f
    exact Filter.mem_of_superset hf (fun _ h => h.1)
  obtain ⟨b, hbC, hb⟩ := hC.ultrafilter_le_nhds' (f.map TotalSpace.proj) hfC
  have hbase : Tendsto TotalSpace.proj (f : Filter (TotalSpace F V)) (𝓝 b) := hb
  let e := trivializationAt F V b
  have heb : b ∈ e.baseSet := mem_baseSet_trivializationAt F V b
  obtain ⟨L, hL, hnear⟩ := eventually_norm_trivializationAt_lt F V b
  have hevent : ∀ᶠ z : TotalSpace F V in (f : Filter (TotalSpace F V)),
      z ∈ e.source ∧ ‖(e z).2‖ ≤ L * R := by
    filter_upwards [hf, hbase.eventually (e.open_baseSet.mem_nhds heb),
      hbase.eventually hnear] with z hz hze hzL
    refine ⟨e.mem_source.mpr hze, ?_⟩
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hze z.2]
    exact ((e.continuousLinearMapAt ℝ z.proj).le_opNorm z.2).trans
      ((mul_le_mul_of_nonneg_right hzL.le (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hz.2 hL.le))
  have hcoord : Metric.closedBall (0 : F) (L * R) ∈ f.map (fun z => (e z).2) := by
    change {z : TotalSpace F V | (e z).2 ∈ Metric.closedBall (0 : F) (L * R)} ∈ f
    filter_upwards [hevent] with z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
  obtain ⟨v, _, hv⟩ := (isCompact_closedBall (0 : F) (L * R)).ultrafilter_le_nhds'
    (f.map (fun z => (e z).2)) hcoord
  have hv' : Tendsto (fun z => (e z).2) (f : Filter (TotalSpace F V)) (𝓝 v) := hv
  have he : Tendsto e (f : Filter (TotalSpace F V)) (𝓝 (b, v)) := by
    apply (hbase.prodMk_nhds hv').congr'
    filter_upwards [hevent] with z hz
    exact Prod.ext (e.coe_fst hz.1).symm rfl
  have hw : Tendsto id (f : Filter (TotalSpace F V))
      (𝓝 (e.toOpenPartialHomeomorph.symm (b, v))) := by
    apply ((e.toOpenPartialHomeomorph.continuousAt_symm
      (e.mem_target.mpr heb)).tendsto.comp he).congr'
    filter_upwards [hevent] with z hz
    exact e.left_inv hz.1
  have hncont : Continuous (fun z : TotalSpace F V => ‖z.2‖) := by
    have hi : Continuous (fun z : TotalSpace F V => inner ℝ z.2 z.2) :=
      continuous_id.inner_bundle continuous_id
    simpa only [← norm_eq_sqrt_real_inner] using hi.sqrt
  refine ⟨e.toOpenPartialHomeomorph.symm (b, v), ⟨?_, ?_⟩, hw⟩
  · simpa only [e.proj_symm_apply' heb] using hbC
  · exact (isClosed_le hncont continuous_const).mem_of_tendsto hw
      (Filter.mem_of_superset hf (fun _ h => h.2))
