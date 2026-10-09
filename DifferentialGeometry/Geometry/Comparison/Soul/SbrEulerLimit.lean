import DifferentialGeometry.Geometry.Comparison.Soul.SbrEulerPolygons
import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_nearest_superlevel_euler_limit
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a T m : ℝ} (ha : 0 ≤ a) (haT : a < T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = a) :
    let mesh : ℕ → ℝ := fun k => (T - a) / ((k + 1 : ℕ) : ℝ)
    let time : ℕ → ℕ → ℝ := fun k i => a + (i : ℝ) * mesh k
    let K : ℝ≥0 := Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))
    ∃ (node : ℕ → ℕ → M) (v : (k i : ℕ) → TangentSpace I (node k i))
      (polygon : ℕ → ℝ → M) (phi : ℕ → ℕ) (eta : ℝ → M),
      (∀ k : ℕ, node k 0 = x ∧
        (∀ i ≤ k + 1, F (node k i) = time k i) ∧
        (∀ i ≤ k + 1, node k i ∈ {z : M | 0 ≤ F z}) ∧
        (∀ i < k + 1,
          IsMinOn (dist (node k i)) {z : M | time k (i + 1) ≤ F z} (node k (i + 1)) ∧
            dist (node k i) (node k (i + 1)) ≤ K * mesh k) ∧
        (∀ i < k + 1, intrinsicGeodesic g hEnorm (node k i) (v k i) 1 = node k (i + 1) ∧
          Real.sqrt (g.inner (node k i) (v k i) (v k i)) = dist (node k i) (node k (i + 1))) ∧
        LipschitzWith K (polygon k) ∧ polygon k a = x ∧
        (∀ i ≤ k + 1, polygon k (time k i) = node k i) ∧
        (∀ i < k + 1, EqOn (polygon k)
          (fun t => intrinsicGeodesic g hEnorm (node k i) (v k i) ((t - time k i) / mesh k))
          (Icc (time k i) (time k (i + 1)))) ∧
        MapsTo (polygon k) (Icc a T) {z : M | 0 ≤ F z} ∧
        ∀ t ∈ Icc a T, t ≤ F (polygon k t) ∧
          F (polygon k t) ≤ t + (L : ℝ) * K * mesh k) ∧
      StrictMono phi ∧
      Tendsto (fun n => mesh (phi n)) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n => polygon (phi n)) eta atTop (Icc a T) ∧
      LipschitzWith K eta ∧ eta a = x ∧
      MapsTo eta (Icc a T) {z : M | 0 ≤ F z} ∧
      ∀ t ∈ Icc a T, F (eta t) = t := by
  classical
  dsimp only
  let mesh : ℕ → ℝ := fun k => (T - a) / ((k + 1 : ℕ) : ℝ)
  let time : ℕ → ℕ → ℝ := fun k i => a + (i : ℝ) * mesh k
  let K : ℝ≥0 := Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))
  have hpolygons := fun k : ℕ => exists_nearest_superlevel_euler_polygon
    g hEnorm F L hF hconc hC ha haT hTm hmax (k + 1) (Nat.succ_pos k) x hx
  dsimp only at hpolygons
  choose node v polygon hnode0 hnodelevel hnodeC hstep hmin hpolyLip hpolyStart
    hpolyNodes hpolyPieces hpolyMaps hpolyLevels using hpolygons
  let family : ℕ → C(Icc a T, M) := fun k =>
    ⟨fun t => polygon k t.1, (hpolyLip k).continuous.comp continuous_subtype_val⟩
  have hfamilyLip (k : ℕ) : LipschitzWith K (family k) := by
    simpa only [mul_one, family, K, ContinuousMap.coe_mk, Function.comp_def] using
      (hpolyLip k).comp (LipschitzWith.subtype_val (Icc a T))
  have hequi : Equicontinuous (fun k => (family k : Icc a T → M)) :=
    (LipschitzWith.uniformEquicontinuous
      (fun k => (family k : Icc a T → M)) K hfamilyLip).equicontinuous
  obtain ⟨phi, limit, hphi, hconv⟩ := DifferentialGeometry.Analysis.arzela_subseq_compact
    {z : M | 0 ≤ F z} hC family (fun k t => hpolyMaps k t.2) hequi
  have hlimitLip : LipschitzWith K limit := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    apply le_of_tendsto ((hconv.tendsto_at s).dist (hconv.tendsto_at t))
    exact Eventually.of_forall fun n => (hfamilyLip (phi n)).dist_le_mul s t
  let eta : ℝ → M := fun t => limit (projIcc a T haT.le t)
  have hetaLip : LipschitzWith K eta := by
    simpa only [mul_one, eta, Function.comp_def] using
      hlimitLip.comp (LipschitzWith.projIcc haT.le)
  have hetaRestrict : eta ∘ (Subtype.val : Icc a T → ℝ) = (limit : Icc a T → M) := by
    funext t
    dsimp only [eta, Function.comp_def]
    rw [projIcc_val haT.le]
  have huniform : TendstoUniformlyOn (fun n => polygon (phi n)) eta atTop (Icc a T) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, hetaRestrict]
    exact hconv
  have hetaStart : eta a = x := by
    have hstartlim : Tendsto (fun _ : ℕ => x) atTop (𝓝 (eta a)) := by
      simpa only [hpolyStart] using huniform.tendsto_at (show a ∈ Icc a T from ⟨le_rfl, haT.le⟩)
    exact tendsto_nhds_unique hstartlim tendsto_const_nhds
  have hetaMaps : MapsTo eta (Icc a T) {z : M | 0 ≤ F z} := by
    intro t ht
    exact hC.isClosed.mem_of_tendsto (huniform.tendsto_at ht)
      (Eventually.of_forall fun n => hpolyMaps (phi n) ht)
  have hmesh : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh, Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T - a)
  have hsubmesh : Tendsto (fun n => mesh (phi n)) atTop (𝓝 0) :=
    hmesh.comp hphi.tendsto_atTop
  have herr : Tendsto (fun n => (L : ℝ) * K * mesh (phi n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsubmesh.const_mul ((L : ℝ) * K)
  have hetaLevel : ∀ t ∈ Icc a T, F (eta t) = t := by
    intro t ht
    have hvalue : Tendsto (fun n => F (polygon (phi n) t)) atTop (𝓝 (F (eta t))) :=
      hF.continuous.continuousAt.tendsto.comp (huniform.tendsto_at ht)
    have hlower : t ≤ F (eta t) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hvalue
        (Eventually.of_forall fun n => (hpolyLevels (phi n) t ht).1)
    have huplimit : Tendsto (fun n => t + (L : ℝ) * K * mesh (phi n)) atTop (𝓝 t) := by
      simpa only [add_zero] using herr.const_add t
    have hupper : F (eta t) ≤ t :=
      le_of_tendsto_of_tendsto hvalue huplimit
        (Eventually.of_forall fun n => (hpolyLevels (phi n) t ht).2)
    exact le_antisymm hupper hlower
  refine ⟨node, v, polygon, phi, eta, ?_, hphi, hsubmesh, huniform,
    hetaLip, hetaStart, hetaMaps, hetaLevel⟩
  intro k
  exact ⟨hnode0 k, hnodelevel k, hnodeC k, hstep k, hmin k, hpolyLip k,
    hpolyStart k, hpolyNodes k, hpolyPieces k, hpolyMaps k, hpolyLevels k⟩

end DifferentialGeometry.Geometry.Topology

end
