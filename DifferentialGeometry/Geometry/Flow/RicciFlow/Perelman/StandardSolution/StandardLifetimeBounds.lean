import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderIdentification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CylinderReferenceCopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cylinder := Metric.sphere (0 : E3) 1 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem not_exists_continuous_metric_extension_shrinkingCylinder :
    ¬ ∃ g : ℝ → SmoothRiemannianMetric IC Cylinder,
      (∀ (x : Cylinder) (v w : TangentSpace IC x),
        ContinuousOn (fun t => (g t).inner x v w) (Icc 0 1)) ∧
      ∀ t ∈ Ico (0 : ℝ) 1, g t = shrinkingCylinderMetric (E := E3) t := by
  rintro ⟨g, hcont, heq⟩
  let x : Cylinder := (DifferentialGeometry.Geometry.Neck.spherePoint, 0)
  let v : TangentSpace IC x := (EuclideanSpace.single 0 1, 0)
  have hv : v ≠ 0 := by
    intro h
    have h' := congrArg (fun w : TangentSpace IC x => w.1 0) h
    change (1 : ℝ) = 0 at h'
    exact one_ne_zero h'
  let A := (roundMetric (E := E3) (n := 2)).inner x.1 v.1 v.1
  have he : EqOn (fun t => (g t).inner x v v) (fun t => 2 * (1 - t) * A) (Ico 0 1) := by
    intro t ht
    change (g t).inner x v v = 2 * (1 - t) * A
    rw [heq t ht, shrinkingCylinderMetric_inner ht.2]
    simp only [v, mul_zero, add_zero, A]
  have hg : ContinuousOn (fun t => (g t).inner x v v) (closure (Ico (0 : ℝ) 1)) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact hcont x v v
  have ha : ContinuousOn (fun t => 2 * (1 - t) * A) (closure (Ico (0 : ℝ) 1)) := by
    fun_prop
  have hzero := he.of_subset_closure hg ha subset_closure Subset.rfl
  have hm : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have hz : (g 1).inner x v v = 0 := by simpa using hzero hm
  exact (ne_of_gt ((g 1).pos x v hv)) hz


private theorem metric_inner_continuousOn_of_gram
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hgram : ∀ (q : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) q p.2 i j)
        (A ×ˢ (trivializationAt E (TangentSpace I) q).baseSet))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => (g t).inner x v w) A := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  exact (tensor0SEvalCLM (I := I) (vec2 v w)).continuous.comp_continuousOn
    (metricCovDeriv_contDiffOn_time g A hgram (g 0) 0 x).continuousOn

private theorem cylinderCopy_extension_impossible
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) cylinderReferenceCopy.Q)
    (hcont : ∀ (x : cylinderReferenceCopy.Q) (v w : TangentSpace (𝓡 3) x),
      ContinuousOn (fun t => (g t).inner x v w) (Icc 0 1))
    (heq : ∀ t ∈ Ico (0 : ℝ) 1,
      Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv =
        shrinkingCylinderMetric (E := E3) t) : False := by
  apply not_exists_continuous_metric_extension_shrinkingCylinder
  refine ⟨fun t => Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv, ?_, heq⟩
  intro x v w
  simpa only [Diffeomorph.pullbackMetricCross_inner] using hcont (cylinderReferenceCopy.equiv x)
    (mfderiv IC (𝓡 3) cylinderReferenceCopy.equiv x v)
    (mfderiv IC (𝓡 3) cylinderReferenceCopy.equiv x w)


theorem uniformStandardLifetime_le_one : uniformStandardLifetime ≤ 1 := by
  by_contra hnot
  obtain ⟨τ, hτ0, hτ1, hτLife⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hnot)
  have honeτ : (1 : ℝ) < τ := ENNReal.one_lt_ofReal.mp hτ1
  have hτ : 0 < τ := zero_lt_one.trans honeτ
  obtain ⟨S₀⟩ := standard_solution_nonempty
  let S : ℕ → StandardSolution := fun _ => S₀
  let x : ℕ → E3 := fun n => EuclideanSpace.single 0 (n : ℝ)
  have hescape : Tendsto
      (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) atTop atTop := by
    have heq : (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) =
        fun n : ℕ => (n : ℝ) := by
      funext n
      rw [(S n).val.initial, StandardCap.distance_zero]
      simp only [x, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
      exact abs_of_nonneg (Nat.cast_nonneg n)
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  obtain ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hmono, hcharts', hzero, hpull, hcomplete,
    hjets, hgram, hpde, hsolutions, hconverge, htime⟩ :=
      exists_standard_cylinder_closed_limit τ hτ hτLife S x hescape
  have hid := standard_cylinder_closed_limit_eq_shrinking Φ
    (standardClosedPointedMaps_sourceSigma Φ) (standardClosedPointedMaps_targetSigma Φ)
    hinit bf co hzero hgram hpde
  let : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
  let : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
  let : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
  let : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
  let : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact
  apply cylinderCopy_extension_impossible co.gInf
  · intro p v w
    exact (metric_inner_continuousOn_of_gram co.gInf (Icc 0 τ) hgram p v w).mono
      (Icc_subset_Icc_right honeτ.le)
  · intro t ht
    exact hid t ⟨ht.1, ht.2.le.trans honeτ.le⟩ ht.2

end DifferentialGeometry.PDE.RicciFlow
