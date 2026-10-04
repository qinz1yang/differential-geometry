import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Metric.LipschitzScaleMultiplicity
import DifferentialGeometry.Geometry.Metric.LipschitzScaleSelectionFinite

/-!
# Multiplicity of scale balls for arbitrary disjoint families (LC86, Riemannian part)

Blueprint row LC86 (`lem:collapse-local-selection-packet`, master207A): on a compact Riemannian
manifold with a positive `Λ`-Lipschitz scale `ρ`, `Λ C ≤ 1 / 4` and a common normalized lower Ricci
bound on the enlarged comparison balls `B(i, (3 C + 2 a) ρ(i))`, the multiplicity of the `C ρ`-balls of
ANY pairwise disjoint family of `a ρ`-balls is bounded by a model-volume ratio depending only on
`a`, `C`, the dimension and the curvature constant.  Combined with the metric part
(`LipschitzScaleSelectionFinite`), every maximal family with centres in a stratum is finite, its
`4 a ρ`-balls cover the stratum and its multiplicity obeys the same bound.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompactSpace M]

open _root_.Metric DifferentialGeometry.Integral.Measure

/-- LC86: the multiplicity bound for an arbitrary finite pairwise disjoint family of `a ρ`-balls
whose enlarged comparison balls carry a common normalized lower Ricci bound. -/
theorem card_le_of_ricci_bound_of_disjoint_finset
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (J : Finset M) {ρ : M → ℝ} {Λ : NNReal} {a C q : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ i ∈ J, 0 < ρ i)
    (ha : 0 < a) (hC : 0 ≤ C) (hq : 0 ≤ q) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hdisj : (J : Set M).PairwiseDisjoint (fun i => ball i (a * ρ i)))
    (hRic : ∀ i ∈ J, ricciBoundedBelowOn (I := I) g
      (ball i ((3 * C + 2 * a) * ρ i))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ i) ^ 2))))
    (x : M) (hx : ∀ i ∈ J, x ∈ ball i (C * ρ i)) :
    (J.card : ℝ) ≤ modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let D := 3 * C + 2 * a
  have haD : a ≤ D := by dsimp only [D]; linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
    modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hball (p : M) (r : ℝ) :
      {y : M | riemannianEDist I p y < ENNReal.ofReal r} = ball p r := by
    ext y
    rw [mem_ofPred_eq, ← IsRiemannianManifold.out (I := I), edist_lt_ofReal]
    exact dist_comm p y ▸ Iff.rfl
  apply GC.MetricGeometry.card_le_of_lipschitz_scale_ball_overlap μ J hρ hρpos ha.le hC
    (div_nonneg (hm D (ha.trans_le haD)).le (hm _ ha).le) hoverlap hdisj
  · intro i hi
    exact ENNReal.toReal_pos (measure_ball_pos μ i (mul_pos ha (hρpos i hi))).ne'
      (measure_ne_top μ _)
  · intro i _
    exact measure_ne_top μ _
  · intro i hi
    have hric := hRic i hi
    rw [← hball i (D * ρ i)] at hric
    have hc := ballVolume_mul_scale_le_model_ratio g hEnorm i hq (hρpos i hi) ha haD hric
    have hv (r : ℝ) : ballVolume g i r = μ (ball i r) := by
      simp only [ballVolume, μ, hball]
    rw [hv, hv] at hc
    have hc' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hc
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (ha.trans_le haD)).le (hm _ ha).le)] at hc'
    simpa only [D, Measure.real] using hc'
  · exact hx

/-- LC86: for ANY pairwise disjoint family of `a ρ`-balls on a compact manifold (finite by
compactness), the number of members whose `C ρ`-ball contains a given point is bounded by the
model-volume ratio. -/
theorem ncard_le_of_ricci_bound_of_pairwiseDisjoint
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (J : Set M) {ρ : M → ℝ} {Λ : NNReal} {a C q : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (ha : 0 < a) (hC : 0 ≤ C) (hq : 0 ≤ q) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hdisj : J.PairwiseDisjoint (fun i => ball i (a * ρ i)))
    (hRic : ∀ i ∈ J, ricciBoundedBelowOn (I := I) g
      (ball i ((3 * C + 2 * a) * ρ i))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ i) ^ 2))))
    (x : M) :
    ((J ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  classical
  obtain ⟨N, hN⟩ := GC.MetricGeometry.exists_ncard_bound_of_pairwiseDisjoint_scale_balls
    hρ.continuous hρpos ha
  have hJ : J.Finite := (hN J hdisj).1
  let T := J ∩ {i | x ∈ ball i (C * ρ i)}
  have hT : T.Finite := hJ.subset inter_subset_left
  have ht (i : M) : i ∈ hT.toFinset ↔ i ∈ J ∧ x ∈ ball i (C * ρ i) := by
    simp only [Set.Finite.mem_toFinset, T, mem_inter_iff, mem_ofPred_eq]
  have hh := card_le_of_ricci_bound_of_disjoint_finset g hEnorm hT.toFinset hρ
    (fun i _ => hρpos i) ha hC hq hoverlap
    (fun i hi j hj hij => hdisj (ht i |>.mp hi).1 (ht j |>.mp hj).1 hij)
    (fun i hi => hRic i (ht i |>.mp hi).1) x (fun i hi => (ht i |>.mp hi).2)
  change (T.ncard : ℝ) ≤ _
  rw [Set.ncard_eq_toFinset_card T hT]
  exact hh

/-- LC86 (whole row, Riemannian form): on a compact Riemannian manifold with a positive
`Λ`-Lipschitz scale, `Λ a ≤ 1 / 2`, `Λ C ≤ 1 / 4` and a common normalized lower Ricci bound on the
enlarged comparison balls about the points of a stratum `S`, maximal pairwise disjoint families
of `a ρ`-balls with centres in `S` exist, and every such family is finite, its `4 a ρ`-balls cover
`S`, and the multiplicity of its `C ρ`-balls is bounded by the model-volume ratio. -/
theorem maximal_scale_selection_of_ricci_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (S : Set M) {ρ : M → ℝ} {Λ : NNReal} {a C q : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (ha : 0 < a) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hsmall : (Λ : ℝ) * a ≤ 1 / 2) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (ball p ((3 * C + 2 * a) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2)))) :
    (∃ J : Set M, Maximal (fun K : Set M => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => ball i (a * ρ i))) J) ∧
    ∀ J : Set M, Maximal (fun K : Set M => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => ball i (a * ρ i))) J →
      J.Finite ∧ S ⊆ ⋃ i ∈ J, ball i (4 * a * ρ i) ∧
      ∀ x : M, ((J ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  obtain ⟨_, hex, hall⟩ := GC.MetricGeometry.lipschitz_scale_maximal_selection S hρ hρpos ha hsmall
  refine ⟨hex, fun J hJ => ⟨(hall J hJ).1, (hall J hJ).2, fun x => ?_⟩⟩
  exact ncard_le_of_ricci_bound_of_pairwiseDisjoint g hEnorm J hρ hρpos ha hC hq hoverlap hJ.1.2
    (fun i hi => hRic i (hJ.1.1 hi)) x

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
