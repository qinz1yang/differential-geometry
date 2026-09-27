import DifferentialGeometry.Geometry.Metric.HalfClosedJets
import DifferentialGeometry.Topology.ClosureSupremum
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Metric.SmoothRiemannianMetricOn
private theorem continuousWithinAt_of_local_eq
    {M : Type*} [TopologicalSpace M] {D : Set M} {q : M} (hq : q ∈ D)
    (U : TopologicalSpace.Opens M) (hqU : q ∈ U)
    (f : M → ℝ) (g : U → ℝ) (hg : Continuous g)
    (heq : ∀ y : U, (y : M) ∈ D → f (y : M) = g y) :
    ContinuousWithinAt f D q := by
  classical
  let F : M → ℝ := fun y => if hy : y ∈ U then g ⟨y, hy⟩ else 0
  have hcomp : F ∘ (Subtype.val : U → M) = g := by
    funext y
    simp only [Function.comp_apply, F, dif_pos y.2]
  have hccomp : ContinuousAt (F ∘ (Subtype.val : U → M)) ⟨q, hqU⟩ :=
    hcomp.symm ▸ hg.continuousAt
  have hc : ContinuousAt F q :=
    (U.isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff
      (g := F) (x := ⟨q, hqU⟩)).mp hccomp
  apply hc.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hq
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (U.isOpen.mem_nhds hqU)]
    with y hyD hyU
  change f y = if hy : y ∈ U then g ⟨y, hy⟩ else 0
  split_ifs with hy
  · exact heq ⟨y, hy⟩ hyD
  · exact False.elim (hy hyU)

section General
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private theorem metricCovDeriv_restrictOpen_eq
    (g gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (m : ℕ) (x : U) :
    metricCovDeriv (g.restrictOpen U) (gRef.restrictOpen U) m x =
      metricCovDeriv g gRef m (x : M) := by
  ext slots
  simpa only [metricCovDeriv_eq_covDerivOfField] using!
    covDerivOfField_restrictOpen gRef U
      (Tensor0SBundle.metricTensorField (g.restrictOpen U))
      (Tensor0SBundle.metricTensorField g) (fun y slots => rfl) m x slots
end General

section Cylinder
variable {E H S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S] [T2Space S]
  {A : ℝ}

def halfClosedDerivNorm
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) : ℝ := by
  classical
  exact if hq : q ∈ univ ×ˢ Ioc (-A) 0 then
    Real.sqrt (Tensor0SBundle.normSq0S gRef q (m + 2)
      (h.halfClosedCovDeriv gRef m q hq - metricCovDeriv gInf gRef m q)) else 0

theorem halfClosedDerivNorm_of_mem
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) :
    h.halfClosedDerivNorm gInf gRef m q =
      Real.sqrt (Tensor0SBundle.normSq0S gRef q (m + 2)
        (h.halfClosedCovDeriv gRef m q hq - metricCovDeriv gInf gRef m q)) := by
  simp only [halfClosedDerivNorm, dif_pos hq]

theorem halfClosedDerivNorm_nonneg
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) : 0 ≤ h.halfClosedDerivNorm gInf gRef m q := by
  classical
  unfold halfClosedDerivNorm
  split_ifs <;> positivity

theorem halfClosedDerivNorm_congr
    (h₁ h₂ : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (heq : ∀ y ∈ (univ ×ˢ Ioc (-A) 0 : Set (S × ℝ)),
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, h₁.inner y v w = h₂.inner y v w)
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) :
    h₁.halfClosedDerivNorm gInf gRef m q = h₂.halfClosedDerivNorm gInf gRef m q := by
  classical
  by_cases hq : q ∈ univ ×ˢ Ioc (-A) 0
  · rw [h₁.halfClosedDerivNorm_of_mem gInf gRef m q hq,
      h₂.halfClosedDerivNorm_of_mem gInf gRef m q hq]
    exact congrArg (fun C : Tensor0SBundle.Tensor0SSpace (m + 2) (I.prod 𝓘(ℝ)) q =>
      Real.sqrt (Tensor0SBundle.normSq0S gRef q (m + 2) (C - metricCovDeriv gInf gRef m q)))
      (h₁.halfClosedCovDeriv_congr h₂ heq gRef m q hq)
  · simp only [halfClosedDerivNorm, dif_neg hq]

theorem halfClosedDerivNorm_eq_local
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (U : TopologicalSpace.Opens (S × ℝ)) (k : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U)
    (heq : ∀ y : U, (y : S × ℝ) ∈ univ ×ˢ Ioc (-A) 0 →
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, k.inner y v w = h.inner (y : S × ℝ) v w)
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) (hqU : q ∈ U) :
    h.halfClosedDerivNorm gInf gRef m q =
      metricDerivNorm m k (gInf.restrictOpen U) (gRef.restrictOpen U) ⟨q, hqU⟩ := by
  rw [h.halfClosedDerivNorm_of_mem gInf gRef m q hq]
  have hj := h.halfClosedCovDeriv_eq_local gRef U k heq m q hq hqU
  have hi := metricCovDeriv_restrictOpen_eq gInf gRef U m ⟨q, hqU⟩
  have hd : h.halfClosedCovDeriv gRef m q hq - metricCovDeriv gInf gRef m q =
      metricCovDeriv k (gRef.restrictOpen U) m ⟨q, hqU⟩ -
        metricCovDeriv (gInf.restrictOpen U) (gRef.restrictOpen U) m ⟨q, hqU⟩ :=
    congrArg₂ (· - ·) hj hi.symm
  exact (congrArg (fun C : Tensor0SBundle.Tensor0SSpace (m + 2) (I.prod 𝓘(ℝ)) q =>
    Real.sqrt (Tensor0SBundle.normSq0S gRef q (m + 2) C)) hd).trans
      (congrArg Real.sqrt (normSq0S_restrictOpen_apply gRef U (m + 2) ⟨q, hqU⟩ _).symm)

theorem continuousOn_halfClosedDerivNorm
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (m : ℕ) :
    ContinuousOn (h.halfClosedDerivNorm gInf gRef m) (univ ×ˢ Ioc (-A) 0) := by
  intro q hq
  obtain ⟨U, hqU, _, k, heq⟩ :=
    exists_local_metric_extension_of_halfClosed_cylinder_section
      h.inner h.contMDiffOn h.symm h.pos q hq
  apply continuousWithinAt_of_local_eq hq U hqU
    (h.halfClosedDerivNorm gInf gRef m)
    (fun y : U => metricDerivNorm m k (gInf.restrictOpen U) (gRef.restrictOpen U) y)
    (metricDerivNorm_cont m k (gInf.restrictOpen U) (gRef.restrictOpen U))
  intro y hy
  exact h.halfClosedDerivNorm_eq_local gInf gRef U k heq m (y : S × ℝ) hy y.2

def halfClosedDerivENormSup
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (p : ℕ) : ℝ≥0∞ :=
  ⨆ (j : ℕ) (_ : j ≤ p) (q : S × ℝ) (_ : q ∈ univ ×ˢ Ioc (-A) 0),
    ENNReal.ofReal (h.halfClosedDerivNorm gInf gRef j q)

theorem halfClosedDerivENormSup_congr
    (h₁ h₂ : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (heq : ∀ y ∈ (univ ×ˢ Ioc (-A) 0 : Set (S × ℝ)),
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, h₁.inner y v w = h₂.inner y v w)
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (p : ℕ) :
    h₁.halfClosedDerivENormSup gInf gRef p = h₂.halfClosedDerivENormSup gInf gRef p := by
  unfold halfClosedDerivENormSup
  refine iSup_congr fun j => iSup_congr fun _ => iSup_congr fun q => iSup_congr fun _ => ?_
  exact congrArg ENNReal.ofReal (h₁.halfClosedDerivNorm_congr h₂ heq gInf gRef j q)

theorem ofReal_halfClosedDerivNorm_le_sup
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (p : ℕ)
    {j : ℕ} (hj : j ≤ p) {q : S × ℝ} (hq : q ∈ univ ×ˢ Ioc (-A) 0) :
    ENNReal.ofReal (h.halfClosedDerivNorm gInf gRef j q) ≤
      h.halfClosedDerivENormSup gInf gRef p :=
  le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le q (le_iSup_of_le hq le_rfl)))

theorem halfClosedDerivENormSup_le_iff
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (p : ℕ) (C : ℝ≥0∞) :
    h.halfClosedDerivENormSup gInf gRef p ≤ C ↔
      ∀ j ≤ p, ∀ q ∈ univ ×ˢ Ioc (-A) 0,
        ENNReal.ofReal (h.halfClosedDerivNorm gInf gRef j q) ≤ C := by
  simp only [halfClosedDerivENormSup, iSup_le_iff]

theorem halfClosedDerivENormSup_eq_interior
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gInf gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ)) (p : ℕ)
    (U : TopologicalSpace.Opens (S × ℝ))
    (hU : (U : Set (S × ℝ)) = univ ×ˢ Ioo (-A) 0) :
    h.halfClosedDerivENormSup gInf gRef p =
      metricDerivENormSupOn univ p
        (h.restrictOpen U (by rw [hU]; exact prod_mono_right Ioo_subset_Ioc_self))
        (gInf.restrictOpen U) (gRef.restrictOpen U) := by
  have hsub : (univ : Set S) ×ˢ Ioo (-A) 0 ⊆ univ ×ˢ Ioc (-A) 0 :=
    prod_mono_right Ioo_subset_Ioc_self
  have hclosure : (univ : Set S) ×ˢ Ioc (-A) 0 ⊆ closure (univ ×ˢ Ioo (-A) 0) := by
    intro q hq
    rw [closure_prod_eq, closure_univ,
      closure_Ioo (ne_of_lt (lt_of_lt_of_le hq.2.1 hq.2.2))]
    exact ⟨mem_univ _, hq.2.1.le, hq.2.2⟩
  have hsup (j : ℕ) :
      (⨆ q ∈ (univ : Set S) ×ˢ Ioc (-A) 0,
        ENNReal.ofReal (h.halfClosedDerivNorm gInf gRef j q)) =
      ⨆ q ∈ (univ : Set S) ×ˢ Ioo (-A) 0,
        ENNReal.ofReal (h.halfClosedDerivNorm gInf gRef j q) := by
    apply DifferentialGeometry.Topology.iSup_eq_of_subset_of_subset_closure hsub hclosure
    intro q hq
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      (h.continuousOn_halfClosedDerivNorm gInf gRef j)) q hq.1).mono hsub
  have hUD : (U : Set (S × ℝ)) ⊆ univ ×ˢ Ioc (-A) 0 := by rw [hU]; exact hsub
  unfold halfClosedDerivENormSup metricDerivENormSupOn
  apply iSup_congr
  intro j
  apply iSup_congr
  intro hj
  rw [hsup j]
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => ?_
    have hqU : q ∈ U := by change q ∈ (U : Set (S × ℝ)); rw [hU]; exact hq
    have hn := h.halfClosedDerivNorm_eq_local gInf gRef U (h.restrictOpen U hUD)
      (fun _ _ _ _ => rfl) j q (hsub hq) hqU
    rw [hn]
    exact le_iSup_of_le ⟨q, hqU⟩ (le_iSup_of_le (mem_univ _) le_rfl)
  · refine iSup_le fun x => iSup_le fun _ => ?_
    have hn := h.halfClosedDerivNorm_eq_local gInf gRef U (h.restrictOpen U hUD)
      (fun _ _ _ _ => rfl) j (x : S × ℝ) (hUD x.2) x.2
    rw [← hn]
    exact le_iSup_of_le (x : S × ℝ) (le_iSup_of_le (by rw [← hU]; exact x.2) le_rfl)
end Cylinder
end DifferentialGeometry.Geometry.Metric.SmoothRiemannianMetricOn
