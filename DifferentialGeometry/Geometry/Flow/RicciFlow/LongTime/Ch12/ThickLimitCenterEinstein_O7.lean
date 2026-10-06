import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.Pinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

/-!
# CH12-O7 / C1, group E: equality in the trace inequality forces Einstein

* `ricci_eq_of_normSq_le_O7` (E1): in dimension three, `|Ric|² ≤ R²/3` at `x` forces
  `Ric = (R/3) g` at `x` (the reverse inequality always holds).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

section Algebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

/-- **E1.** Equality in the trace inequality: `|Ric|² ≤ R²/3` forces `Ric = (R/3) g`. -/
theorem ricci_eq_of_normSq_le_O7 [T2Space M] (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (h : normSq0S g x 2 (metricRicciAt g x) ≤ (metricScalarAt g x) ^ 2 / 3) :
    ∀ v w : TangentSpace ThreeModel x,
      ricciTensor g x v w = metricScalarAt g x / 3 * g.inner x v w := by
  classical
  intro v w
  let Ric := metricRicciAt g x
  have hdimT : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp
  have hsym : RicciSymAt (I := ThreeModel) Ric := fun X Y => metricRicciAt_symm g x X Y
  obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ := ricciEigen3 (I := ThreeModel) g Ric hdimT hsym
  have hscalarTrace := PDE.RicciFlow.scalarTrace_delta (I := ThreeModel) g Ric horth
  have hscalar : metricScalarAt g x = ricciEigenScalar3 l1 l2 l3 :=
    PDE.RicciFlow.scalar_eq_diag (I := ThreeModel) hscalarTrace hdiag
  have hinv : MetricInverseInBasis (I := ThreeModel) g x basis delta3 :=
    orthonormal_invBasis3 (I := ThreeModel) g basis horth
  have hnorm : normSq0S g x 2 Ric = ricciEigenNormSq3 l1 l2 l3 := by
    rw [← PDE.RicciFlow.ricciNorm_inner (I := ThreeModel) g Ric basis hinv]
    exact PDE.RicciFlow.ricciNormAt_diag (I := ThreeModel) hdiag
  have htf : tracefreeRicciEigenNormSq3 l1 l2 l3 = 0 := by
    have h1 := tracefreeRicciEigenNormSq3_nonneg l1 l2 l3
    have h2 : tracefreeRicciEigenNormSq3 l1 l2 l3 ≤ 0 := by
      rw [← PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues]
      unfold PDE.RicciFlow.traceFreeRicciNormSqAt PDE.RicciFlow.traceFreeRicciNormSqAtOf
      have h' := h
      change normSq0S g x 2 Ric ≤ _ at h'
      rw [hnorm, hscalar] at h'
      linarith
    linarith
  obtain ⟨h12, h23⟩ := (tracefreeRicciEigenNormSq3_eq_zero_iff l1 l2 l3).1 htf
  have hscalar_l1 : metricScalarAt g x / 3 = l1 := by
    rw [hscalar, h12, h23]
    unfold ricciEigenScalar3
    ring
  let T := ricciEndAt (I := ThreeModel) g Ric
  obtain ⟨hT0, hT1, hT2⟩ := PDE.RicciFlow.ricciEnd_diagVec (I := ThreeModel) g horth hdiag
  have hT_basis : ∀ i : Fin 3, T (basis i) = l1 • basis i := by
    intro i
    fin_cases i
    · simpa [T] using hT0
    · simpa [T, h12] using hT1
    · simpa [T, h12, h23] using hT2
  have hT_all : T v = l1 • v := by
    calc T v = T (∑ i : Fin 3, basis.repr v i • basis i) := by rw [basis.sum_repr]
      _ = ∑ i : Fin 3, basis.repr v i • T (basis i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ i : Fin 3, basis.repr v i • (l1 • basis i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hT_basis i]
      _ = l1 • (∑ i : Fin 3, basis.repr v i • basis i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [smul_smul, mul_comm]
      _ = l1 • v := by rw [basis.sum_repr]
  rw [← metricRicciAt_apply_eq_ricciTensor]
  calc metricRicciAt g x (vec2 v w) = g.inner x (T v) w := (ricciEnd_inner (I := ThreeModel) g Ric v w).symm
    _ = g.inner x (l1 • v) w := by rw [hT_all]
    _ = l1 * g.inner x v w := by simp
    _ = metricScalarAt g x / 3 * g.inner x v w := by rw [hscalar_l1]

end Algebra

section Flow

variable {V : Type*} [TopologicalSpace V] [ChartedSpace ThreeSpace V]
  [IsManifold ThreeModel ∞ V] [T2Space V] [SigmaCompactSpace V]

omit [SigmaCompactSpace V] in
/-- Pointwise continuity in time of `Ric(g s)(v,w) + (2(σ₀+s))⁻¹ g s (v,w)` for a solution on
`[a,b]` with `σ₀ + a > 0`. -/
theorem continuousOn_ricci_add_metric_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V) {a b : ℝ}
    (hab : a ≤ b)
    (hS : PDE.RicciFlow.IsSolutionOn ({ base.metric := g } : PDE.RicciFlow.SolutionOn
      (I := ThreeModel) (M := V) (RealTimeInterval.closed a b hab)))
    {σ₀ : ℝ} (hpos : 0 < σ₀ + a) (x : V) (v w : TangentSpace ThreeModel x) :
    ContinuousOn (fun s => ricciTensor (g s) x v w + (2 * (σ₀ + s))⁻¹ * (g s).inner x v w)
      (Icc a b) := by
  have hric : ContinuousOn (fun s => metricRicciAt (g s) x (vec2 v w)) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact tensor0SFamilyContinuousOnSet.eval_continuous hS.ricciCont
      (P := {t : ℝ // t ∈ Icc a b}) (τ := fun p => p.1) (b := fun _ => x)
      (v := fun i _ => vec2 v w i) continuous_subtype_val (fun p => p.2) continuous_const
      (fun _ => continuous_const)
  have hmet : ContinuousOn (fun s => (g s).inner x v w) (Icc a b) :=
    hS.smoothMetric.coeff_cont x v w
  have hden : ContinuousOn (fun s : ℝ => (2 * (σ₀ + s))⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    have := hs.1
    have : 0 < σ₀ + s := by linarith
    positivity
  have h := hric.add (hden.mul hmet)
  refine h.congr fun s _ => ?_
  simp only [metricRicciAt_apply_eq_ricciTensor, Pi.add_apply, Pi.mul_apply]

/-- **E2.** A three-dimensional Ricci flow on `[a,b]` whose scalar curvature is the spatial
constant `-3/(2(σ₀+s))` is Einstein: `Ric(g s) = -(2(σ₀+s))⁻¹ g s` for every `s ∈ [a,b]`. -/
theorem ricci_of_scalar_eq_flow_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V) {a b σ₀ : ℝ}
    (hab : a < b) (hpos : 0 < σ₀ + a)
    (hS : PDE.RicciFlow.IsSolutionOn ({ base.metric := g } : PDE.RicciFlow.SolutionOn
      (I := ThreeModel) (M := V) (RealTimeInterval.closed a b hab.le)))
    (hR : ∀ s ∈ Icc a b, ∀ x, metricScalarAt (g s) x = -3 / (2 * (σ₀ + s))) :
    ∀ s ∈ Icc a b, RicciEqualsMetricMultiple_S13 (g s) (-(2 * (σ₀ + s))⁻¹) := by
  let S : PDE.RicciFlow.SolutionOn (I := ThreeModel) (M := V)
      (RealTimeInterval.closed a b hab.le) := { base.metric := g }
  -- interior times: scalar evolution + equality in the trace inequality
  have hint : ∀ s ∈ Ioo a b, ∀ x (v w : TangentSpace ThreeModel x),
      ricciTensor (g s) x v w + (2 * (σ₀ + s))⁻¹ * (g s).inner x v w = 0 := by
    intro s hs x v w
    have hsp : 0 < σ₀ + s := by linarith [hs.1]
    have he := PDE.RicciFlow.scalar_evolution_of_smooth_solution S
      (PDE.RicciFlow.smoothOfSolution S hS) (PDE.RicciFlow.flowG S) (fun _ => rfl) (fun _ => rfl)
      ⟨s, hs⟩ x
    have hconst : S.scalar s = fun _ => -3 / (2 * (σ₀ + s)) := by
      funext y
      exact hR s (Ioo_subset_Icc_self hs) y
    simp only [hconst, laplacianAt, DifferentialGeometry.Geometry.Operator.laplacian_const,
      zero_add] at he
    have hd := he.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hf : HasDerivAt (fun r : ℝ => -3 / (2 * (σ₀ + r))) (3 / (2 * (σ₀ + s) ^ 2)) s := by
      have h1 : HasDerivAt (fun r : ℝ => 2 * (σ₀ + r)) 2 s := by
        simpa using ((hasDerivAt_id s).const_add σ₀).const_mul 2
      have h2 := (hasDerivAt_const s (-3 : ℝ)).div h1 (by positivity)
      convert h2 using 1
      field_simp
      ring
    have heq : (fun r => S.scalar r x) =ᶠ[𝓝 s] fun r : ℝ => -3 / (2 * (σ₀ + r)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hR r hr x
    have hu := hd.unique (hf.congr_of_eventuallyEq heq)
    have hnorm : normSq0S (g s) x 2 (metricRicciAt (g s) x) ≤ (metricScalarAt (g s) x) ^ 2 / 3 := by
      have : PDE.RicciFlow.ricciNorm S s x = normSq0S (g s) x 2 (metricRicciAt (g s) x) := rfl
      rw [← this, hR s (Ioo_subset_Icc_self hs) x]
      have h2 : 2 * PDE.RicciFlow.ricciNorm S s x = 3 / (2 * (σ₀ + s) ^ 2) := hu
      have : (-3 / (2 * (σ₀ + s))) ^ 2 / 3 = 3 / (4 * (σ₀ + s) ^ 2) := by
        field_simp; ring
      rw [this]
      have : 3 / (2 * (σ₀ + s) ^ 2) = 2 * (3 / (4 * (σ₀ + s) ^ 2)) := by field_simp; ring
      linarith
    have hE := ricci_eq_of_normSq_le_O7 (g s) x hnorm v w
    rw [hE, hR s (Ioo_subset_Icc_self hs) x]
    field_simp
    ring
  intro s hs x v w
  have hc := continuousOn_ricci_add_metric_O7 g hab.le hS hpos x v w
  have hzero : ricciTensor (g s) x v w + (2 * (σ₀ + s))⁻¹ * (g s).inner x v w = 0 := by
    have hcl : s ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hs
    have hsub : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
    have := (hc.mono hsub)
    have hmem : (fun r => ricciTensor (g r) x v w + (2 * (σ₀ + r))⁻¹ * (g r).inner x v w) s ∈
        closure ((fun r => ricciTensor (g r) x v w + (2 * (σ₀ + r))⁻¹ * (g r).inner x v w) ''
          Ioo a b) :=
      ContinuousWithinAt.mem_closure_image (hc s hs |>.mono hsub) hcl
    have himg : (fun r => ricciTensor (g r) x v w + (2 * (σ₀ + r))⁻¹ * (g r).inner x v w) ''
        Ioo a b ⊆ {0} := by
      rintro _ ⟨r, hr, rfl⟩
      exact hint r hr x v w
    have := closure_mono himg hmem
    simpa using this
  linarith

omit [SigmaCompactSpace V] in
/-- Continuity in time of the scalar curvature at a fixed point. -/
theorem continuousOn_scalar_time_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V) {a b : ℝ}
    (hab : a ≤ b)
    (hS : PDE.RicciFlow.IsSolutionOn ({ base.metric := g } : PDE.RicciFlow.SolutionOn
      (I := ThreeModel) (M := V) (RealTimeInterval.closed a b hab))) (y : V) :
    ContinuousOn (fun r => metricScalarAt (g r) y) (Icc a b) := by
  have h : ContinuousOn (fun q : ℝ × V => metricScalarAt (g q.1) q.2) (Icc a b ×ˢ univ) :=
    hS.scalarCont
  have hmaps : MapsTo (fun r : ℝ => (r, y)) (Icc a b) (Icc a b ×ˢ (univ : Set V)) :=
    fun r hr => ⟨hr, mem_univ _⟩
  have hf : ContinuousOn (fun r : ℝ => ((r, y) : ℝ × V)) (Icc a b) :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact ContinuousOn.comp (g := fun q : ℝ × V => metricScalarAt (g q.1) q.2)
    (f := fun r : ℝ => ((r, y) : ℝ × V)) h hf hmaps

end Flow
end GC.LongTime.Ch12
