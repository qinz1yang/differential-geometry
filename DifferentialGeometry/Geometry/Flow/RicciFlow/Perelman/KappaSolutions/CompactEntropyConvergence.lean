import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyContinuity
import DifferentialGeometry.Geometry.Metric.Convergence.Window.AllOrders
import Mathlib.Topology.UniformSpace.CompactConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] [CompactSpace M]

local instance compactEntropyConvergenceOne : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

local instance compactEntropyConvergenceTopSucc :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

private local instance compactEntropyOnePointFirstCountable :
    FirstCountableTopology (OnePoint ℕ) where
  nhds_generated_countable p := by
    induction p using OnePoint.rec with
    | infty =>
      rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact,
        cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
      infer_instance
    | coe k =>
      rw [OnePoint.nhds_coe_eq]
      infer_instance

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem chartGram_joint_continuous_onePoint
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq g g)
    (x0 : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : OnePoint ℕ × M =>
      chartGramMatrix (I := I) (p.1.elim g gSeq) x0 p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet) := by
  let U : TopologicalSpace.Opens M :=
    ⟨(trivializationAt E (TangentSpace I) x0).baseSet,
      (trivializationAt E (TangentSpace I) x0).open_baseSet⟩
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let F (h : SmoothRiemannianMetric I M) (a b : Fin (Module.finrank ℝ E)) : C(U, ℝ) :=
    ⟨fun x => chartGramMatrix (I := I) h x0 (x : M) a b,
      (chartGramMatrix_entry_contMDiffOn (I := I) h x0 a b).continuousOn.domRestrict⟩
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hf : Tendsto (fun k => F (gSeq k) i j) atTop (𝓝 (F g i j)) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    let S : U → ℝ := fun x => 2 * (F g i i x + F g i j x + F g j j x)
    have hS : Continuous S :=
      continuous_const.mul (((F g i i).continuous.add (F g i j).continuous).add
        (F g j j).continuous)
    obtain ⟨C0, hC0⟩ := (hK.image hS).bddAbove
    let C : ℝ := max C0 0 + 1
    have hC : 0 < C := by dsimp only [C]; positivity
    have hSC (x : U) (hx : x ∈ K) : S x ≤ C :=
      (hC0 ⟨x, hx, rfl⟩).trans (by dsimp only [C]; linarith [le_max_left C0 0])
    have hSvalue (x : U) :
        g.inner (x : M)
            (chartBasisVecFiber (I := I) x0 i x + chartBasisVecFiber (I := I) x0 j x)
            (chartBasisVecFiber (I := I) x0 i x + chartBasisVecFiber (I := I) x0 j x) +
          g.inner (x : M) (chartBasisVecFiber (I := I) x0 i x)
            (chartBasisVecFiber (I := I) x0 i x) +
          g.inner (x : M) (chartBasisVecFiber (I := I) x0 j x)
            (chartBasisVecFiber (I := I) x0 j x) = S x := by
      simp only [S, F, ContinuousMap.coe_mk, chartGramMatrix_apply]
      rw [metric_add_self]
      ring
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    have hden : 0 < n * C + 1 := by positivity
    obtain ⟨k0, hk0⟩ := hconv Set.univ isCompact_univ 0
      (eps / (n * C + 1)) (div_pos heps hden)
    filter_upwards [eventually_ge_atTop k0] with k hk
    intro x hx
    have hd : metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) <
        eps / (n * C + 1) :=
      (derivNorm_le_sup (I := I) isCompact_univ le_rfl (gSeq k) g g
        (Set.mem_univ (x : M))).trans_lt (hk0 k hk)
    have ht := metricInnerApply_diff_le (I := I) (gSeq k) g g (x : M)
      (chartBasisVecFiber (I := I) x0 i x) (chartBasisVecFiber (I := I) x0 j x)
    change |(gSeq k).inner (x : M) (chartBasisVecFiber (I := I) x0 i x)
        (chartBasisVecFiber (I := I) x0 j x) -
      g.inner (x : M) (chartBasisVecFiber (I := I) x0 i x)
        (chartBasisVecFiber (I := I) x0 j x)| ≤
      n * metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) *
        (g.inner (x : M)
            (chartBasisVecFiber (I := I) x0 i x + chartBasisVecFiber (I := I) x0 j x)
            (chartBasisVecFiber (I := I) x0 i x + chartBasisVecFiber (I := I) x0 j x) +
          g.inner (x : M) (chartBasisVecFiber (I := I) x0 i x)
            (chartBasisVecFiber (I := I) x0 i x) +
          g.inner (x : M) (chartBasisVecFiber (I := I) x0 j x)
            (chartBasisVecFiber (I := I) x0 j x)) at ht
    rw [hSvalue x] at ht
    change |F (gSeq k) i j x - F g i j x| ≤
      n * metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) * S x at ht
    have hbound : n * metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) * S x ≤
        (n * C) * (eps / (n * C + 1)) := by
      calc
        _ ≤ n * metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) * C :=
          mul_le_mul_of_nonneg_left (hSC x hx) (mul_nonneg hn (Real.sqrt_nonneg _))
        _ = (n * C) * metricDerivNorm (I := I) 0 (gSeq k) g g (x : M) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd.le (mul_nonneg hn hC.le)
    have hfrac : (n * C) * (eps / (n * C + 1)) < eps := by
      have hid : (eps / (n * C + 1)) * (n * C + 1) = eps :=
        div_mul_cancel₀ eps hden.ne'
      have hp : 0 < eps / (n * C + 1) := div_pos heps hden
      nlinarith
    change dist (F g i j x) (F (gSeq k) i j x) < eps
    rw [Real.dist_eq, abs_sub_comm]
    exact ht.trans_lt (hbound.trans_lt hfrac)
  let G : C(OnePoint ℕ, C(U, ℝ)) :=
    OnePoint.continuousMapMkNat (fun k => F (gSeq k) i j) (F g i j) hf
  have hG : Continuous (fun p : OnePoint ℕ × U =>
      chartGramMatrix (I := I) (p.1.elim g gSeq) x0 (p.2 : M) i j) := by
    refine (ContinuousMap.continuous_uncurry_of_continuous G).congr ?_
    intro p
    obtain ⟨t, x⟩ := p
    induction t using OnePoint.rec with
    | infty => rfl
    | coe k => rfl
  rw [continuousOn_iff_continuous_domRestrict]
  let V : Set (OnePoint ℕ × M) := Set.univ ×ˢ (U : Set M)
  have hmap : Continuous (fun p : V =>
      (p.val.1, (⟨p.val.2, p.property.2⟩ : U))) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk fun p => p.property.2)
  exact hG.comp hmap

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metric_integrals_continuous_onePoint [Nonempty M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq g g) :
    Continuous (fun p : OnePoint ℕ => surfaceArea (p.elim g gSeq)) ∧
      Continuous (fun p : OnePoint ℕ => totalScalarCurvature (p.elim g gSeq)) ∧
      Continuous (fun p : OnePoint ℕ => surfaceEntropy (p.elim g gSeq)) := by
  let G : OnePoint ℕ → SmoothRiemannianMetric I M := fun p => p.elim g gSeq
  have hGram (x0 : M) (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun p : OnePoint ℕ × M => chartGramMatrix (I := I) (G p.1) x0 p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet) :=
    chartGram_joint_continuous_onePoint gSeq g hconv x0 i j
  have hScalar : ContinuousOn
      (fun p : OnePoint ℕ × M => metricScalarAt (I := I) (G p.1) p.2)
      (Set.univ ×ˢ Set.univ) :=
    (metricScalar_joint_continuous_onePoint gSeq g hconv).continuousOn
  exact ⟨continuousOn_univ.mp (surfaceArea_continuousOn isCompact_univ hGram),
    continuousOn_univ.mp (totalScalarCurvature_continuousOn isCompact_univ hGram hScalar),
    continuousOn_univ.mp (surfaceEntropy_continuousOn isCompact_univ hGram hScalar)⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metric_integrals_tendsto_of_metricCInf [Nonempty M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq g g) :
    Tendsto (fun k => surfaceArea (gSeq k)) atTop (𝓝 (surfaceArea g)) ∧
      Tendsto (fun k => totalScalarCurvature (gSeq k)) atTop
        (𝓝 (totalScalarCurvature g)) ∧
      Tendsto (fun k => surfaceEntropy (gSeq k)) atTop (𝓝 (surfaceEntropy g)) := by
  obtain ⟨hA, hC, hN⟩ := metric_integrals_continuous_onePoint gSeq g hconv
  refine ⟨?_, ?_, ?_⟩
  · exact (OnePoint.continuous_iff_from_nat
      (fun p : OnePoint ℕ => surfaceArea (p.elim g gSeq))).mp hA
  · exact (OnePoint.continuous_iff_from_nat
      (fun p : OnePoint ℕ => totalScalarCurvature (p.elim g gSeq))).mp hC
  · exact (OnePoint.continuous_iff_from_nat
      (fun p : OnePoint ℕ => surfaceEntropy (p.elim g gSeq))).mp hN

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
