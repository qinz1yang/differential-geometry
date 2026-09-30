import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Initial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem csInf_two_mul_matrix_rayleigh_eq
    (g : SmoothRiemannianMetric ThreeModel X) (x : X)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x))
    (hB : OrthonormalBasisAt g x B) :
    sInf {r : ℝ | ∃ v : Fin 3 → ℝ, (∑ i, (v i)^2) = 1 ∧
      r = 2 * ∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j} =
        2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) := by
  let A := metricAlgebraicCurvatureTensorAt g x
  have hquad (v : Fin 3 → ℝ) :
      (∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j) =
      algebraicCurvatureOperatorQuadraticEval A v
        (fun i => B (bivectorIndex3 i).1) (fun i => B (bivectorIndex3 i).2) := by
    rw [algebraicCurvatureOperatorQuadraticEval_eq_matrixQuad]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change v i * curvatureOperatorMatrixAt x B A i j * v j =
      v i * v j * curvatureOperatorMatrixAt x B A i j
    ring
  have hleast : IsLeast
      {r : ℝ | ∃ v : Fin 3 → ℝ, (∑ i, (v i)^2) = 1 ∧
        r = 2 * ∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j}
      (2 * leastCurvatureOperatorEigenvalueAt g x A) := by
    constructor
    · obtain ⟨v, hv, heq⟩ := exists_leastCurvatureOperatorEigenvalueAt_rayleigh_minimizer g x B hB A
      refine ⟨v, ?_, ?_⟩
      · simpa only [algebraicCurvatureIdentityQuadraticEval_bivectorBasis g x B hB] using hv
      · rw [hquad, heq]
    · rintro r ⟨v, hv, rfl⟩
      have hb := leastCurvatureOperatorEigenvalueAt_mul_identity_le g x B hB A v
        (fun i => B (bivectorIndex3 i).1) (fun i => B (bivectorIndex3 i).2)
      rw [algebraicCurvatureIdentityQuadraticEval_bivectorBasis g x B hB, hv, mul_one] at hb
      rw [hquad]
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
  exact hleast.csInf_eq

theorem inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
    (g : SmoothRiemannianMetric ThreeModel X) (a : ℝ) (x : X) :
    InFixedHamiltonIveyRegion g a x ↔
      (metricScalarAt g x, 2 * leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x)) ∈ fixedHamiltonIveyRegion a := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := exists_orthonormalBasisAt g x (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      simp)
    have hB' : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 := by
      simpa only [OrthonormalBasisAt, delta3] using hB
    have hh := h B hB'
    change 0 ≤ _ ∨ fixedHamiltonIveyBarrier a (-_) ≤ metricScalarAt g x at hh
    rw [csInf_two_mul_matrix_rayleigh_eq g x B hB] at hh
    exact hh
  · intro h B hB
    have hB' : OrthonormalBasisAt g x B := by
      simpa only [OrthonormalBasisAt, delta3] using hB
    change 0 ≤ _ ∨ fixedHamiltonIveyBarrier a (-_) ≤ metricScalarAt g x
    rw [csInf_two_mul_matrix_rayleigh_eq g x B hB']
    exact h

theorem exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound
    [CompactSpace X] (g : SmoothRiemannianMetric ThreeModel X) :
    ∃ a : ℝ, 0 < a ∧ (∀ x : X, InFixedHamiltonIveyRegion g a x) ∧
      ∀ x : X, -3 / a ≤ metricScalarAt g x := by
  obtain ⟨a,ha,hbound⟩ := DimensionThree.exists_pos_fixedHamiltonIveyRegion_of_compact
    g (by simp [ThreeSpace])
  exact ⟨a,ha,fun x => (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mpr
    (hbound x).1,fun x => (hbound x).2⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Surgery.Topology

universe u

theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X],
        ∀ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := X) D)
          (W : Set ℝ) (a : ℝ → ℝ),
          (∀ t ∈ W, a₀ ≤ a t) →
          (∀ t ∈ W, ∀ x : X, InFixedHamiltonIveyRegion (S.base.metric t) (a t) x) →
          PhiAlmostNonnegative S W Phi := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion ha₀
  refine ⟨Phi, hPhi, ?_⟩
  intro X _ _ _ _ D S W a ha hregion
  apply (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    S W Phi (by simp [ThreeSpace])).mpr
  intro t ht x
  have hr := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
    (S.base.metric t) (a t) x).mp (hregion t ht x)
  have hb := hbound (a t) (ha t ht) _ _ hr
  have hp := hPhi.pos (S.scalar t x)
  change -(2 * leastCurvatureOperatorEigenvalueAt (S.base.metric t) x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (S.base.metric t) x⟩) ≤ Phi (S.scalar t x) at hb
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Convex

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem curvatureOperatorMatrixAt_mem_initial_of_fixed_region
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    {t A : ℝ} (hA : 0 < A) (x : X)
    (hfixed : InFixedHamiltonIveyRegion (S.base.metric t) A x)
    (hscalar : -3 / A ≤ S.scalar t x)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x))
    (hB : OrthonormalBasisAt (S.base.metric t) x B) :
    curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt (S.base.metric t) x) ∈
      hamiltonIveyConvexMatrixRegion (2 * A)⁻¹ 0 := by
  let C := metricAlgebraicCurvatureTensorAt (S.base.metric t) x
  let M := curvatureOperatorMatrixAt x B C
  let K := (2 * A)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hM : M.IsHermitian := curvatureOperatorMatrixAt_isHermitian x B C
  have hmin : minimumRayleighQuotient3 M =
      leastCurvatureOperatorEigenvalueAt (S.base.metric t) x C := by
    rw [minimumRayleighQuotient3_eq_min_eigenvalue hM,
      leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (S.base.metric t) x B hB C]
    rfl
  have htrace : M.trace = S.scalar t x / 2 := by
    rw [curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt]
    have h := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt S B hB
    change S.scalar t x = 2 * ∑ i, orderedSectionalCurvaturesAt x B C i at h
    linarith
  apply (mem_hamiltonIveyConvexMatrixRegion_initial_iff hK).mpr
  refine ⟨hM, ?_, ?_⟩
  · change -3 * K ≤ M.trace
    rw [htrace]
    have heq : -3 * K = (-3 / A) / 2 := by dsimp [K]; ring
    rw [heq]
    linarith
  · intro hle
    have hν : minimumRayleighQuotient3 M < 0 := lt_of_le_of_lt hle (neg_neg_of_pos hK)
    have hfix := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
      (S.base.metric t) A x).mp hfixed
    rw [← hmin] at hfix
    have hb : fixedHamiltonIveyBarrier A (-(2 * minimumRayleighQuotient3 M)) ≤ S.scalar t x := by
      rcases hfix with hnonneg | hb
      · linarith
      · exact hb
    have heq := two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier
      (K := K) (t := 0) hK le_rfl (by linarith : 0 < -(2 * minimumRayleighQuotient3 M))
    have hparam : (2 * K)⁻¹ + 0 = A := by dsimp [K]; field_simp; ring
    rw [hparam] at heq
    have hhalf : -(2 * minimumRayleighQuotient3 M) / 2 = -minimumRayleighQuotient3 M := by ring
    rw [hhalf] at heq
    rw [htrace]
    simp only [hamiltonIveyBarrier, mul_zero, add_zero, Real.log_one] at heq
    linarith

theorem fixedHamiltonIveyRegion_and_scalar_lower_on_slab
    [CompactSpace X] {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) {u T A : ℝ} (hT : 0 ≤ T) (hA : 0 < A)
    (hslab : Icc u (u + T) ⊆ D.carrier) (hreg : Ioo u (u + T) ⊆ D.regular)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (S.base.metric u) A x)
    (hscalar : ∀ x, -3 / A ≤ S.scalar u x) :
    ∀ t ∈ Icc u (u + T), ∀ x,
      InFixedHamiltonIveyRegion (S.base.metric t) (A + t - u) x ∧
        -3 / (A + t - u) ≤ S.scalar t x := by
  let K := (2 * A)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_region S hS hT hK hslab hreg
    (by simp [ThreeSpace]) (fun x B hB =>
      curvatureOperatorMatrixAt_mem_initial_of_fixed_region S hA x (hfixed x) (hscalar x) B hB)
  obtain ⟨hlo, hbar⟩ := hamilton_ivey_pinching_of_curvatureOperatorRegionPropagationOn S hprop
  intro t ht x
  have hτ : 0 ≤ t - u := sub_nonneg.mpr ht.1
  have hden : 0 < 1 + 4 * K * (t - u) := by positivity
  have hAτ : 0 < A + (t - u) := add_pos_of_pos_of_nonneg hA hτ
  have hA2τ : 0 < A + 2 * (t - u) := by positivity
  constructor
  · apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
      (S.base.metric t) (A + t - u) x).mpr
    let ν := leastCurvatureOperatorEigenvalueAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)
    change 0 ≤ 2 * ν ∨ fixedHamiltonIveyBarrier (A + t - u) (-(2 * ν)) ≤ S.scalar t x
    by_cases hν : 0 ≤ ν
    · exact Or.inl (mul_nonneg (by norm_num) hν)
    right
    have hνneg : ν < 0 := lt_of_not_ge hν
    have hb := hbar t ht x hνneg
    have heq := two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier hK hτ
      (by linarith : 0 < -(2 * ν))
    have hparam : (2 * K)⁻¹ + (t - u) = A + t - u := by dsimp [K]; field_simp; ring
    rw [hparam, show -(2 * ν) / 2 = -ν by ring] at heq
    rw [← heq]
    change 2 * (-ν) * (Real.log (-ν / K) + Real.log (1 + 2 * K * (t - u)) - 3) ≤
      S.scalar t x at hb
    dsimp only [hamiltonIveyBarrier]
    nlinarith [hb]
  · have hb := hlo t ht x
    have heq : -6 * K / (1 + 4 * K * (t - u)) = -3 / (A + 2 * (t - u)) := by
      dsimp [K]
      field_simp
      ring
    rw [heq] at hb
    have hcompare : -3 / (A + (t - u)) ≤ -3 / (A + 2 * (t - u)) := by
      apply (div_le_div_iff₀ hAτ hA2τ).mpr
      nlinarith
    simpa only [← add_sub_assoc] using hcompare.trans hb

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem IncomingSlab.fixedHamiltonIveyRegion_and_scalar_lower (G : P.IncomingSlab a s)
    {A : ℝ} (hA : 0 < A)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (G.flow.base.metric a) A x)
    (hscalar : ∀ x, -3 / A ≤ G.flow.scalar a x) :
    ∀ t ∈ Ico a s, ∀ x,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) (A + t - a) x ∧
        -3 / (A + t - a) ≤ G.flow.scalar t x := by
  intro t ht x
  exact fixedHamiltonIveyRegion_and_scalar_lower_on_slab G.flow G.equation
    (T := t - a) (sub_nonneg.mpr ht.1) hA
    (fun u hu => ⟨hu.1, by have := hu.2; linarith [ht.2]⟩)
    (fun u hu => ⟨hu.1, by have := hu.2; linarith [ht.2]⟩)
    hfixed hscalar t ⟨ht.1, by linarith⟩ x

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Bundle Manifold Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.inFixedHamiltonIveyRegion_of_tendsto
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    {A : ℝ → ℝ} {A₀ : ℝ} (hA₀ : 0 < A₀) (hA : Tendsto A (𝓝[<] s) (𝓝 A₀))
    (hregion : ∀ᶠ t in 𝓝[<] s, InFixedHamiltonIveyRegion (G.flow.base.metric t) (A t) x.1) :
    InFixedHamiltonIveyRegion L.metric A₀ x := by
  apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion L.metric A₀ x).mpr
  apply mem_fixedHamiltonIveyRegion_of_tendsto hA₀ hA (L.tendsto_metricScalarAt x)
    ((L.tendsto_leastCurvatureOperatorEigenvalueAt x).const_mul 2)
  filter_upwards [hregion] with t ht
  exact (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
    (G.flow.base.metric t) (A t) x.1).mp ht

theorem TerminalLimitMetric.fixedHamiltonIveyRegion_and_scalar_lower
    (L : G.TerminalLimitMetric) {A : ℝ} (hA : 0 < A)
    (hincoming : ∀ t ∈ Ico a s, ∀ x : P.Carrier,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) (A + t - a) x ∧
        -3 / (A + t - a) ≤ metricScalarAt (G.flow.base.metric t) x) :
    ∀ x : G.terminalRegularOpen,
      InFixedHamiltonIveyRegion L.metric (A + s - a) x ∧
        -3 / (A + s - a) ≤ metricScalarAt L.metric x := by
  have hAs : 0 < A + s - a := by linarith [G.lt]
  have hparam : Tendsto (fun t : ℝ => A + t - a) (𝓝[<] s) (𝓝 (A + s - a)) :=
    ((tendsto_const_nhds.add tendsto_id).sub_const a).mono_left nhdsWithin_le_nhds
  intro x
  constructor
  · apply L.inFixedHamiltonIveyRegion_of_tendsto x hAs hparam
    filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
    exact (hincoming t ⟨ht.1.le, ht.2⟩ x.1).1
  · apply L.scalar_lower_bound_of_tendsto x
      (tendsto_const_nhds.div hparam hAs.ne')
    filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
    exact (hincoming t ⟨ht.1.le, ht.2⟩ x.1).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
    (E : MetricCutCapEvent P Q a s)
    (hcurvature : ∀ b : ℝ, 0 < b →
      (∀ x, InFixedHamiltonIveyRegion E.terminal.metric b x) →
      ∀ x, InFixedHamiltonIveyRegion E.outputMetric b x)
    (hpreserve : ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt E.terminal.metric x) →
      ∀ x, B ≤ metricScalarAt E.outputMetric x)
    {A : ℝ} (hA : 0 < A)
    (hincoming : ∀ t ∈ Ico a s, ∀ x : P.Carrier,
      InFixedHamiltonIveyRegion (E.incoming.flow.base.metric t) (A + t - a) x ∧
        -3 / (A + t - a) ≤ metricScalarAt (E.incoming.flow.base.metric t) x) :
    (∀ x : E.incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion E.terminal.metric (A + s - a) x ∧
        -3 / (A + s - a) ≤ metricScalarAt E.terminal.metric x) ∧
    ∀ x : Q.Carrier,
      InFixedHamiltonIveyRegion E.outputMetric (A + s - a) x ∧
        -3 / (A + s - a) ≤ metricScalarAt E.outputMetric x := by
  have hterminal := E.terminal.fixedHamiltonIveyRegion_and_scalar_lower hA hincoming
  have hAs : 0 < A + s - a := by linarith [E.incoming.lt]
  exact ⟨hterminal, fun x =>
    ⟨hcurvature _ hAs (fun y => (hterminal y).1) x,
      hpreserve _ (div_nonpos_of_nonpos_of_nonneg (by norm_num) hAs.le)
        (fun y => (hterminal y).2) x⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem fixedHamiltonIveyRegion_and_scalar_lower_output_of_incoming
    (G : GeometricCutoffRecord H i parameters) {A : ℝ} (hA : 0 < A)
    (hincoming : ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
        InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric t)
          (A + t - H.time i.castSucc) x ∧
        -3 / (A + t - H.time i.castSucc) ≤
          metricScalarAt ((H.event i).incoming.flow.base.metric t) x) :
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric
        (A + H.time i.succ - H.time i.castSucc) x ∧
      -3 / (A + H.time i.succ - H.time i.castSucc) ≤ metricScalarAt (H.event i).terminal.metric x) ∧
    ∀ x : (H.stage i.succ).Carrier,
      InFixedHamiltonIveyRegion (H.initialMetric i.succ)
        (A + H.time i.succ - H.time i.castSucc) x ∧
      -3 / (A + H.time i.succ - H.time i.castSucc) ≤ metricScalarAt (H.initialMetric i.succ) x := by
  simpa only [H.event_output i] using
    (H.event i).fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
      G.curvature_preserving G.scalar_preserving hA hincoming

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

section

variable (H : ObservedHistory.{u})
  (hcurvature : ∀ i : Fin H.eventCount, ∀ b : ℝ, 0 < b →
    (∀ x, InFixedHamiltonIveyRegion (H.event i).terminal.metric b x) →
    ∀ x, InFixedHamiltonIveyRegion (H.event i).outputMetric b x)
  (hpreserve : ∀ i : Fin H.eventCount, ∀ B : ℝ, B ≤ 0 →
    (∀ x, B ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x, B ≤ metricScalarAt (H.event i).outputMetric x)
  {a₀ : ℝ} (ha₀ : 0 < a₀)
  (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
  (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)

include hcurvature hpreserve ha₀ hfixed hscalar

private theorem fixedHamiltonIveyRegion_and_scalar_lower_initialMetric :
    ∀ j : Fin (H.eventCount + 1), ∀ x : (H.stage j).Carrier,
      InFixedHamiltonIveyRegion (H.initialMetric j) (a₀ + H.time j) x ∧
        -3 / (a₀ + H.time j) ≤ metricScalarAt (H.initialMetric j) x := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro x
    simpa only [H.time_zero, add_zero] using And.intro (hfixed x) (hscalar x)
  | succ i ih =>
    have hA : 0 < a₀ + H.time i.castSucc := add_pos_of_pos_of_nonneg ha₀ (H.time_nonneg _)
    have hfixed' : ∀ x,
        InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
          (a₀ + H.time i.castSucc) x := by
      intro x
      rw [H.event_initial]
      exact (ih x).1
    have hscalar' : ∀ x, -3 / (a₀ + H.time i.castSucc) ≤
        (H.event i).incoming.flow.scalar (H.time i.castSucc) x := by
      intro x
      change -3 / (a₀ + H.time i.castSucc) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) x
      rw [H.event_initial]
      exact (ih x).2
    have hincoming := (H.event i).incoming.fixedHamiltonIveyRegion_and_scalar_lower
      hA hfixed' hscalar'
    have hout := (H.event i).fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
      (hcurvature i) (hpreserve i) hA hincoming
    have heq : a₀ + H.time i.castSucc + H.time i.succ - H.time i.castSucc =
        a₀ + H.time i.succ := by ring
    intro x
    simpa only [H.event_output i, heq] using hout.2 x

theorem fixedHamiltonIveyRegion_and_scalar_lower_of_preservation :
    (∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      InFixedHamiltonIveyRegion (H.stageMetric j t) (a₀ + t) x ∧
        -3 / (a₀ + t) ≤ metricScalarAt (H.stageMetric j t) x) ∧
    ∀ i : Fin H.eventCount, ∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric (a₀ + H.time i.succ) x ∧
        -3 / (a₀ + H.time i.succ) ≤ metricScalarAt (H.event i).terminal.metric x := by
  have hinit := H.fixedHamiltonIveyRegion_and_scalar_lower_initialMetric
    hcurvature hpreserve ha₀ hfixed hscalar
  have hincoming (i : Fin H.eventCount) :
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ), ∀ x : (H.stage i.castSucc).Carrier,
        InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric t) (a₀ + t) x ∧
          -3 / (a₀ + t) ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x := by
    have hA : 0 < a₀ + H.time i.castSucc := add_pos_of_pos_of_nonneg ha₀ (H.time_nonneg _)
    have hf : ∀ x,
        InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric (H.time i.castSucc))
          (a₀ + H.time i.castSucc) x := by
      intro x
      rw [H.event_initial]
      exact (hinit _ x).1
    have hs : ∀ x, -3 / (a₀ + H.time i.castSucc) ≤
        (H.event i).incoming.flow.scalar (H.time i.castSucc) x := by
      intro x
      change -3 / (a₀ + H.time i.castSucc) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) x
      rw [H.event_initial]
      exact (hinit _ x).2
    intro t ht x
    have heq : a₀ + H.time i.castSucc + t - H.time i.castSucc = a₀ + t := by ring
    have hp := (H.event i).incoming.fixedHamiltonIveyRegion_and_scalar_lower hA hf hs t ht x
    change InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric t)
        (a₀ + H.time i.castSucc + t - H.time i.castSucc) x ∧
      -3 / (a₀ + H.time i.castSucc + t - H.time i.castSucc) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric t) x at hp
    simpa only [heq] using hp
  constructor
  · intro j
    cases j using Fin.lastCases with
    | cast i =>
      simpa only [stageDomain, stageMetric, Fin.lastCases_castSucc] using hincoming i
    | last =>
      intro t ht x
      simp only [stageDomain, Fin.lastCases_last] at ht
      by_cases hlast : H.time (Fin.last H.eventCount) < H.horizon
      · let G := H.finalSlab hlast
        have hA : 0 < a₀ + H.time (Fin.last H.eventCount) :=
          add_pos_of_pos_of_nonneg ha₀ (H.time_nonneg _)
        have hf : ∀ x, InFixedHamiltonIveyRegion
            (G.flow.base.metric (H.time (Fin.last H.eventCount)))
            (a₀ + H.time (Fin.last H.eventCount)) x := by
          intro x
          change InFixedHamiltonIveyRegion
            ((H.finalSlab hlast).flow.base.metric (H.time (Fin.last H.eventCount))) _ x
          rw [H.final_initial]
          exact (hinit _ x).1
        have hs : ∀ x, -3 / (a₀ + H.time (Fin.last H.eventCount)) ≤
            G.flow.scalar (H.time (Fin.last H.eventCount)) x := by
          intro x
          change -3 / (a₀ + H.time (Fin.last H.eventCount)) ≤ metricScalarAt
            ((H.finalSlab hlast).flow.base.metric (H.time (Fin.last H.eventCount))) x
          rw [H.final_initial]
          exact (hinit _ x).2
        have hp := fixedHamiltonIveyRegion_and_scalar_lower_on_slab G.flow G.equation
          (T := H.horizon - H.time (Fin.last H.eventCount)) (sub_nonneg.mpr hlast.le) hA
          (by intro v hv; exact ⟨hv.1, by have := hv.2; linarith⟩)
          (by intro v hv; exact ⟨hv.1, by have := hv.2; linarith⟩)
          hf hs t ⟨ht.1, by linarith [ht.2]⟩ x
        have heq : a₀ + H.time (Fin.last H.eventCount) + t - H.time (Fin.last H.eventCount) =
            a₀ + t := by ring
        change InFixedHamiltonIveyRegion (G.flow.base.metric t)
            (a₀ + H.time (Fin.last H.eventCount) + t - H.time (Fin.last H.eventCount)) x ∧
          -3 / (a₀ + H.time (Fin.last H.eventCount) + t - H.time (Fin.last H.eventCount)) ≤
            metricScalarAt (G.flow.base.metric t) x at hp
        simpa only [stageMetric, Fin.lastCases_last, dite_eq_left hlast, heq] using hp
      · have heq : H.horizon = H.time (Fin.last H.eventCount) :=
          le_antisymm (le_of_not_gt hlast) H.time_le_horizon
        have ht' : t = H.time (Fin.last H.eventCount) := le_antisymm (ht.2.trans heq.le) ht.1
        subst t
        simpa only [stageMetric, Fin.lastCases_last, dite_eq_right hlast] using hinit _ x
  · intro i x
    have hA : 0 < a₀ + H.time i.castSucc := add_pos_of_pos_of_nonneg ha₀ (H.time_nonneg _)
    have hin : ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
        ∀ x : (H.stage i.castSucc).Carrier,
          InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric t)
            (a₀ + H.time i.castSucc + t - H.time i.castSucc) x ∧
          -3 / (a₀ + H.time i.castSucc + t - H.time i.castSucc) ≤
            metricScalarAt ((H.event i).incoming.flow.base.metric t) x := by
      intro t ht x
      have heq : a₀ + H.time i.castSucc + t - H.time i.castSucc = a₀ + t := by ring
      simpa only [heq] using hincoming i t ht x
    have hterm := ((H.event i).fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
      (hcurvature i) (hpreserve i) hA hin).1 x
    have heq : a₀ + H.time i.castSucc + H.time i.succ - H.time i.castSucc =
        a₀ + H.time i.succ := by ring
    simpa only [heq] using hterm


end

variable (H : ObservedHistory.{u}) {parameters : CutoffParameters}
  (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
  {a₀ : ℝ} (ha₀ : 0 < a₀)
  (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
  (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)

include records ha₀ hfixed hscalar

theorem fixedHamiltonIveyRegion_and_scalar_lower :
    (∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      InFixedHamiltonIveyRegion (H.stageMetric j t) (a₀ + t) x ∧
        -3 / (a₀ + t) ≤ metricScalarAt (H.stageMetric j t) x) ∧
    ∀ i : Fin H.eventCount, ∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric (a₀ + H.time i.succ) x ∧
        -3 / (a₀ + H.time i.succ) ≤ metricScalarAt (H.event i).terminal.metric x :=
  H.fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
    (fun i => (records i).curvature_preserving) (fun i => (records i).scalar_preserving)
    ha₀ hfixed hscalar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Surgery.Topology
open DifferentialGeometry.Geometry.Curvature.DimensionThree

universe u

private theorem curvatureOperatorLowerBoundAt_of_fixedHamiltonIveyRegion
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {a₀ : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, a₀ ≤ a → ∀ R ν : ℝ,
      (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (g : SmoothRiemannianMetric ThreeModel X) {a : ℝ} (ha : a₀ ≤ a) (x : X)
    (hfixed : InFixedHamiltonIveyRegion g a x) :
    curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x)
      (Phi (metricScalarAt g x)) := by
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt g x (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp)
  apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le B hB).mpr
  have hb := hbound a ha _ _
    ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mp hfixed)
  have hp := hPhi.pos (metricScalarAt g x)
  linarith

theorem exists_admissiblePinchingFunction_for_observedHistories_of_preservation
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (H : ObservedHistory.{u}),
        (∀ i : Fin H.eventCount, ∀ b : ℝ, 0 < b →
          (∀ x, InFixedHamiltonIveyRegion (H.event i).terminal.metric b x) →
          ∀ x, InFixedHamiltonIveyRegion (H.event i).outputMetric b x) →
        (∀ i : Fin H.eventCount, ∀ B : ℝ, B ≤ 0 →
          (∀ x, B ≤ metricScalarAt (H.event i).terminal.metric x) →
          ∀ x, B ≤ metricScalarAt (H.event i).outputMetric x) →
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
        (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
        (∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
          curvatureOperatorLowerBoundAt (H.stageMetric j t) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric j t) x)
            (Phi (metricScalarAt (H.stageMetric j t) x))) ∧
        ∀ i : Fin H.eventCount, ∀ x : (H.event i).incoming.terminalRegularOpen,
          curvatureOperatorLowerBoundAt (H.event i).terminal.metric x
            (metricAlgebraicCurvatureTensorAt (H.event i).terminal.metric x)
            (Phi (metricScalarAt (H.event i).terminal.metric x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion ha₀
  refine ⟨Phi, hPhi, ?_⟩
  intro H hcurvature hpreserve hfixed hscalar
  have hfull := H.fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
    hcurvature hpreserve ha₀ hfixed hscalar
  constructor
  · intro j t ht x
    have hstart : H.time j ≤ t := by
      cases j using Fin.lastCases with
      | cast i =>
        simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at ht
        exact ht.1
      | last =>
        simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at ht
        exact ht.1
    have htime : 0 ≤ t := (H.time_nonneg j).trans hstart
    exact curvatureOperatorLowerBoundAt_of_fixedHamiltonIveyRegion hPhi hbound
      (H.stageMetric j t) (by linarith) x (hfull.1 j t ht x).1
  · intro i x
    exact curvatureOperatorLowerBoundAt_of_fixedHamiltonIveyRegion hPhi hbound
      (H.event i).terminal.metric (by linarith [H.time_nonneg i.succ]) x (hfull.2 i x).1

theorem exists_admissiblePinchingFunction_for_observedHistories
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) →
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
        (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
        (∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
          curvatureOperatorLowerBoundAt (H.stageMetric j t) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric j t) x)
            (Phi (metricScalarAt (H.stageMetric j t) x))) ∧
        ∀ i : Fin H.eventCount, ∀ x : (H.event i).incoming.terminalRegularOpen,
          curvatureOperatorLowerBoundAt (H.event i).terminal.metric x
            (metricAlgebraicCurvatureTensorAt (H.event i).terminal.metric x)
            (Phi (metricScalarAt (H.event i).terminal.metric x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_for_observedHistories_of_preservation ha₀
  exact ⟨Phi, hPhi, fun H parameters records hfixed hscalar =>
    hbound H (fun i => (records i).curvature_preserving)
      (fun i => (records i).scalar_preserving) hfixed hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman


set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

theorem fixedHamiltonIveyRegion_and_scalar_lower_bound
    (A : InitialIdentification P g H) {a : ℝ}
    (hfixed : ∀ x, InFixedHamiltonIveyRegion g a x)
    (hlower : ∀ x, -3 / a ≤ metricScalarAt g x) :
    (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a x) ∧
      ∀ x, -3 / a ≤ metricScalarAt (H.initialMetric 0) x := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcurv (x : P.Carrier) :=
    curvature_of_injective_local_isometry g (H.initialMetric 0) A.map
      A.map.isLocalDiffeomorph A.map.injective (fun x v w => (A.metric_eq x v w).symm) x
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := A.map.surjective y
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a _).mpr
    erw [← (hcurv x).1, ← (hcurv x).2]
    exact (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a x).mp (hfixed x)
  · intro y
    obtain ⟨x, rfl⟩ := A.map.surjective y
    erw [← (hcurv x).1]
    exact hlower x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_pos_fixedHamiltonIveyRegion_for_identified_histories
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a x) ∧
          ∀ x, -3 / a ≤ metricScalarAt (H.initialMetric 0) x := by
  obtain ⟨a, ha, hfixed, hlower⟩ := exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  exact ⟨a, ha, fun H A => A.fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hlower⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Surgery.Topology
universe u

theorem exists_admissiblePinchingFunction_for_identified_incomingSlabs
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      ∀ (parameters : CutoffParameters),
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) →
      ∀ (last : Fin (H.eventCount + 1)) (s : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) s),
        G.flow.base.metric (H.time last) = H.initialMetric last →
        PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi := by
  obtain ⟨a₀, ha₀, hfixed, hlower⟩ := exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  obtain ⟨Phi, hPhi, hphi⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u} ha₀
  refine ⟨Phi, hPhi, ?_⟩
  intro H A parameters records last s G hinit
  have hzero := A.fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hlower
  have hhistory := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hzero.1 hzero.2
  have hstart : H.time last ∈ H.stageDomain last := by
    cases last using Fin.lastCases with
    | last =>
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_last] using
        (show H.time (Fin.last H.eventCount) ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
          ⟨le_rfl, H.time_le_horizon⟩)
    | cast j =>
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show H.time j.castSucc ∈ Ico (H.time j.castSucc) (H.time j.succ) from
          ⟨le_rfl, H.time_strictMono j.castSucc_lt_succ⟩)
  have hstage (x : (H.stage last).Carrier) :
      InFixedHamiltonIveyRegion (H.initialMetric last) (a₀ + H.time last) x ∧
        -3 / (a₀ + H.time last) ≤ metricScalarAt (H.initialMetric last) x := by
    simpa only [H.stageMetric_initial] using hhistory.1 last (H.time last) hstart x
  have hfuture := G.fixedHamiltonIveyRegion_and_scalar_lower
    (by linarith [H.time_nonneg last] : 0 < a₀ + H.time last)
    (fun x => by rw [hinit]; exact (hstage x).1)
    (fun x => by
      change -3 / (a₀ + H.time last) ≤ metricScalarAt (G.flow.base.metric (H.time last)) x
      rw [hinit]
      exact (hstage x).2)
  apply hphi (H.stage last).Carrier _ G.flow (Ico (H.time last) s) (fun t => a₀ + t)
  · intro t ht
    linarith [(H.time_nonneg last).trans ht.1]
  · intro t ht x
    simpa only [show a₀ + H.time last + t - H.time last = a₀ + t by ring] using
      (hfuture t ht x).1

end DifferentialGeometry.PDE.RicciFlow.Perelman
