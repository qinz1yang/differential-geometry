import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Vanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Connection.CovariantDerivativeCoordinates
import DifferentialGeometry.Geometry.Connection.MetricTrace.Connection
import DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section JointInvGram

variable (g : ℝ → SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem chartGramDet_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp : (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det) =
      (fun p : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 (σ k) k) := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  exact contMDiffOn_finsetProd (fun k _ => hgram (σ k) k)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem chartGramAdj_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp : (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j) =
      (fun p : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext p
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : ℝ × M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext p
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun p : ℝ × M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 (σ k) k) := by
      funext p
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact hgram (σ k) k

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem chartInvGram_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hcongr : ∀ p ∈ J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
      chartInvGramMatrix (I := I) (g p.1) x₀ p.2 i j =
        ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det)⁻¹ *
          (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j := by
    rintro p ⟨-, hp⟩
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det •
            (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate) i j = _
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ (chartGramAdj_jointContMDiffOn (I := I) g x₀ hgram i j)
  have hdet := chartGramDet_jointContMDiffOn (I := I) g x₀ hgram
  rintro p ⟨hpJ, hp⟩
  have hdet_ne : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det ≠ 0 :=
    ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g p.1) x₀ hp)
  exact (contDiffAt_inv _ hdet_ne).contMDiffAt.comp_contMDiffWithinAt p (hdet p ⟨hpJ, hp⟩)

end JointInvGram

section JointNormSq

omit [T2Space M] [CompactSpace M] in
private theorem prodOpen_nhdsWithin {S : Set M} (hS : IsOpen S) {x₀ : M} (hx₀ : x₀ ∈ S)
    (J : Set ℝ) (t : ℝ) :
    J ×ˢ S ∈ 𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) := by
  have hset : (J ×ˢ (Set.univ : Set M)) ∩ ((fun p : ℝ × M => p.2) ⁻¹' S) = J ×ˢ S := by
    ext p
    simp [Set.mem_prod]
  have hopen : ((fun p : ℝ × M => p.2) ⁻¹' S) ∈ nhds ((t, x₀) : ℝ × M) :=
    (hS.preimage continuous_snd).mem_nhds hx₀
  have h := inter_mem_nhdsWithin (J ×ˢ (Set.univ : Set M)) (a := ((t, x₀) : ℝ × M)) hopen
  rwa [hset] at h

variable (g : ℝ → SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem normSq0S_jointContMDiffOn {J : Set ℝ} {s : ℕ}
    (A : ℝ → (x : M) → Tensor0SSpace s I x)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (x₀ : M) (K : Fin s → Fin (Module.finrank ℝ E)) {t : ℝ}, t ∈ J →
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (J ×ˢ (Set.univ : Set M)) (t, x₀)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  rintro ⟨t, x₀⟩ ⟨htJ, -⟩
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hqbase : x₀ ∈ e.baseSet := by
    rw [he]
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hnhd : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
    prodOpen_nhdsWithin e.open_baseSet hqbase J t
  have hsum : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        ∑ K : Fin s → Fin (Module.finrank ℝ E),
          ∑ L : Fin s → Fin (Module.finrank ℝ E),
            (∏ a : Fin s, chartInvGramMatrix (I := I) (g p.1) x₀ p.2 (K a) (L a)) *
              A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2) *
              A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (L a) p.2))
      (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) := by
    refine ContMDiffWithinAt.sum fun K _ => ContMDiffWithinAt.sum fun L _ => ?_
    have hinvAt : ∀ k l : Fin (Module.finrank ℝ E),
        ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 k l)
          (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) :=
      fun k l => (chartInvGram_jointContMDiffOn (I := I) g x₀ (hgram x₀) k l
        ((t, x₀) : ℝ × M) ⟨htJ, hqbase⟩).mono_of_mem_nhdsWithin hnhd
    have hAAt : ∀ N : Fin s → Fin (Module.finrank ℝ E),
        ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M =>
            A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (N a) p.2))
          (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) :=
      fun N => hA x₀ N htJ
    exact ((ContMDiffWithinAt.prod fun a _ => hinvAt (K a) (L a)).mul (hAAt K)).mul (hAAt L)
  have heq : (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      =ᶠ[𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M)]
      fun p : ℝ × M =>
        ∑ K : Fin s → Fin (Module.finrank ℝ E),
          ∑ L : Fin s → Fin (Module.finrank ℝ E),
            (∏ a : Fin s, chartInvGramMatrix (I := I) (g p.1) x₀ p.2 (K a) (L a)) *
              A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2) *
              A p.1 p.2 (fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (L a) p.2) := by
    filter_upwards [hnhd] with p hp
    have hpb : p.2 ∈ e.baseSet := hp.2
    rw [normSq0S_eq_coord (I := I) (g p.1) p.2 s (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) x₀ hpb)
      (fun k l => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 k l)
      (chartInvGram_inverse (I := I) (g p.1) x₀ hpb) (A p.1 p.2)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have hbas : ∀ N : Fin s → Fin (Module.finrank ℝ E),
        (fun a : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) x₀ hpb) (N a)) =
          fun a : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (N a) p.2 := by
      intro N
      funext a
      exact DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply (I := I) x₀ hpb (N a)
    rw [hbas K, hbas L]
  exact hsum.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin ⟨htJ, Set.mem_univ x₀⟩)

end JointNormSq

section MetricDiff

variable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem metricChartComp_jointContMDiffOn (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i p.2) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
  hgram x₀ i j

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem metricDiffSq_jointContMDiffOn {J : Set ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => metricDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  simp only [metricDiffSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁
    (fun t x => metricDiffAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K t ht
  have hsub : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        (g₁ p.1).inner p.2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K 1) p.2) -
          (g₂ p.1).inner p.2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K 1) p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (metricChartComp_jointContMDiffOn (I := I) g₁ hgram₁ x₀ (K 0) (K 1)).sub
      (metricChartComp_jointContMDiffOn (I := I) g₂ hgram₂ x₀ (K 0) (K 1))
  have hnhd : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
    prodOpen_nhdsWithin (trivializationAt E (TangentSpace I) x₀).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' x₀) J t
  refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ((hsub.congr ?_) ((t, x₀) : ℝ × M)
    ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩) hnhd
  intro p _
  exact (metricDiffAt_apply (I := I) (g₁ p.1) (g₂ p.1) p.2
    (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2)).symm

end MetricDiff

section ChartComponents

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem inner_sum_left (g : SmoothRiemannianMetric I M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (u : TangentSpace I x) :
    g.inner x (∑ m, c m • w m) u = ∑ m, c m * g.inner x (w m) u := by
  classical
  rw [map_sum, sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem inner_sum_right (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    g.inner x u (∑ m, c m • w m) = ∑ m, c m * g.inner x u (w m) := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem connChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    connectionDifferenceLowAt (I := I) g₁ g₂ x
        (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ α x m (K 2) := by
  classical
  have hd := IsCovariantDerivativeOn.difference_apply
    (hcov := (metricCov (I := I) g₁).isCovariantDerivativeOnUniv)
    (hcov' := (metricCov (I := I) g₂).isCovariantDerivativeOnUniv)
    (σ := fun b : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) b) (x := x) (hx := by trivial)
    (chartBasisVec_alpha_mdifferentiableAt (I := I) α (K 1) hx)
  have hd' :
      CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x) =
        (metricCov (I := I) g₁) (fun b : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) b) x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x) -
            (metricCov (I := I) g₂) (fun b : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) b) x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x) := by
    unfold CovariantDerivative.difference
    exact congrArg
      (fun L : TangentSpace I x →L[ℝ] TangentSpace I x =>
        L (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x)) hd
  have hLC₁ : metricCov (I := I) g₁ = LeviCivita (I := I) g₁ := rfl
  have hLC₂ : metricCov (I := I) g₂ = LeviCivita (I := I) g₂ := rfl
  change Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x)
      (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) = _
  rw [connectionDifferenceLowAt_apply]
  rw [hd', hLC₁, hLC₂,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₁ α (K 0) (K 1) hx,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₂ α (K 0) (K 1) hx,
    ← Finset.sum_sub_distrib]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m x -
          chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x) •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m x)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m x from
    Finset.sum_congr rfl fun m _ => (sub_smul _ _ _).symm]
  rw [inner_sum_left]
  exact Finset.sum_congr rfl fun m _ => by rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rm04ChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j k n : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x
        (vec4 (I := I) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n x)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g₂ α i j k l (extChartAt I α x) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ α x n l := by
  classical
  have : CovariantDerivative.ContMDiffCovariantDerivative
      (metricCov (I := I) g₂) (∞ : WithTop ℕ∞) := LeviCivita_isContMDiff (I := I) g₂
  rw [CovariantDerivative.riemannCurvature04At_apply_const,
    connectionRiemannCurvatureField_tangentConst_eq_riemannOp (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x _ _ _,
    show riemannOp (cov := metricCov (I := I) g₂) x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
        = riemannOp (cov := LeviCivita (I := I) g₂) x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) from rfl,
    riemannOp_chartBasisVec_alpha_eq (I := I) g₂ α i j k hx, inner_sum_right]
  exact Finset.sum_congr rfl fun l _ => by rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rm04ChartMap (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x
        (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g₂ α (K 2) (K 0) (K 1) l (extChartAt I α x) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ α x (K 3) l := by
  have hvec : (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) =
      vec4 (I := I) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 2) x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 3) x) := by
    funext a
    fin_cases a <;> rfl
  rw [hvec]
  exact rm04ChartComp (I := I) g₁ g₂ α (K 2) (K 0) (K 1) (K 3) hx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rmChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    rmDiffLowAt (I := I) g₁ g₂ x
        (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (chartRiemannTensor (I := I) g₁ α (K 2) (K 0) (K 1) l (extChartAt I α x) -
            chartRiemannTensor (I := I) g₂ α (K 2) (K 0) (K 1) l (extChartAt I α x)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ α x (K 3) l := by
  classical
  have hvec : (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K a) x) =
      vec4 (I := I) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 0) x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 1) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 2) x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (K 3) x) := by
    funext a
    fin_cases a <;> rfl
  rw [hvec, rmDiffLowAt_apply,
    show metricRm04At (I := I) g₁ x =
        CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₁)
          (metricCov_smooth (I := I) g₁) x from rfl,
    rm04ChartComp (I := I) g₁ g₁ α (K 2) (K 0) (K 1) (K 3) hx,
    rm04ChartComp (I := I) g₁ g₂ α (K 2) (K 0) (K 1) (K 3) hx,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => (sub_mul _ _ _).symm

end ChartComponents

section JointChart

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private theorem good_nhdsWithin (x₀ : M) (J : Set ℝ) (t : ℝ) :
    J ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ∈
      𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
  prodOpen_nhdsWithin (chartLeviCivitaGoodSet_isOpen (I := I) x₀)
    (self_mem_chartLeviCivitaGoodSet (I := I) x₀) J t

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem connChartJoint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (x₀ : M)
    (hgram₁ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => connectionDifferenceLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  have hG₁ := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g₁ x₀ hgram₁
  have hG₂ := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g₂ x₀ hgram₂
  have hxs : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hnhdS := prodOpen_nhdsWithin (chartAt H x₀).open_source
    (mem_chart_source H x₀) J t
  have hnhdB : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
    prodOpen_nhdsWithin (trivializationAt E (TangentSpace I) x₀).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' x₀) J t
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) (g₁ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2) -
            chartChristoffel (I := I) (g₂ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 m (K 2))
      (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) := by
    refine ContMDiffWithinAt.sum fun m _ => ?_
    exact
      (((chartChristoffel_comp_extChartAt_contMDiffWithinAt (I := I) g₁ x₀ hG₁ (K 0) (K 1) m ht hxs).mono_of_mem_nhdsWithin
          hnhdS).sub
        ((chartChristoffel_comp_extChartAt_contMDiffWithinAt (I := I) g₂ x₀ hG₂ (K 0) (K 1) m ht hxs).mono_of_mem_nhdsWithin
          hnhdS)).mul
      ((hgram₁ m (K 2) ((t, x₀) : ℝ × M)
        ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩).mono_of_mem_nhdsWithin hnhdB)
  have heq : (fun p : ℝ × M => connectionDifferenceLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      =ᶠ[𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M)]
      fun p : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) (g₁ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2) -
            chartChristoffel (I := I) (g₂ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 m (K 2) := by
    filter_upwards [good_nhdsWithin (I := I) x₀ J t] with p hp
    exact connChartComp (I := I) (g₁ p.1) (g₂ p.1) x₀ K hp.2
  exact hΦ.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin ⟨ht, Set.mem_univ x₀⟩)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rmChartJoint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (x₀ : M)
    (hgram₁ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  have hG₁ := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g₁ x₀ hgram₁
  have hG₂ := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g₂ x₀ hgram₂
  have hxs : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hnhdS := prodOpen_nhdsWithin (chartAt H x₀).open_source
    (mem_chart_source H x₀) J t
  have hnhdB : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
    prodOpen_nhdsWithin (trivializationAt E (TangentSpace I) x₀).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' x₀) J t
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ l : Fin (Module.finrank ℝ E),
        (chartRiemannTensor (I := I) (g₁ p.1) x₀ (K 2) (K 0) (K 1) l (extChartAt I x₀ p.2) -
            chartRiemannTensor (I := I) (g₂ p.1) x₀ (K 2) (K 0) (K 1) l
              (extChartAt I x₀ p.2)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 (K 3) l)
      (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) := by
    refine ContMDiffWithinAt.sum fun l _ => ?_
    exact
      (((chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (I := I) g₁ x₀ hG₁ (K 2) (K 0) (K 1) l ht hxs).mono_of_mem_nhdsWithin
          hnhdS).sub
        ((chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (I := I) g₂ x₀ hG₂ (K 2) (K 0) (K 1) l ht hxs).mono_of_mem_nhdsWithin
          hnhdS)).mul
      ((hgram₁ (K 3) l ((t, x₀) : ℝ × M)
        ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩).mono_of_mem_nhdsWithin hnhdB)
  have heq : (fun p : ℝ × M => rmDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      =ᶠ[𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M)]
      fun p : ℝ × M => ∑ l : Fin (Module.finrank ℝ E),
        (chartRiemannTensor (I := I) (g₁ p.1) x₀ (K 2) (K 0) (K 1) l (extChartAt I x₀ p.2) -
            chartRiemannTensor (I := I) (g₂ p.1) x₀ (K 2) (K 0) (K 1) l
              (extChartAt I x₀ p.2)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 (K 3) l := by
    filter_upwards [good_nhdsWithin (I := I) x₀ J t] with p hp
    exact rmChartComp (I := I) (g₁ p.1) (g₂ p.1) x₀ K hp.2
  exact hΦ.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin ⟨ht, Set.mem_univ x₀⟩)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem nablaRicChartJoint (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        metricNabla0S (I := I) (g p.1)
          (CovariantDerivative.ricciSection (I := I)
            (metricCov (I := I) (g p.1)) (metricCov_smooth (I := I) (g p.1))) p.2
          (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  have hG := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g x₀ hgram
  have hxs : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hnhdS := prodOpen_nhdsWithin (chartAt H x₀).open_source
    (mem_chart_source H x₀) J t
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) (K 0)
            (chartRicciTensor (I := I) (g p.1) x₀ (K 1) (K 2))
            (extChartAt I x₀ p.2) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g p.1) x₀ (K 0) (K 1) m
                (extChartAt I x₀ p.2) *
              chartRicciTensor (I := I) (g p.1) x₀ m (K 2)
                (extChartAt I x₀ p.2) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g p.1) x₀ (K 0) (K 2) m
                (extChartAt I x₀ p.2) *
              chartRicciTensor (I := I) (g p.1) x₀ (K 1) m
                (extChartAt I x₀ p.2))
      (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) := by
    refine
      ((partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG (K 0) (K 1) (K 2) ht hxs).mono_of_mem_nhdsWithin
        hnhdS).sub ?_ |>.sub ?_
    · refine ContMDiffWithinAt.sum fun m _ => ?_
      exact
        ((chartChristoffel_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG (K 0) (K 1) m ht hxs).mono_of_mem_nhdsWithin
          hnhdS).mul
        ((chartRicciTensor_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG m (K 2) ht hxs).mono_of_mem_nhdsWithin
          hnhdS)
    · refine ContMDiffWithinAt.sum fun m _ => ?_
      exact
        ((chartChristoffel_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG (K 0) (K 2) m ht hxs).mono_of_mem_nhdsWithin
          hnhdS).mul
        ((chartRicciTensor_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG (K 1) m ht hxs).mono_of_mem_nhdsWithin
          hnhdS)
  have heq :
      (fun p : ℝ × M =>
        metricNabla0S (I := I) (g p.1)
          (CovariantDerivative.ricciSection (I := I)
            (metricCov (I := I) (g p.1)) (metricCov_smooth (I := I) (g p.1))) p.2
          (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2)) =ᶠ[
        𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M)]
      fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) (K 0)
            (chartRicciTensor (I := I) (g p.1) x₀ (K 1) (K 2))
            (extChartAt I x₀ p.2) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g p.1) x₀ (K 0) (K 1) m
                (extChartAt I x₀ p.2) *
              chartRicciTensor (I := I) (g p.1) x₀ m (K 2)
                (extChartAt I x₀ p.2) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g p.1) x₀ (K 0) (K 2) m
                (extChartAt I x₀ p.2) *
              chartRicciTensor (I := I) (g p.1) x₀ (K 1) m
                (extChartAt I x₀ p.2) := by
    filter_upwards [good_nhdsWithin (I := I) x₀ J t] with p hp
    exact nablaRicChartComp (I := I) (g p.1)
      (CovariantDerivative.ricciSection (I := I)
        (metricCov (I := I) (g p.1)) (metricCov_smooth (I := I) (g p.1)))
      (fun y => by
        rw [CovariantDerivative.ricciSection_apply]
        rfl)
      x₀ K hp.2
  exact hΦ.congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin ⟨ht, Set.mem_univ x₀⟩)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem metricChartJoint (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 2 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => metricTensorField (I := I) (g p.1) p.2
        (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  have hfun : (fun p : ℝ × M => metricTensorField (I := I) (g p.1) p.2
        (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2)) =
      fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 (K 0) (K 1) := by
    funext p
    rw [metricTensorField_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rw [hfun]
  exact (hgram (K 0) (K 1) ((t, x₀) : ℝ × M)
    ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩).mono_of_mem_nhdsWithin
    (prodOpen_nhdsWithin (trivializationAt E (TangentSpace I) x₀).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' x₀) J t)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rm04ChartJoint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (x₀ : M)
    (hgram₁ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        CovariantDerivative.riemannCurvature04At (I := I) (g₁ p.1) (metricCov (I := I) (g₂ p.1))
          (metricCov_smooth (I := I) (g₂ p.1)) p.2
          (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  have hG₂ := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g₂ x₀ hgram₂
  have hxs : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hnhdS := prodOpen_nhdsWithin (chartAt H x₀).open_source
    (mem_chart_source H x₀) J t
  have hnhdB : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M) :=
    prodOpen_nhdsWithin (trivializationAt E (TangentSpace I) x₀).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' x₀) J t
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (g₂ p.1) x₀ (K 2) (K 0) (K 1) l (extChartAt I x₀ p.2) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 (K 3) l)
      (J ×ˢ (Set.univ : Set M)) ((t, x₀) : ℝ × M) := by
    refine ContMDiffWithinAt.sum fun l _ => ?_
    exact ((chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (I := I) g₂ x₀ hG₂ (K 2) (K 0) (K 1) l ht hxs).mono_of_mem_nhdsWithin
        hnhdS).mul
      ((hgram₁ (K 3) l ((t, x₀) : ℝ × M)
        ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩).mono_of_mem_nhdsWithin hnhdB)
  have heq : (fun p : ℝ × M =>
        CovariantDerivative.riemannCurvature04At (I := I) (g₁ p.1) (metricCov (I := I) (g₂ p.1))
          (metricCov_smooth (I := I) (g₂ p.1)) p.2
          (fun a : Fin 4 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K a) p.2))
      =ᶠ[𝓝[J ×ˢ (Set.univ : Set M)] ((t, x₀) : ℝ × M)]
      fun p : ℝ × M => ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (g₂ p.1) x₀ (K 2) (K 0) (K 1) l (extChartAt I x₀ p.2) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 (K 3) l := by
    filter_upwards [good_nhdsWithin (I := I) x₀ J t] with p hp
    exact rm04ChartMap (I := I) (g₁ p.1) (g₂ p.1) x₀ K hp.2
  exact hΦ.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin ⟨ht, Set.mem_univ x₀⟩)

end JointChart

section Density

variable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem connectionDifferenceSq_jointContMDiffOn {J : Set ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => connectionDifferenceSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  simp only [connectionDifferenceSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁
    (fun t x => connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K t ht
  exact connChartJoint (I := I) g₁ g₂ x₀ (hgram₁ x₀) (hgram₂ x₀) K ht

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem rmDiffSq_jointContMDiffOn {J : Set ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  simp only [rmDiffSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁
    (fun t x => rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K t ht
  exact rmChartJoint (I := I) g₁ g₂ x₀ (hgram₁ x₀) (hgram₂ x₀) K ht

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem dens_jointContMDiffOn {J : Set ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  have h := ((metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂).add
    (connectionDifferenceSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂)).add
    (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂)
  exact h.congr fun p _ => rfl

end Density

section Integrability

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem integrable_of_continuous (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianMeasureFamily (I := I) (M := M) g t) := by
  have : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) (g t)
  rw [riemannianMeasureFamily_def]
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem normSq0S_continuous {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun x : M => normSq0S (I := I) g x s (A x)) :=
  (normSq0S_smooth (I := I) g A).continuous

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem inner0S_smooth {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => inner0S (I := I) g x s (A x) (B x)) := by
  have hfun : (fun x : M => inner0S (I := I) g x s (A x) (B x)) =
      fun x : M => (normSq0S (I := I) g x s ((A + B) x) -
        normSq0S (I := I) g x s (A x) - normSq0S (I := I) g x s (B x)) * (1 / 2 : ℝ) := by
    funext x
    have hsplit : (A + B) x = A x + B x := rfl
    rw [hsplit, normSq0S_add]
    ring
  rw [hfun]
  exact (((normSq0S_smooth (I := I) g (A + B)).sub (normSq0S_smooth (I := I) g A)).sub
    (normSq0S_smooth (I := I) g B)).mul contMDiff_const

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem inner0S_continuous {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun x : M => inner0S (I := I) g x s (A x) (B x)) :=
  (inner0S_smooth (I := I) g A B).continuous

section Slots

variable (g₁ : ℝ → SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem ilap_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (roughLap0SField (I := I) (g₁ t) Sfield) Sfield)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem idiv_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) Uflux x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (covDiv0SField (I := I) (g₁ t) Uflux) Sfield)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem inab_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (Uflux x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) Sfield) Uflux)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem idis_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Integrable (fun x : M => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (normSq0S_continuous (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) Sfield))

end Slots

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem dens_integrable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hdcont : Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)) :
    Integrable (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t hdcont

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem dens_continuous_of_joint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b t : ℝ}
    (ht : t ∈ Set.Ioo a b)
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M))) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) := by
  have hslice : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun x : M => (t, x)) Set.univ
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) :=
    fun x _ => ⟨ht, Set.mem_univ x⟩
  have hcomp := hdens.comp hslice.contMDiffOn hmaps
  rw [contMDiffOn_univ] at hcomp
  exact hcomp.continuous

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem dens_continuous (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) := by
  have hconst : ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ p.2 i j)
        (Set.Ioo (t - 1) (t + 1) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro g x₀ i j
    have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (Set.Ioo (t - 1) (t + 1) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      contMDiffOn_snd
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g x₀ i j).comp hsnd fun p hp => hp.2
  have ht : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hcont := dens_continuous_of_joint (I := I) (fun _ => g₁ t) (fun _ => g₂ t) ht
    (dens_jointContMDiffOn (I := I) (fun _ => g₁ t) (fun _ => g₂ t)
      (fun x₀ i j => hconst (g₁ t) x₀ i j) (fun x₀ i j => hconst (g₂ t) x₀ i j))
  have hfun :
      (fun x : M => forwardUniqueDensity (I := I) (fun _ => g₁ t) (fun _ => g₂ t) t x) =
        fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x := rfl
  rwa [hfun] at hcont

omit [NeZero (Module.finrank ℝ E)] in
theorem dcont_idens (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) ∧
      Integrable (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  ⟨dens_continuous (I := I) g₁ g₂ t,
    dens_integrable (I := I) g₁ g₂ t (dens_continuous (I := I) g₁ g₂ t)⟩

end Integrability

end DifferentialGeometry.PDE.RicciFlow

end
