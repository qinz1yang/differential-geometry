import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.FixedDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.Bounds
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal


namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_pullback
    (K : Set N) (gRef h : SmoothRiemannianMetric I N) (C : ℝ)
    (hequiv : MetricUniformEquivalentOn (I := I) K gRef h C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricUniformEquivalentOn (I := I) V
      (Diffeomorph.pullbackMetric (I := I) gRef Φ)
      (Diffeomorph.pullbackMetric (I := I) h Φ) C := by
  obtain ⟨hC, hbound⟩ := hequiv
  refine ⟨hC, fun x hx v => ?_⟩
  rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
  exact hbound (Φ x) (hV x hx) (mfderiv I I (Φ : M → N) x v)

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_pullback
    (K : Set N) (β ψ : ℝ) (gRef : SmoothRiemannianMetric I N)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N) (B : ℝ → ℝ)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricUniformEquivalentOnWindow (I := I) V β ψ
      (Diffeomorph.pullbackMetric (I := I) gRef Φ)
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) B := by
  intro i t ht
  exact metricUniformEquivalentOn_pullback (I := I) K gRef (gSeq i t) (B t)
    (hequiv i t ht) Φ hV

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem solutionSubsequenceMetricLowerBound_pullback
    (β ψ : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N)
    (hLow : SolutionSubsequenceMetricLowerBound (I := I) β ψ gSeq gRef)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionSubsequenceMetricLowerBound (I := I) β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) := by
  intro ρ hρ t ht
  obtain ⟨c, hc, hbound⟩ := hLow ρ hρ t ht
  refine ⟨c, hc, fun k x v => ?_⟩
  rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
  exact hbound k (Φ x) (mfderiv I I (Φ : M → N) x v)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricCovDerivOrderBoundOn_pullback
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (K : Set N) (a : ℕ) (h gRef : SmoothRiemannianMetric I N) (C : ℝ)
    (hbound : MetricCovDerivOrderBoundOn (I := I) K a h gRef C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricCovDerivOrderBoundOn (I := I) V a
      (Diffeomorph.pullbackMetric (I := I) h Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) C := by
  intro x hx
  rw [metricCovDerivNorm_pullback (I := I) a h gRef Φ x]
  exact hbound (Φ x) (hV x hx)

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivOrderBoundOnWindow_pullback
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (K : Set N) (β ψ : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (a : ℕ) (C : ℝ)
    (hbound : MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C)
    (Φ : M ≃ₘ⟮I, I⟯ N) {V : Set M} (hV : ∀ x ∈ V, (Φ : M → N) x ∈ K) :
    MetricCovDerivOrderBoundOnWindow (I := I) V β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) a C := by
  intro i t ht
  exact metricCovDerivOrderBoundOn_pullback (I := I) K a (gSeq i t) gRef C (hbound i t ht) Φ hV

noncomputable def solutionZeroOrderMetricBoundsPullback
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [T2Space N]
    (K : Set N) (β ψ : ℝ)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N) (gRef : SmoothRiemannianMetric I N)
    (hData : SolutionZeroOrderMetricBounds (I := I) K β ψ gSeq gRef)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionZeroOrderMetricBounds (I := I) ((Φ : M → N) ⁻¹' K) β ψ
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) where
  U0 := (Φ : M → N) ⁻¹' hData.U0
  subset_domain := fun _x hx => hData.subset_domain hx
  B0 := hData.B0
  uniform_equivalence := metricUniformEquivalentOnWindow_pullback (I := I) hData.U0 β ψ gRef gSeq
    hData.B0 hData.uniform_equivalence Φ (fun _x hx => hx)
  Bmax0 := hData.Bmax0
  one_le_equivalenceBound := hData.one_le_equivalenceBound
  equivalence_le_bound := hData.equivalence_le_bound
  KShi0 := hData.KShi0
  curvatureBound_nonneg := hData.curvatureBound_nonneg
  ricci_bound := fun i t ht x hx => by
    have key :
        Tensor0SBundle.normSq0S (I := I)
            (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) x 2
            (ricCovTower (I := I) (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
              (Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ) 0 x)
          = Tensor0SBundle.normSq0S (I := I) (gSeq i t) (Φ x) 2
              (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 (Φ x)) :=
      ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ 0 x
    rw [key]
    exact hData.ricci_bound i t ht (Φ x) hx

omit [I.Boundaryless] in
theorem solutionCovariantDerivativeBounds_pullback
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (β ψ t0 : ℝ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (D : ℕ → RealTimeInterval)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolutionCovariantDerivativeBounds (I := I) β ψ t0 gSeq gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionCovariantDerivativeBounds (I := I) β ψ t0
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOnPullback (I := I) (S i) Φ) where
  pack := by
    intro K' hK' n hn
    obtain ⟨U, hUopen, hK'U, B, Bmax, KShi, initialC, timeRadius,
        hequiv, hBmax1, hBmax, hKShi0, hShi, ht0, hreg, hinitC0, hinitCbound, htime⟩ :=
      hData.pack ((Φ : M → N) '' K') (hK'.image Φ.continuous) n hn
    refine ⟨(Φ : M → N) ⁻¹' U, hUopen.preimage Φ.continuous, ?_, B, Bmax, KShi, initialC,
      timeRadius, ?_, hBmax1, hBmax, hKShi0, ?_, ht0, hreg, hinitC0, ?_, htime⟩
    · exact fun x hx => hK'U ⟨x, hx, rfl⟩
    · exact metricUniformEquivalentOnWindow_pullback (I := I) U β ψ gRef gSeq B hequiv Φ
        (fun _x hx => hx)
    · intro s hs i t ht x hx
      rw [ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ s x]
      exact hShi s hs i t ht (Φ x) hx
    · intro r hr1 hrn i x hx
      rw [metricCovDerivNorm_pullback (I := I) r (gSeq i t0) gRef Φ x]
      exact hinitCbound r hr1 hrn i (Φ x) hx

omit [I.Boundaryless] in
theorem solutionMetricLipschitzBounds_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (K : Set N) (β ψ : ℝ) (p : ℕ) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I N)
    (gRef : SmoothRiemannianMetric I N) (D : ℕ → RealTimeInterval)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolutionMetricLipschitzBounds (I := I) K β ψ p gSeq gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionMetricLipschitzBounds (I := I) ((Φ : M → N) ⁻¹' K) β ψ p
      (fun i t => Diffeomorph.pullbackMetric (I := I) (gSeq i t) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOnPullback (I := I) (S i) Φ) where
  pack := by
    let _ := (inferInstance : (NeZero (Module.finrank ℝ E)))
    intro a ha1 hap
    obtain ⟨U, hUopen, hKU, B, Bmax, Cg, KShi, CN,
        hequiv, hBmax1, hBmax, hCg, hKShi0, hShi, hCN0, hCN⟩ := hData.pack a ha1 hap
    refine ⟨(Φ : M → N) ⁻¹' U, hUopen.preimage Φ.continuous, fun x hx => hKU hx,
      B, Bmax, Cg, KShi, CN, ?_, hBmax1, hBmax, ?_, hKShi0, ?_, hCN0, ?_⟩
    · exact metricUniformEquivalentOnWindow_pullback (I := I) U β ψ gRef gSeq B hequiv Φ
        (fun _x hx => hx)
    · intro r hr1 hra
      exact metricCovDerivOrderBoundOnWindow_pullback (I := I) U β ψ gSeq gRef r (Cg r)
        (hCg r hr1 hra) Φ (fun _x hx => hx)
    · intro s hs i t ht x hx
      rw [ricCovTower_normSq0S_pullback (I := I) (gSeq i t) Φ s x]
      exact hShi s hs i t ht (Φ x) hx
    · exact metricCovDerivOrderBoundOnWindow_pullback (I := I) K β ψ gSeq gRef a CN hCN Φ
        (fun _x hx => hx)

omit [I.Boundaryless] in
theorem solutionMetricField_pullback
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (r : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solutionMetricField (I := I) (solutionOnPullback (I := I) S Φ) r y slots
      = solutionMetricField (I := I) S r (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) := by
  simp only [solutionMetricField]
  rw [Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply]
  exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric r) Φ y (slots 0) (slots 1)

omit [I.Boundaryless] in
theorem solutionRicField_pullback
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M]
    [IsManifold I 1 N]
    [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (t : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solutionRicField (I := I) (solutionOnPullback (I := I) S Φ) t y slots
      = solutionRicField (I := I) S t (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) :=
  ricciSection_pullback (I := I) (S.family.metric t) Φ y slots

omit [I.Boundaryless] in
theorem solutionEvolutionField_pullback
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [hManifoldM : IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [hManifoldN : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (t : ℝ) (y : M) (slots : Fin 2 → TangentSpace I y) :
    solutionEvolutionField (I := I) (solutionOnPullback (I := I) S Φ) t y slots
      = solutionEvolutionField (I := I) S t (Φ y)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) y (slots q)) := by
  let _ := hManifoldM
  let _ := hManifoldN
  simp only [solutionEvolutionField, ContMDiffSection.coe_smul, Pi.smul_apply,
    Tensor0SBundle.Tensor0SSpace.smul_apply,
    solutionRicField_pullback (I := I) S Φ t y slots]

omit [I.Boundaryless] in
theorem solutionTimeDerivativeCommutation_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    {D : ℕ → RealTimeInterval} (gRef : SmoothRiemannianMetric I N)
    (S : (i : ℕ) → SolutionOn (I := I) (M := N) (D i))
    (hData : SolutionTimeDerivativeCommutation (I := I) gRef D S) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionTimeDerivativeCommutation (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOnPullback (I := I) (S i) Φ) := by
  let _ := (inferInstance : (NeZero (Module.finrank ℝ E)))
  intro i n p' hp' V x0 t ht x hx Vdir
  have hfield : ∀ (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
      (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      (∀ (y : M) (sl : Fin 2 → TangentSpace I y),
          A0M y sl = A0N (Φ y) (fun q => mfderiv I I (Φ : M → N) y (sl q))) →
      (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
            A0M p' y (fun a => V a y))
        = fun y : M => (fun z : N => covDerivOfField (I := I) gRef A0N p' z
            (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ y) := by
    intro A0M A0N hA0
    funext y
    rw [covDerivOfField_pullback (I := I) gRef Φ A0M A0N hA0 p' y (fun a => V a y)]
    congr 1
    funext a
    rw [pushFwdSection_apply_at_image]
  have hMDiff : ∀ (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z : N => covDerivOfField (I := I) gRef A0N p' z
          (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x) := by
    intro A0N
    exact (covDerivOfField_eval_contMDiff (I := I) gRef A0N p'
      (fun a => pushFwdSection (I := I) Φ (V a))).contMDiffAt.mdifferentiableAt (by simp)
  have hconv : ∀ (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
      (A0N : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2),
      (∀ (y : M) (sl : Fin 2 → TangentSpace I y),
          A0M y sl = A0N (Φ y) (fun q => mfderiv I I (Φ : M → N) y (sl q))) →
      mvfderiv (I := I)
          (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
            A0M p' y (fun a => V a y)) x Vdir
        = mvfderiv (I := I)
            (fun z : N => covDerivOfField (I := I) gRef A0N p' z
              (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x)
            (mfderiv I I (Φ : M → N) x Vdir) := by
    intro A0M A0N hA0
    rw [hfield A0M A0N hA0]
    exact mvfderiv_comp_diffeomorph
      (fun z : N => covDerivOfField (I := I) gRef A0N p' z
        (fun a => (pushFwdSection (I := I) Φ (V a)) z)) Φ x Vdir (hMDiff A0N)
  have hfun : (fun s : ℝ => mvfderiv (I := I)
        (fun y : M => covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Φ)
          (solutionMetricField (I := I) (solutionOnPullback (I := I) (S i) Φ) s) p' y
          (fun a => V a y)) x Vdir)
      = fun s : ℝ => mvfderiv (I := I)
          (fun z : N => covDerivOfField (I := I) gRef (solutionMetricField (I := I) (S i) s) p' z
            (fun a => (pushFwdSection (I := I) Φ (V a)) z)) (Φ x)
          (mfderiv I I (Φ : M → N) x Vdir) := by
    funext s
    exact hconv _ _ (fun y sl => solutionMetricField_pullback (I := I) (S i) Φ s y sl)
  rw [hfun, hconv _ _ (fun y sl => solutionEvolutionField_pullback (I := I) (S i) Φ t y sl)]
  exact hData i n p' hp' (fun a => pushFwdSection (I := I) Φ (V a)) (Φ x0) t ht (Φ x)
    (by rw [Set.mem_singleton_iff] at hx ⊢; rw [hx]) (mfderiv I I (Φ : M → N) x Vdir)

noncomputable def solutionWindowCompactnessPullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (W : SolutionWindowCompactness (I := I) (M := N)) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionWindowCompactness (I := I) (M := M) := by
  cases W with
  | mk K hK beta psiT t0 hbeta p gSeq gRef D S hS hmet hreg H0 hswap Hcov Hlip hlow =>
    refine SolutionWindowCompactness.mk ((Φ : M → N) ⁻¹' K) ?_ beta psiT t0 hbeta p
      (fun i r => Diffeomorph.pullbackMetric (I := I) (gSeq i r) Φ)
      (Diffeomorph.pullbackMetric (I := I) gRef Φ) D
      (fun i => solutionOnPullback (I := I) (S i) Φ)
      (fun i => isSolutionOn_pullback (I := I) (S i) (hS i) Φ)
      (fun i r => congrArg (fun g => Diffeomorph.pullbackMetric (I := I) g Φ) (hmet i r))
      hreg
      (solutionZeroOrderMetricBoundsPullback (I := I) K beta psiT gSeq gRef H0 Φ)
      (solutionTimeDerivativeCommutation_pullback (I := I) gRef S hswap Φ)
      (solutionCovariantDerivativeBounds_pullback (I := I) beta psiT t0 gSeq gRef D S Hcov Φ)
      (solutionMetricLipschitzBounds_pullback (I := I) K beta psiT p gSeq gRef D S Hlip Φ)
      (solutionSubsequenceMetricLowerBound_pullback (I := I) beta psiT gSeq gRef hlow Φ)
    have hset : (Φ : M → N) ⁻¹' K = (Φ.symm : N → M) '' K := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz
        exact ⟨Φ z, hz, Φ.symm_apply_apply z⟩
      · rintro ⟨k, hk, rfl⟩
        rwa [Φ.apply_symm_apply]
    rw [hset]
    exact hK.image Φ.symm.continuous

theorem hasMetricWindowSubsequence_of_pullback
    [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [T2Space N]
    (hne : Nonempty M) (W : SolutionWindowCompactness (I := I) (M := N)) (Φ : M ≃ₘ⟮I, I⟯ N) :
    HasMetricWindowSubsequence (E := E) (H := H) (I := I) (M := M) :=
  hasMetricWindowSubsequence_of_solution (I := I) hne
    (solutionWindowCompactnessPullback (I := I) W Φ)

end CheegerGromovCompactness
end DifferentialGeometry
