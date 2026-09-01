import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DistanceControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricBallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationMonotonicity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.DirectLimit.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.ComponentSubsequence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormFlat
import DifferentialGeometry.Geometry.Metric.Convergence.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.WindowAllOrders
import DifferentialGeometry.Topology.SigmaCompactOpen
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

def ballOpen (b : ∀ j, M j) (r : ℕ → ℝ) (j : ℕ) : Opens (M j) :=
  ⟨Metric.ball (b j) (r j), Metric.isOpen_ball⟩

def tailBallOpen (b : ∀ j, M j) (j₀ n : ℕ) : Opens (M (j₀ + n)) :=
  ⟨Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n), Metric.isOpen_ball⟩

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem ballOpen_nonempty (b : ∀ j, M j) (r : ℕ → ℝ) (j : ℕ) (hr : 0 < r j) :
    Nonempty (ballOpen b r j) := by
  refine ⟨⟨b j, ?_⟩⟩
  exact Metric.mem_ball_self hr

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem tailBall_nonempty (b : ∀ j, M j) (j₀ n : ℕ) :
    Nonempty (tailBallOpen b j₀ n) :=
  ⟨⟨b (j₀ + n), Metric.mem_ball_self (by positivity)⟩⟩

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem tailBall_le_large (b : ∀ j, M j) (j₀ n : ℕ) :
    tailBallOpen b j₀ n ≤ ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) := by
  intro x hx
  change x ∈ Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n) at hx
  change x ∈ Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))
  rw [Metric.mem_ball] at hx ⊢
  exact hx.trans_le (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))

noncomputable def tailMetric
    (b : ∀ j, M j) (j₀ : ℕ)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (n : ℕ) : SmoothRiemannianMetric I (tailBallOpen b j₀ n) := by
  letI : SigmaCompactSpace (tailBallOpen b j₀ n) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  exact (gInf n).restrictOpenOfSubset (I := I) (tailBall_le_large b j₀ n)

def coreRadius (n : ℕ) : ℝ := (2 : ℝ) ^ n / 2

def tailCenter (b : ∀ j, M j) (j₀ n : ℕ) : tailBallOpen b j₀ n :=
  ⟨b (j₀ + n), Metric.mem_ball_self (by positivity)⟩

def tailCore (b : ∀ j, M j) (j₀ n : ℕ) : Set (tailBallOpen b j₀ n) :=
  {x | dist (b (j₀ + n)) (x : M (j₀ + n)) ≤ coreRadius n}

def limitCore (b : ∀ j, M j) (j₀ : ℕ)
    [∀ n, Nonempty (tailBallOpen b j₀ n)]
    (S : SmoothSeqSystem I (fun n => tailBallOpen b j₀ n)) (n : ℕ) :
    Set S.toSeqSystem.Lim :=
  S.toSeqSystem.incl n '' tailCore b j₀ n

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem core_subset_tail (b : ∀ j, M j) (j₀ n : ℕ) :
    Metric.closedBall (b (j₀ + n)) (coreRadius n) ⊆
      (tailBallOpen b j₀ n : Set (M (j₀ + n))) := by
  intro x hx
  change dist x (b (j₀ + n)) < (2 : ℝ) ^ n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hx' : dist x (b (j₀ + n)) ≤ coreRadius n := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  dsimp only [coreRadius] at hx'
  nlinarith

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem tailCore_compact (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))] : IsCompact (tailCore b j₀ n) := by
  rw [Subtype.isCompact_iff]
  have hval : Subtype.val '' tailCore b j₀ n =
      Metric.closedBall (b (j₀ + n)) (coreRadius n) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [tailCore, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm] using hx
    · intro hy
      refine ⟨⟨y, core_subset_tail b j₀ n hy⟩, ?_, rfl⟩
      simpa only [tailCore, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm] using hy
  rw [hval]
  exact isCompact_closedBall _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] in
theorem limitCore_closed (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    IsClosed (limitCore b j₀ S n) := by
  exact ((tailCore_compact b j₀ n).image
    (S.toSeqSystem.continuous_incl n)).isClosed

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem incl_mem_coreInt (b : ∀ j, M j) (j₀ n : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    {x : tailBallOpen b j₀ n}
    (hx : dist (b (j₀ + n)) (x : M (j₀ + n)) < coreRadius n) :
    S.toSeqSystem.incl n x ∈ interior (limitCore b j₀ S n) := by
  let W : Set (tailBallOpen b j₀ n) :=
    (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ⁻¹'
      Metric.ball (b (j₀ + n)) (coreRadius n)
  have hWopen : IsOpen W := Metric.isOpen_ball.preimage continuous_subtype_val
  have hxW : x ∈ W := by
    simpa only [W, Set.mem_preimage, Metric.mem_ball, dist_comm] using hx
  have hWsub : S.toSeqSystem.incl n '' W ⊆ limitCore b j₀ S n := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have hy' : dist (b (j₀ + n)) (y : M (j₀ + n)) < coreRadius n := by
      simpa only [W, Set.mem_preimage, Metric.mem_ball, dist_comm] using hy
    exact hy'.le
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    ((S.toSeqSystem.incl_isOpenMap n) W hWopen |>.mem_nhds
      (Set.mem_image_of_mem _ hxW)) hWsub

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem center_mem_coreInt (b : ∀ j, M j) (j₀ n : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    S.toSeqSystem.incl n (tailCenter b j₀ n) ∈ interior (limitCore b j₀ S n) := by
  apply incl_mem_coreInt b j₀ n S
  simp only [tailCenter, dist_self, coreRadius]
  positivity

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] in
theorem frontier_core_radius (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    {q : S.toSeqSystem.Lim} (hq : q ∈ frontier (limitCore b j₀ S n)) :
    ∃ x : tailBallOpen b j₀ n,
      S.toSeqSystem.incl n x = q ∧
        dist (b (j₀ + n)) (x : M (j₀ + n)) = coreRadius n := by
  have hclosed := limitCore_closed b j₀ n S
  have hqK : q ∈ limitCore b j₀ S n := by
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hq
  have hnotInt : q ∉ interior (limitCore b j₀ S n) :=
    (mem_frontier_iff_notMem_interior hqK).mp hq
  obtain ⟨x, hx, hxeq⟩ := hqK
  refine ⟨x, hxeq, le_antisymm hx ?_⟩
  by_contra hnot
  have hlt : dist (b (j₀ + n)) (x : M (j₀ + n)) < coreRadius n :=
    lt_of_not_ge hnot
  have hint := incl_mem_coreInt b j₀ n S hlt
  exact hnotInt (hxeq ▸ hint)

def ballStep
    (b : ∀ j, M j) (r : ℕ → ℝ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1))))
    (j : ℕ) : ballOpen b r j → ballOpen b r (j + 1) :=
  PartialDiffeomorph.opensMap (I := I) (M := M j) (N := M (j + 1))
    (Ψ j) (hmap j)

variable [I.Boundaryless]

def ballSystem
    (b : ∀ j, M j) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1)))) :
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
  exact SmoothSeqSystem.ofSucc (fun j => ballStep b r Ψ hmap j)
    (fun j => PartialDiffeomorph.opensMap_isOpenEmb (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))
    (fun j => PartialDiffeomorph.opensMap_contMDiff (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))
    (fun j => PartialDiffeomorph.opensMap_invFun_contMDiffOn
      (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))

omit [CompleteSpace E] [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
private theorem pullbackMetricOn_cast {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (g : ∀ n, SmoothRiemannianMetric I (M n))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hU' : (U : Set (M j)) ⊆ (h ▸ Φ).source) :
    PartialDiffeomorph.pullbackMetricOn (h ▸ Φ) U hU' (g m) = PartialDiffeomorph.pullbackMetricOn Φ U hU (g l) := by
  subst h
  rfl

omit [CompleteSpace E] [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chainPullback_assoc
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j a b : ℕ} (U : Opens (M j))
    (hA : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (hU : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j (a + b)).source) :
    PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hA
        (g ((j + a) + b)) =
      PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j (a + b)) U hU
        (g (j + (a + b))) := by
  simpa only [chainCompAssoc] using
    pullbackMetricOn_cast (I := I) (M := M) (Nat.add_assoc j a b).symm
      (chainComp (I := I) (Mf := M) Ψ j (a + b)) g U hU hA

noncomputable def chainPullbackSeq
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j))
    (hU : ∀ k : ℕ, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source)
    (k : ℕ) : SmoothRiemannianMetric I U :=
  PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) (g (j + k))

omit [CompleteSpace E] [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chainPullback_zero
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j))
    (hU : ∀ k : ℕ, (U : Set (M j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j k).source) :
    chainPullbackSeq (I := I) Ψ g U hU 0 =
      (g j).restrictOpen (I := I) U := by
  let hU0 : (U : Set (M j)) ⊆
      (PartialDiffeomorph.refl (I := I) (M j)).source := hU 0
  with_unfolding_all
    change PartialDiffeomorph.pullbackMetricOn (I := I)
      (PartialDiffeomorph.refl (I := I) (M j)) U hU0 (g j) =
        (g j).restrictOpen (I := I) U
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I U),
      (∀ (x : U) (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) →
        g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  with_unfolding_all
    rw [PartialDiffeomorph.pullbackMetricOn_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have hmfd : mfderiv I I
      (PartialDiffeomorph.refl (I := I) (M j) : M j → M j) (x : M j) =
        ContinuousLinearMap.id ℝ (TangentSpace I (x : M j)) := mfderiv_id
  rw [hmfd]
  rfl

omit [CompleteSpace E] [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chainPullback_step
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j)) (V : Opens (M (j + 1)))
    (hU : ∀ k, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source)
    (hV : ∀ k, (V : Set (M (j + 1))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j + 1) k).source)
    (hmap : (chainComp (I := I) (Mf := M) Ψ j 1 : M j → M (j + 1)) ''
      (U : Set (M j)) ⊆ (V : Set (M (j + 1))))
    (b : ℕ) (x : U) (v w : TangentSpace I x) :
    (chainPullbackSeq (I := I) Ψ g U hU (1 + b)).inner x v w =
      (chainPullbackSeq (I := I) Ψ g V hV b).inner
        (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) hmap x)
        (mfderiv I I (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) hmap) x v)
        (mfderiv I I (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) hmap) x w) := by
  let Φ := chainComp (I := I) (Mf := M) Ψ j 1
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + 1) b
  let F : U → V := PartialDiffeomorph.opensMap Φ hmap
  have hnext : (Φ : M j → M (j + 1)) '' (U : Set (M j)) ⊆ Θ.source :=
    hmap.trans (hV b)
  have hA : (U : Set (M j)) ⊆
      (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b).source := by
    rw [chainAssoc_source (I := I) (Mf := M) Ψ j 1 b]
    exact hU (1 + b)
  have htrans : (U : Set (M j)) ⊆
      (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    PartialDiffeomorph.subset_trans_source Φ Θ U (hU 1) hnext
  have hassoc := chainPullback_assoc (I := I) Ψ g U hA (hU (1 + b))
  have hcongr := PartialDiffeomorph.pullbackMetricOn_congr (I := I)
    (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b)
    (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U hA htrans (g ((j + 1) + b))
    (fun x _ => congrFun (chainCompAssoc_eq (I := I) (Mf := M) Ψ j 1 b) x)
  have htransMetric := PartialDiffeomorph.pullbackMetricOn_trans (I := I) Φ Θ U (hU 1) hnext (g ((j + 1) + b))
  calc
    (chainPullbackSeq (I := I) Ψ g U hU (1 + b)).inner x v w =
        (PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b)
          U hA (g ((j + 1) + b))).inner x v w := by
      simpa only [chainPullbackSeq] using congrArg (fun h => h.inner x v w) hassoc.symm
    _ = (PartialDiffeomorph.pullbackMetricOn (_root_.PartialDiffeomorph.trans (I := I) Φ Θ)
          U htrans (g ((j + 1) + b))).inner x v w :=
      congrArg (fun h => h.inner x v w) hcongr
    _ = (PartialDiffeomorph.nestedPullbackMetricOn Φ Θ U (hU 1) hnext (g ((j + 1) + b))).inner x v w :=
      congrArg (fun h => h.inner x v w) htransMetric
    _ = (chainPullbackSeq (I := I) Ψ g V hV b).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w) := by
      change (PartialDiffeomorph.nestedPullbackMetricOn Φ Θ U (hU 1) hnext (g ((j + 1) + b))).inner x v w =
        (PartialDiffeomorph.pullbackMetricOn Θ V (hV b) (g ((j + 1) + b))).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)
      unfold PartialDiffeomorph.nestedPullbackMetricOn
      rw [Diffeomorph.pullbackMetric_inner, PartialDiffeomorph.pullbackMetricOn_inner, PartialDiffeomorph.pullbackMetricOn_inner,
        PartialDiffeomorph.mfderiv_toOpensDiffeo,
        PartialDiffeomorph.mfderiv_toOpensDiffeo,
        PartialDiffeomorph.opensMap_mfderiv (hU := hU 1),
        PartialDiffeomorph.opensMap_mfderiv (hU := hU 1)]
      rfl
    _ = _ := rfl

noncomputable def chainBallSystem
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1))))) :
    SmoothSeqSystem I (fun n => U n) :=
  SmoothSeqSystem.ofSucc
    (fun n => PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_isOpenEmb
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_contMDiff
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_invFun_contMDiffOn
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (j : ℕ), SigmaCompactSpace (M j)]
    [∀ (j : ℕ), T2Space (M j)] [I.Boundaryless] in
theorem chainMetricCocycle
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) :
    (chainBallSystem (I := I) j₀ U Ψ hU hmap).MetricCocycle gInf := by
  apply SmoothSeqSystem.MetricCocycle.ofSucc
  intro n x v w
  have hF : (chainBallSystem (I := I) j₀ U Ψ hU hmap).toSeqSystem.F
      (Nat.le_succ n) = PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n) := by
    unfold chainBallSystem
    apply SmoothSeqSystem.ofSucc_F_succ
  rw [hF]
  exact (hstep n x v w).symm

def chainAmbientSeq
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j)) :
    PointedRiemannianSeq (I := I) where
  obj n :=
    { M := M (j₀ + n)
      basepoint := (S.toSeqSystem.F (Nat.zero_le n) O₀ : M (j₀ + n))
      metric := g (j₀ + n) }

noncomputable def chainAmbientMaps
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf) :
    PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id where
  partialDiffeomorph n := by
    change PartialDiffeomorph I I S.toSeqSystem.Lim (M (j₀ + n))
      (∞ : WithTop ℕ∞)
    exact PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  source_exhausts := range_exhausts S
  base_mem n := by
    change S.toSeqSystem.incl 0 O₀ ∈ Set.range (S.toSeqSystem.incl n)
    exact
      ⟨S.toSeqSystem.F (Nat.zero_le n) O₀,
        S.toSeqSystem.incl_comp (Nat.zero_le n) O₀⟩
  basepoint_map n := by
    exact congrArg Subtype.val (S.invIncl_incl_le (Nat.zero_le n) O₀)

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
include I in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (j : ℕ), IsManifold I ∞ (M j)]
    [∀ (j : ℕ), SigmaCompactSpace (M j)] [∀ (j : ℕ), T2Space (M j)] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)] in
theorem tailBall_preconn (b : ∀ j, M j) (j₀ n : ℕ) :
    PreconnectedSpace (tailBallOpen b j₀ n) := by
  have hR : 0 < (2 : ℝ) ^ n := by positivity
  have hpath : IsPathConnected
      (Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n) : Set (M (j₀ + n))) := by
    refine ⟨b (j₀ + n), Metric.mem_ball_self hR, ?_⟩
    intro y hy
    have hy' : Manifold.riemannianEDist I (b (j₀ + n)) y <
        ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [← IsRiemannianManifold.out (I := I) (b (j₀ + n)) y, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff hR]
      simpa only [Metric.mem_ball, dist_comm] using hy
    obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hy'
    refine JoinedIn.ofLine hγC.continuousOn hγ0 hγ1 ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, ← ENNReal.ofReal_lt_ofReal_iff hR, ← edist_dist,
      edist_comm, IsRiemannianManifold.out (I := I) (b (j₀ + n)) (γ t)]
    calc
      Manifold.riemannianEDist I (b (j₀ + n)) (γ t) ≤
          Manifold.pathELength I γ 0 t := by
        exact Manifold.riemannianEDist_le_pathELength
          (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
      _ ≤ Manifold.pathELength I γ 0 1 :=
        Manifold.pathELength_mono le_rfl ht.2
      _ < ENNReal.ofReal ((2 : ℝ) ^ n) := hγlen
  let _ : PathConnectedSpace (tailBallOpen b j₀ n) := by
    apply (isPathConnected_iff_pathConnectedSpace
      (F := (tailBallOpen b j₀ n : Set (M (j₀ + n))))).mp
    change IsPathConnected (Metric.ball (b (j₀ + n)) ((2 : Real) ^ n))
    exact hpath
  infer_instance

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)]
  [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] [∀ (j : ℕ), SigmaCompactSpace (M j)] [∀ (j : ℕ), T2Space (M j)] in
theorem speed_ge_of_c0 {j : ℕ}
    (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M j) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I (M j)) {ε : ℝ} {x : M j}
    (hc0 : metricTensorErrorNorm (I := I) P g x ≤ ε)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤ P x (fun _ => v) := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i k => hON i k)
    (P x - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : (P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
      P x (fun _ => v) - g.inner x v v := by
    simp [Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) g x v
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |P x (fun _ => v) - g.inner x v v| ≤ ε * g.inner x v v := by
    unfold metricTensorErrorNorm at hc0
    calc
      |P x (fun _ => v) - g.inner x v v| =
          |(P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by
            rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            (P x - Tensor0SBundle.metricTensorField (I := I) g x)) *
          ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
        rw [hprod]
        exact mul_le_mul_of_nonneg_right hc0 hnn
  nlinarith [abs_le.mp habs]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem ballPullback_covNorm {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (q : ℕ) (x : U) :
    metricCovDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
        (gRef.restrictOpen (I := I) U) x =
      tensor02CovDerivNormWith (I := I) q D.pullback gRef gRef (x : M j) := by
  let hB := PartialDiffeomorph.pullbackMetricOn Φ U hU g
  have hbase : ∀ (y : U) (slots : Fin 2 → TangentSpace I y),
      Tensor0SBundle.metricTensorField (I := I) hB y slots =
        D.pullback (y : M j) slots := by
    intro y slots
    rw [Tensor0SBundle.metricTensorField_apply, PartialDiffeomorph.pullbackMetricOn_inner]
    exact (D.pullback_apply (y : M j) (hUK y.2) slots).symm
  have htower := covDerivOfField_restrictOpen (I := I) gRef U
    (Tensor0SBundle.metricTensorField (I := I) hB) D.pullback hbase q x
  have hT : metricCovDeriv (I := I) hB (gRef.restrictOpen (I := I) U) q x =
      covDerivOfField (I := I) gRef D.pullback q (x : M j) := by
    rw [metricCovDeriv_eq_covDerivOfField]
    exact ContinuousMultilinearMap.ext htower
  unfold metricCovDerivNorm tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, hT]
  congr 1
  exact normSq0S_restrictOpen_apply (I := I) gRef U (q + 2) x _

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem ballPullback_cov_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    metricCovDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
      (gRef.restrictOpen (I := I) U) x ≤ ε := by
  rw [ballPullback_covNorm Φ U hU hUK gRef g D q x]
  exact D.cov_deriv_small q hq1 hqp (x : M j) (hUK x.2)

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem prefixTail_cov_le {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    {K : Set (M l)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (hUK : (Φ : M j → M l) '' (U : Set (M j)) ⊆ K)
    (gMid : SmoothRiemannianMetric I (M l)) (g : SmoothRiemannianMetric I (M m))
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Θ : M l → M m) gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (PartialDiffeomorph.pullbackMetricOn (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U
          (PartialDiffeomorph.subset_trans_source Φ Θ U hU hnext) g)
        (PartialDiffeomorph.pullbackMetricOn Φ U hU gMid) x ≤ ε := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [PartialDiffeomorph.pullbackMetricOn_trans]
  · let W : Opens (M l) :=
      ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
    let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
    let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
      PartialDiffeomorph.toOpensDiffeo Φ hU
    change metricCovDerivNorm (I := I) q
        (Diffeomorph.pullbackMetric (I := I) (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F)
        (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ ε
    rw [metricCovDerivNorm_pullback (I := I)]
    exact ballPullback_cov_le Θ W hnext hUK gMid g D hq1 hqp (F x)

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem chainPrefix_cov_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤ ε := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    PartialDiffeomorph.subset_trans_source Φ Θ U hpre hnext
  rw [PartialDiffeomorph.pullbackMetricOn_congr A (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (fun x _ => congrFun (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b) x)]
  exact prefixTail_cov_le Φ Θ U hpre hnext hUK gMid g D hq1 hqp x

omit [I.Boundaryless]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem ballPullback_lower {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (x : U) (v : TangentSpace I x) :
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v ≤
      (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by
  let vM : TangentSpace I (x : M j) := (v : E)
  calc
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v =
        (1 - ε) * gRef.inner (x : M j) vM vM := rfl
    _ ≤ D.pullback (x : M j) (fun _ => vM) :=
      speed_ge_of_c0 D.pullback gRef
        (D.c0_small (x : M j) (hUK x.2)) vM
    _ = (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by
      with_unfolding_all
        rw [D.pullback_apply (x : M j) (hUK x.2), PartialDiffeomorph.pullbackMetricOn_inner]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem ballPullback_upper {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (x : U) (v : TangentSpace I x) :
    (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v ≤
      (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := by
  let vM : TangentSpace I (x : M j) := (v : E)
  calc
    (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v =
        D.pullback (x : M j) (fun _ => vM) := by
      with_unfolding_all
        rw [D.pullback_apply (x : M j) (hUK x.2), PartialDiffeomorph.pullbackMetricOn_inner]
    _ ≤ (1 + ε) * gRef.inner (x : M j) vM vM :=
      speed_le_of_c0 (I := I) D.pullback gRef
        (D.c0_small (x : M j) (hUK x.2)) vM
    _ = (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := rfl

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem ballPullback_zero_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hε : ε ≤ 1 / 2) (x : U) :
    metricCovDerivNorm (I := I) 0 (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
        (gRef.restrictOpen (I := I) U) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  apply covNorm0_le (I := I) (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
    (gRef.restrictOpen (I := I) U) x (C := 2) (by norm_num)
  intro v
  have hl := ballPullback_lower Φ U hU hUK gRef g D x v
  have hu := ballPullback_upper Φ U hU hUK gRef g D x v
  have hnn : 0 ≤ (gRef.restrictOpen (I := I) U).inner x v v :=
    metric_inner_self_nonneg (I := I) (gRef.restrictOpen (I := I) U) x v
  constructor
  · have hu' : (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v ≤
        (3 / 2 : ℝ) * (gRef.restrictOpen (I := I) U).inner x v v := by
      nlinarith
    calc
      (2 : ℝ)⁻¹ * (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v =
          (1 / 2 : ℝ) * (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by norm_num
      _ ≤ (1 / 2 : ℝ) * ((3 / 2 : ℝ) *
          (gRef.restrictOpen (I := I) U).inner x v v) :=
        mul_le_mul_of_nonneg_left hu' (by norm_num)
      _ ≤ (gRef.restrictOpen (I := I) U).inner x v v := by nlinarith
  · nlinarith

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem pullbackDiff_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hqp : q ≤ p) (x : U) :
    metricDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
      (gRef.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x ≤ ε := by
  let hB := PartialDiffeomorph.pullbackMetricOn Φ U hU g
  let gU := gRef.restrictOpen (I := I) U
  by_cases hq0 : q = 0
  · subst q
    have hpb : Tensor0SBundle.metricTensorField (I := I) hB x = D.pullback (x : M j) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      let slotsM : Fin 2 → TangentSpace I (x : M j) :=
        fun i => (slots i : E)
      change hB.inner x (slots 0) (slots 1) =
        D.pullback (x : M j) slotsM
      with_unfolding_all
        rw [PartialDiffeomorph.pullbackMetricOn_inner]
      exact (D.pullback_apply (x : M j) (hUK x.2) slotsM).symm
    have href : Tensor0SBundle.metricTensorField (I := I) gU x =
        Tensor0SBundle.metricTensorField (I := I) gRef (x : M j) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      change gU.inner x (slots 0) (slots 1) =
        gRef.inner (x : M j) (slots 0) (slots 1)
      rfl
    unfold metricDerivNorm metricDiffCovDerivAt
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gU x 2
      (Tensor0SBundle.metricTensorField (I := I) hB x -
        Tensor0SBundle.metricTensorField (I := I) gU x)) ≤ ε
    rw [hpb, href, normSq0S_restrictOpen_apply (I := I)]
    exact D.c0_small (x : M j) (hUK x.2)
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hzero : metricCovDeriv (I := I) gU gU q x = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov,
        iterCov_metric_zero]
      exact DFunLike.congr_fun (MultilinearSection.domDomCongr_zero
        (IB := I) (F := E) (n := (∞ : WithTop ℕ∞)) (acEquiv r.succ)) x
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [hzero, sub_zero]
    exact ballPullback_cov_le Φ U hU hUK gRef g D hq1 hqp x

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem limitDiff_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N]
    [IsManifold I ∞ N] [IsManifold I 1 N]
    (gSeq : ℕ → SmoothRiemannianMetric I N)
    (gInf g₀ gRef : SmoothRiemannianMetric I N)
    (hconv : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef)
    {a : ℕ} {x : N} {δ : ℝ}
    (hbound : ∀ k, metricDerivNorm (I := I) a (gSeq k) g₀ gRef x ≤ δ) :
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤ δ := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨k₀, hk₀⟩ := hconv {x} isCompact_singleton a η hη
  have hpoint : metricDerivNorm (I := I) a (gSeq k₀) gInf gRef x < η :=
    lt_of_le_of_lt
      (derivNorm_le_sup (I := I) isCompact_singleton le_rfl
        (gSeq k₀) gInf gRef (Set.mem_singleton x))
      (hk₀ k₀ le_rfl)
  have hsymm : metricDerivNorm (I := I) a gInf (gSeq k₀) gRef x =
      metricDerivNorm (I := I) a (gSeq k₀) gInf gRef x := by
    have hneg : metricDiffCovDerivAt (I := I) a gInf (gSeq k₀) gRef x =
        -metricDiffCovDerivAt (I := I) a (gSeq k₀) gInf gRef x := by
      simp [metricDiffCovDerivAt]
    rw [metricDerivNorm, metricDerivNorm, hneg, normSq0S_neg]
  calc
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤
        metricDerivNorm (I := I) a gInf (gSeq k₀) gRef x +
          metricDerivNorm (I := I) a (gSeq k₀) g₀ gRef x :=
      metricDerivNorm_triangle (I := I) a gInf (gSeq k₀) g₀ gRef x
    _ ≤ δ + η := by rw [hsymm]; linarith [hbound k₀]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem chainLimit_base_le
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ}
    (U : Opens (M j))
    (hUball : (U : Set (M j)) = Metric.ball (b j) ((2 : ℝ) ^ j))
    (hU : ∀ l, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j l).source)
    {δ : ℝ} {p : ℕ}
    (D : ∀ l, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
      (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))
    (ρ : ℕ → ℕ)
    (gInf : SmoothRiemannianMetric I U)
    (hconv :
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      MetricCInfConvOnCompacts (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
        ((g j).restrictOpen (I := I) U))
    {q : ℕ} (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricDerivNorm (I := I) q gInf ((g j).restrictOpen (I := I) U)
      ((g j).restrictOpen (I := I) U) x ≤ δ := by
  let _ := (inferInstance : (∀ (j : ℕ), SigmaCompactSpace (M j)))
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  apply limitDiff_le (I := I)
    (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
    ((g j).restrictOpen (I := I) U) ((g j).restrictOpen (I := I) U) hconv
  intro k
  have hUK : (U : Set (M j)) ⊆ Metric.closedBall (b j) ((2 : ℝ) ^ j) := by
    intro y hy
    rw [hUball] at hy
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
  simpa only [chainPullbackSeq] using
    pullbackDiff_le (I := I)
      (chainComp (I := I) (Mf := M) Ψ j (ρ k)) U (hU (ρ k)) hUK
      (g j) (g (j + ρ k)) (D (ρ k)).forward hqp x

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem diffNorm_change_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A B gInf gBase : SmoothRiemannianMetric I N)
    (p r : ℕ) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gBase.inner x v v ≤ gInf.inner x v v ∧
        gInf.inner x v v ≤ (1 + eps) * gBase.inner x v v)
    (hInf : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      metricDerivNorm (I := I) j gInf gBase gBase x ≤ eps)
    (x : N) (hx : x ∈ u) (hr0 : 0 < r) (hrp : r ≤ p) :
    metricDerivNorm (I := I) r A B gInf x ≤
      Real.sqrt ((1 + eps) ^ (2 + r)) *
        (metricDerivNorm (I := I) r A B gBase x +
          eps * metricCovariantDerivativeComparisonConstant (E := E) 2 p * ∑ k ∈ Finset.range r,
            metricDerivNorm (I := I) k A B gBase x) := by
  classical
  obtain ⟨bBase, hBaseON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) gBase x
  have hBaseInv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gBase x bBase
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) gBase bBase hBaseON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  obtain ⟨bInf, hInfON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) gInf x
  have hInfInv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gInf x bInf
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) gInf bInf hInfON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  have hInfIter : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase y (2 + j)
        (iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y)) ≤ eps := by
    intro y hy j hj1 hjp
    obtain ⟨b, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) gBase y
    have hinv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gBase y b
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I y)))) := by
      have h := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
        (I := I) gBase b hON
      intro i k
      simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i k
    have heq := metricDerivNorm_eq_iterCov (I := I) gInf gBase gBase j b hinv
    have hiter : iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) gInf -
          Tensor0SBundle.metricTensorField (I := I) gBase) j y =
        iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y := by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj1
      rw [show 1 + j' = j' + 1 by omega, iterCov_sub, iterCov_metric_zero, sub_zero]
    rw [hiter] at heq
    rw [← heq]
    exact hInf y hy j hj1 hjp
  let T : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2 :=
    Tensor0SBundle.metricTensorField (I := I) A -
      Tensor0SBundle.metricTensorField (I := I) B
  have hcor := iterated_covariant_derivative_norm_comparison_bound (I := I) hu gInf gBase T
    p eps heps0 heps1 hequiv hInfIter x hx r hr0 hrp
  dsimp only [T] at hcor
  have hleft := metricDerivNorm_eq_iterCov (I := I) A B gInf r bInf hInfInv
  have hright : ∀ k, Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (2 + k)
      (iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) A -
          Tensor0SBundle.metricTensorField (I := I) B) k x)) =
      metricDerivNorm (I := I) k A B gBase x :=
    fun k => (metricDerivNorm_eq_iterCov (I := I) A B gBase k bBase hBaseInv).symm
  rw [← hleft] at hcor
  simp_rw [hright] at hcor
  exact hcor

noncomputable def limitRefFactor (p : ℕ) : ℝ :=
  4 + ∑ r ∈ Finset.range (p + 1),
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ))

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem limitRefFactor_pos (p : ℕ) : 0 < limitRefFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem four_le_refFactor (p : ℕ) : 4 ≤ limitRefFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem refTerm_le_factor (p r : ℕ) (hrp : r ≤ p) :
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) ≤
      limitRefFactor (E := E) p := by
  have hterm : ∀ q : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) := by
    intro q
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hmem : r ∈ Finset.range (p + 1) := by simp only [Finset.mem_range]; omega
  have hsum : Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) ≤
      ∑ q ∈ Finset.range (p + 1), Real.sqrt ((2 : ℝ) ^ (2 + q)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) := by
    exact Finset.single_le_sum (fun q _ => hterm q) hmem
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_refDelta (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2 ∧
      limitRefFactor (E := E) p * δ ≤ ε := by
  let n : ℝ := Module.finrank ℝ E
  let F : ℝ := limitRefFactor (E := E) p
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hn1 : 0 < n + 1 := by linarith
  have hF : 0 < F := by exact limitRefFactor_pos (E := E) p
  let δ : ℝ := min (1 / (4 * (n + 1))) (ε / (2 * F))
  have hleft : 0 < 1 / (4 * (n + 1)) := by positivity
  have hright : 0 < ε / (2 * F) := by positivity
  have hδpos : 0 < δ := by simpa only [δ] using lt_min hleft hright
  have hδleft : δ ≤ 1 / (4 * (n + 1)) := min_le_left _ _
  have hδright : δ ≤ ε / (2 * F) := min_le_right _ _
  refine ⟨δ, hδpos, ?_, ?_, ?_⟩
  · have hden_ge : (4 : ℝ) ≤ 4 * (n + 1) := by nlinarith
    have hinv : 1 / (4 * (n + 1)) ≤ (1 : ℝ) / 4 :=
      one_div_le_one_div_of_le (by norm_num) hden_ge
    nlinarith
  · change n * δ ≤ 1 / 2
    have hmul := mul_le_mul_of_nonneg_left hδleft hn
    have hden : 0 < 4 * (n + 1) := by positivity
    have hfrac : n * (1 / (4 * (n + 1))) ≤ (1 : ℝ) / 4 := by
      calc
        n * (1 / (4 * (n + 1))) = n / (4 * (n + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := (div_le_iff₀ hden).2 (by nlinarith)
    linarith
  · change F * δ ≤ ε
    calc
      F * δ ≤ F * (ε / (2 * F)) := mul_le_mul_of_nonneg_left hδright hF.le
      _ = ε / 2 := by field_simp [ne_of_gt hF]
      _ ≤ ε := by linarith

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem diffNorm_limit_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A gInf gBase : SmoothRiemannianMetric I N)
    (p : ℕ) {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδdim : (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2)
    (hδbudget : limitRefFactor (E := E) p * δ ≤ ε)
    (hA : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q A gBase gBase x ≤ δ)
    (hInf : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q gInf gBase gBase x ≤ δ)
    (x : N) (hx : x ∈ u) (q : ℕ) (hqp : q ≤ p) :
    metricDerivNorm (I := I) q A gInf gInf x ≤ ε := by
  let _ := (inferInstance : (SigmaCompactSpace N))
  classical
  have hBaseNN (y : N) (v : TangentSpace I y) : 0 ≤ gBase.inner y v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (gBase.pos y v hv).le
  have hnorm0 (y : N) (hy : y ∈ u) : (Module.finrank ℝ E : ℝ) *
      metricDerivNorm (I := I) 0 gInf gBase gBase y ≤ 1 / 2 := by
    have hn : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left (hInf y hy 0 (Nat.zero_le p)) hn) hδdim
  have hequiv : ∀ y ∈ u, ∀ v : TangentSpace I y,
      ((2 : ℝ)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v) ∧
        gInf.inner y v v ≤ 2 * gBase.inner y v v := by
    intro y hy v
    have hquad := metricQuadFormDiff_le_metricDerivNorm
      (I := I) gInf gBase gBase y v
    have habs : |gInf.inner y v v - gBase.inner y v v| ≤
        (1 / 2 : ℝ) * gBase.inner y v v :=
      le_trans hquad (mul_le_mul_of_nonneg_right (hnorm0 y hy) (hBaseNN y v))
    rw [abs_le] at habs
    constructor <;> norm_num at habs ⊢ <;> linarith
  have hsymm (a : ℕ) : metricDerivNorm (I := I) a gBase gInf gBase x =
      metricDerivNorm (I := I) a gInf gBase gBase x := by
    have hneg : metricDiffCovDerivAt (I := I) a gBase gInf gBase x =
        -metricDiffCovDerivAt (I := I) a gInf gBase gBase x := by
      simp [metricDiffCovDerivAt]
    rw [metricDerivNorm, metricDerivNorm, hneg, normSq0S_neg]
  have hbase (a : ℕ) (hap : a ≤ p) :
      metricDerivNorm (I := I) a A gInf gBase x ≤ 2 * δ := by
    calc
      metricDerivNorm (I := I) a A gInf gBase x ≤
          metricDerivNorm (I := I) a A gBase gBase x +
            metricDerivNorm (I := I) a gBase gInf gBase x :=
        metricDerivNorm_triangle (I := I) a A gBase gInf gBase x
      _ ≤ δ + δ := by rw [hsymm]; exact add_le_add (hA x hx a hap) (hInf x hx a hap)
      _ = 2 * δ := by ring
  by_cases hq0 : q = 0
  · subst q
    have hzero := diffNorm_zero_change (I := I) A gInf gInf gBase x
      (C := (2 : ℝ)) (by norm_num) (hequiv x hx)
    norm_num at hzero
    calc
      metricDerivNorm (I := I) 0 A gInf gInf x ≤
          2 * metricDerivNorm (I := I) 0 A gInf gBase x := hzero
      _ ≤ 4 * δ := by nlinarith [hbase 0 (Nat.zero_le p)]
      _ ≤ limitRefFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (four_le_refFactor (E := E) p) hδ0
      _ ≤ ε := hδbudget
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hInf1 : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
        metricDerivNorm (I := I) j gInf gBase gBase y ≤ 1 := by
      intro y hy j _ hjp
      exact le_trans (hInf y hy j hjp) hδ1
    have hequiv1 : ∀ y ∈ u, ∀ v : TangentSpace I y,
        ((1 : ℝ) + 1)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v ∧
          gInf.inner y v v ≤ ((1 : ℝ) + 1) * gBase.inner y v v := by
      intro y hy v
      norm_num
      simpa only [one_div] using hequiv y hy v
    have hchange := diffNorm_change_le (I := I) hu A gInf gInf gBase p q 1
      (by norm_num) (by norm_num) hequiv1 hInf1 x hx hqpos hqp
    norm_num at hchange
    have hsum : ∑ k ∈ Finset.range q,
        metricDerivNorm (I := I) k A gInf gBase x ≤ (q : ℝ) * (2 * δ) := by
      calc
        (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
            ∑ _k ∈ Finset.range q, 2 * δ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hbase k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hqp)
        _ = (q : ℝ) * (2 * δ) := by simp
    have hC : 0 ≤ metricCovariantDerivativeComparisonConstant (E := E) 2 p := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    have hinside : metricDerivNorm (I := I) q A gInf gBase x +
          metricCovariantDerivativeComparisonConstant (E := E) 2 p *
            (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) * δ := by
      calc
        _ ≤ 2 * δ + metricCovariantDerivativeComparisonConstant (E := E) 2 p * ((q : ℝ) * (2 * δ)) :=
          add_le_add (hbase q hqp) (mul_le_mul_of_nonneg_left hsum hC)
        _ = _ := by ring
    calc
      metricDerivNorm (I := I) q A gInf gInf x ≤
          Real.sqrt ((2 : ℝ) ^ (2 + q)) *
            (metricDerivNorm (I := I) q A gInf gBase x +
              metricCovariantDerivativeComparisonConstant (E := E) 2 p *
                (∑ k ∈ Finset.range q,
                  metricDerivNorm (I := I) k A gInf gBase x)) := hchange
      _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          ((2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) * δ) :=
        mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg _)
      _ = (Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ))) * δ := by ring
      _ ≤ limitRefFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (refTerm_le_factor (E := E) p q hqp) hδ0
      _ ≤ ε := hδbudget

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem prefixTail_zero_le {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    {K : Set (M l)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (hUK : (Φ : M j → M l) '' (U : Set (M j)) ⊆ K)
    (gMid : SmoothRiemannianMetric I (M l)) (g : SmoothRiemannianMetric I (M m))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Θ : M l → M m) gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (PartialDiffeomorph.pullbackMetricOn (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U
          (PartialDiffeomorph.subset_trans_source Φ Θ U hU hnext) g)
        (PartialDiffeomorph.pullbackMetricOn Φ U hU gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [PartialDiffeomorph.pullbackMetricOn_trans]
  · let W : Opens (M l) :=
      ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
    let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
    let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
      PartialDiffeomorph.toOpensDiffeo Φ hU
    change metricCovDerivNorm (I := I) 0
        (Diffeomorph.pullbackMetric (I := I) (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F)
        (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ _
    rw [metricCovDerivNorm_pullback (I := I)]
    exact ballPullback_zero_le Θ W hnext hUK gMid g D hε (F x)

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem chainPrefix_zero_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    PartialDiffeomorph.subset_trans_source Φ Θ U hpre hnext
  rw [PartialDiffeomorph.pullbackMetricOn_congr A (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (fun x _ => congrFun (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b) x)]
  exact prefixTail_zero_le Φ Θ U hpre hnext hUK gMid g D hε x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chain_image_open
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.ball (b (j + a)) ((2 : ℝ) ^ (j + a)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ a := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < (2 : ℝ) ^ (j + a) := by
    rw [pow_add]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < 2 * (2 : ℝ) ^ j :=
        mul_lt_mul_of_pos_right hsqrt hr
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ a := by
        rw [mul_comm 2]
        exact mul_le_mul_of_nonneg_left hpow hr.le
  have hdata : MapMetricApproximationOn (I := I)
      (Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) (g j) (g (j + a)) := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.forward
  have hsource : Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j a).source := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.source_sub
  have himg := data_image_metric_ball (I := I)
    (chainComp (I := I) (Mf := M) Ψ j a) (hnorm j) (hnorm (j + a))
    hr le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hdata hsource
  intro y hy
  have hyball := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase j a] at hyball
  exact hyball

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [∀ j, SigmaCompactSpace (M j)] in
theorem chain_image_ball
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a)) :=
  (chain_image_open (I := I) b Ψ hbase g hnorm ha D).trans Metric.ball_subset_closedBall

omit [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem tailBall_source
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (j₀ n : ℕ)
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    ∀ k, (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source := by
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  intro k x hx
  apply (D0 k).source_sub
  exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hx).le.trans hpow)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailBall_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ n < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hr hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailClosed_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ) (hj₀ : 1 ≤ j₀)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  let rMid : ℝ := (3 / 2 : ℝ) * (2 : ℝ) ^ n
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hrMid : 0 < rMid := by
    dsimp only [rMid]
    positivity
  have hr_lt : (2 : ℝ) ^ n < rMid := by
    dsimp only [rMid]
    nlinarith
  have hrr₂ : rMid ≤ (2 : ℝ) ^ (j₀ + n) := by
    have hjpow : (2 : ℝ) ≤ (2 : ℝ) ^ j₀ := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj₀
    rw [pow_add]
    dsimp only [rMid]
    nlinarith
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 4 / 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)
    have hs0 := Real.sqrt_nonneg (1 + (1 / 2 : ℝ))
    nlinarith
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * rMid < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    dsimp only [rMid]
    nlinarith
  have hclosed : Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b (j₀ + n)) rMid := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr_lt)
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hrMid hrr₂
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg (Set.image_mono hclosed hy)
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

end ApproxData

end HCGCompactness
end DifferentialGeometry
