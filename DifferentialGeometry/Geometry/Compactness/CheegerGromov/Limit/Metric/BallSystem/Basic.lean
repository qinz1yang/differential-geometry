import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.DirectLimit.Defs
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import DifferentialGeometry.Topology.SigmaCompactOpen
import Mathlib.Geometry.Manifold.Riemannian.PathELength
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
theorem ball_open_nonempty (b : ∀ j, M j) (r : ℕ → ℝ) (j : ℕ) (hr : 0 < r j) :
    Nonempty (ballOpen b r j) := by
  refine ⟨⟨b j, ?_⟩⟩
  exact Metric.mem_ball_self hr

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem tail_ball_nonempty (b : ∀ j, M j) (j₀ n : ℕ) :
    Nonempty (tailBallOpen b j₀ n) :=
  ⟨⟨b (j₀ + n), Metric.mem_ball_self (by positivity)⟩⟩

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem tail_ball_le_large (b : ∀ j, M j) (j₀ n : ℕ) :
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
  exact (gInf n).restrictOpenOfSubset (I := I) (tail_ball_le_large b j₀ n)

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
theorem tail_core_compact (b : ∀ j, M j) (j₀ n : ℕ)
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
theorem limit_core_closed (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    IsClosed (limitCore b j₀ S n) := by
  exact ((tail_core_compact b j₀ n).image
    (S.toSeqSystem.continuous_incl n)).isClosed

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in
theorem incl_mem_core_interior (b : ∀ j, M j) (j₀ n : ℕ)
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
theorem center_mem_core_interior (b : ∀ j, M j) (j₀ n : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    S.toSeqSystem.incl n (tailCenter b j₀ n) ∈ interior (limitCore b j₀ S n) := by
  apply incl_mem_core_interior b j₀ n S
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
  have hclosed := limit_core_closed b j₀ n S
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
  have hint := incl_mem_core_interior b j₀ n S hlt
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
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ball_open_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ball_open_nonempty b r j (hr j)
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
private theorem pullback_metric_on_cast {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (g : ∀ n, SmoothRiemannianMetric I (M n))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hU' : (U : Set (M j)) ⊆ (h ▸ Φ).source) :
    PartialDiffeomorph.pullbackMetricOn (h ▸ Φ) U hU' (g m) = PartialDiffeomorph.pullbackMetricOn Φ U hU (g l) := by
  subst h
  rfl

omit [CompleteSpace E] [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chain_pullback_assoc
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
    pullback_metric_on_cast (I := I) (M := M) (Nat.add_assoc j a b).symm
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
theorem chain_pullback_zero
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
theorem chain_pullback_step
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
  have hassoc := chain_pullback_assoc (I := I) Ψ g U hA (hU (1 + b))
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
theorem chain_metric_cocycle
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
    PointedRiemannianConvergenceMaps (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf) id where
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
theorem tail_ball_preconnected (b : ∀ j, M j) (j₀ n : ℕ) :
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

end ApproxData

end HCGCompactness
end DifferentialGeometry
