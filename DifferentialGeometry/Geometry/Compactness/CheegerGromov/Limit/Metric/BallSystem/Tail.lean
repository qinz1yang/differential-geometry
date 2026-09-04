import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Images
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

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
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def tailBallSystem
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
    SmoothSeqSystem I (fun n => tailBallOpen b j₀ n) := by
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let hU := fun n => tail_ball_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    intro y hy
    change y ∈ Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1))
    exact tail_ball_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1) hy
  exact chainBallSystem (I := I) j₀ (tailBallOpen b j₀) Ψ hU hmap

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_ball_system_map_center_succ
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.le_succ n) (tailCenter b j₀ n) = tailCenter b j₀ (n + 1) := by
  let _ : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
  let hU := fun m => tail_ball_source (I := I) b Ψ g j₀ m (D₀ m)
  let hmap : ∀ m,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + m) 1 :
        M (j₀ + m) → M (j₀ + (m + 1))) ''
          (tailBallOpen b j₀ m : Set (M (j₀ + m))) ⊆
        (tailBallOpen b j₀ (m + 1) : Set (M (j₀ + (m + 1)))) := fun m => by
    intro y hy
    change y ∈ Metric.ball (b ((j₀ + m) + 1)) ((2 : ℝ) ^ (m + 1))
    exact tail_ball_image (I := I) b Ψ hbase g hnorm j₀ m (D₀ m 1) hy
  have hF :
      (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
          (Nat.le_succ n) =
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n) := by
    unfold tailBallSystem
    apply SmoothSeqSystem.ofSucc_F_succ
  rw [hF]
  apply Subtype.ext
  change (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
    M (j₀ + n) → M ((j₀ + n) + 1)) (b (j₀ + n)) = b (j₀ + (n + 1))
  exact chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_ball_system_map_center
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.zero_le n) (tailCenter b j₀ 0) = tailCenter b j₀ n := by
  let _ : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  induction n with
  | zero =>
      exact S.toSeqSystem.map_self 0 (tailCenter b j₀ 0)
  | succ n ih =>
      calc
        S.toSeqSystem.F (Nat.zero_le (n + 1)) (tailCenter b j₀ 0) =
            S.toSeqSystem.F ((Nat.zero_le n).trans (Nat.le_succ n))
              (tailCenter b j₀ 0) :=
          S.toSeqSystem.F_apply_irrel _ _ _
        _ = S.toSeqSystem.F (Nat.le_succ n)
              (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0)) :=
          (S.toSeqSystem.map_map (Nat.zero_le n) (Nat.le_succ n)
            (tailCenter b j₀ 0)).symm
        _ = S.toSeqSystem.F (Nat.le_succ n) (tailCenter b j₀ n) := by rw [ih]
        _ = tailCenter b j₀ (n + 1) :=
          tail_ball_system_map_center_succ (I := I) b Ψ hbase g hnorm j₀ D₀ n

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_ball_system_incl_center
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    S.toSeqSystem.incl n (tailCenter b j₀ n) =
      S.toSeqSystem.incl 0 (tailCenter b j₀ 0) := by
  let _ : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        S.toSeqSystem.incl (n + 1) (tailCenter b j₀ (n + 1)) =
            S.toSeqSystem.incl (n + 1)
              (S.toSeqSystem.F (Nat.le_succ n) (tailCenter b j₀ n)) := by
          rw [tail_ball_system_map_center_succ (I := I) b Ψ hbase g hnorm j₀ D₀ n]
        _ = S.toSeqSystem.incl n (tailCenter b j₀ n) :=
          S.toSeqSystem.incl_comp (Nat.le_succ n) (tailCenter b j₀ n)
        _ = S.toSeqSystem.incl 0 (tailCenter b j₀ 0) := ih

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_ball_system_step_range_compact
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
    ∀ n, ∃ K : Set (tailBallOpen b j₀ (n + 1)), IsCompact K ∧
      Set.range ((tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.le_succ n)) ⊆ K := by
  classical
  let _ : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let hU := fun n => tail_ball_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    intro y hy
    change y ∈ Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1))
    exact tail_ball_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1) hy
  intro n
  let Φ := chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1
  let C : Set (M (j₀ + n)) := Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n)
  let K : Set (tailBallOpen b j₀ (n + 1)) := Subtype.val ⁻¹' ((Φ : M (j₀ + n) → _) '' C)
  refine ⟨K, ?_, ?_⟩
  · have hC : IsCompact C := isCompact_closedBall _ _
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hCsrc : C ⊆ Φ.source := by
      intro x hx
      apply (D₀ n 1).source_sub
      exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hx).trans hpow)
    have hΦc : ContinuousOn (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) C :=
      Φ.contMDiffOn_toFun.continuousOn.mono hCsrc
    have hImage : IsCompact ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) :=
      hC.image_of_continuousOn hΦc
    have hImageSub : ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := by
      intro y hy
      change y ∈ Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1))
      exact tail_closed_ball_image (I := I) b Ψ hbase g hnorm j₀ n hj₀ (D₀ n 1) hy
    dsimp only [K]
    rw [Subtype.isCompact_iff]
    have hval : Subtype.val ''
          (Subtype.val ⁻¹' ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) :
            Set (tailBallOpen b j₀ (n + 1))) =
        (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y, hImageSub hy⟩, hy, rfl⟩
    rw [hval]
    exact hImage
  · have hF :
        (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
            (Nat.le_succ n) =
          PartialDiffeomorph.opensMap Φ (hmap n) := by
      unfold tailBallSystem
      apply SmoothSeqSystem.ofSucc_F_succ
    rw [hF]
    rintro _ ⟨x, rfl⟩
    change ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) x ∈
      (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C)
    exact ⟨x, Metric.mem_closedBall.mpr (Metric.mem_ball.mp x.property).le, rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_ball_system_metric_cocycle
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).MetricCocycle
      (tailMetric (I := I) b j₀ gInf) := by
  classical
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let V : ∀ n, Opens (M (j₀ + n)) := tailBallOpen b j₀
  let _ : ∀ n, Nonempty (V n) := fun n => tail_ball_nonempty b j₀ n
  let _ : ∀ n, SigmaCompactSpace (V n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (V n).isOpen)
  let hV := fun n => tail_ball_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmapV : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (V n : Set (M (j₀ + n))) ⊆
          (V (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    intro y hy
    change y ∈ Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1))
    exact tail_ball_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1) hy
  let gTail : ∀ n, SmoothRiemannianMetric I (V n) :=
    tailMetric (I := I) b j₀ gInf
  have hstepV : ∀ n,
      let F : V n → V (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmapV n)
      ∀ (x : V n) (v w : TangentSpace I x),
        (gTail n).inner x v w =
          (gTail (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w) := by
    intro n
    dsimp only
    let Fbig : U n → U (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
    let Fsmall : V n → V (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmapV n)
    let inc : V n → U n := Opens.inclusion (tail_ball_le_large b j₀ n)
    let incNext : V (n + 1) → U (n + 1) :=
      Opens.inclusion (tail_ball_le_large b j₀ (n + 1))
    intro x v w
    let vBig : TangentSpace I (inc x) := (v : E)
    let wBig : TangentSpace I (inc x) := (w : E)
    have hbig := hstep n (inc x) vBig wBig
    have hpoint : Fbig (inc x) = incNext (Fsmall x) := by
      apply Subtype.ext
      rfl
    have hderiv (u : TangentSpace I x) :
        mfderiv I I Fbig (inc x) (u : E) = mfderiv I I Fsmall x u := by
      have hbigDeriv :
          (mfderiv I I Fbig (inc x) (u : E) : E) =
            (mfderiv I I
              (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
                M (j₀ + n) → M ((j₀ + n) + 1))
              (inc x : M (j₀ + n)) (u : E) : E) :=
        PartialDiffeomorph.opensMap_mfderiv
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
          (hU n 1) (hmap n) (inc x) (u : E)
      have hsmallDeriv :
          (mfderiv I I Fsmall x u : E) =
            (mfderiv I I
              (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
                M (j₀ + n) → M ((j₀ + n) + 1))
              (x : M (j₀ + n)) u : E) :=
        PartialDiffeomorph.opensMap_mfderiv
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
          (hV n 1) (hmapV n) x u
      exact hbigDeriv.trans hsmallDeriv.symm
    change (gInf n).inner (inc x) vBig wBig =
      (gInf (n + 1)).inner (incNext (Fsmall x))
        (mfderiv I I Fsmall x v) (mfderiv I I Fsmall x w)
    rw [← hpoint, ← hderiv v, ← hderiv w]
    exact hbig
  change (chainBallSystem (I := I) j₀ V Ψ hV hmapV).MetricCocycle gTail
  exact chain_metric_cocycle (I := I) j₀ V Ψ hV hmapV gTail hstepV

end ApproxData

end HCGCompactness
end DifferentialGeometry
