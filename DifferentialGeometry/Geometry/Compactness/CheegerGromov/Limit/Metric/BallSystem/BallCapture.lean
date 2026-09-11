import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Tail

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Bundle Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)]
variable [∀ j, Bundle.RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tail_ball_system_exists_compact_eventually_ball_subset_image
    [∀ j, ProperSpace (M j)]
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
    ∀ (A : ℝ),
      let : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
      let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧
        ∀ᶠ m : ℕ in Filter.atTop,
          let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim (M (j₀ + m))
              (∞ : WithTop ℕ∞) :=
            PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
          K ⊆ Φ.source ∧ Metric.ball (b (j₀ + m)) A ⊆ (Φ : _ → _) '' K := by
  intro A
  let : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tail_ball_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  have hevPow : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1) < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually
      (Filter.eventually_gt_atTop (2 * (Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1)))
  obtain ⟨n, hn⟩ := hevPow.exists
  have hmargin : Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1 < coreRadius n := by
    dsimp only [coreRadius]
    nlinarith
  refine ⟨limitCore b j₀ S n, ?_, ?_⟩
  · exact (tail_core_compact b j₀ n).image (S.toSeqSystem.continuous_incl n)
  · filter_upwards [Filter.eventually_ge_atTop n] with m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    dsimp only
    constructor
    · change limitCore b j₀ S n ⊆ Set.range (S.toSeqSystem.incl (n + k))
      rintro q ⟨x, hx, rfl⟩
      exact ⟨S.toSeqSystem.map (Nat.le_add_right n k) x,
        S.toSeqSystem.incl_comp (Nat.le_add_right n k) x⟩
    · have hRle : coreRadius n ≤ (2 : ℝ) ^ (j₀ + n) := by
        rw [pow_add]
        have hn0 : 0 ≤ (2 : ℝ) ^ n := by positivity
        have hj1 : 1 ≤ (2 : ℝ) ^ j₀ := one_le_pow₀ (by norm_num)
        dsimp only [coreRadius]
        nlinarith
      let Dcore := (D₀ n k).mono
        (Metric.closedBall_subset_closedBall hRle) (le_refl (1 / 2 : ℝ)) (by norm_num)
      have hball := PartialDiffeomorphMetricApproximation.ball_subset_image_closedBall (I := I)
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
        (hnorm (j₀ + n)) (hnorm ((j₀ + n) + k)) (isCompact_closedBall _ _)
        (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) hmargin Dcore
      have hball' : Metric.ball (b ((j₀ + n) + k)) A ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
            M (j₀ + n) → M ((j₀ + n) + k)) ''
              Metric.closedBall (b (j₀ + n)) (coreRadius n) := by
        change Metric.ball
            ((chainComp (I := I) (Mf := M) Ψ (j₀ + n) k) (b (j₀ + n))) A ⊆ _
          at hball
        rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) k] at hball
        exact hball
      intro y hy
      let e : M (j₀ + (n + k)) = M ((j₀ + n) + k) :=
        congrArg M (Nat.add_assoc j₀ n k).symm
      let y' : M ((j₀ + n) + k) := cast e y
      have hyball : y' ∈ Metric.ball (b ((j₀ + n) + k)) A := by
        have cast_ball : ∀ {a c : ℕ} (h : a = c) {z : M a},
            z ∈ Metric.ball (b a) A →
              cast (congrArg M h) z ∈ Metric.ball (b c) A := by
          intro a c h z hz
          cases h
          exact hz
        exact cast_ball (Nat.add_assoc j₀ n k).symm hy
      obtain ⟨z, hz, hzy⟩ := hball' hyball
      let x : tailBallOpen b j₀ n := ⟨z, core_subset_tail b j₀ n hz⟩
      have hx : x ∈ tailCore b j₀ n := by
        simpa only [x, tailCore, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm] using hz
      refine ⟨S.toSeqSystem.incl n x, ⟨x, hx, rfl⟩, ?_⟩
      have hmember := tail_ball_system_invIncl_incl (I := I) b Ψ hbase g hnorm j₀ D₀ n k x
      have hcast : cast e
          ((PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl :
            S.toSeqSystem.Lim → M (j₀ + (n + k))) (S.toSeqSystem.incl n x)) =
          cast e y := by
        calc
          cast e
              ((PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl :
                S.toSeqSystem.Lim → M (j₀ + (n + k))) (S.toSeqSystem.incl n x)) =
              (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
                M (j₀ + n) → M ((j₀ + n) + k)) x := by
            exact hmember
          _ = y' := hzy
          _ = cast e y := rfl
      exact (Equiv.cast e).injective hcast

end DifferentialGeometry.CheegerGromovCompactness
