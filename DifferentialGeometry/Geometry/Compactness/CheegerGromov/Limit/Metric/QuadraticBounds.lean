import DifferentialGeometry.Geometry.Metric.DirectLimit.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)]

theorem eventually_quadratic_bounds_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 0
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    ∀ K : Set S.toSeqSystem.Lim, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop,
        let Φ := PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
        K ⊆ Φ.source ∧ ∀ z ∈ K, ∀ v : TangentSpace I z,
          (1 - ε) * (S.limitMetric gInf hg).inner z v v ≤
            (g (φ k)).inner (Φ z) (mfderiv I I Φ z v) (mfderiv I I Φ z v) ∧
          (g (φ k)).inner (Φ z) (mfderiv I I Φ z v) (mfderiv I I Φ z v) ≤
            (1 + ε) * (S.limitMetric gInf hg).inner z v v := by
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
  dsimp only
  intro K hK ε hε
  let Φ : ∀ m, PartialDiffeomorph I I S.toSeqSystem.Lim (M m) ∞ :=
    fun m => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
  apply S.eventually_quadratic_bounds_of_pullback_convergence gInf hg
    (fun k => g (φ k)) (fun k => Φ (φ k)) ?_
    (fun j k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) gRef hconv ?_ hK hε
  · intro j
    filter_upwards [eventually_ge_atTop j] with k hk
    exact S.toSeqSystem.range_incl_mono (hk.trans (hφ.id_le k))
  · intro j
    filter_upwards [eventually_ge_atTop j] with k hk
    have hj : j ≤ φ k := hk.trans (hφ.id_le k)
    have hgeneral (l : ℕ) (a : U j) (v : TangentSpace I a) :
        (chainPullbackSeq Ψ g (U j) (hU j) l).inner a v v =
          (g (j + l)).inner (Φ (j + l) (S.toSeqSystem.incl j a))
            (mfderiv I I ((Φ (j + l) : S.toSeqSystem.Lim → M (j + l)) ∘
              S.toSeqSystem.incl j) a v)
            (mfderiv I I ((Φ (j + l) : S.toSeqSystem.Lim → M (j + l)) ∘
              S.toSeqSystem.incl j) a v) := by
      have hfun : (Φ (j + l) : S.toSeqSystem.Lim → M (j + l)) ∘ S.toSeqSystem.incl j =
          fun x : U j => chainComp Ψ j l (x : M j) := by
        funext x
        exact SmoothSeqSystem.ofPartialDiffeomorphs_invIncl_incl U Ψ hUstep hmap j l x
      have hpoint : Φ (j + l) (S.toSeqSystem.incl j a) = chainComp Ψ j l (a : M j) :=
        congrFun hfun a
      rw [hfun, hpoint, chainPullbackSeq, PartialDiffeomorph.pullbackMetricOn_inner]
      have hdiff := (chainComp Ψ j l).mdifferentiableAt (by simp) (hU j l a.2)
      have hval := (contMDiff_subtype_val (I := I) (U := U j) (n := ∞)).mdifferentiableAt
        (by simp) (x := a)
      have hcomp := mfderiv_comp_apply a hdiff hval v
      rw [mfderiv_subtype_val_apply] at hcomp
      change mfderiv I I (fun x : U j => chainComp Ψ j l (x : M j)) a v = _ at hcomp
      rw [hcomp]
    intro a v
    generalize φ k = m at hj ⊢
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hj
    simpa only [Nat.add_sub_cancel_left] using hgeneral l a v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_enorm_mfderiv_le_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    [Bundle.RiemannianBundle (fun z :
      (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).toSeqSystem.Lim => TangentSpace I z)]
    [∀ j, Bundle.RiemannianBundle (fun z : M j => TangentSpace I z)]
    (hGNorm : Geometry.Riemannian.IsMetricNorm
      ((SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).limitMetric gInf hg))
    (hgNorm : ∀ j, Geometry.Riemannian.IsMetricNorm (g j))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 0
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    ∀ K : Set S.toSeqSystem.Lim, IsCompact K → ∀ L : ℝ, 1 < L →
      ∀ᶠ k in atTop,
        let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
          PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
        K ⊆ Φ.source ∧ (∀ z ∈ K, ContMDiffAt I I 1 Φ z) ∧
          ∀ z ∈ K, ∀ v : TangentSpace I z,
            ‖mfderiv I I (Φ : S.toSeqSystem.Lim → M (φ k)) z v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ := by
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
  dsimp only
  intro K hK L hL
  have hL0 : 0 ≤ L := by linarith
  have hε : 0 < L ^ 2 - 1 := by nlinarith
  filter_upwards [eventually_quadratic_bounds_of_chain_pullback_convergence
    U Ψ hUstep hmap hU g gInf gRef hg φ hφ hconv K hK (L ^ 2 - 1) hε] with k hk
  let Φ := PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
  refine ⟨hk.1, ?_, ?_⟩
  · intro z hz
    exact ((Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hk.1 hz))).of_le (by simp))
  · intro z hz v
    rw [hgNorm, hGNorm, ← ENNReal.ofReal_mul hL0]
    apply ENNReal.ofReal_le_ofReal
    have hupper := (hk.2 z hz v).2
    have heq : 1 + (L ^ 2 - 1) = L ^ 2 := by ring
    rw [heq] at hupper
    calc
      _ ≤ Real.sqrt (L ^ 2 * (S.limitMetric gInf hg).inner z v v) :=
        Real.sqrt_le_sqrt hupper
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0]

end DifferentialGeometry.CheegerGromovCompactness
