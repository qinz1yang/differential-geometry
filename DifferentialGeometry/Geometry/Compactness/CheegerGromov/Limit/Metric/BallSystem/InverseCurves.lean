import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.InverseCurves
import DifferentialGeometry.Topology.DirectLimit.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n, IsManifold I ∞ (M n)]

variable (U : ∀ n, Opens (M n)) [∀ n, Nonempty (U n)]
  (Ψ : ∀ n, PartialDiffeomorph I I (M n) (M (n + 1)) (∞ : WithTop ℕ∞))
  (hU : ∀ n, (U n : Set (M n)) ⊆ (Ψ n).source)
  (hmap : ∀ n, (Ψ n : M n → M (n + 1)) '' (U n : Set (M n)) ⊆
    (U (n + 1) : Set (M (n + 1))))

private theorem liftTargetOpen_symm_apply_of_incl
    (S : SmoothSeqSystem I (fun n => U n)) (n : ℕ) (x : U n) :
    (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).symm
        (x : M n) = S.toSeqSystem.incl n x := by
  change S.toSeqSystem.incl n
      (Function.invFun (Subtype.val : U n → M n) (x : M n)) = _
  rw [Function.leftInverse_invFun (U n).isOpenEmbedding'.injective x]

private theorem liftTargetOpen_symm_chainComp
    (n k : ℕ) (x : U n) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hU hmap
    (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl).symm
        ((chainComp Ψ n k : M n → M (n + k)) x) =
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).symm
        (x : M n) := by
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hU hmap
  have hsymm : ∀ (j : ℕ) (q : U j),
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo j) rfl).symm
          (q : M j) = S.toSeqSystem.incl j q := by
    intro j q
    exact liftTargetOpen_symm_apply_of_incl U S j q
  let y : U (n + k) := S.toSeqSystem.map (Nat.le_add_right n k) x
  have hy : (y : M (n + k)) = chainComp Ψ n k x :=
    SmoothSeqSystem.ofPartialDiffeomorphs_map_apply U Ψ hU hmap n k x
  calc
    (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl).symm
        (chainComp Ψ n k x) =
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl).symm
        (y : M (n + k)) := congrArg _ hy.symm
    _ = S.toSeqSystem.incl (n + k) y := hsymm (n + k) y
    _ = S.toSeqSystem.incl n x := S.toSeqSystem.incl_comp (Nat.le_add_right n k) x
    _ = (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).symm
        (x : M n) := (hsymm n x).symm

private theorem liftTargetOpen_symm_chainComp_of_image
    (n k : ℕ) {C : Set (M n)} (hC : C ⊆ (U n : Set (M n)))
    (hCsource : C ⊆ (chainComp Ψ n k).source)
    {y : M (n + k)}
    (hy : y ∈ (chainComp Ψ n k : M n → M (n + k)) '' C) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hU hmap
    (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl).symm y =
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).symm
        ((chainComp Ψ n k).symm y) := by
  rcases hy with ⟨x, hxC, rfl⟩
  have hright :
      (chainComp Ψ n k).symm ((chainComp Ψ n k : M n → M (n + k)) x) = x :=
    (chainComp Ψ n k).left_inv' (hCsource hxC)
  rw [hright]
  exact liftTargetOpen_symm_chainComp U Ψ hU hmap n k ⟨x, hC hxC⟩

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set TopologicalSpace Filter Bundle
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u}
  [∀ n, MetricSpace (M n)]
  [∀ n, ChartedSpace H (M n)] [∀ n, IsManifold I ∞ (M n)]
  [∀ n, Bundle.RiemannianBundle (fun x : M n => TangentSpace I x)]
  [∀ n, IsRiemannianManifold I (M n)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_uniform_inverse_curve_bound_of_chain_metric_approximation
    (U : ∀ n, Opens (M n)) [∀ n, Nonempty (U n)]
    (Ψ : ∀ n, PartialDiffeomorph I I (M n) (M (n + 1)) ∞)
    (hU : ∀ n, (U n : Set (M n)) ⊆ (Ψ n).source)
    (hmap : ∀ n, (Ψ n : M n → M (n + 1)) '' (U n : Set (M n)) ⊆
      (U (n + 1) : Set (M (n + 1))))
    (base : ∀ n, M n)
    (hbase : ∀ n, Ψ n (base n) = base (n + 1))
    (g : ∀ n, SmoothRiemannianMetric I (M n))
    (hnorm : ∀ n, Geometry.Riemannian.IsMetricNorm (g n))
    (n : ℕ) {R A ε : ℝ}
    (hcompact : IsCompact (Metric.closedBall (base n) R))
    (hball : Metric.closedBall (base n) R ⊆ (U n : Set (M n)))
    (hmargin : Real.sqrt (1 + ε) * A < R)
    (D : ∀ k, Nonempty (PartialDiffeomorphMetricApproximation
      (Metric.closedBall (base n) R) ε 0 (chainComp Ψ n k) (g n) (g (n + k))))
    (gamma : ∀ k, ℝ → M (n + k)) {a b : ℝ} {C : ℝ≥0}
    (hgamma : ∀ k, LipschitzOnWith C (gamma k) (Icc a b))
    (hmem : ∀ k, MapsTo (gamma k) (Icc a b) (Metric.ball (base (n + k)) A)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hU hmap
    ∀ G : SmoothRiemannianMetric I S.toSeqSystem.Lim,
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∃ L : ℝ≥0, ∀ k,
        let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim (M (n + k)) ∞ :=
          PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl
        K ⊆ Φ.source ∧
        MapsTo ((Φ.symm : M (n + k) → S.toSeqSystem.Lim) ∘ gamma k) (Icc a b) K ∧
          (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
            riemannianEDistOf G (Φ.symm (gamma k s)) (Φ.symm (gamma k t)) ≤
              (L : ℝ≥0∞) * edist s t) ∧
          ∀ s ∈ Icc a b, Φ (Φ.symm (gamma k s)) = gamma k s := by
  intro S G
  have : T2Space S.toSeqSystem.Lim := S.toSeqSystem.instT2SpaceLim
  let : LocallyCompactSpace S.toSeqSystem.Lim := Manifold.locallyCompact_of_finiteDimensional I
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace S.toSeqSystem.Lim := .ofRiemannianMetric I S.toSeqSystem.Lim
  have : IsRiemannianManifold I S.toSeqSystem.Lim := ⟨fun _ _ => rfl⟩
  let : IsContinuousRiemannianBundle E (fun x : M n => TangentSpace I x) :=
    (hnorm n).isContinuousRiemannianBundle
  let ι : PartialDiffeomorph I I (M n) S.toSeqSystem.Lim ∞ :=
    (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).symm
  have hsource : Metric.closedBall (base n) R ⊆ ι.source := hball
  have hlocal : ∀ x ∈ Metric.closedBall (base n) R,
      ∃ B : ℝ≥0, ∃ V ∈ 𝓝 x, LipschitzOnWith B (ι : M n → S.toSeqSystem.Lim) V := by
    intro x hx
    have hsm : ContMDiffAt I I 1 (ι : M n → S.toSeqSystem.Lim) x :=
      (ι.contMDiffOn_toFun.contMDiffAt (ι.open_source.mem_nhds (hsource hx))).of_le (by decide)
    exact hsm.exists_lipschitzOnWith
  obtain ⟨B, hB⟩ := Topology.IsCompact.exists_uniform_lipschitzOnWith_nhds hcompact hlocal
  let K := (ι : M n → S.toSeqSystem.Lim) '' Metric.closedBall (base n) R
  have hK : IsCompact K := hcompact.image_of_continuousOn
    (ι.contMDiffOn_toFun.continuousOn.mono hsource)
  let r := (R - Real.sqrt (1 + ε) * A) / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  have hmargin' : Real.sqrt (1 + ε) * A + r < R := by dsimp only [r]; linarith
  refine ⟨K, hK, B * (⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩ * C), ?_⟩
  intro k Φ
  obtain ⟨Dk⟩ := D k
  have hmem' : MapsTo (gamma k) (Icc a b) (Metric.ball (chainComp Ψ n k (base n)) A) := by
    simpa only [chainComp_base Ψ base hbase] using hmem k
  obtain ⟨hlip, htrap, hforward⟩ := Dk.lipschitzOnWith_symm_comp_of_mapsTo_ball
    (chainComp Ψ n k) (hnorm n) (hnorm (n + k)) hcompact
    (Metric.mem_ball_self hr) hmargin' (hgamma k) hmem'
  have htransport : ∀ s ∈ Icc a b,
      Φ.symm (gamma k s) = ι ((chainComp Ψ n k).symm (gamma k s)) := by
    intro s hs
    exact liftTargetOpen_symm_chainComp_of_image U Ψ hU hmap n k hball Dk.source_sub
      ⟨_, htrap hs, hforward s hs⟩
  have hL := Topology.lipschitzOnWith_comp_of_locally_lipschitzOn
    (f := (ι : M n → S.toSeqSystem.Lim)) hlip (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := hx
      exact hB _ (htrap hs))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z ⟨x, _, rfl⟩
    change S.toSeqSystem.incl n (Function.invFun (Subtype.val : U n → M n) x) ∈
      Set.range (S.toSeqSystem.incl (n + k))
    exact ⟨S.toSeqSystem.map (Nat.le_add_right n k) _,
      S.toSeqSystem.incl_comp (Nat.le_add_right n k) _⟩
  · intro s hs
    rw [Function.comp_apply, htransport s hs]
    exact ⟨_, htrap hs, rfl⟩
  · intro s hs t ht
    rw [htransport s hs, htransport t ht]
    have hdist : ∀ x y : S.toSeqSystem.Lim, riemannianEDistOf G x y = edist x y := by
      intro x y
      rfl
    rw [hdist]
    exact hL hs ht
  · intro s hs
    have hy : gamma k s ∈ Φ.target := by
      have hincl := SmoothSeqSystem.ofPartialDiffeomorphs_map_apply U Ψ hU hmap n k
        ⟨(chainComp Ψ n k).symm (gamma k s), hball (htrap hs)⟩
      rw [hforward s hs] at hincl
      exact hincl ▸ (S.toSeqSystem.map (Nat.le_add_right n k)
        ⟨(chainComp Ψ n k).symm (gamma k s), hball (htrap hs)⟩).property
    exact Φ.right_inv' hy

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set TopologicalSpace Filter Bundle
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u}
  [∀ n, MetricSpace (M n)]
  [∀ n, ChartedSpace H (M n)] [∀ n, IsManifold I ∞ (M n)]
  [∀ n, Bundle.RiemannianBundle (fun x : M n => TangentSpace I x)]
  [∀ n, IsRiemannianManifold I (M n)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_eventually_inverse_curve_bound_of_eventual_metric_approximations
    (U : ∀ n, Opens (M n)) [∀ n, Nonempty (U n)]
    (Ψ : ∀ n, PartialDiffeomorph I I (M n) (M (n + 1)) ∞)
    (hU : ∀ n, (U n : Set (M n)) ⊆ (Ψ n).source)
    (hmap : ∀ n, (Ψ n : M n → M (n + 1)) '' (U n : Set (M n)) ⊆
      (U (n + 1) : Set (M (n + 1))))
    (base : ∀ n, M n)
    (hbase : ∀ n, Ψ n (base n) = base (n + 1))
    (g : ∀ n, SmoothRiemannianMetric I (M n))
    (hnorm : ∀ n, Geometry.Riemannian.IsMetricNorm (g n))
    (r : ℕ → ℝ) {ell : ℝ} (hr : Tendsto r atTop (𝓝 ell))
    (hcompact : ∀ᶠ n in atTop, IsCompact (Metric.closedBall (base n) (r n)))
    (hball : ∀ᶠ n in atTop, Metric.ball (base n) (r n) ⊆ (U n : Set (M n)))
    (hdata : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ J : ℕ, ∀ n, J ≤ n → ∀ k,
      Nonempty (PartialDiffeomorphMetricApproximation
        (Metric.closedBall (base n) (r n)) ε 0 (chainComp Ψ n k) (g n) (g (n + k))))
    (gamma : ∀ n, ℝ → M n) {a b A : ℝ} {C : ℝ≥0}
    (hAL : A < ell)
    (hgamma : ∀ᶠ n in atTop, LipschitzOnWith C (gamma n) (Icc a b))
    (hmem : ∀ᶠ n in atTop, MapsTo (gamma n) (Icc a b) (Metric.ball (base n) A)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hU hmap
    ∀ G : SmoothRiemannianMetric I S.toSeqSystem.Lim,
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∃ L : ℝ≥0, ∀ᶠ m in atTop,
        let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim (M m) ∞ :=
          PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
        K ⊆ Φ.source ∧
        MapsTo ((Φ.symm : M m → S.toSeqSystem.Lim) ∘ gamma m) (Icc a b) K ∧
          (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
            riemannianEDistOf G (Φ.symm (gamma m s)) (Φ.symm (gamma m t)) ≤
              (L : ℝ≥0∞) * edist s t) ∧
          ∀ s ∈ Icc a b, Φ (Φ.symm (gamma m s)) = gamma m s := by
  intro S G
  by_cases hA0 : 0 ≤ A
  swap
  · refine ⟨∅, isCompact_empty, 0, hmem.mono fun m hm => ?_⟩
    have hfalse : ∀ s ∈ Icc a b, False := by
      intro s hs
      have h := hm hs
      rw [Metric.ball_eq_empty.mpr (lt_of_not_ge hA0).le] at h
      exact h
    exact ⟨empty_subset _, fun s hs => (hfalse s hs).elim,
      fun s hs => (hfalse s hs).elim, fun s hs => (hfalse s hs).elim⟩
  let T := (A + ell) / 2
  have hAT : A < T := by dsimp [T]; linarith
  have hTL : T < ell := by dsimp [T]; linarith
  let ε := min (1 / 2 : ℝ) ((T - A) / (2 * (A + 1)))
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (sub_pos.mpr hAT) (by positivity))
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεgap : ε * (2 * (A + 1)) ≤ T - A :=
    (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp (min_le_right _ _)
  have hsqrt : Real.sqrt (1 + ε) ≤ 1 + ε := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg ε]⟩
  have hεA : ε * A < T - A := by nlinarith
  have hsqrtA : Real.sqrt (1 + ε) * A < T := by
    have h := mul_le_mul_of_nonneg_right hsqrt hA0
    nlinarith
  obtain ⟨J, hJ⟩ := hdata ε hε0 hε1
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hgamma.and hmem))
  obtain ⟨n, ⟨⟨⟨⟨hnJ, hnN⟩, hnr⟩, hncompact⟩, hnball⟩⟩ :=
    (((((eventually_ge_atTop J).and (eventually_ge_atTop N)).and
      (hr.eventually (eventually_gt_nhds hTL))).and hcompact).and hball).exists
  let R := (T + r n) / 2
  have hTR : T < R := by dsimp [R]; linarith
  have hRr : R < r n := by dsimp [R]; linarith
  have D : ∀ k, Nonempty (PartialDiffeomorphMetricApproximation
      (Metric.closedBall (base n) R) ε 0 (chainComp Ψ n k) (g n) (g (n + k))) := by
    intro k
    obtain ⟨D⟩ := hJ n hnJ k
    exact ⟨D.mono (Metric.closedBall_subset_closedBall hRr.le) le_rfl hε1⟩
  obtain ⟨K, hK, L, hL⟩ :=
    exists_compact_uniform_inverse_curve_bound_of_chain_metric_approximation
      U Ψ hU hmap base hbase g hnorm n
      (hncompact.of_isClosed_subset Metric.isClosed_closedBall
        (Metric.closedBall_subset_closedBall hRr.le))
      ((Metric.closedBall_subset_ball hRr).trans hnball)
      (hsqrtA.trans hTR) D (fun k => gamma (n + k))
      (fun k => (hN (n + k) (by omega)).1)
      (fun k => (hN (n + k) (by omega)).2) G
  refine ⟨K, hK, L, (eventually_ge_atTop n).mono ?_⟩
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact hL k

end DifferentialGeometry.CheegerGromovCompactness

end

end
