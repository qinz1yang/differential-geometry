import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedMinimizingLimit
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.MovingPairingLimit

/-!
# LC51, first half: the pushed collar field keeps its margin on one source tail

Setting of LC50 (master207A, A:22511): a complete limit `(N, g)`, an open `U ⊇ closedBall(n, 10)`,
actual embeddings `j i : U → M i` with source `U`, pullbacks `hSeq i = (j i)^* (gSeq i)` converging
to `g|U` in `C¹` on every compact subset of `U`. For a compact collar `C ⊆ B(n, 3) \ {n}` carrying
a continuous field `V` with `|V| ≤ B` and `g(V, v) ≤ -2α` for every inward unit minimizing direction
`v` (the output of LC49), LC51 (A:22607) asserts that on one tail the pushed fields
`Z_i = d(j i) V` satisfy `|Z_i| ≤ 2B` and `g_i(Z_i, w) ≤ -α` for EVERY inward unit minimizing
direction `w` at `j i q` towards `j i n`, uniformly in `q ∈ C`.

The proof is the blueprint's: the norm bound is uniform `C⁰` convergence; the margin is proved by
contradiction, extracting bad indices, applying LC50 (`exists_subseq_inward_direction_limit`) to
the bad subsequence, and passing to the limit in the moving pairing
`g_i(Z_i, w_i) = h_i(V, (d j_i)⁻¹ w_i)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The differential of a partial diffeomorphism undoes the differential of its inverse. -/
theorem mfderiv_apply_mfderiv_symm_of_mem_target {X Y : Type*} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y]
    (j : PartialDiffeomorph I I X Y ∞) {y : Y} (hy : y ∈ j.target)
    (u : TangentSpace I y) :
    mfderiv I I (j : X → Y) (j.symm y) (mfderiv I I (j.symm : Y → X) y u) = u := by
  have heq : (fun z : Y => j (j.symm z)) =ᶠ[𝓝 y] id :=
    j.toOpenPartialHomeomorph.eventually_right_inverse hy
  have hc := mfderiv_comp_apply y
    (j.mdifferentiableAt (by simp) (j.map_target hy))
    (j.symm.mdifferentiableAt (by simp) hy) u
  have hh := congrArg (fun L : TangentSpace I y →L[ℝ] TangentSpace I y => L u)
    (heq.mfderiv_eq (I := I) (I' := I))
  rw [mfderiv_id] at hh
  exact hc.symm.trans hh

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- `C¹` convergence on every compact set gives `C⁰` convergence on every compact set. -/
theorem metricCPConvergenceOn_zero_of_one {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] {hSeq : ℕ → SmoothRiemannianMetric I X}
    {hInf : SmoothRiemannianMetric I X} {D : Set X} (hD : IsCompact D)
    (hconv : MetricCPConvergenceOn D 1 hSeq hInf hInf) :
    MetricCPConvergenceOn D 0 hSeq hInf hInf := by
  intro epsilon hepsilon
  obtain ⟨i0, hi0⟩ := hconv (epsilon / 2) (half_pos hepsilon)
  refine ⟨i0, fun i hi => lt_of_le_of_lt ?_ (half_lt_self hepsilon)⟩
  apply metricDerivNormSupOn_le_of_forall D 0 (hSeq i) hInf hInf
    (epsilon / 2) (half_pos hepsilon).le
  intro a ha x hx
  exact (derivNorm_le_sup hD (by omega : a ≤ 1) (hSeq i) hInf hInf hx).trans (hi0 i hi).le

/-- **LC51, first half** (master207A, A:22607), on the actual LC50 data. For a compact collar
`C ⊆ B(n, 3) \ {n}` with a continuous field `V`, `|V|_g ≤ B` and `g(V, v) ≤ -2α` against every
inward unit minimizing direction (LC49's output), the pushed fields `d(j i) V` satisfy, on ONE
tail and uniformly in `q ∈ C`, `|d(j i) V|_{g_i} ≤ 2B` and `g_i(d(j i) V, w) ≤ -α` for EVERY
inward unit minimizing direction `w` from `j i q` to `j i n`. -/
theorem eventually_pushed_field_collar_margin
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens N) (n : U)
    (hbuffer : Metric.closedBall (n : N) 10 ⊆ U)
    (hSeq : ℕ → SmoothRiemannianMetric I U)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i))
    (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I U (M i) ∞)
    (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : U, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : U → M i) x v) (mfderiv I I (j i : U → M i) x w))
    (hconv : ∀ C : Set U, IsCompact C →
      MetricCPConvergenceOn C 1 hSeq (g.restrictOpen U) (g.restrictOpen U))
    {C : Set U} (hC : IsCompact C)
    (hCnear : ∀ q ∈ C, (q : N) ∈ Metric.ball (n : N) 3)
    (hCaway : ∀ q ∈ C, (q : N) ≠ (n : N))
    (V : (x : U) → TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I U)) C)
    {α B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hVB : ∀ q ∈ C, g.inner (q : N) (V q) (V q) ≤ B ^ 2)
    (hdir : ∀ q ∈ C, ∀ v ∈ inwardMinimizingDirections g hNorm (n : N) (q : N),
      g.inner (q : N) (V q) v ≤ -(2 * α)) :
    ∀ᶠ i in atTop, ∀ q ∈ C,
      √((gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q))
          (mfderiv I I (j i : U → M i) q (V q))) ≤ 2 * B ∧
      ∀ w ∈ inwardMinimizingDirections (gSeq i) (hSeqNorm i) (j i n) (j i q),
        (gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q)) w ≤ -α := by
  let hInf := g.restrictOpen U
  have hconv0 : MetricCPConvergenceOn C 0 hSeq hInf hInf :=
    metricCPConvergenceOn_zero_of_one hC (hconv C hC)
  have hnorm : ∀ᶠ i in atTop, ∀ q ∈ C,
      √((gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q))
          (mfderiv I I (j i : U → M i) q (V q))) ≤ 2 * B := by
    filter_upwards [hconv0.eventually_quadratic_bounds hC one_pos] with i hi q hq
    have hup := (hi q hq (V q)).2
    rw [hmetric i q (V q) (V q)] at hup
    have hinf : hInf.inner q (V q) (V q) = g.inner (q : N) (V q) (V q) := rfl
    rw [hinf] at hup
    have hsq : (gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q))
        (mfderiv I I (j i : U → M i) q (V q)) ≤ (2 * B) ^ 2 := by
      nlinarith [hVB q hq]
    calc _ ≤ √((2 * B) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * B := Real.sqrt_sq (by positivity)
  have hmargin : ∀ᶠ i in atTop, ∀ q ∈ C,
      ∀ w ∈ inwardMinimizingDirections (gSeq i) (hSeqNorm i) (j i n) (j i q),
        (gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q)) w ≤ -α := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨psi, hpsi, hbad⟩ := Filter.extraction_of_frequently_atTop hcon
    have hbad' : ∀ k, ∃ q ∈ C, ∃ w ∈ inwardMinimizingDirections (gSeq (psi k))
        (hSeqNorm (psi k)) (j (psi k) n) (j (psi k) q),
        -α < (gSeq (psi k)).inner (j (psi k) q)
          (mfderiv I I (j (psi k) : U → M (psi k)) q (V q)) w := by
      intro k
      have hk := hbad k
      push Not at hk
      exact hk
    choose qS hqS wS hwS hlt using hbad'
    have hconvPsi : ∀ D : Set U, IsCompact D →
        MetricCPConvergenceOn D 1 (fun k => hSeq (psi k)) hInf hInf := by
      intro D hD epsilon hepsilon
      obtain ⟨k0, hk0⟩ := hconv D hD epsilon hepsilon
      exact ⟨k0, fun k hk => hk0 (psi k) (hk.trans (hpsi.id_le k))⟩
    obtain ⟨xInf, hxC, hxDir, phi, hphi, hlim⟩ :=
      exists_subseq_inward_direction_limit (M := fun k => M (psi k)) g hNorm U n hbuffer
        (fun k => hSeq (psi k)) (fun k => gSeq (psi k)) (fun k => hSeqNorm (psi k))
        (fun k => j (psi k)) (fun k => hj (psi k)) (fun k => hmetric (psi k)) hconvPsi
        hC hCnear hCaway qS hqS wS hwS
    have hconvSub : MetricCPConvergenceOn C 0 (fun k => hSeq (psi (phi k))) hInf hInf := by
      intro epsilon hepsilon
      obtain ⟨k0, hk0⟩ := hconv0 epsilon hepsilon
      exact ⟨k0, fun k hk => hk0 (psi (phi k))
        (hk.trans ((hpsi.comp hphi).id_le k))⟩
    have hpair := MetricCPConvergenceOn.tendsto_inner_section_of_tendsto
      (fun k => hSeq (psi (phi k))) hInf hC hconvSub V hV _ xInf
      (fun k => hqS (phi k)) hlim
    have hterm : ∀ k, -α ≤ (hSeq (psi (phi k))).inner (qS (phi k)) (V (qS (phi k)))
        (mfderiv I I ((j (psi (phi k))).symm : M (psi (phi k)) → U)
          (j (psi (phi k)) (qS (phi k))) (wS (phi k))) := by
      intro k
      set i := psi (phi k)
      set q := qS (phi k)
      have hsrc : q ∈ (j i).source := (hj i).symm ▸ mem_univ q
      have htgt : j i q ∈ (j i).target := (j i).map_source hsrc
      have hleft : (j i).symm (j i q) = q := (j i).left_inv hsrc
      have hinv := mfderiv_apply_mfderiv_symm_of_mem_target (j i) htgt (wS (phi k))
      have hrw : mfderiv I I (j i : U → M i) q
          (mfderiv I I ((j i).symm : M i → U) (j i q) (wS (phi k))) = wS (phi k) := by
        have h2 := hinv
        rw [hleft] at h2
        exact h2
      have hm := hmetric i q (V q)
        (mfderiv I I ((j i).symm : M i → U) (j i q) (wS (phi k)))
      rw [hrw] at hm
      exact (hlt (phi k)).le.trans_eq hm.symm
    have hge : -α ≤ hInf.inner xInf.proj (V xInf.proj) xInf.snd :=
      ge_of_tendsto hpair (Eventually.of_forall hterm)
    have hle : hInf.inner xInf.proj (V xInf.proj) xInf.snd ≤ -(2 * α) :=
      hdir xInf.proj hxC xInf.snd hxDir
    linarith
  filter_upwards [hnorm, hmargin] with i hi hi' q hq
  exact ⟨hi q hq, hi' q hq⟩

end DifferentialGeometry.Geometry.Collapse
