import DifferentialGeometry.Geometry.Collapse.SublevelCore.PushedCollarMargin
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ModelCoreTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformCollar
import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedOpenCompact
import DifferentialGeometry.Topology.VectorField.OpenRestriction

/-!
# LC51, second half: the model core is carried onto every radial sublevel on one tail

Setting of LC50/LC51 (master207A, A:22511, A:22607). A compact model core `D ⊆ N` with
`closedBall(n, 1/2) ⊆ int D`, `D ⊆ B(n, 2)`, its own smooth field `V`, strictly outward on
`∂D` (local defining functions with positive `V`-derivative), and an open collar `W ⊇ ∂D`
whose compact closure lies in `B(n, 3) \ {n}` and carries `|V| ≤ B`, `g(V, v) ≤ -2α` against
every inward unit minimizing direction. Selected radial functions `η i` on `M i` with the LC30
clauses and Lipschitz error `ε`, `2Bε < α`. Then on ONE tail, for every `ρ ∈ [1/5, 2]`, a
compactly supported smooth isotopy of `M i` carries `j i (D)` onto `{η i ≤ ρ}` (the LC48 model
side, `exists_model_core_collar_isotopy`, fed by the first half
`eventually_pushed_field_collar_margin`).

`eventually_core_isotopy_of_collar_margin` takes the collar and its constants (the form LC57
consumes with LC55's explicit `α = 1/8`, `B = 2`); `exists_collar_constants_core_isotopy` is the
blueprint's statement, choosing the collar and `α, B` by LC49 before the smoothing tolerance.
The noncompactness of `N` is not needed (it only makes `∂D` nonempty).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A tangent field smooth on an open `O` restricts to a smooth field of the open submanifold
`U` on `U ∩ O`. -/
theorem contMDiffOn_restrict_tangentSection (U : TopologicalSpace.Opens X)
    {V : (x : X) → TangentSpace I x} {O : Set X} (hO : IsOpen O)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I X)) O) :
    ContMDiffOn I I.tangent ∞ (fun x : U => (⟨x, V x⟩ : TangentBundle I U))
      (Subtype.val ⁻¹' O) := by
  intro x hx
  let f := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U ⟨x⟩
  have hfx : f x = (x : X) := rfl
  have hVx : ContMDiffAt I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I X)) (f x) := by
    rw [hfx]
    exact hV.contMDiffAt (hO.mem_nhds hx)
  have h := DifferentialGeometry.VectorField.contMDiffAt_mpullback_partialDiffeomorph f
    (by simp) (x := x) (by simp [f]) hVx
  refine (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  exact Filter.Eventually.of_forall fun y => congrArg
    (fun v : TangentSpace I y => (⟨y, v⟩ : TangentBundle I U))
    (DifferentialGeometry.Manifold.mpullback_openSubtype I U ⟨x⟩ V y).symm

omit [IsManifold I ∞ X] in
/-- Local defining functions with positive `V`-derivative restrict to an open submanifold. -/
theorem restrict_local_defining_functions (U : TopologicalSpace.Opens X) {D : Set X}
    (V : (x : X) → TangentSpace I x)
    (hdef : ∀ q ∈ frontier D, ∃ L : Set X, IsOpen L ∧ q ∈ L ∧ ∃ f : X → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q)) :
    ∀ q ∈ frontier (Subtype.val ⁻¹' D : Set U), ∃ L : Set U, IsOpen L ∧ q ∈ L ∧
      ∃ f : U → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧
        (Subtype.val ⁻¹' D : Set U) ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q) := by
  intro q hq
  have hqN : (q : X) ∈ frontier D := continuous_subtype_val.frontier_preimage_subset D hq
  obtain ⟨L, hL, hqL, f, hf, hDL, hpos⟩ := hdef q hqN
  refine ⟨Subtype.val ⁻¹' L, hL.preimage continuous_subtype_val, hqL, f ∘ Subtype.val,
    hf.comp contMDiff_subtype_val.contMDiffOn (fun x hx => hx), ?_, ?_⟩
  · ext x
    have h := congrArg (fun s : Set X => (x : X) ∈ s) hDL
    simp only [mem_inter_iff, eq_iff_iff] at h
    simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
    exact h
  · have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (q : X) :=
      (hf.contMDiffAt (hL.mem_nhds hqL)).mdifferentiableAt (by norm_num)
    have hc := mfderiv_comp_apply q hfd
      ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by norm_num))
      (V q)
    have hval := DifferentialGeometry.mfderiv_subtype_val_apply (I := I) U q (V q)
    have heq : mvfderiv (I := I) (f ∘ Subtype.val) q (V q) = mvfderiv (I := I) f q (V q) := by
      change mfderiv I 𝓘(ℝ, ℝ) (f ∘ Subtype.val) q (V q) = mfderiv I 𝓘(ℝ, ℝ) f (q : X) (V q)
      rw [hc, hval]
    rw [heq]
    exact hpos

end Restriction

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

/-- **LC51, second half, collar form** (master207A, A:22607). On the actual LC50 data, a closed
model core `D` with `closedBall(n, 1/2) ⊆ int D` and `D ⊆ B(n, 2)`, its own field `V` smooth on an
open `O`, strictly outward on `∂D`, an open collar `W ⊇ ∂D` with compact closure in
`(B(n, 3) \ {n}) ∩ O` carrying `|V|² ≤ B²` and `g(V, v) ≤ -2α` on `𝒰_n`, and selected radial
functions `η i` (LC30 clauses, value errors `e i < 1/40`, Lipschitz error `ε`, `ε · 2B < α`) on a
tail: then on one tail and for every `ρ ∈ [1/5, 2]` a compactly supported smooth isotopy of `M i`
carries `j i (D)` onto `{η i ≤ ρ}`. -/
theorem eventually_core_isotopy_of_collar_margin
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
    {D : Set N} (hDc : IsClosed D)
    (hin : Metric.closedBall (n : N) (1 / 2) ⊆ interior D)
    (hout : D ⊆ Metric.ball (n : N) 2)
    {W O : Set N} (hW : IsOpen W) (hfrW : frontier D ⊆ W) (hWcpt : IsCompact (closure W))
    (hWnear : closure W ⊆ (Metric.ball (n : N) 3 \ {(n : N)}) ∩ O) (hO : IsOpen O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hdef : ∀ q ∈ frontier D, ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q))
    {α B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hVB : ∀ q ∈ closure W, g.inner q (V q) (V q) ≤ B ^ 2)
    (hdir : ∀ q ∈ closure W, ∀ v ∈ inwardMinimizingDirections g hNorm (n : N) q,
      g.inner q (V q) v ≤ -(2 * α))
    {ε : ℝ≥0} (hε1 : (ε : ℝ) < 1) (hεB : (ε : ℝ) * (2 * B) < α)
    (η : ∀ i, M i → ℝ) (e : ℕ → ℝ)
    (hη : ∀ᶠ i in atTop, e i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < e i) ∧
      LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
      ∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
            (gradientFun (I := I) (gSeq i) (η i) x)) :
    ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ Hs : ℝ → Diffeomorph I I (M i) (M i) ∞,
      Hs 0 = Diffeomorph.refl I (M i) ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => (Hs q.1).symm q.2) ∧
      (∃ S : Set (M i), IsCompact S ∧ S ⊆ η i ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' ((j i : U → M i) '' (Subtype.val ⁻¹' D)) = {x | η i x ≤ ρ} := by
  let hInf := g.restrictOpen U
  have hd (x y : N) : riemannianEDistOf g x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hNorm, ← IsRiemannianManifold.out (I := I)]
  have hWU : closure W ⊆ (U : Set N) := fun x hx =>
    hbuffer (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by norm_num : (3 : ℝ) ≤ 10)
      ((hWnear hx).1.1)))
  -- the collar as a compact subset of `U`
  let C : Set U := Subtype.val ⁻¹' closure W
  have hC : IsCompact C := by
    change IsCompact (Subtype.val ⁻¹' closure W : Set U)
    rw [Subtype.isCompact_iff,
      image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hWU hx⟩, rfl⟩)]
    exact hWcpt
  have hCnear : ∀ q ∈ C, (q : N) ∈ Metric.ball (n : N) 3 := fun q hq => (hWnear hq).1.1
  have hCaway : ∀ q ∈ C, (q : N) ≠ (n : N) := fun q hq => (hWnear hq).1.2
  let V' : (x : U) → TangentSpace I x := fun x => V x
  have hV' : ContMDiffOn I I.tangent ∞ (fun x : U => (⟨x, V' x⟩ : TangentBundle I U))
      (Subtype.val ⁻¹' O) := contMDiffOn_restrict_tangentSection U hO hV
  have hV'C : ContinuousOn (fun x : U => (⟨x, V' x⟩ : TangentBundle I U)) C :=
    hV'.continuousOn.mono (fun x hx => (hWnear hx).2)
  have hmargin := eventually_pushed_field_collar_margin g hNorm U n hbuffer hSeq gSeq hSeqNorm
    j hj hmetric hconv hC hCnear hCaway V' hV'C hα hB (fun q hq => hVB q hq)
    (fun q hq v hv => hdir q hq v hv)
  -- two-sided metric comparison on the closed `10`-ball of `U`
  have hK := bufferedOpen_native_closedBall_compact g hNorm U n hbuffer
  have hq10 := (metricCPConvergenceOn_zero_of_one hK (hconv _ hK)).eventually_quadratic_bounds
    hK (by norm_num : (0 : ℝ) < 1 / 20)
  -- the core in `U`
  have hinU : riemannianClosedBallOf hInf n (1 / 2) ⊆
      interior (Subtype.val ⁻¹' D : Set U) := by
    intro z hz
    apply preimage_interior_subset_interior_preimage continuous_subtype_val
    apply hin
    have hle : riemannianEDistOf g (n : N) (z : N) ≤ ENNReal.ofReal (1 / 2) :=
      (riemannianEDistOf_le_restrictOpen g U n z).trans hz
    rw [hd, edist_dist] at hle
    rw [Metric.mem_closedBall, dist_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hle
  have houtU : (Subtype.val ⁻¹' D : Set U) ⊆ riemannianBallOf hInf n 2 := by
    intro z hz
    have hz2 : (z : N) ∈ Metric.ball (n : N) 2 := hout hz
    have hz3 : (z : N) ∈ Metric.ball (n : N) 3 :=
      Metric.ball_subset_ball (by norm_num) hz2
    change riemannianEDistOf hInf n z < ENNReal.ofReal 2
    rw [bufferedOpen_restricted_edist_eq g hNorm U n z hbuffer hz3, edist_dist]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).2
    simpa only [Metric.mem_ball, dist_comm] using hz2
  have hfrU : frontier (Subtype.val ⁻¹' D : Set U) ⊆ Subtype.val ⁻¹' W := fun x hx =>
    hfrW (continuous_subtype_val.frontier_preimage_subset D hx)
  have hnU : n ∉ (Subtype.val ⁻¹' W : Set U) := fun h =>
    (hWnear (subset_closure h)).1.2 rfl
  have hdefU := restrict_local_defining_functions U V hdef
  filter_upwards [hmargin, hq10, hη] with i hm hq ⟨he, hclose, hlip, Wi, hWi, hCWi, hηWi, hgrad⟩
    ρ hρ
  have hsrc : riemannianClosedBallOf hInf n 10 ⊆ (j i).source := by
    rw [hj i]
    exact subset_univ _
  refine exists_model_core_collar_isotopy (N := U) hInf (gSeq i) (hSeqNorm i) (j i) n
    (lam := 1 / 20) (by norm_num) (by norm_num) hK hsrc ?_ ?_ hε1 he hclose hlip hWi hCWi
    hηWi hgrad (hDc.preimage continuous_subtype_val) hinU houtU
    (hW.preimage continuous_subtype_val) hfrU hnU V'
    (hV'.mono (fun x hx => (hWnear (subset_closure hx)).2)) hdefU (B := 2 * B) ?_ ?_ hεB hρ
  · intro z hz v
    have h1 := (hq z hz v).1
    rw [hmetric i z v v] at h1
    have h0 : 0 ≤ hInf.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (hInf.pos z v hv).le
    nlinarith
  · intro z hz v
    have h1 := (hq z hz v).2
    rw [hmetric i z v v] at h1
    have h0 : 0 ≤ hInf.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (hInf.pos z v hv).le
    nlinarith
  · rintro x ⟨q, ⟨hqW, -⟩, rfl⟩
    rw [modelPushedField_apply (j i) V' ((hj i).symm ▸ mem_univ q)]
    exact (hm q (subset_closure hqW)).1
  · rintro x ⟨q, ⟨hqW, -⟩, rfl⟩ u hu
    rw [modelPushedField_apply (j i) V' ((hj i).symm ▸ mem_univ q)]
    exact (hm q (subset_closure hqW)).2 u hu

/-- **LC51** (master207A, A:22607), the blueprint's quantifier order. On the actual LC50 data, a
compact model core `D` with `closedBall(n, 1/2) ⊆ int D`, `D ⊆ B(n, 2)`, its own field `V` smooth
on an open `O ⊇ ∂D`, strictly outward on `∂D` and pairing strictly negatively with every inward
unit minimizing direction along `∂D`. LC49 first fixes `α, B > 0` and an open collar `W ⊇ ∂D`.
Then (1) on one tail the pushed fields satisfy `|d(j i) V| ≤ 2B` and `g_i(d(j i) V, w) ≤ -α` for
every inward unit minimizing direction `w`, at every point of the collar; (2) for EVERY smoothing
tolerance `ε < 1` with `ε · 2B < α`, fixed afterwards, and selected radial functions `η i` with the
LC30 clauses on a tail, one tail carries, for every `ρ ∈ [1/5, 2]`, a compactly supported smooth
isotopy of `M i` moving `j i (D)` onto `{η i ≤ ρ}`. -/
theorem exists_collar_constants_core_isotopy
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
    {D : Set N} (hDc : IsCompact D)
    (hin : Metric.closedBall (n : N) (1 / 2) ⊆ interior D)
    (hout : D ⊆ Metric.ball (n : N) 2)
    {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hdef : ∀ q ∈ frontier D, ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q))
    (hneg : ∀ q ∈ frontier D, ∀ v ∈ inwardMinimizingDirections g hNorm (n : N) q,
      g.inner q (V q) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ W : Set N, IsOpen W ∧ frontier D ⊆ W ∧
      (∀ᶠ i in atTop, ∀ q ∈ (Subtype.val ⁻¹' W : Set U),
        √((gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q))
            (mfderiv I I (j i : U → M i) q (V q))) ≤ 2 * B ∧
        ∀ w ∈ inwardMinimizingDirections (gSeq i) (hSeqNorm i) (j i n) (j i q),
          (gSeq i).inner (j i q) (mfderiv I I (j i : U → M i) q (V q)) w ≤ -α) ∧
      ∀ ε : ℝ≥0, (ε : ℝ) < 1 → (ε : ℝ) * (2 * B) < α →
      ∀ (η : ∀ i, M i → ℝ) (e : ℕ → ℝ),
      (∀ᶠ i in atTop, e i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < e i) ∧
        LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
        ∃ Wi : Set (M i), IsOpen Wi ∧
          (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
          ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
            (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
              (gradientFun (I := I) (gSeq i) (η i) x)) →
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ Hs : ℝ → Diffeomorph I I (M i) (M i) ∞,
        Hs 0 = Diffeomorph.refl I (M i) ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => (Hs q.1).symm q.2) ∧
        (∃ S : Set (M i), IsCompact S ∧ S ⊆ η i ⁻¹' Ioo (1 / 8) 3 ∧
          ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
        Hs 1 '' ((j i : U → M i) '' (Subtype.val ⁻¹' D)) = {x | η i x ≤ ρ} := by
  have hfrD : frontier D ⊆ D := hDc.isClosed.frontier_subset
  have hnD : (n : N) ∉ frontier D := fun h =>
    h.2 (hin (Metric.mem_closedBall_self (by norm_num)))
  have hC₀n : frontier D ⊆ Metric.ball (n : N) 3 \ {(n : N)} := fun x hx =>
    ⟨Metric.ball_subset_ball (by norm_num) (hout (hfrD hx)),
      fun h => hnD (by rw [mem_singleton_iff] at h; rwa [← h])⟩
  obtain ⟨α, B, hα, hB, W, hW, hfrW, hWcpt, hWsub, hbounds⟩ :=
    exists_uniform_collar_of_strict_point_directions g hNorm (n : N)
      (hDc.of_isClosed_subset isClosed_frontier hfrD) hC₀n hO hDO V hV.continuousOn hneg
  refine ⟨α, B, hα, hB, W, hW, hfrW, ?_, ?_⟩
  · have hWU : closure W ⊆ (U : Set N) := fun x hx =>
      hbuffer (Metric.ball_subset_closedBall (Metric.ball_subset_ball
        (by norm_num : (3 : ℝ) ≤ 10) ((hWsub hx).1.1)))
    have hC : IsCompact (Subtype.val ⁻¹' closure W : Set U) := by
      rw [Subtype.isCompact_iff,
        image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hWU hx⟩, rfl⟩)]
      exact hWcpt
    have hV' := contMDiffOn_restrict_tangentSection U hO hV
    have hm := eventually_pushed_field_collar_margin g hNorm U n hbuffer hSeq gSeq hSeqNorm
      j hj hmetric hconv hC (fun q hq => (hWsub hq).1.1) (fun q hq => (hWsub hq).1.2)
      (fun x : U => V x) (hV'.continuousOn.mono (fun x hx => (hWsub hx).2)) hα hB.le
      (fun q hq => (hbounds q hq).1) (fun q hq v hv => (hbounds q hq).2 v hv)
    filter_upwards [hm] with i hi q hq
    exact hi q (subset_closure hq)
  · intro ε hε1 hεB η e hη
    exact eventually_core_isotopy_of_collar_margin g hNorm U n hbuffer hSeq gSeq hSeqNorm j hj
      hmetric hconv hDc.isClosed hin hout hW hfrW hWcpt hWsub hO V hV hdef hα hB.le
      (fun q hq => (hbounds q hq).1) (fun q hq v hv => (hbounds q hq).2 v hv) hε1 hεB η e hη

end DifferentialGeometry.Geometry.Collapse
