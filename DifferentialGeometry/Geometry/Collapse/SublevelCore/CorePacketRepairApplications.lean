import DifferentialGeometry.Geometry.Collapse.SublevelCore.CorePacketRepair
import DifferentialGeometry.Geometry.Collapse.SublevelCore.SoulSublevelType

/-!
# Consumer of the LC48 packet repair: LC38 gives the soul type of every radial sublevel

Master207A, A:22349 (LC48, last line of the proof: "LC38 then gives the stated soul type"). The
model core is the image `D_N = eN '' D₁` of the closed unit disc bundle under the soul disc
identification `eN`. LC48 in the blueprint's source-collar form
(`lc48_source_collar_packet_repair`) produces the repaired embedding `j₁` with all LC37 clauses;
LC38 (`lc38_noncompact_sublevel_diffeomorph`) applied to `j₁` identifies every `A_ρ`,
`ρ ∈ [1/5, 2]`, with the closed unit disc bundle as manifolds with boundary
(`lc48_repaired_packet_soul_sublevel_type`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [CompactSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **LC48 followed by LC38.** For the model core `D_N = eN '' D₁` (the soul disc
identification of the closed unit disc bundle) and the hypotheses of LC48 in its source-collar
form: the repaired embedding `j₁` (same source, `j₁ n = j n`, `j₁(D_N) = A₁`) exists, and for
every `ρ ∈ [1/5, 2]` the radial sublevel `A_ρ`, as the regular sublevel `{f ≤ ρ}` of a globally
smooth `f` with the same sublevel, is diffeomorphic as a manifold with boundary to the closed
unit disc bundle by `K ∘ j₁ ∘ eN` for an ambient diffeomorphism `K`. -/
theorem lc48_repaired_packet_soul_sublevel_type {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N] (gN : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1 / 10) (hcpt : IsCompact (riemannianClosedBallOf gN n 10))
    (hsrc : riemannianClosedBallOf gN n 10 ⊆ j.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ v : TangentSpace I z,
      (1 - lam) ^ 2 * gN.inner z v v ≤
        g.inner (j z) (mfderiv I I j z v) (mfderiv I I j z v))
    (hupper : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ v : TangentSpace I z,
      g.inner (j z) (mfderiv I I j z v) (mfderiv I I j z v) ≤
        (1 + lam) ^ 2 * gN.inner z v v)
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist (j n) x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist (j n) x))
    {W : Set M} (hW : IsOpen W)
    (hCW : ∀ x, 1 / 10 ≤ dist (j n) x → dist (j n) x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist (j n) x → dist (j n) x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    (eN : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ eN.source)
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆
      interior ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}))
    (hout : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆ riemannianBallOf gN n 2)
    {O : Set N} (hO : IsOpen O) (Vf : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, Vf x⟩ : TangentBundle I N)) O)
    (hdef : ∀ q ∈ frontier ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}),
      ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧
        (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (Vf q))
    {Wc : Set M} (hWc : IsOpen Wc)
    (hfrWc : frontier ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})) ⊆ Wc)
    (hWcO : Wc ⊆ (j : N → M) '' (O ∩ j.source)) (hpWc : j n ∉ Wc)
    {α Bd : ℝ}
    (hZB : ∀ x ∈ Wc, √(g.inner x (modelPushedField j Vf x) (modelPushedField j Vf x)) ≤ Bd)
    (hdir : ∀ x ∈ Wc, ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm (j n) x,
      g.inner x (modelPushedField j Vf x) u ≤ -α)
    (hmargin : ε * Bd < α)
    {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) (hE : Module.finrank ℝ E = m + 1) :
    let I' := I.transContinuousLinearEquiv
      (ContinuousLinearEquiv.ofFinrankEq (hE.trans (Module.finrank_fin_fun ℝ).symm) :
        E ≃L[ℝ] MorseModel (m + 1))
    ∃ j₁ : PartialDiffeomorph I I N M ∞, j₁.source = j.source ∧ j₁ n = j n ∧
      (j₁ : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}) = {x | η x ≤ 1} ∧
      ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ f : M → ℝ, ∃ hf : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f,
        ∃ hr : ∀ x, f x = ρ → mfderiv I' 𝓘(ℝ, ℝ) f x ≠ 0,
        (∀ x, f x ≤ ρ ↔ η x ≤ ρ) ∧
        let _ := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
        let _ := sublevelChartedSpace I' hf hr
        ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} {x : M // f x ≤ ρ} ∞,
          ∃ K : Diffeomorph I I M M ∞, ∀ z, (Φ z : M) = K (j₁ (eN z)) := by
  intro I'
  obtain ⟨gB, hgB, hgBeq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle IB ∞ F V).exists_contMDiff
  have : IsContinuousRiemannianBundle F V := ⟨gB, hgB.continuous, hgBeq⟩
  have hDNc : IsClosed ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}) :=
    ((isCompact_closedDiscBundle 1).image_of_continuousOn
      (eN.contMDiffOn.continuousOn.mono hdisc)).isClosed
  have hDN10 : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆
      riemannianClosedBallOf gN n 10 := fun z hz => by
    have h := hout hz
    change riemannianEDistOf gN n z < _ at h
    change riemannianEDistOf gN n z ≤ _
    exact h.le.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  obtain ⟨-, -, -, -, -, j₁, hj₁s, -, hj₁n, hj₁D, -, hAD, hDb, hdef₁⟩ :=
    lc48_source_collar_packet_repair gN g hEnorm j n hlam0 hlam1 hcpt hsrc hlower hupper hε1
      he hclose hlip hW hCW hηW hgrad hDNc hin hout hO Vf hV hdef hWc hfrWc hWcO hpWc hZB hdir
      hmargin
  refine ⟨j₁, hj₁s, hj₁n, hj₁D, fun ρ hρ => ?_⟩
  have hclose₁ : ∀ x, |η x - dist (j₁ n) x| < e := by rw [hj₁n]; exact hclose
  have hlip₁ : LipschitzWith ε (fun x => η x - dist (j₁ n) x) := by rw [hj₁n]; exact hlip
  have hCW₁ : ∀ x, 1 / 10 ≤ dist (j₁ n) x → dist (j₁ n) x ≤ 10 → x ∈ W := by
    rw [hj₁n]; exact hCW
  have hgrad₁ : ∀ x, 1 / 10 ≤ dist (j₁ n) x → dist (j₁ n) x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := by
    rw [hj₁n]; exact hgrad
  obtain ⟨f, hf, hr, hle, -, -, Hs, -, -, -, -, hΦ⟩ :=
    lc38_noncompact_sublevel_diffeomorph g hEnorm hε1 he hclose₁ hlip₁ hW hCW₁ hηW hgrad₁ j₁ eN
      hdisc (by rw [hj₁s]; exact hDN10.trans hsrc) hAD hDb
      (fun q hq => by
        obtain ⟨L, hL, hqL, f', hf', hset, h1⟩ := hdef₁ q hq
        exact ⟨L, hL, hqL, f', hf', hset, by rw [h1]; exact one_pos⟩) hd hE hρ
  obtain ⟨Φ, hΦ'⟩ := hΦ
  exact ⟨f, hf, hr, hle, Φ, Hs 1, hΦ'⟩

end DifferentialGeometry.Geometry.Collapse
