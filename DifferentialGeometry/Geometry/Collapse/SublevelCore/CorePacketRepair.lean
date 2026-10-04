import DifferentialGeometry.Geometry.Collapse.SublevelCore.PushedCollarPacket
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# LC48, model side: the repaired embedding produces the original noncompact LC37 packet

Master207A, A:22349 (LC48), second paragraph, and the last sentence of LC51 (A:22607). The
model-side isotopy and the repaired embedding `j₁ = H₁ ∘ j₀` with `j₁(D_N) = A₁` are X84's
(`exists_model_core_collar_isotopy`, `exists_model_core_packet_repair`); this file adds the LC37
clauses for `j₁`, the blueprint's source-collar form of the hypotheses and the tail version.

* `radialSublevel_lc36_clauses`: for the LC30 radial function, every `A_ρ`, `ρ ∈ (1/8, 3)`, is
  closed, contains `A_{1/8}` in its interior, lies in `{η < 3}`, and along its frontier
  `f = η - ρ` is a local defining function with `df(X) = 1` for `X = ∇η / |∇η|²` — exactly the
  enclosure and outward transversality of LC36/LC37.
* `image_frontier_subset_frontier_image`: a partial diffeomorphism carries the frontier of a
  closed set inside its source into the frontier of the image.
* `exists_packet_of_time_one_core`: a time-one map fixing the base point that carries `j(D_N)` onto
  `A₁` repairs `j` on the same source.
* `lc48_exists_core_packet_repair` (X84's model-side hypotheses) and
  `lc48_source_collar_packet_repair` (the blueprint's hypotheses: margins for `Z = (j₀)_* V` on an
  open source collar `W ∌ p` of `∂ j₀(D_N)`): the repaired `j₁` with ALL LC37 clauses.
* `lc51_eventually_core_packets`: LC51 in its quantifier order, ending with the repaired packets
  on one tail.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- A partial diffeomorphism carries the frontier of a closed set inside its source into the
frontier of the image. -/
theorem image_frontier_subset_frontier_image (j : PartialDiffeomorph I I N M ∞) {D : Set N}
    (hD : IsClosed D) (hDs : D ⊆ j.source) :
    (j : N → M) '' frontier D ⊆ frontier ((j : N → M) '' D) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxD : x ∈ D := hD.frontier_subset hx
  refine ⟨subset_closure ⟨x, hxD, rfl⟩, fun hint => hx.2 ?_⟩
  let T := interior ((j : N → M) '' D)
  have hO : IsOpen (j.source ∩ (j : N → M) ⁻¹' T) :=
    j.contMDiffOn.continuousOn.isOpen_inter_preimage j.open_source isOpen_interior
  refine interior_maximal ?_ hO ⟨hDs hxD, hint⟩
  rintro y ⟨hys, hyT⟩
  obtain ⟨z, hz, hzy⟩ := interior_subset hyT
  rwa [← j.injOn (hDs hz) hys hzy]

/-- **Repair by a time-one map.** If `H₁` fixes everything outside `S ⊆ η⁻¹(1/8, 3)`,
`η (j n) < 1/8` and `H₁ (j D) = {η ≤ 1}`, then `j₁ = H₁ ∘ j` is a partial diffeomorphism on the
same source with `j₁ n = j n` and `j₁ D = {η ≤ 1}`. -/
theorem exists_packet_of_time_one_core (j : PartialDiffeomorph I I N M ∞) (n : N)
    (H₁ : Diffeomorph I I M M ∞) {η : M → ℝ} {S : Set M} (hS : S ⊆ η ⁻¹' Ioo (1 / 8) 3)
    (hfix : ∀ x, x ∉ S → H₁ x = x) (hn : η (j n) < 1 / 8) {D : Set N}
    (himg : H₁ '' ((j : N → M) '' D) = {x | η x ≤ 1}) :
    ∃ j₁ : PartialDiffeomorph I I N M ∞, j₁.source = j.source ∧ (∀ x, j₁ x = H₁ (j x)) ∧
      j₁ n = j n ∧ (j₁ : N → M) '' D = {x | η x ≤ 1} := by
  refine ⟨j.trans H₁.toPartialDiffeomorph, ?_, fun x => rfl, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    change j.source ∩ (j : N → M) ⁻¹' univ = j.source
    rw [preimage_univ, inter_univ]
  · exact hfix (j n) (fun h => absurd (hS h).1 (not_lt.mpr hn.le))
  · change ((H₁ : M → M) ∘ (j : N → M)) '' D = _
    rw [image_comp]
    exact himg

end Generic

section Single

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- **The LC36/LC37 clauses of a radial sublevel.** For the LC30 radial function and
`ρ ∈ (1/8, 3)`, `A_ρ` is closed, `A_{1/8} ⊆ int A_ρ`, `A_ρ ⊆ {η < 3}`, and at every frontier
point `η - ρ` is a local defining function with derivative `1` along `X = ∇η / |∇η|²`. -/
theorem radialSublevel_lc36_clauses (g : SmoothRiemannianMetric I M)
    {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Ioo (1 / 8 : ℝ) 3) :
    IsClosed {x | η x ≤ ρ} ∧ {x | η x ≤ 1 / 8} ⊆ interior {x | η x ≤ ρ} ∧
      {x | η x ≤ ρ} ⊆ {x | η x < 3} ∧
      ∀ q ∈ frontier {x | η x ≤ ρ}, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ {x | η x ≤ ρ} ∩ U = {x | f x ≤ 0} ∩ U ∧
          mvfderiv (I := I) f q
            ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
              gradientFun (I := I) g η q) = 1 := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have hcl : IsClosed {x | η x ≤ ρ} := isClosed_le hη continuous_const
  have hopen : IsOpen {x | η x < ρ} := isOpen_lt hη continuous_const
  refine ⟨hcl, fun x hx => interior_maximal (fun y hy => le_of_lt hy) hopen
    (lt_of_le_of_lt hx hρ.1), fun x hx => lt_of_le_of_lt hx hρ.2, ?_⟩
  intro q hq
  have hqle : η q ≤ ρ := hcl.frontier_subset hq
  have hqge : ρ ≤ η q := by
    by_contra h
    exact hq.2 (interior_maximal (fun y hy => le_of_lt hy) hopen (lt_of_not_ge h))
  have hqρ : η q = ρ := le_antisymm hqle hqge
  have hqK : q ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3 := by
    change η q ∈ Icc (1 / 8 : ℝ) 3
    rw [hqρ]
    exact ⟨hρ.1.le, hρ.2.le⟩
  have hann := radialBand_subset_annulus hclose he hqK
  have hqW : q ∈ W := hCW q hann.1.le hann.2.le
  refine ⟨W, hW, hqW, fun x => η x - ρ, hηW.sub contMDiffOn_const, ?_, ?_⟩
  · ext x
    simp only [mem_inter_iff, mem_ofPred_eq, sub_nonpos]
  · have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ) η q :=
      (hηW.contMDiffAt (hW.mem_nhds hqW)).mdifferentiableAt (by simp)
    have hm : 0 < 1 - (ε : ℝ) := by linarith
    have hpos : 0 < g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q) :=
      lt_of_lt_of_le (by positivity) (hgrad q hann.1.le hann.2.le)
    rw [mvfderiv_fun_sub hηd mdifferentiableAt_const, mvfderiv_const, sub_zero, map_smul,
      ← inner_gradientFun (I := I) g η q, smul_eq_mul, inv_mul_cancel₀ hpos.ne']

/-- **LC48, model side, with the original LC37 packet** (master207A, A:22349). Under X84's
model-side hypotheses (LC39 comparison at `L = 10`, `λ < 1/10`; the LC30 radial function; a
closed model core `D_N` with `B̄(n, 1/2) ⊆ int D_N ⊆ D_N ⊆ B(n, 2)` and its own outward field `V`
on a collar `U ∌ n`; the margins `|Z| ≤ B`, `g(Z, w) ≤ -α`, `εB < α` for `Z = (j₀)_* V`): a
compactly supported isotopy `H` and the repaired embedding `j₁ = H₁ ∘ j₀` on the same source,
with `j₁ n = j₀ n`, `j₁(D_N) = A₁`, and all LC37 clauses for `j₁(D_N)`: closed, `A_{1/8}` in its
interior, inside `{η < 3}`, and `η - 1` a local defining function with `d(η - 1)(X) = 1` at every
frontier point. -/
theorem lc48_exists_core_packet_repair {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [T3Space N] (gN : SmoothRiemannianMetric I N)
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
    {DN : Set N} (hDNc : IsClosed DN)
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆ interior DN)
    (hout : DN ⊆ riemannianBallOf gN n 2)
    {U : Set N} (hU : IsOpen U) (hfrU : frontier DN ⊆ U) (hnU : n ∉ U)
    (V : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) U)
    (hdef : ∀ q ∈ frontier DN, ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ DN ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q))
    {α B : ℝ}
    (hZB : ∀ x ∈ (j : N → M) '' (U ∩ j.source),
      √(g.inner x (modelPushedField j V x) (modelPushedField j V x)) ≤ B)
    (hdir : ∀ x ∈ (j : N → M) '' (U ∩ j.source),
      ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm (j n) x,
        g.inner x (modelPushedField j V x) u ≤ -α)
    (hmargin : ε * B < α) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      ∃ j₁ : PartialDiffeomorph I I N M ∞,
        j₁.source = j.source ∧ (∀ x, j₁ x = Hs 1 (j x)) ∧ j₁ n = j n ∧
        (j₁ : N → M) '' DN = {x | η x ≤ 1} ∧
        IsClosed ((j₁ : N → M) '' DN) ∧ {x | η x ≤ 1 / 8} ⊆ interior ((j₁ : N → M) '' DN) ∧
        (j₁ : N → M) '' DN ⊆ {x | η x < 3} ∧
        ∀ q ∈ frontier ((j₁ : N → M) '' DN), ∃ L : Set M, IsOpen L ∧ q ∈ L ∧ ∃ f : M → ℝ,
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ (j₁ : N → M) '' DN ∩ L = {x | f x ≤ 0} ∩ L ∧
            mvfderiv (I := I) f q
              ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
                gradientFun (I := I) g η q) = 1 := by
  obtain ⟨Hs, h0, hs1, hs2, hsupp, j₁, hj₁s, hj₁, hj₁n, hj₁D⟩ :=
    exists_model_core_packet_repair gN g hEnorm j n hlam0 hlam1 hcpt hsrc hlower hupper hε1 he
      hclose hlip hW hCW hηW hgrad hDNc hin hout hU hfrU hnU V hV hdef hZB hdir hmargin
  have hcl := radialSublevel_lc36_clauses g hε1 he hclose hlip hW hCW hηW hgrad
    (by norm_num : (1 : ℝ) ∈ Ioo (1 / 8 : ℝ) 3)
  rw [← hj₁D] at hcl
  exact ⟨Hs, h0, hs1, hs2, hsupp, j₁, hj₁s, hj₁, hj₁n, hj₁D, hcl⟩

/-- **LC48, model side, in the blueprint's form** (master207A, A:22349). The margins for the
pushed field `Z = (j₀)_* V` are assumed on an OPEN SOURCE collar `Wc ⊆ M \ {j₀ n}` of
`∂ j₀(D_N)` on which `Z` is defined (`Wc ⊆ j₀(O ∩ source)`, `V` smooth on `O`). Conclusion as in
`lc48_exists_core_packet_repair`. -/
theorem lc48_source_collar_packet_repair {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [T3Space N] (gN : SmoothRiemannianMetric I N)
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
    {DN : Set N} (hDNc : IsClosed DN)
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆ interior DN)
    (hout : DN ⊆ riemannianBallOf gN n 2)
    {O : Set N} (hO : IsOpen O) (V : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hdef : ∀ q ∈ frontier DN, ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ DN ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q))
    {Wc : Set M} (hWc : IsOpen Wc) (hfrWc : frontier ((j : N → M) '' DN) ⊆ Wc)
    (hWcO : Wc ⊆ (j : N → M) '' (O ∩ j.source)) (hpWc : j n ∉ Wc)
    {α B : ℝ}
    (hZB : ∀ x ∈ Wc, √(g.inner x (modelPushedField j V x) (modelPushedField j V x)) ≤ B)
    (hdir : ∀ x ∈ Wc, ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm (j n) x,
      g.inner x (modelPushedField j V x) u ≤ -α)
    (hmargin : ε * B < α) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      ∃ j₁ : PartialDiffeomorph I I N M ∞,
        j₁.source = j.source ∧ (∀ x, j₁ x = Hs 1 (j x)) ∧ j₁ n = j n ∧
        (j₁ : N → M) '' DN = {x | η x ≤ 1} ∧
        IsClosed ((j₁ : N → M) '' DN) ∧ {x | η x ≤ 1 / 8} ⊆ interior ((j₁ : N → M) '' DN) ∧
        (j₁ : N → M) '' DN ⊆ {x | η x < 3} ∧
        ∀ q ∈ frontier ((j₁ : N → M) '' DN), ∃ L : Set M, IsOpen L ∧ q ∈ L ∧ ∃ f : M → ℝ,
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ (j₁ : N → M) '' DN ∩ L = {x | f x ≤ 0} ∩ L ∧
            mvfderiv (I := I) f q
              ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
                gradientFun (I := I) g η q) = 1 := by
  have hDN10 : DN ⊆ riemannianClosedBallOf gN n 10 := fun z hz => by
    have h := hout hz
    change riemannianEDistOf gN n z < _ at h
    change riemannianEDistOf gN n z ≤ _
    exact h.le.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hDNs : DN ⊆ j.source := hDN10.trans hsrc
  let U : Set N := O ∩ (j.source ∩ (j : N → M) ⁻¹' Wc)
  have hU : IsOpen U :=
    hO.inter (j.contMDiffOn.continuousOn.isOpen_inter_preimage j.open_source hWc)
  have hfrU : frontier DN ⊆ U := by
    intro x hx
    have hxs : x ∈ j.source := hDNs (hDNc.frontier_subset hx)
    have hjx : j x ∈ Wc := hfrWc (image_frontier_subset_frontier_image j hDNc hDNs ⟨x, hx, rfl⟩)
    obtain ⟨y, ⟨hyO, hys⟩, hyx⟩ := hWcO hjx
    rw [j.injOn hys hxs hyx] at hyO
    exact ⟨hyO, hxs, hjx⟩
  have hnU : n ∉ U := fun h => hpWc h.2.2
  have hUW : ∀ x ∈ (j : N → M) '' (U ∩ j.source), x ∈ Wc := by
    rintro _ ⟨y, ⟨hyU, -⟩, rfl⟩
    exact hyU.2.2
  exact lc48_exists_core_packet_repair gN g hEnorm j n hlam0 hlam1 hcpt hsrc hlower hupper hε1
    he hclose hlip hW hCW hηW hgrad hDNc hin hout hU hfrU hnU V
    (hV.mono inter_subset_left) hdef (fun x hx => hZB x (hUW x hx))
    (fun x hx => hdir x (hUW x hx)) hmargin

end Single

section Sequence

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

/-- **LC51 with the repaired packets** (master207A, A:22607, last sentence; LC48 second
paragraph). On the actual LC50 data and a compact model core `D` with its own outward field `V`
pairing strictly negatively with `𝒰_n` along `∂D`: LC49 fixes `α, B > 0` and an open collar
`W ⊇ ∂D` with the uniform pushed margins on one tail; then for every smoothing tolerance `ε < 1`
with `ε · 2B < α` and selected radial functions `η i` (LC30 clauses on a tail), on one tail the
repaired embeddings `j₁ = H₁ ∘ j i` (same source `univ`, `j₁ n = j i n`) carry `D` onto
`A_{i,1} = {η i ≤ 1}`, and `A_{i,1}` satisfies all LC37 clauses (closed, `A_{i,1/8}` in its
interior, inside `{η i < 3}`, `η i - 1` a frontier defining function with derivative `1` along
`∇η i / |∇η i|²`). -/
theorem lc51_eventually_core_packets
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
      ∀ᶠ i in atTop, ∃ j₁ : PartialDiffeomorph I I U (M i) ∞,
        j₁.source = univ ∧ j₁ n = j i n ∧
        (∃ H₁ : Diffeomorph I I (M i) (M i) ∞, ∀ x, j₁ x = H₁ (j i x)) ∧
        (j₁ : U → M i) '' (Subtype.val ⁻¹' D) = {x | η i x ≤ 1} ∧
        IsClosed {x | η i x ≤ 1} ∧ {x | η i x ≤ 1 / 8} ⊆ interior {x | η i x ≤ 1} ∧
        {x | η i x ≤ 1} ⊆ {x | η i x < 3} ∧
        ∀ q ∈ frontier {x | η i x ≤ 1}, ∃ L : Set (M i), IsOpen L ∧ q ∈ L ∧
          ∃ f : M i → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧
            {x | η i x ≤ 1} ∩ L = {x | f x ≤ 0} ∩ L ∧
            mvfderiv (I := I) f q
              (((gSeq i).inner q (gradientFun (I := I) (gSeq i) (η i) q)
                  (gradientFun (I := I) (gSeq i) (η i) q))⁻¹ •
                gradientFun (I := I) (gSeq i) (η i) q) = 1 := by
  obtain ⟨α, B, hα, hB, W, hW, hfrW, hm, hrest⟩ :=
    exists_collar_constants_core_isotopy g hNorm U n hbuffer hSeq gSeq hSeqNorm j hj hmetric
      hconv hDc hin hout hO hDO V hV hdef hneg
  refine ⟨α, B, hα, hB, W, hW, hfrW, hm, fun ε hε1 hεB η e hη => ?_⟩
  filter_upwards [hrest ε hε1 hεB η e hη, hη] with i hi
    ⟨he, hclose, hlip, Wi, hWi, hCWi, hηWi, hgrad⟩
  obtain ⟨Hs, -, -, -, ⟨S, -, hS, hfix⟩, himg⟩ :=
    hi 1 (⟨by norm_num, by norm_num⟩ : (1 : ℝ) ∈ Icc (1 / 5 : ℝ) 2)
  have hn : η i (j i n) < 1 / 8 := by
    have h := (abs_lt.mp (hclose (j i n))).2
    rw [dist_self, sub_zero] at h
    linarith
  obtain ⟨j₁, hj₁s, hj₁, hj₁n, hj₁D⟩ := exists_packet_of_time_one_core (j i) n (Hs 1) hS
    (fun x hx => (hfix 1 x hx).1) hn himg
  exact ⟨j₁, hj₁s.trans (hj i), hj₁n, ⟨Hs 1, hj₁⟩, hj₁D,
    radialSublevel_lc36_clauses (gSeq i) hε1 he hclose hlip hWi hCWi hηWi hgrad
      (by norm_num : (1 : ℝ) ∈ Ioo (1 / 8 : ℝ) 3)⟩

end Sequence

end DifferentialGeometry.Geometry.Collapse
