import DifferentialGeometry.Geometry.Metric.Comparison.BufferedEmbedding
import DifferentialGeometry.Analysis.InnerProductSpace.BilinearConormalStability
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

/-!
# LC41: finite comparison data produce a transverse core (hypotheses of LC36)

Blueprint LC41 (master207A:21794), with LC39 at `L = 10`, `0 ≤ λ < 1/10`, the LC30 radial
function (`|η - d_p| < e < 1/40`) and a closed model core `D_N` with
`B̄(n, 1/2) ⊆ int D_N`, `D_N ⊆ B(n, 2)`.

* `transverse_core_enclosure`: `{η ≤ 1/8} ⊆ int j(D_N)`, `j(D_N) ⊆ {η < 3}`, and the image of
  the frontier of `D_N` lies in `9/20 < d_p < 11/5` (inside the smooth region of `η`).
* `transverse_core_outward`: at a frontier point `x` of `D_N` with a local defining function `v`
  (`D_N = {v ≤ 0}` near `x`), the conormal closeness `|d(η ∘ j) - dv| ≤ σ |·|` with
  `σ < (1-δ)/(1+δ) m`, `m ≤ |∇v|`, and `(1-δ) g ≤ j^* ĝ ≤ (1+δ) g` at `x` give the local defining
  function `v ∘ j⁻¹` of `j(D_N)` near `j x` with `d(v ∘ j⁻¹)(∇η) > 0` (LC40, gradient naturality).

Together these are every hypothesis of LC36 for `D = j(D_N)` with the field `∇η`
(equivalently `X = ∇η / |∇η|²`). The conclusion "smoothly isotopic to every `A_ρ`" is LC36
itself, supplied by W3-F5b's common-field isotopy.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [T3Space N] in
private theorem edist_eq_riemannianEDistOf' (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x y : M) :
    edist x y = riemannianEDistOf g x y := by
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, IsRiemannianManifold.out (I := I)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M] in
/-- LC41, enclosure part. -/
theorem transverse_core_enclosure (gN : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1 / 10) (hcpt : IsCompact (riemannianClosedBallOf gN n 10))
    (hsrc : riemannianClosedBallOf gN n 10 ⊆ j.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ v : TangentSpace I z,
      (1 - lam) ^ 2 * gN.inner z v v ≤
        g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v))
    (hupper : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ v : TangentSpace I z,
      g.inner (j z) (mfderiv I I (j : N → M) z v) (mfderiv I I (j : N → M) z v) ≤
        (1 + lam) ^ 2 * gN.inner z v v)
    {η : M → ℝ} {e : ℝ} (he : e < 1 / 40) (hclose : ∀ x, |η x - dist (j n) x| < e)
    {DN : Set N} (hDNc : IsClosed DN)
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆ interior DN)
    (hout : DN ⊆ riemannianBallOf gN n 2) :
    {x | η x ≤ 1 / 8} ⊆ interior ((j : N → M) '' DN) ∧
      (j : N → M) '' DN ⊆ {x | η x < 3} ∧
      ∀ x ∈ frontier DN, 9 / 20 < dist (j n) (j x) ∧ dist (j n) (j x) < 11 / 5 := by
  have hm : 0 < 1 - lam := by linarith
  have hball2 : riemannianBallOf gN n 2 ⊆ riemannianBallOf gN n 10 := riemannianBallOf_mono gN n
    (by norm_num)
  have hd : ∀ x, riemannianEDistOf gN n x < ENNReal.ofReal 10 →
      ENNReal.ofReal (1 - lam) * riemannianEDistOf gN n x ≤ ENNReal.ofReal (dist (j n) (j x)) ∧
      ENNReal.ofReal (dist (j n) (j x)) ≤ ENNReal.ofReal (1 + lam) * riemannianEDistOf gN n x := by
    intro x hx
    rw [← edist_dist, edist_eq_riemannianEDistOf' g hEnorm]
    exact ⟨le_riemannianEDistOf_map_of_buffered gN g j n (by linarith) hcpt hsrc hlower hx,
      riemannianEDistOf_map_le_of_buffered gN g j n (by norm_num) hlam0 hsrc hupper hx⟩
  -- distances in `N` as real numbers
  have hfin : ∀ x, riemannianEDistOf gN n x < ENNReal.ofReal 10 →
      riemannianEDistOf gN n x ≠ ⊤ := fun x hx => ne_top_of_lt hx
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hq' : dist (j n) q < 3 / 20 := by
      have := abs_lt.mp (hclose q)
      change η q ≤ 1 / 8 at hq
      linarith [this.1]
    have hcov := riemannianBallOf_subset_image_ball_of_buffered gN g j n (by linarith) hcpt hsrc
      hlower
    have hqball : q ∈ riemannianBallOf g (j n) ((1 - lam) * 10) := by
      change riemannianEDistOf g (j n) q < ENNReal.ofReal ((1 - lam) * 10)
      rw [← edist_eq_riemannianEDistOf' g hEnorm, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mpr (by linarith)
    obtain ⟨x, hx, rfl⟩ := hcov hqball
    have hlow := (hd x hx).1
    have hxhalf : x ∈ riemannianClosedBallOf gN n (1 / 2) := by
      change riemannianEDistOf gN n x ≤ ENNReal.ofReal (1 / 2)
      have hx' := hfin x hx
      rw [← ENNReal.ofReal_toReal hx'] at hlow ⊢
      rw [← ENNReal.ofReal_mul hm.le] at hlow
      have h1 := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hlow
      apply ENNReal.ofReal_le_ofReal
      have h2 : (1 - lam) * (riemannianEDistOf gN n x).toReal < 3 / 20 := lt_of_le_of_lt h1 hq'
      by_contra hc
      push Not at hc
      nlinarith
    have hopen : IsOpen ((j : N → M) '' interior DN) :=
      j.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
        (fun y hy => hsrc ((riemannianClosedBallOf_mono gN n (by norm_num : (2 : ℝ) ≤ 10))
          (by
            have h := hout (interior_subset hy)
            change riemannianEDistOf gN n y < _ at h
            change riemannianEDistOf gN n y ≤ _
            exact h.le)))
    exact interior_maximal (image_mono interior_subset) hopen ⟨x, hin hxhalf, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx2 := hout hx
    have hx10 := hball2 hx2
    have hup := (hd x hx10).2
    have hx' := hfin x hx10
    rw [← ENNReal.ofReal_toReal hx', ← ENNReal.ofReal_mul (by linarith)] at hup
    have h1 := (ENNReal.ofReal_le_ofReal_iff (by
      have := ENNReal.toReal_nonneg (a := riemannianEDistOf gN n x); nlinarith)).mp hup
    have h2 : (riemannianEDistOf gN n x).toReal < 2 := by
      have := (ENNReal.toReal_lt_toReal hx' ENNReal.ofReal_ne_top).mpr hx2
      rwa [ENNReal.toReal_ofReal (by norm_num)] at this
    have h3 := abs_lt.mp (hclose (j x))
    change η (j x) < 3
    have h0 := ENNReal.toReal_nonneg (a := riemannianEDistOf gN n x)
    nlinarith
  · intro x hx
    have hxD : x ∈ DN := hDNc.frontier_subset hx
    have hx2 := hout hxD
    have hx10 := hball2 hx2
    have hx' := hfin x hx10
    have hgt : 1 / 2 < (riemannianEDistOf gN n x).toReal := by
      by_contra hc
      push Not at hc
      have hxin : x ∈ riemannianClosedBallOf gN n (1 / 2) := by
        change riemannianEDistOf gN n x ≤ ENNReal.ofReal (1 / 2)
        rw [← ENNReal.ofReal_toReal hx']
        exact ENNReal.ofReal_le_ofReal hc
      exact hx.2 (hin hxin)
    have hlt : (riemannianEDistOf gN n x).toReal < 2 := by
      have := (ENNReal.toReal_lt_toReal hx' ENNReal.ofReal_ne_top).mpr hx2
      rwa [ENNReal.toReal_ofReal (by norm_num)] at this
    obtain ⟨hlow, hup⟩ := hd x hx10
    rw [← ENNReal.ofReal_toReal hx', ← ENNReal.ofReal_mul hm.le] at hlow
    rw [← ENNReal.ofReal_toReal hx', ← ENNReal.ofReal_mul (by linarith)] at hup
    have h1 := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hlow
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).mp hup
    constructor <;> nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M]
  [T3Space N] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- LC41, outward part: the local defining function `v ∘ j⁻¹` of `j(D_N)` has positive
derivative along `∇η` at `j x`. -/
theorem transverse_core_outward (gN : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric I M) (j : PartialDiffeomorph I I N M ∞) {DN : Set N}
    (hDNsrc : DN ⊆ j.source) {x : N} (hxs : x ∈ j.source) {U : Set N} (hU : IsOpen U)
    (hxU : x ∈ U) {v : N → ℝ} (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v U)
    (hdef : DN ∩ U = {z | v z ≤ 0} ∩ U) {η : M → ℝ}
    (hη : MDifferentiableAt I 𝓘(ℝ, ℝ) η (j x)) {δ σ m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlowδ : ∀ w : TangentSpace I x, (1 - δ) * gN.inner x w w ≤
      g.inner (j x) (mfderiv I I (j : N → M) x w) (mfderiv I I (j : N → M) x w))
    (hupδ : ∀ w : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x w) (mfderiv I I (j : N → M) x w) ≤
        (1 + δ) * gN.inner x w w)
    (hmpos : 0 < m) (hmv : m ≤ √(gN.inner x (gradientFun (I := I) gN v x)
      (gradientFun (I := I) gN v x)))
    (herror : ∀ w : TangentSpace I x,
      |mvfderiv (I := I) (fun z => η (j z)) x w - mvfderiv (I := I) v x w| ≤
        σ * √(gN.inner x w w))
    (hbudget : σ < (1 - δ) / (1 + δ) * m) :
    ∃ U' : Set M, IsOpen U' ∧ j x ∈ U' ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => v (j.symm y)) U' ∧
      ((j : N → M) '' DN) ∩ U' = {y | v (j.symm y) ≤ 0} ∩ U' ∧
      0 < mvfderiv (I := I) (fun y => v (j.symm y)) (j x) (gradientFun (I := I) g η (j x)) := by
  set U' : Set M := (j : N → M) '' (U ∩ j.source) with hU'def
  have hU'o : IsOpen U' :=
    j.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hU.inter j.open_source)
      inter_subset_right
  have hU'tgt : U' ⊆ j.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact j.map_source' hz.2
  have hjx : j x ∈ U' := ⟨x, ⟨hxU, hxs⟩, rfl⟩
  have hli : ∀ z ∈ j.source, (j.symm : M → N) (j z) = z := fun z hz => j.left_inv hz
  have hsymmU : ∀ y ∈ U', j.symm y ∈ U ∧ j.symm y ∈ j.source := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hli z hz.2]
    exact hz
  -- smoothness of `v ∘ j⁻¹` on `U'`
  have hsm : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => v (j.symm y)) U' := by
    intro y hy
    have hyt := hU'tgt hy
    have h1 : ContMDiffAt I I ∞ (j.symm : M → N) y :=
      (j.contMDiffOn_invFun y hyt).contMDiffAt (j.open_target.mem_nhds hyt)
    have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ v (j.symm y) :=
      hv.contMDiffAt (hU.mem_nhds (hsymmU y hy).1)
    exact (h2.comp y h1).contMDiffWithinAt
  -- the set identity
  have hset : ((j : N → M) '' DN) ∩ U' = {y | v (j.symm y) ≤ 0} ∩ U' := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      have hzU : z ∈ U := by
        obtain ⟨z', hz', hz'eq⟩ := hy
        have := j.injOn hz'.2 (hDNsrc hz) hz'eq
        rw [← this]; exact hz'.1
      refine ⟨?_, hy⟩
      change v (j.symm (j z)) ≤ 0
      rw [hli z (hDNsrc hz)]
      have hmem : z ∈ {z | v z ≤ 0} ∩ U := by rw [← hdef]; exact ⟨hz, hzU⟩
      exact hmem.1
    · rintro ⟨hy, hyU⟩
      obtain ⟨hzU, hzs⟩ := hsymmU y hyU
      have hzD : j.symm y ∈ DN := by
        have hmem : j.symm y ∈ DN ∩ U := by rw [hdef]; exact ⟨hy, hzU⟩
        exact hmem.1
      exact ⟨⟨j.symm y, hzD, j.right_inv (hU'tgt hyU)⟩, hyU⟩
  refine ⟨U', hU'o, hjx, hsm, hset, ?_⟩
  -- the derivative computation
  have hjxt : j x ∈ j.target := j.map_source' hxs
  have hjd : MDifferentiableAt I I (j : N → M) x :=
    ((j.contMDiffOn_toFun x hxs).contMDiffAt (j.open_source.mem_nhds hxs)).mdifferentiableAt
      (by simp)
  have hjsd : MDifferentiableAt I I (j.symm : M → N) (j x) :=
    ((j.contMDiffOn_invFun (j x) hjxt).contMDiffAt
      (j.open_target.mem_nhds hjxt)).mdifferentiableAt (by simp)
  have hvd : MDifferentiableAt I 𝓘(ℝ, ℝ) v x :=
    (hv.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hjsx : j.symm (j x) = x := j.left_inv hxs
  set G := gradientFun (I := I) g η (j x) with hGdef
  set w : TangentSpace I x := mfderiv I I (j.symm : M → N) (j x) G with hwdef
  have hchain0 : mfderiv I I (j : N → M) (j.symm (j x))
      (mfderiv I I (j.symm : M → N) (j x) G) = G := by
    have heq : (j : N → M) ∘ (j.symm : M → N) =ᶠ[𝓝 (j x)] id := by
      filter_upwards [j.open_target.mem_nhds hjxt] with q hq
      exact j.right_inv hq
    have hh := (mfderiv_comp (j x) (by rw [hjsx]; exact hjd) hjsd).symm.trans heq.mfderiv_eq
    have hw := DFunLike.congr_fun hh G
    simp only [mfderiv_id] at hw
    exact hw
  have hchain : mfderiv I I (j : N → M) x w = G := by
    have h0 := hchain0
    rwa [hjsx] at h0
  -- the two covectors
  let β : TangentSpace I x →L[ℝ] ℝ := mvfderiv (I := I) v x
  let ξ : TangentSpace I x →L[ℝ] ℝ := mvfderiv (I := I) (fun z => η (j z)) x
  let Hf : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    ((g.inner (j x) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (mfderiv I I (j : N → M) x : E →L[ℝ] E) (mfderiv I I (j : N → M) x : E →L[ℝ] E) :
      E →L[ℝ] E →L[ℝ] ℝ)
  have hHf : ∀ a c, Hf a c =
      g.inner (j x) (mfderiv I I (j : N → M) x a) (mfderiv I I (j : N → M) x c) := fun _ _ => rfl
  have hξ : ∀ c, ξ c = mvfderiv (I := I) η (j x) (mfderiv I I (j : N → M) x c) := by
    intro c
    change NormedSpace.fromTangentSpace (η (j x)) (mfderiv I 𝓘(ℝ, ℝ) (η ∘ (j : N → M)) x c) =
      NormedSpace.fromTangentSpace (η (j x)) (mfderiv I 𝓘(ℝ, ℝ) η (j x)
        (mfderiv I I (j : N → M) x c))
    rw [mfderiv_comp x hη hjd]
    rfl
  have hw : Hf w = ξ := by
    ext c
    rw [hHf, hchain, hξ, hGdef, inner_gradientFun]
  have hb : gN.inner x (gradientFun (I := I) gN v x) = β := by
    ext c
    exact inner_gradientFun (I := I) gN v x c
  have hpos := SmoothRiemannianMetric.conormal_apply_pos gN x Hf
    (fun a c => by rw [hHf, hHf, g.symm]) hδ hδ1 (fun c => by rw [hHf]; exact hlowδ c)
    (fun c => by rw [hHf]; exact hupδ c) β ξ hb hw hmpos hmv (fun c => herror c) hbudget
  -- `β w` is the derivative of `v ∘ j⁻¹` along `∇η`
  have hfinal : mvfderiv (I := I) (fun y => v (j.symm y)) (j x) G = β w := by
    change NormedSpace.fromTangentSpace (v (j.symm (j x)))
        (mfderiv I 𝓘(ℝ, ℝ) (v ∘ (j.symm : M → N)) (j x) G) =
      NormedSpace.fromTangentSpace (v x) (mfderiv I 𝓘(ℝ, ℝ) v x w)
    rw [mfderiv_comp (j x) (by rw [hjsx]; exact hvd) hjsd]
    have key : ∀ y : N, y = x → ∀ L : TangentSpace I (j x) →L[ℝ] TangentSpace I y,
        NormedSpace.fromTangentSpace (v y) (((mfderiv I 𝓘(ℝ, ℝ) v y).comp L) G) =
          NormedSpace.fromTangentSpace (v x) (mfderiv I 𝓘(ℝ, ℝ) v x (L G)) := by
      intro y hy L
      subst hy
      rfl
    exact key _ hjsx _
  rw [hfinal]
  exact hpos

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

/-- LC42, constants: the eventual metric bound with `δ = 1/10` gives the LC39 bounds with
`λ = 1/16`, and the boundary budget `σ = m/4` is admissible for `δ = 1/10`. -/
theorem eventual_transfer_constants {G Hq m : ℝ} (hG : 0 ≤ G) (hm : 0 < m)
    (hlow : (1 - 1 / 10) * G ≤ Hq) (hup : Hq ≤ (1 + 1 / 10) * G) :
    (1 - 1 / 16) ^ 2 * G ≤ Hq ∧ Hq ≤ (1 + 1 / 16) ^ 2 * G ∧
      m / 4 < (1 - 1 / 10) / (1 + 1 / 10) * m := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- LC42: one fixed model core transfers on one common tail. If the pullback metrics converge
uniformly to the model metric on `B̄(n, 10)` (relative error `ε_i → 0`) and the boundary
differential error is eventually at most `m/4`, then eventually `j_i(D_N)` satisfies every
hypothesis of LC36: enclosure between `{η_i ≤ 1/8}` and `{η_i < 3}`, frontier image in the
smooth region, and the local defining function `v ∘ j_i⁻¹` with positive derivative along
`∇η_i`. -/
theorem eventually_transverse_core (gN : SmoothRiemannianMetric I N)
    (g : ∀ i, SmoothRiemannianMetric I (M i)) (hEnorm : ∀ i, IsMetricNorm (I := I) (g i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞) (n : N)
    (hcpt : IsCompact (riemannianClosedBallOf gN n 10))
    (hsrc : ∀ i, riemannianClosedBallOf gN n 10 ⊆ (j i).source)
    {εs : ℕ → ℝ} (hεs : Tendsto εs atTop (𝓝 0))
    (hconv : ∀ i, ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ v : TangentSpace I z,
      |(g i).inner (j i z) (mfderiv I I (j i : N → M i) z v) (mfderiv I I (j i : N → M i) z v) -
        gN.inner z v v| ≤ εs i * gN.inner z v v)
    {η : ∀ i, M i → ℝ} {e : ℝ} (he : e < 1 / 40)
    (hclose : ∀ i x, |η i x - dist (j i n) x| < e)
    {DN : Set N} (hDNc : IsClosed DN)
    (hηd : ∀ i, ∀ x ∈ frontier DN, MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i x))
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆ interior DN)
    (hout : DN ⊆ riemannianBallOf gN n 2)
    {U : Set N} (hU : IsOpen U) (hfrU : frontier DN ⊆ U) {v : N → ℝ}
    (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v U) (hdef : DN ∩ U = {z | v z ≤ 0} ∩ U) {m : ℝ}
    (hm : 0 < m)
    (hmv : ∀ x ∈ frontier DN,
      m ≤ √(gN.inner x (gradientFun (I := I) gN v x) (gradientFun (I := I) gN v x)))
    (hdiff : ∀ᶠ i in atTop, ∀ x ∈ frontier DN, ∀ w : TangentSpace I x,
      |mvfderiv (I := I) (fun z => η i (j i z)) x w - mvfderiv (I := I) v x w| ≤
        m / 4 * √(gN.inner x w w)) :
    ∀ᶠ i in atTop,
      ({x | η i x ≤ 1 / 8} ⊆ interior ((j i : N → M i) '' DN) ∧
        (j i : N → M i) '' DN ⊆ {x | η i x < 3} ∧
        ∀ x ∈ frontier DN, 9 / 20 < dist (j i n) (j i x) ∧ dist (j i n) (j i x) < 11 / 5) ∧
      ∀ x ∈ frontier DN, ∃ U' : Set (M i), IsOpen U' ∧ j i x ∈ U' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => v ((j i).symm y)) U' ∧
        ((j i : N → M i) '' DN) ∩ U' = {y | v ((j i).symm y) ≤ 0} ∩ U' ∧
        0 < mvfderiv (I := I) (fun y => v ((j i).symm y)) (j i x)
          (gradientFun (I := I) (g i) (η i) (j i x)) := by
  have hDN10 : DN ⊆ riemannianClosedBallOf gN n 10 := fun z hz => by
    have h := hout hz
    change riemannianEDistOf gN n z < _ at h
    change riemannianEDistOf gN n z ≤ _
    exact h.le.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hfr10 : ∀ x ∈ frontier DN, x ∈ riemannianClosedBallOf gN n 10 := fun x hx =>
    hDN10 (hDNc.frontier_subset hx)
  filter_upwards [hεs.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)), hdiff]
    with i hi hdi
  have hb : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ w : TangentSpace I z,
      (1 - 1 / 10) * gN.inner z w w ≤
        (g i).inner (j i z) (mfderiv I I (j i : N → M i) z w) (mfderiv I I (j i : N → M i) z w) ∧
      (g i).inner (j i z) (mfderiv I I (j i : N → M i) z w) (mfderiv I I (j i : N → M i) z w) ≤
        (1 + 1 / 10) * gN.inner z w w := by
    intro z hz w
    have h := abs_le.mp (hconv i z hz w)
    have hG := metric_inner_self_nonneg gN z w
    have : εs i * gN.inner z w w ≤ 1 / 10 * gN.inner z w w := mul_le_mul_of_nonneg_right hi hG
    constructor <;> linarith [h.1, h.2]
  have hconst : ∀ z ∈ riemannianClosedBallOf gN n 10, ∀ w : TangentSpace I z,
      (1 - 1 / 16) ^ 2 * gN.inner z w w ≤
        (g i).inner (j i z) (mfderiv I I (j i : N → M i) z w) (mfderiv I I (j i : N → M i) z w) ∧
      (g i).inner (j i z) (mfderiv I I (j i : N → M i) z w) (mfderiv I I (j i : N → M i) z w) ≤
        (1 + 1 / 16) ^ 2 * gN.inner z w w := fun z hz w =>
    let h := eventual_transfer_constants (metric_inner_self_nonneg gN z w) hm (hb z hz w).1
      (hb z hz w).2
    ⟨h.1, h.2.1⟩
  refine ⟨transverse_core_enclosure gN (g i) (hEnorm i) (j i) n (by norm_num) (by norm_num) hcpt
    (hsrc i) (fun z hz w => (hconst z hz w).1) (fun z hz w => (hconst z hz w).2) he
    (hclose i) hDNc hin hout, fun x hx => ?_⟩
  exact transverse_core_outward gN (g i) (j i) (hDN10.trans (hsrc i)) (hsrc i (hfr10 x hx)) hU
    (hfrU hx) hv hdef (hηd i x hx) (by norm_num) (by norm_num)
    (fun w => (hb x (hfr10 x hx) w).1) (fun w => (hb x (hfr10 x hx) w).2) hm (hmv x hx)
    (hdi x hx) (by norm_num; linarith)

end DifferentialGeometry.Geometry.Collapse
