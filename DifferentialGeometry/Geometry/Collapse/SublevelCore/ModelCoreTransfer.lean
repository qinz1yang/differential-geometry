import DifferentialGeometry.Geometry.Collapse.SublevelCore.CollarFieldTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.TransverseCore
import DifferentialGeometry.Topology.VectorField.Pushforward
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# Model fields and defining functions under a partial diffeomorphism

The actual model field is transported using the inverse partial diffeomorphism. Its
smoothness and strict outward derivative are retained on the image of the model collar.
Buffered metric comparison then supplies the whole core isotopy. Postcomposition at time
one repairs the pointed embedding on exactly its original source, keeping the selected radial
function and original comparison embedding available.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

def modelPushedField (j : PartialDiffeomorph I I N M ∞)
    (V : (x : N) → TangentSpace I x) (y : M) : TangentSpace I y :=
  _root_.VectorField.mpullback I I j.symm V y

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem modelPushedField_apply (j : PartialDiffeomorph I I N M ∞)
    (V : (x : N) → TangentSpace I x) {x : N} (hx : x ∈ j.source) :
    modelPushedField j V (j x) = mfderiv I I j x (V x) := by
  exact DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply
    j (by simp) V hx

theorem modelPushedField_contMDiffOn (j : PartialDiffeomorph I I N M ∞)
    (V : (x : N) → TangentSpace I x) {U : Set N} (hU : IsOpen U)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) U) :
    ContMDiffOn I I.tangent ∞
      (fun y => (⟨y, modelPushedField j V y⟩ : TangentBundle I M))
      ((j : N → M) '' (U ∩ j.source)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have ht := j.map_source hx.2
  have hf := j.symm.contMDiffOn.contMDiffAt (j.open_target.mem_nhds ht)
  have hv := hV.contMDiffAt (hU.mem_nhds hx.1)
  have hv' : ContMDiffAt I I.tangent ∞
      (fun z => (⟨z, V z⟩ : TangentBundle I N)) (j.symm (j x)) := by
    erw [j.left_inv hx.2]
    exact hv
  exact (hv'.mpullback_vectorField_preimage hf
    (DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph j.symm (by simp) ht)
    (by simp)).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem model_defining_function_pushforward (j : PartialDiffeomorph I I N M ∞)
    (V : (x : N) → TangentSpace I x) {DN : Set N} (hDN : DN ⊆ j.source)
    {x : N} (hxs : x ∈ j.source) {U : Set N} (hU : IsOpen U) (hxU : x ∈ U)
    {v : N → ℝ} (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v U)
    (hdef : DN ∩ U = {z | v z ≤ 0} ∩ U) (hout : 0 < mvfderiv (I := I) v x (V x)) :
    ∃ U' : Set M, IsOpen U' ∧ j x ∈ U' ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => v (j.symm y)) U' ∧
      ((j : N → M) '' DN) ∩ U' = {y | v (j.symm y) ≤ 0} ∩ U' ∧
      0 < mvfderiv (I := I) (fun y => v (j.symm y)) (j x)
        (modelPushedField j V (j x)) := by
  let U' : Set M := (j : N → M) '' (U ∩ j.source)
  have ho : IsOpen U' :=
    j.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hU.inter j.open_source)
      inter_subset_right
  have ht : U' ⊆ j.target := by
    rintro y ⟨z, hz, rfl⟩
    exact j.map_source hz.2
  have hi : ∀ y ∈ U', j.symm y ∈ U ∩ j.source := by
    rintro y ⟨z, hz, rfl⟩
    erw [j.left_inv hz.2]
    exact hz
  have hs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => v (j.symm y)) U' := by
    intro y hy
    exact ((hv.contMDiffAt (hU.mem_nhds (hi y hy).1)).comp y
      (j.symm.contMDiffOn.contMDiffAt (j.open_target.mem_nhds (ht hy)))).contMDiffWithinAt
  have heq : ((j : N → M) '' DN) ∩ U' = {y | v (j.symm y) ≤ 0} ∩ U' := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      have hzU : z ∈ U := by
        have hiU := (hi (j z) hy).1
        erw [j.left_inv (hDN hz)] at hiU
        exact hiU
      refine ⟨?_, hy⟩
      change v (j.symm (j z)) ≤ 0
      erw [j.left_inv (hDN hz)]
      have hzv : z ∈ {z | v z ≤ 0} ∩ U := by
        rw [← hdef]
        exact ⟨hz, hzU⟩
      exact hzv.1
    · rintro ⟨hy, hyU⟩
      have hzD : j.symm y ∈ DN := by
        have hmem : j.symm y ∈ DN ∩ U := by
          rw [hdef]
          exact ⟨hy, (hi y hyU).1⟩
        exact hmem.1
      exact ⟨⟨j.symm y, hzD, j.right_inv (ht hyU)⟩, hyU⟩
  refine ⟨U', ho, ⟨x, ⟨hxU, hxs⟩, rfl⟩, hs, heq, ?_⟩
  have hvd := (hv.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hjs := j.symm.mdifferentiableAt (by simp) (j.map_source hxs)
  have hvd' : MDifferentiableAt I 𝓘(ℝ, ℝ) v (j.symm (j x)) := by
    erw [j.left_inv hxs]
    exact hvd
  have hchain : (fun z => v (j.symm (j z))) =ᶠ[𝓝 x] v :=
    Filter.eventuallyEq_of_mem (j.open_source.mem_nhds hxs)
      (fun z hz => congrArg v (j.left_inv hz))
  have hd := mvfderiv_comp x (hvd'.comp (j x) hjs)
    (j.mdifferentiableAt (by simp) hxs)
  have hscalar : mvfderiv (I := I) (fun z => v (j.symm (j z))) x =
      mvfderiv (I := I) v x := by
    unfold mvfderiv
    rw [hchain.mfderiv_eq]
    rfl
  have hval := DFunLike.congr_fun (hd.symm.trans hscalar) (V x)
  rw [modelPushedField_apply j V hxs]
  change 0 < mvfderiv (I := I) (fun y => v (j.symm y)) (j x)
    (mfderiv I I j x (V x))
  change mvfderiv (I := I) (fun y => v (j.symm y)) (j x)
    (mfderiv I I j x (V x)) = mvfderiv (I := I) v x (V x) at hval
  rw [hval]
  exact hout

end Transport

section Riemannian

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_model_core_collar_isotopy (gN : SmoothRiemannianMetric I N)
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
    (hmargin : ε * B < α) {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' ((j : N → M) '' DN) = {x | η x ≤ ρ} := by
  have hDN10 : DN ⊆ riemannianClosedBallOf gN n 10 := fun z hz => by
    have h := hout hz
    change riemannianEDistOf gN n z < _ at h
    change riemannianEDistOf gN n z ≤ _
    exact h.le.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hDNsrc : DN ⊆ j.source := hDN10.trans hsrc
  have hnc : n ∈ j.source := hsrc (by
    change riemannianEDistOf gN n n ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le)
  have hcompact := hcpt.of_isClosed_subset hDNc hDN10
  obtain ⟨hAD, hDb, hfrdist⟩ := transverse_core_enclosure gN g hEnorm j n hlam0 hlam1
    hcpt hsrc hlower hupper he hclose hDNc hin hout
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist (j n) x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hann := radialBand_subset_annulus hclose he
  have hKC : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3,
      1 / 10 ≤ dist (j n) x ∧ dist (j n) x ≤ 10 := fun x hx =>
    ⟨(hann hx).1.le, (hann hx).2.le⟩
  have hKW : η ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ W := fun x hx =>
    hCW x (hKC x hx).1 (hKC x hx).2
  have hpos : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3,
      0 < g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := by
    intro x hx
    have hm : 0 < 1 - (ε : ℝ) := by linarith
    exact lt_of_lt_of_le (sq_pos_of_pos hm) (hgrad x (hKC x hx).1 (hKC x hx).2)
  have hjclosed : IsClosed ((j : N → M) '' DN) :=
    (hcompact.image_of_continuousOn (j.contMDiffOn.continuousOn.mono hDNsrc)).isClosed
  have hfr : frontier ((j : N → M) '' DN) ⊆ (j : N → M) '' (U ∩ j.source) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := frontier_image_subset_image_frontier j hcompact hDNsrc hq
    exact ⟨x, ⟨hfrU hx, hDNsrc (hDNc.frontier_subset hx)⟩, rfl⟩
  have hnot : j n ∉ (j : N → M) '' (U ∩ j.source) := by
    rintro ⟨x, hx, heq⟩
    have he : x = n := j.injOn hx.2 hnc heq
    exact hnU (he ▸ hx.1)
  have hdeff : ∀ q ∈ frontier ((j : N → M) '' DN), ∃ L : Set M,
      IsOpen L ∧ q ∈ L ∧ ∃ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧
        ((j : N → M) '' DN) ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (modelPushedField j V q) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := frontier_image_subset_image_frontier j hcompact hDNsrc hq
    obtain ⟨L, hL, hxL, f, hf, hLf, hfv⟩ := hdef x hx
    obtain ⟨L', hL', hjL', hf', hset, hpos'⟩ := model_defining_function_pushforward j V
      hDNsrc (hDNsrc (hDNc.frontier_subset hx)) hL hxL hf hLf hfv
    exact ⟨L', hL', hjL', fun y => f (j.symm y), hf', hset, hpos'⟩
  exact exists_isotopy_of_collar_direction_margin g hEnorm hη hW hηW
    (⟨by linarith [hρ.1], by linarith [hρ.2]⟩ : ρ ∈ Ioo (1 / 8 : ℝ) 3)
    hK hKW hpos hlip hjclosed hAD hDb
    (j.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hU.inter j.open_source)
      inter_subset_right) hfr hnot (modelPushedField j V)
    (modelPushedField_contMDiffOn j V hU hV) hZB hdir hmargin hdeff

theorem exists_model_core_packet_repair (gN : SmoothRiemannianMetric I N)
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
      ∃ j1 : PartialDiffeomorph I I N M ∞,
        j1.source = j.source ∧ (∀ x, j1 x = Hs 1 (j x)) ∧
        j1 n = j n ∧ (j1 : N → M) '' DN = {x | η x ≤ 1} := by
  obtain ⟨Hs, hzero, hforward, hback, hsupport, hcore⟩ :=
    exists_model_core_collar_isotopy gN g hEnorm j n hlam0 hlam1 hcpt hsrc hlower hupper
      hε1 he hclose hlip hW hCW hηW hgrad hDNc hin hout hU hfrU hnU V hV hdef hZB hdir
      hmargin (by norm_num : (1 : ℝ) ∈ Icc (1 / 5 : ℝ) 2)
  let j1 := j.trans (Hs 1).toPartialDiffeomorph
  have hj1 : ∀ x, j1 x = Hs 1 (j x) := fun x => rfl
  have hfixed : Hs 1 (j n) = j n := by
    obtain ⟨S, hSc, hSband, hSfix⟩ := hsupport
    have hnsmall : η (j n) < 1 / 8 := by
      have hc := (abs_lt.mp (hclose (j n))).2
      simp only [dist_self, sub_zero] at hc
      linarith
    have hnS : j n ∉ S := fun h => (not_lt_of_ge hnsmall.le) (hSband h).1
    exact (hSfix 1 (j n) hnS).1
  refine ⟨Hs, hzero, hforward, hback, hsupport, j1, ?_, hj1, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    change j.source ∩ (j : N → M) ⁻¹' univ = j.source
    simp only [preimage_univ, inter_univ]
  · rw [hj1, hfixed]
  · change ((Hs 1) ∘ (j : N → M)) '' DN = {x | η x ≤ 1}
    exact (image_image (Hs 1) (j : N → M) DN).symm.trans hcore

end Riemannian

def realDoubleModel : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 (2 : ℝ) (by norm_num))).toDiffeomorph.toPartialDiffeomorph

theorem exists_realDoubleModel_outward_neighborhood :
    ∃ U : Set ℝ, IsOpen U ∧ 2 ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun y => realDoubleModel.symm y - 1) U ∧
      ((realDoubleModel : ℝ → ℝ) '' Iic 1) ∩ U =
        {y | realDoubleModel.symm y - 1 ≤ 0} ∩ U ∧
      0 < mvfderiv (I := 𝓘(ℝ, ℝ)) (fun y => realDoubleModel.symm y - 1) 2
        (modelPushedField realDoubleModel
          (fun x => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1) 2) := by
  have hdef : Iic (1 : ℝ) ∩ univ = {x : ℝ | x - 1 ≤ 0} ∩ univ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_univ, and_true, mem_ofPred_eq]
    exact sub_nonpos.symm
  have hout : 0 < mvfderiv (I := 𝓘(ℝ, ℝ)) (fun x : ℝ => x - 1) 1
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (1 : ℝ)).symm 1) := by
    rw [mvfderiv_eq_fderiv]
    simp
  have htwo : realDoubleModel (1 : ℝ) = 2 := by
    change (2 : ℝ) • (1 : ℝ) = 2
    norm_num
  have hs : realDoubleModel.source = univ := rfl
  have hc := model_defining_function_pushforward realDoubleModel
    (fun x => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1) (DN := Iic 1)
    (by rw [hs]; exact subset_univ _)
    (x := 1) (by rw [hs]; exact mem_univ _) isOpen_univ (mem_univ 1)
    (contMDiff_id.sub contMDiff_const).contMDiffOn hdef hout
  erw [htwo] at hc
  simpa only [id_eq] using hc

end DifferentialGeometry.Geometry.Collapse
