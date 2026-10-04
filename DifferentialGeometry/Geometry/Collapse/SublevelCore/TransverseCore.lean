import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CoreTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ProperSublevel
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

/-!
# LC36 and the isotopy clauses of LC38 (noncompact alternative) and LC41

* `radial_core_isotopy_of_transverse` (LC36, master207A:21573): a closed domain `D` with
  `{η ≤ 1/8} ⊆ int D`, `D ⊆ {η < 3}` and a local defining function at each frontier point with
  positive derivative along `X = ∇η / |∇η|²` is carried onto every `A_ρ`, `ρ ∈ [1/5, 2]`, by a
  smooth ambient isotopy supported in one compact subset of `η⁻¹(1/8, 3)`. This is the instance
  `Y = ∇η` of W3-F5b's common-field isotopy (LC47, `CommonFieldCore.lean`); the crossing count
  and the smooth height are proved there.
* `frontier_image_subset_image_frontier`: the frontier of `j(D)` is the image of the frontier of
  `D` for a compact `D` inside the source of a partial diffeomorphism.
* `transverse_core_isotopy` (LC41 full, and LC38's comparison for the noncompact alternative):
  LC39-type metric bounds at `L = 10`, the LC30 radial function and the conormal closeness on the
  frontier of a model core `D_N` give an ambient isotopy carrying `j(D_N)` onto every `A_ρ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC36, binding form (PC setting, LC30 radial function, LC32 constants `a = 1/8`, `b = 3`). -/
theorem radial_core_isotopy_of_transverse (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {D : Set M} (hD : IsClosed D) (hAD : {x | η x ≤ 1 / 8} ⊆ interior D)
    (hDb : D ⊆ {x | η x < 3})
    (hdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q
          ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
            gradientFun (I := I) g η q))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' D = {x | η x ≤ ρ} := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  have hKC : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3, 1 / 10 ≤ dist p x ∧ dist p x ≤ 10 := fun x hx =>
    ⟨(hKann hx).1.le, (hKann hx).2.le⟩
  have hKW : η ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ W := fun x hx => hCW x (hKC x hx).1 (hKC x hx).2
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  have hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, gradientFun (I := I) g η x⟩ : TangentBundle I M)) W := fun x hx =>
    (gradientFun_contMDiffAt (I := I) g (hηW.contMDiffAt (hW.mem_nhds hx))).contMDiffWithinAt
  have hnormpos : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3,
      0 < g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := fun x hx =>
    lt_of_lt_of_le (by positivity) (hgrad x (hKC x hx).1 (hKC x hx).2)
  have hpos : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3,
      0 < mvfderiv (I := I) η x (gradientFun (I := I) g η x) := by
    intro x hx
    rw [← inner_gradientFun (I := I) g η x]
    exact hnormpos x hx
  have hdef' : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (gradientFun (I := I) g η q) := by
    intro q hq
    obtain ⟨U, hU, hqU, f, hf, hDU, hd⟩ := hdef q hq
    refine ⟨U, hU, hqU, f, hf, hDU, ?_⟩
    have hqD : q ∈ D := hD.frontier_subset hq
    have hqK : q ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3 := by
      refine ⟨?_, (hDb hqD).le⟩
      by_contra hlt
      exact hq.2 (hAD (le_of_lt (not_le.mp hlt)))
    rw [map_smul, smul_eq_mul] at hd
    exact pos_of_mul_pos_right hd (inv_pos.mpr (hnormpos q hqK)).le
  exact exists_isotopy_of_common_outward_field hη hW hηW
    (⟨by linarith [hρ.1], by linarith [hρ.2]⟩ : ρ ∈ Ioo (1 / 8 : ℝ) 3) hK hKW
    (gradientFun (I := I) g η) hY hpos hD hAD hDb hdef'

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The frontier of the image of a compact set inside the source of a partial diffeomorphism is
the image of its frontier. -/
theorem frontier_image_subset_image_frontier {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] (j : PartialDiffeomorph I I N M ∞) {DN : Set N} (hDNc : IsCompact DN)
    (hDNs : DN ⊆ j.source) : frontier ((j : N → M) '' DN) ⊆ (j : N → M) '' frontier DN := by
  intro q hq
  have hcont : ContinuousOn (j : N → M) j.source := j.contMDiffOn_toFun.continuousOn
  have hcl : IsClosed ((j : N → M) '' DN) :=
    (hDNc.image_of_continuousOn (hcont.mono hDNs)).isClosed
  obtain ⟨x, hx, rfl⟩ := hcl.frontier_subset hq
  refine ⟨x, ⟨subset_closure hx, fun hxi => hq.2 ?_⟩, rfl⟩
  have hopen : IsOpen ((j : N → M) '' interior DN) :=
    j.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (interior_subset.trans hDNs)
  exact interior_maximal (image_mono interior_subset) hopen ⟨x, hxi, rfl⟩

/-- LC41 (full) and LC38's sublevel comparison for the noncompact alternative: finite comparison
data at scale `L = 10` with `0 ≤ λ < 1/10`, the LC30 radial function, and conormal closeness on
the frontier of a closed model core `D_N` with `B̄(n, 1/2) ⊆ int D_N`, `D_N ⊆ B(n, 2)` give an
ambient isotopy carrying `j(D_N)` onto every `A_ρ`, `ρ ∈ [1/5, 2]`. -/
theorem transverse_core_isotopy {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [T3Space N] (gN : SmoothRiemannianMetric I N)
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
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist (j n) x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist (j n) x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist (j n) x → dist (j n) x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist (j n) x → dist (j n) x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {DN : Set N} (hDNc : IsClosed DN)
    (hin : riemannianClosedBallOf gN n (1 / 2) ⊆ interior DN)
    (hout : DN ⊆ riemannianBallOf gN n 2)
    {U : Set N} (hU : IsOpen U) (hfrU : frontier DN ⊆ U) {v : N → ℝ}
    (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v U) (hdefN : DN ∩ U = {z | v z ≤ 0} ∩ U)
    {δ σ m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlowδ : ∀ x ∈ frontier DN, ∀ w : TangentSpace I x, (1 - δ) * gN.inner x w w ≤
      g.inner (j x) (mfderiv I I (j : N → M) x w) (mfderiv I I (j : N → M) x w))
    (hupδ : ∀ x ∈ frontier DN, ∀ w : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x w) (mfderiv I I (j : N → M) x w) ≤
        (1 + δ) * gN.inner x w w)
    (hmpos : 0 < m)
    (hmv : ∀ x ∈ frontier DN,
      m ≤ √(gN.inner x (gradientFun (I := I) gN v x) (gradientFun (I := I) gN v x)))
    (herror : ∀ x ∈ frontier DN, ∀ w : TangentSpace I x,
      |mvfderiv (I := I) (fun z => η (j z)) x w - mvfderiv (I := I) v x w| ≤
        σ * √(gN.inner x w w))
    (hbudget : σ < (1 - δ) / (1 + δ) * m) {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
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
  have hDNcpt : IsCompact DN := hcpt.of_isClosed_subset hDNc hDN10
  obtain ⟨hAD, hDb, -⟩ := transverse_core_enclosure gN g hEnorm j n hlam0 hlam1 hcpt hsrc
    hlower hupper he hclose hDNc hin hout
  have hηd : ∀ x ∈ frontier DN, MDifferentiableAt I 𝓘(ℝ, ℝ) η (j x) := by
    intro x hx
    obtain ⟨-, -, hfr⟩ := transverse_core_enclosure gN g hEnorm j n hlam0 hlam1 hcpt hsrc
      hlower hupper he hclose hDNc hin hout
    have h := hfr x hx
    have hW' : j x ∈ W := hCW (j x) (by linarith [h.1]) (by linarith [h.2])
    exact (hηW.contMDiffAt (hW.mem_nhds hW')).mdifferentiableAt (by simp)
  have hjcl : IsClosed ((j : N → M) '' DN) :=
    (hDNcpt.image_of_continuousOn
      (j.contMDiffOn_toFun.continuousOn.mono (hDN10.trans hsrc))).isClosed
  apply radial_core_isotopy_of_transverse g hEnorm hε1 he hclose hlip hW hCW hηW hgrad hjcl hAD
    hDb _ hρ
  intro q hq
  obtain ⟨x, hx, rfl⟩ := frontier_image_subset_image_frontier j hDNcpt (hDN10.trans hsrc) hq
  obtain ⟨U', hU', hxU', hsm, hset, hpos⟩ := transverse_core_outward gN g j (hDN10.trans hsrc)
    (hsrc (hDN10 (hDNc.frontier_subset hx))) hU (hfrU hx) hv hdefN (hηd x hx) hδ hδ1
    (hlowδ x hx) (hupδ x hx) hmpos (hmv x hx) (herror x hx) hbudget
  refine ⟨U', hU', hxU', _, hsm, hset, ?_⟩
  have hK : 1 / 8 < η (j x) := by
    by_contra hle
    exact hq.2 (hAD (not_lt.mp hle))
  rw [map_smul, smul_eq_mul]
  have hjx : j x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3 := ⟨hK.le, (hDb ⟨x, hDNc.frontier_subset hx, rfl⟩).le⟩
  have hann := radialBand_subset_annulus hclose he hjx
  have hnorm := hgrad (j x) hann.1.le hann.2.le
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  have hpos' : 0 < g.inner (j x) (gradientFun (I := I) g η (j x))
      (gradientFun (I := I) g η (j x)) := lt_of_lt_of_le (by positivity) hnorm
  exact mul_pos (inv_pos.mpr hpos') hpos

end DifferentialGeometry.Geometry.Collapse
