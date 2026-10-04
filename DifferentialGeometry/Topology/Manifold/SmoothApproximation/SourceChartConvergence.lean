import DifferentialGeometry.Topology.Manifold.SmoothApproximation.NoncompactSourceEmbedding
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Overlap
import DifferentialGeometry.Topology.UniformConvergence

/-!
# Approximations of a partial diffeomorphism, read in the source charts (LFR48, tier T2b)

The approximations `hs n → j` of T1 (`exists_smooth_seq_chart_tendsto_near_isCompact`) converge in
pairs of charts (source chart `φ_p`, target chart `ψ_q`). LFR48 compares the pulled-back metrics
of `hs n` and of the `C^s` partial diffeomorphism `j` in the SAME source chart, through the
coordinate change `φ_p ∘ j⁻¹ ∘ hs n ∘ φ_p⁻¹` of the source. This file shows that it is eventually
defined and converges to the identity.

* `eventually_mapsTo_and_mapCPConvergenceOn_chart_symm_comp` (T2b): `hs n` `C^k` on an open
  `O ⊆ j.source`, chartwise `C^k` convergent to `j` (`k ≤ s`) on compact chart pieces over `O`;
  then on every compact `L` in the target of `φ_p` over `O`, eventually `hs n (φ_p⁻¹ L) ⊆ j.target`
  and `j⁻¹ (hs n (φ_p⁻¹ L)) ⊆ source φ_p`, and `φ_p ∘ j⁻¹ ∘ hs n ∘ φ_p⁻¹ → id` in `C^k` on `L`.

Route: on the open pieces `U q = target φ_p ∩ φ_p⁻¹⁻¹ (O ∩ j⁻¹ (source ψ_q))` the map is the
fixed `C^k` map `φ_p ∘ j⁻¹ ∘ ψ_q⁻¹` composed with `ψ_q ∘ hs n ∘ φ_p⁻¹`
(`mapCPConvergenceOn_comp_of_eventually_contDiffOn`); finitely many pieces cover `L`
(`GC.MetricGeometry.mapCPConvergenceOn_of_isCompact_subset_sUnion`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

private theorem eventually_forall_of_isCompact_local {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {P : ℕ → X → Prop}
    (hP : ∀ x ∈ S, ∃ N ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ z ∈ N, P n z) :
    ∀ᶠ n in atTop, ∀ z ∈ S, P n z := by
  refine hS.induction_on (p := fun T => ∀ᶠ n in atTop, ∀ z ∈ T, P n z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ _ hz => hz.elim
  · intro s t hst ht
    exact ht.mono fun n hn z hz => hn z (hst hz)
  · intro s t hs ht
    filter_upwards [hs, ht] with n hn1 hn2 z hz
    exact hz.elim (hn1 z) (hn2 z)
  · intro x hx
    obtain ⟨N, hN, hev⟩ := hP x hx
    exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, hev⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **LFR48 T2b: approximations read in the source charts.** -/
theorem eventually_mapsTo_and_mapCPConvergenceOn_chart_symm_comp {k : ℕ} {s : ℕ∞ω}
    (hks : (k : ℕ∞ω) ≤ s) (j : PartialDiffeomorph I J A B s) {O : Set A} (hO : IsOpen O)
    (hOj : O ⊆ j.source) {hs : ℕ → A → B} (hsm : ∀ n, ContMDiffOn I J k (hs n) O)
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K →
        K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' O →
        MapsTo (fun y => j ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun n y => extChartAt J q (hs n ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (j ((extChartAt I p).symm y))))
    (p : A) {L : Set E} (hL : IsCompact L)
    (hLO : L ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' O) :
    (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) L j.target ∧
        MapsTo (fun y => j.symm (hs n ((extChartAt I p).symm y))) L (extChartAt I p).source) ∧
      MapCPConvergenceOn L k
        (fun n y => extChartAt I p (j.symm (hs n ((extChartAt I p).symm y)))) id := by
  -- the open pieces
  let U : B → Set E := fun q => (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (O ∩ j ⁻¹' (extChartAt J q).source)
  have hU : ∀ q, IsOpen (U q) := fun q =>
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
      ((j.contMDiffOn.continuousOn.mono hOj).isOpen_inter_preimage hO
        (isOpen_extChartAt_source q))
  have hpiece : ∀ q (K : Set E), IsCompact K → K ⊆ U q →
      K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' O ∧
        MapsTo (fun y => j ((extChartAt I p).symm y)) K (extChartAt J q).source :=
    fun q K _ hK => ⟨fun y hy => ⟨(hK hy).1, (hK hy).2.1⟩, fun y hy => (hK hy).2.2⟩
  -- the local statement on one piece
  have hlocal : ∀ q (D : Set E), IsCompact D → D ⊆ U q →
      (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) D j.target ∧
        MapsTo (fun y => j.symm (hs n ((extChartAt I p).symm y))) D (extChartAt I p).source) ∧
      MapCPConvergenceOn D k
        (fun n y => extChartAt I p (j.symm (hs n ((extChartAt I p).symm y)))) id := by
    intro q D hD hDU
    let Z : Set E' := (extChartAt J q).target ∩
      (extChartAt J q).symm ⁻¹' (j.target ∩ j.symm ⁻¹' (extChartAt I p).source)
    have hZ : IsOpen Z := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q)
      (j.symm.contMDiffOn.continuousOn.isOpen_inter_preimage j.open_target
        (isOpen_extChartAt_source p))
    let T : E' → E := fun z => extChartAt I p (j.symm ((extChartAt J q).symm z))
    have hT : ContDiffOn ℝ ((k : ℕ∞) : ℕ∞ω) T Z := by
      have h1 : ContMDiffOn J I k j.symm j.target := j.symm.contMDiffOn.of_le hks
      have h2 : ContMDiffOn 𝓘(ℝ, E') I k (fun z => j.symm ((extChartAt J q).symm z)) Z :=
        h1.comp ((contMDiffOn_extChartAt_symm q).mono inter_subset_left) fun z hz => hz.2.1
      refine contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (n := k) (x := p)).comp h2 ?_)
      intro z hz
      have h := hz.2.2
      simp only [mem_preimage, extChartAt_source] at h ⊢
      exact h
    let Bn : ℕ → E → E' := fun n y => extChartAt J q (hs n ((extChartAt I p).symm y))
    let Binf : E → E' := fun y => extChartAt J q (j ((extChartAt I p).symm y))
    have hB : ∀ K : Set E, IsCompact K → K ⊆ U q → MapCPConvergenceOn K k Bn Binf :=
      fun K hK hKU => (hconv p q K hK (hpiece q K hK hKU).1 (hpiece q K hK hKU).2).2
    have hBc : ∀ K : Set E, IsCompact K → K ⊆ U q →
        ∀ᶠ n in atTop, ContDiffOn ℝ ((k : ℕ∞) : ℕ∞ω) (Bn n) K := by
      intro K hK hKU
      filter_upwards [(hconv p q K hK (hpiece q K hK hKU).1 (hpiece q K hK hKU).2).1] with n hn
      have h1 : ContMDiffOn 𝓘(ℝ, E) J k (fun y => hs n ((extChartAt I p).symm y)) K :=
        (hsm n).comp ((contMDiffOn_extChartAt_symm p).mono fun y hy => (hKU hy).1)
          fun y hy => (hKU hy).2.1
      refine contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (n := k) (x := q)).comp h1 ?_)
      intro y hy
      have h := hn hy
      simp only [mem_preimage, extChartAt_source] at h ⊢
      exact h
    have hBinfc : ContDiffOn ℝ ((k : ℕ∞) : ℕ∞ω) Binf (U q) := by
      have h1 : ContMDiffOn 𝓘(ℝ, E) J k (fun y => j ((extChartAt I p).symm y)) (U q) :=
        ((j.contMDiffOn.of_le hks).mono hOj).comp
          ((contMDiffOn_extChartAt_symm p).mono inter_subset_left) fun y hy => hy.2.1
      refine contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (n := k) (x := q)).comp h1 ?_)
      intro y hy
      have h := hy.2.2
      simp only [mem_preimage, extChartAt_source] at h ⊢
      exact h
    have hmap : MapsTo Binf (U q) Z := by
      intro y hy
      have hx : (extChartAt I p).symm y ∈ j.source := hOj hy.2.1
      have hjq : j ((extChartAt I p).symm y) ∈ (extChartAt J q).source := hy.2.2
      refine ⟨(extChartAt J q).map_source hjq, ?_⟩
      change (extChartAt J q).symm (extChartAt J q (j ((extChartAt I p).symm y))) ∈
        j.target ∩ j.symm ⁻¹' (extChartAt I p).source
      rw [(extChartAt J q).left_inv hjq]
      refine ⟨j.toPartialEquiv.map_source hx, ?_⟩
      change j.symm (j ((extChartAt I p).symm y)) ∈ (extChartAt I p).source
      rw [show j.symm (j ((extChartAt I p).symm y)) = (extChartAt I p).symm y from
        j.toPartialEquiv.left_inv hx]
      exact (extChartAt I p).map_target hy.1
    have hmain := mapCPConvergenceOn_comp_of_eventually_contDiffOn (hU q) hZ hB
      (fun S _ _ => MapCPConvergenceOn.const_seq (p := k) T) hBc hBinfc
      (fun S _ hSZ => Eventually.of_forall fun _ => hT.mono hSZ) hT hmap hD hDU
    -- capture
    have hzero := tendstoUniformlyOn_of_cPConvergence ((hB D hD hDU).mono_order (Nat.zero_le k))
    have hmapsZ := hzero.eventually_mapsTo_of_isCompact hD (hBinfc.continuousOn.mono hDU) hZ
      (hmap.mono_left hDU)
    have hsrcD := (hconv p q D hD (hpiece q D hD hDU).1 (hpiece q D hD hDU).2).1
    refine ⟨?_, ?_⟩
    · filter_upwards [hmapsZ, hsrcD] with n hZn hsrc
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · have h := (hZn hy).2.1
        change (extChartAt J q).symm (extChartAt J q (hs n ((extChartAt I p).symm y))) ∈
          j.target at h
        rwa [(extChartAt J q).left_inv (hsrc hy)] at h
      · have h := (hZn hy).2.2
        change j.symm ((extChartAt J q).symm (extChartAt J q (hs n ((extChartAt I p).symm y))))
          ∈ (extChartAt I p).source at h
        rwa [(extChartAt J q).left_inv (hsrc hy)] at h
    · -- identification on an open neighbourhood of `D`
      obtain ⟨D', hD', hDD', hD'U, hD'c⟩ :=
        exists_open_between_and_isCompact_closure hD (hU q) hDU
      have hcap := (hconv p q (closure D') hD'c (hpiece q _ hD'c hD'U).1
        (hpiece q _ hD'c hD'U).2).1
      refine hmain.congr_eventually hD' hDD' ?_ ?_
      · filter_upwards [hcap] with n hn y hy
        change extChartAt I p (j.symm (hs n ((extChartAt I p).symm y))) =
          extChartAt I p (j.symm ((extChartAt J q).symm
            (extChartAt J q (hs n ((extChartAt I p).symm y)))))
        rw [(extChartAt J q).left_inv (hn (subset_closure hy))]
      · intro y hy
        have hyU := hD'U (subset_closure hy)
        have hx : (extChartAt I p).symm y ∈ j.source := hOj hyU.2.1
        change y = extChartAt I p (j.symm ((extChartAt J q).symm
          (extChartAt J q (j ((extChartAt I p).symm y)))))
        rw [(extChartAt J q).left_inv hyU.2.2,
          show j.symm (j ((extChartAt I p).symm y)) = (extChartAt I p).symm y from
            j.toPartialEquiv.left_inv hx, (extChartAt I p).right_inv hyU.1]
  -- finitely many pieces
  have hcov : ∀ y ∈ L, y ∈ U (j ((extChartAt I p).symm y)) := fun y hy =>
    ⟨(hLO hy).1, (hLO hy).2, mem_extChartAt_source _⟩
  refine ⟨?_, ?_⟩
  · have hev := eventually_forall_of_isCompact_local hL (P := fun n y =>
      hs n ((extChartAt I p).symm y) ∈ j.target ∧
        j.symm (hs n ((extChartAt I p).symm y)) ∈ (extChartAt I p).source) (by
      intro y hy
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (hU _) y (hcov y hy)
      have hDU : closedBall y (ε / 2) ⊆ U (j ((extChartAt I p).symm y)) := fun z hz =>
        hεU (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (half_lt_self hε)))
      refine ⟨closedBall y (ε / 2), closedBall_mem_nhds y (half_pos hε), ?_⟩
      filter_upwards [(hlocal _ _ (isCompact_closedBall y (ε / 2)) hDU).1] with n hn z hz
      exact ⟨hn.1 hz, hn.2 hz⟩)
    filter_upwards [hev] with n hn
    exact ⟨fun y hy => (hn y hy).1, fun y hy => (hn y hy).2⟩
  · refine GC.MetricGeometry.mapCPConvergenceOn_of_isCompact_subset_sUnion (S := range U)
      (by rintro _ ⟨q, rfl⟩; exact hU q) ?_ hL ?_
    · rintro _ ⟨q, rfl⟩ D hD hDU
      exact (hlocal q D hD hDU).2
    · intro y hy
      exact ⟨U _, ⟨_, rfl⟩, hcov y hy⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
