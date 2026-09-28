import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampExtension

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem solutionOn_Ico_of_local_agreement
    (g : ℝ → SmoothRiemannianMetric I M) (q : CurveMap M) {a T : ℝ}
    (hlocal : ∀ t ∈ Ico a T, ∃ r : ℝ, t < r ∧ ∃ c : CurveMap M,
      c.IsSolutionOn g (Icc a r) ∧
      ∀ z τ, τ ∈ Ico a T → τ ≤ r → q z τ = c z τ) :
    q.IsSolutionOn g (Ico a T) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, t⟩ hp
    obtain ⟨r, htr, c, hc, heq⟩ := hlocal t hp.2
    have hV : (univ : Set ℝ) ×ˢ Iio r ∈ 𝓝 (x, t) :=
      (isOpen_univ.prod isOpen_Iio).mem_nhds ⟨mem_univ x, htr⟩
    have hmem : (univ ×ˢ Icc a r) ∈ 𝓝[univ ×ˢ Ico a T] (x, t) :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨univ ×ˢ Iio r, hV, fun p hp => ⟨mem_univ _, hp.2.2.1, hp.1.2.le⟩⟩
    have hs := (hc.smooth (x, t) ⟨mem_univ x, hp.2.1, htr.le⟩).mono_of_mem_nhdsWithin hmem
    apply hs.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hV] with p hp hr
      exact heq p.1 p.2 hp.2 hr.2.le
    · exact heq x t hp.2 htr.le
  · intro x t ht
    obtain ⟨r, htr, c, hc, heq⟩ := hlocal t ht
    rw [CurveMap.X_congr (fun z => heq z t ht htr.le) x]
    exact hc.immersed x t ⟨ht.1, htr.le⟩
  · intro x t ht
    obtain ⟨r, htr, c, hc, heq⟩ := hlocal t ht
    have hset : Ico a T =ᶠ[𝓝 t] Icc a r := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [isOpen_Iio.mem_nhds (lt_min ht.2 htr)] with τ hτ
      exact ⟨fun h => ⟨h.1, (hτ.trans_le (min_le_right _ _)).le⟩,
        fun h => ⟨h.1, hτ.trans_le (min_le_left _ _)⟩⟩
    have hev : q.lift x =ᶠ[𝓝[Ico a T] t] c.lift x := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htr)] with τ hτ hr
      exact heq x τ hτ hr.le
    have hv : q.velocity (I := I) (Ico a T) x t = c.velocity (I := I) (Icc a r) x t := by
      unfold CurveMap.velocity
      rw [hev.mfderivWithin_eq (heq x t ht htr.le), mfderivWithin_congr_set hset]
      rfl
    rw [hv, hc.equation x t ⟨ht.1, htr.le⟩]
    exact (CurveMap.curvatureVector_congr (fun z => heq z t ht htr.le) x).symm

namespace ProductCurve

variable [T2Space M] [CompactSpace M] [I.Boundaryless]
  {D : RealTimeInterval} {a b : ℝ}

private theorem map_eq_of_isSolutionOn
    (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) {r s : ℝ}
    (har : a < r) (has : a < s) (hrb : r ≤ b) (hsb : s ≤ b)
    (c d : ProductCurve M)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a r))
    (hd : d.IsSolutionOn B.family.metric lambda (Icc a s))
    (hinit : ∀ z, c.map z a = d.map z a) :
    ∀ z t, t ∈ Icc a (min r s) → c.map z t = d.map z t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hcm : c.map.IsSolutionOn Bhat.family.metric (Icc a r) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc har) hc
  have hdm : d.map.IsSolutionOn Bhat.family.metric (Icc a s) := by
    rw [hm]
    exact d.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc has) hd
  exact curveShorteningLocalUniqueness_of_compact Bhat.toSmoothMetricWindow
    a r s le_rfl har has hrb hsb c.map d.map hcm hdm hinit


theorem exists_ramp_solution_on_Icc
    (B : RicciBackground (I := I) (M := M) D a b)
    (seed : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    (hseed : seed.IsSolutionOn B.family.metric lambda (Icc a d))
    (hrseed : seed.IsRampOn B.family.metric lambda (Icc a d)) :
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      ∀ z t, t ∈ Icc a d → c.map z t = seed.map z t := by
  classical
  rcases hdb.eq_or_lt with hdb | hdb
  · subst d
    exact ⟨seed, hseed, hrseed, fun _ _ _ => rfl⟩
  let S : Set ℝ := {r | d ≤ r ∧ r ≤ b ∧ ∃ c : ProductCurve M,
    c.IsSolutionOn B.family.metric lambda (Icc a r) ∧
    c.IsRampOn B.family.metric lambda (Icc a r) ∧
    ∀ z t, t ∈ Icc a d → c.map z t = seed.map z t}
  have hSne : S.Nonempty := ⟨d, le_rfl, hdb.le, seed, hseed, hrseed, fun _ _ _ => rfl⟩
  have hSbdd : BddAbove S := ⟨b, fun r hr => hr.2.1⟩
  let T : ℝ := sSup S
  have hTb : T ≤ b := csSup_le hSne (fun r hr => hr.2.1)
  obtain ⟨r₁, hdr₁, hr₁b, c₁, hc₁, hrc₁, heq₁⟩ :=
    seed.exists_ramp_extension B lambda hlambda had hdb hseed hrseed
  have hr₁S : r₁ ∈ S := ⟨hdr₁.le, hr₁b, c₁, hc₁, hrc₁, heq₁⟩
  have hdT : d < T := hdr₁.trans_le (le_csSup hSbdd hr₁S)
  have haT : a < T := had.trans hdT
  let horizon := {r : ℝ // r ∈ S}
  let flow : horizon → ProductCurve M := fun r => Classical.choose r.2.2.2
  have hflow (r : horizon) :
      (flow r).IsSolutionOn B.family.metric lambda (Icc a r.1) ∧
      (flow r).IsRampOn B.family.metric lambda (Icc a r.1) ∧
      ∀ z t, t ∈ Icc a d → (flow r).map z t = seed.map z t :=
    Classical.choose_spec r.2.2.2
  have hcover (t : Ico a T) : ∃ r : horizon, (t : ℝ) < r.1 := by
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hSne t.2.2
    exact ⟨⟨r, hr⟩, htr⟩
  choose cover hcover using hcover
  let q : CurveMap (M × Surgery.Topology.Circle) := fun z t =>
    if ht : t ∈ Ico a T then (flow (cover ⟨t, ht⟩)).map z t else seed.map z a
  have hqeq (r : horizon) (z : Surgery.Topology.Circle) (t : ℝ)
      (ht : t ∈ Ico a T) (htr : t ≤ r.1) : q z t = (flow r).map z t := by
    dsimp only [q]
    rw [dite_eq_left ht]
    exact map_eq_of_isSolutionOn B lambda hlambda
      (had.trans_le (cover ⟨t, ht⟩).2.1) (had.trans_le r.2.1)
      (cover ⟨t, ht⟩).2.2.1 r.2.2.1 (flow (cover ⟨t, ht⟩)) (flow r)
      (hflow _).1 (hflow r).1
      (fun z => ((hflow _).2.2 z a ⟨le_rfl, had.le⟩).trans
        ((hflow r).2.2 z a ⟨le_rfl, had.le⟩).symm) z t
      ⟨ht.1, le_min (hcover ⟨t, ht⟩).le htr⟩
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  let ghat := fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda
  have hqsol : q.IsSolutionOn ghat (Ico a T) := by
    apply solutionOn_Ico_of_local_agreement
    intro t ht
    let r := cover ⟨t, ht⟩
    refine ⟨r.1, hcover ⟨t, ht⟩, (flow r).map, ?_, fun z τ hτ hτr => hqeq r z τ hτ hτr⟩
    exact (flow r).isSolutionOn_map A B.family.metric lambda hlambda
      (uniqueDiffOn_Icc (had.trans_le r.2.1)) (hflow r).1
  obtain ⟨c, hc, heq⟩ := product_solution_lift A B.family.metric lambda hlambda q
    haT (Ico a T) (Or.inl rfl) hqsol
  have hr : c.IsRampOn B.family.metric lambda (Ico a T) := by
    refine ⟨hc.immersed, ?_⟩
    intro x t ht
    let r := cover ⟨t, ht⟩
    have htr : t ∈ Icc a r.1 := ⟨ht.1, (hcover ⟨t, ht⟩).le⟩
    have hcsm : c.SmoothOn (I := I) {t} :=
      ⟨hc.smooth.1.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht)),
        hc.smooth.2.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht))⟩
    have hrsm : (flow r).SmoothOn (I := I) {t} :=
      ⟨(hflow r).1.smooth.1.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr htr)),
        (hflow r).1.smooth.2.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr htr))⟩
    rw [c.angle_eq_of_map_eq (flow r) B.family.metric lambda t hcsm hrsm
      (fun z => (heq z t ht).trans (hqeq r z t ht htr.2)) x]
    exact (hflow r).2.1.2 x t htr
  obtain ⟨closed, hclosed, hrclosed, hclosedEq⟩ :=
    c.exists_isSolutionOn_Icc_isRampOn_of_isRampOn_Ico B lambda hlambda haT hTb hc hr
  have htrace (z : Surgery.Topology.Circle) (t : ℝ) (ht : t ∈ Icc a d) :
      closed.map z t = seed.map z t := by
    have htT : t ∈ Ico a T := ⟨ht.1, ht.2.trans_lt hdT⟩
    rw [hclosedEq z t htT, heq z t htT]
    exact (hqeq ⟨r₁, hr₁S⟩ z t htT (ht.2.trans hdr₁.le)).trans
      ((hflow ⟨r₁, hr₁S⟩).2.2 z t ht)
  have hTb_eq : T = b := by
    by_contra hne
    have hlt : T < b := hTb.lt_of_ne hne
    obtain ⟨u, hTu, hub, ext, hext, hrext, hextEq⟩ :=
      closed.exists_ramp_extension B lambda hlambda haT hlt hclosed hrclosed
    have huS : u ∈ S := ⟨hdT.le.trans hTu.le, hub, ext, hext, hrext, fun z t ht =>
      (hextEq z t ⟨ht.1, ht.2.trans hdT.le⟩).trans (htrace z t ht)⟩
    exact hTu.not_ge (le_csSup hSbdd huS)
  rw [hTb_eq] at hclosed hrclosed
  exact ⟨closed, hclosed, hrclosed, htrace⟩

end ProductCurve
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
