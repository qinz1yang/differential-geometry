import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryArcShellChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ShellCrossingFan

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_axis_charts_of_exterior_collar_paths
    {D W A B : Set (ℝ × ℝ)} {q : (Fin 3 → ℝ) → ℝ × ℝ}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ 2 * d)
    {γ : Fin 2 → ℝ → ℝ × ℝ}
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d))
    (hγbd : ∀ k, γ k '' Icc (-d) d ⊆ q '' stdSimplexBoundary 2)
    (hdis : Pairwise fun i j => Disjoint (γ i '' Icc (-d) d) (γ j '' Icc (-d) d))
    (hB : B ⊆ q '' stdSimplexBoundary 2)
    (hAB : A ∩ B = {γ 0 0, γ 1 0})
    (hpos : ∀ k, γ k '' Icc 0 d ⊆ A) (hneg : ∀ k, γ k '' Icc (-d) 0 ⊆ B)
    {ρ : (ℝ × ℝ) × ℝ → ℝ × ℝ}
    (hρ : IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 c) W)
    (hzero : ∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hWD : W ∩ D = q '' stdSimplexBoundary 2) :
    let X := A ∪ ⋃ k, (fun r : ℝ => ρ (γ k (-r / 2), r)) '' Icc 0 c
    let Y := B ∪ ⋃ k, (fun r : ℝ => ρ (γ k (r / 2), r)) '' Icc 0 c
    ∀ k, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ),
      0 < ε ∧ IsPLHomeomorphOn e e.source e.target ∧ e (0, 0) = γ k 0 ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, e p ∈ Y ↔ p.2 = 0) ∧
      ∀ s ∈ Ioo (-ε) ε, e (0, s) ∈ X := by
  dsimp only
  have hd : 0 < d := by linarith
  have h0d : (0 : ℝ) ∈ Icc (-d) d := ⟨by linarith, hd.le⟩
  have hhalf {r : ℝ} (hr : r ∈ Icc 0 c) : r / 2 ∈ Icc (-d) d := by
    constructor <;> linarith [hr.1, hr.2]
  have hjoint {i j : Fin 2} {s t : ℝ} (hs : s ∈ Icc (-d) d)
      (ht : t ∈ Icc (-d) d) (heq : γ i s = γ j t) : i = j ∧ s = t := by
    by_cases hij : i = j
    · subst j
      exact ⟨rfl, (hγ i).bijOn.injOn hs ht heq⟩
    · exact False.elim (disjoint_left.mp (hdis hij) (mem_image_of_mem _ hs)
        ⟨t, ht, heq.symm⟩)
  have hγB (k : Fin 2) {t : ℝ} (ht : t ∈ Icc (-d) d) : γ k t ∈ B ↔ t ≤ 0 := by
    constructor
    · intro hb
      by_contra hn
      have ha := hpos k (mem_image_of_mem _ (show t ∈ Icc 0 d from
        ⟨(lt_of_not_ge hn).le, ht.2⟩))
      rcases hAB.subset ⟨ha, hb⟩ with h | h
      · have heq := (hjoint ht h0d h).2
        exact hn heq.le
      · have heq := (hjoint ht h0d h).2
        exact hn heq.le
    · intro ht0
      exact hneg k (mem_image_of_mem _ ⟨ht.1, ht0⟩)
  let Y := B ∪ ⋃ k, (fun r : ℝ => ρ (γ k (r / 2), r)) '' Icc 0 c
  have hYD : Y ∩ D ⊆ q '' stdSimplexBoundary 2 := by
    rintro y ⟨hy | hy, hyD⟩
    · exact hB hy
    · obtain ⟨k, r, hr, rfl⟩ := mem_iUnion.mp hy
      exact hWD.subset ⟨hρ.bijOn.mapsTo
        ⟨hγbd k (mem_image_of_mem _ (hhalf hr)), hr⟩, hyD⟩
  intro k
  obtain ⟨e, hesrc, hepl, heout, hezero, hein⟩ :=
    hq.exists_boundary_arc_chart_of_exterior_collar hc hd (hγ k) (hγbd k) hρ hzero hWD
  have hpre {t r : ℝ} (ht : t ∈ Ioo (-d) d) (hr : r ∈ Ioo (-1 : ℝ) c) :
      e (t, r) ∈ Y ↔ r = 2 * max t 0 := by
    have htI := Ioo_subset_Icc_self ht
    by_cases hr0 : 0 ≤ r
    · rw [heout t ht r ⟨hr0, hr.2⟩]
      constructor
      · rintro (hy | hy)
        · have heq := hρ.bijOn.injOn
            ⟨hγbd k (mem_image_of_mem _ htI), hr0, hr.2.le⟩
            ⟨hB hy, le_rfl, hc.le⟩ (hzero _ (hB hy)).symm
          have hrz : r = 0 := congrArg Prod.snd heq
          have hbase : γ k t = ρ (γ k t, r) := congrArg Prod.fst heq
          have ht0 := (hγB k htI).mp (by rw [hbase]; exact hy)
          rw [hrz, max_eq_right ht0, mul_zero]
        · obtain ⟨j, s, hs, hse⟩ := mem_iUnion.mp hy
          have heq := hρ.bijOn.injOn
            ⟨hγbd j (mem_image_of_mem _ (hhalf hs)), hs⟩
            ⟨hγbd k (mem_image_of_mem _ htI), hr0, hr.2.le⟩ hse
          have hsr : s = r := congrArg Prod.snd heq
          have hst : s / 2 = t := (hjoint (hhalf hs) htI (congrArg Prod.fst heq)).2
          rw [max_eq_left (by linarith [hs.1] : 0 ≤ t)]
          linarith
      · intro heq
        by_cases ht0 : t ≤ 0
        · have hrz : r = 0 := by simpa only [max_eq_right ht0, mul_zero] using heq
          rw [hrz, hzero _ (hγbd k (mem_image_of_mem _ htI))]
          exact Or.inl ((hγB k htI).mpr ht0)
        · have hrt : r / 2 = t := by rw [max_eq_left (lt_of_not_ge ht0).le] at heq; linarith
          exact Or.inr (mem_iUnion.mpr ⟨k, r, ⟨hr0, hr.2.le⟩,
            by change ρ (γ k (r / 2), r) = _; rw [hrt]⟩)
    · have hrneg : r < 0 := lt_of_not_ge hr0
      have hnot : e (t, r) ∉ Y := fun hy =>
        (hein t ht r ⟨hr.1, hrneg⟩).2 (hYD ⟨hy, (hein t ht r ⟨hr.1, hrneg⟩).1⟩)
      refine ⟨fun hy => (hnot hy).elim, ?_⟩
      intro heq
      exfalso
      linarith [le_max_right t 0]
  let F := section34ShellCrossingFan
  let e' := F.toOpenPartialHomeomorph.trans e
  have hFzero : F (0, 0) = (0, 0) := by norm_num [F, section34ShellCrossingFan]
  have h0source : (0, 0) ∈ e'.source := by
    change (0, 0) ∈ univ ∩ F ⁻¹' e.source
    exact ⟨mem_univ _, by rw [mem_preimage, hFzero, hesrc]; exact ⟨by constructor <;> linarith,
      by constructor <;> linarith⟩⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (e'.open_source.mem_nhds h0source)
  have hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e'.source := by
    intro p hp
    apply hεsub
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero,
      max_lt_iff, abs_lt, Prod.fst_zero, Prod.snd_zero, mem_prod, mem_Ioo] using hp
  have hsource {p : ℝ × ℝ} (hp : p ∈ e'.source) :
      F p ∈ Ioo (-d) d ×ˢ Ioo (-1 : ℝ) c := hesrc ▸ hp.2
  have he'pl : IsPiecewiseAffineOn e' e'.source := by
    exact hepl.isPiecewiseAffineOn.comp
      isPLHomeomorphOn_section34ShellCrossingFan.isPiecewiseAffineOn
  refine ⟨e', ε, hε, isPLHomeomorphOn_openPartialHomeomorph e' he'pl, ?_, hbox, ?_, ?_⟩
  · change e (F (0, 0)) = γ k 0
    rw [hFzero, hezero 0 (by constructor <;> linarith)]
  · intro p hp
    change e (F p) ∈ Y ↔ p.2 = 0
    exact (hpre (hsource (hbox hp)).1 (hsource (hbox hp)).2).trans
      (section34ShellCrossingFan_horizontal_iff p)
  · intro s hs
    have hp := hsource (hbox (show (0, s) ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε from
      ⟨⟨neg_neg_of_pos hε, hε⟩, hs⟩))
    change e (F (0, s)) ∈ A ∪ _
    by_cases hs0 : 0 ≤ s
    · have hform : F (0, s) = (-s / 2, s) := by
        dsimp [F, section34ShellCrossingFan]
        rw [max_eq_right (by linarith : (0 : ℝ) - s / 2 ≤ 0)]
        ext <;> dsimp <;> ring
      rw [hform] at hp ⊢
      rw [heout (-s / 2) hp.1 s ⟨hs0, hp.2.2⟩]
      exact Or.inr (mem_iUnion.mpr ⟨k, s, ⟨hs0, hp.2.2.le⟩, rfl⟩)
    · have hform : F (0, s) = (-s / 2, 0) := by
        dsimp [F, section34ShellCrossingFan]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ 0 - s / 2)]
        ext <;> dsimp <;> ring
      rw [hform] at hp ⊢
      rw [hezero (-s / 2) hp.1]
      exact Or.inl (hpos k (mem_image_of_mem _ ⟨by linarith, hp.1.2.le⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
