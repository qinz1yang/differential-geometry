import DifferentialGeometry.Topology.PiecewiseLinear.Section34IsolatedBigonNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonChartTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonSideDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSphere
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)

private theorem exists_side_disk_of_unordered_charts
    {N J L : Set E2} (hN : IsPLBall 2 N) {γ δ : ℝ → E2}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (t : Fin 2 → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (hne : t 0 ≠ t 1)
    (htrace : J ∩ L = {γ (t 0), γ (t 1)})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) E2) (ε : Fin 2 → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ L ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J) :
    ∃ A : Set E2, IsPLBall 2 A ∧ A ⊆ N ∧
      A ∩ (L ∪ frontier N) ⊆ frontier A ∧
      γ 0 ∈ frontier A ∧ γ 1 ∈ frontier A ∧ γ 0 ∉ L ∧ γ 1 ∉ L := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact exists_bigon_side_disk_of_two_crossing_charts hN hγ hJN hJends hδ hLN hLends
      t (ht 0).1 hlt (ht 1).2 htrace e ε hε hsource hcenter hcurve haxis
  · exact exists_bigon_side_disk_of_two_crossing_charts hN hγ hJN hJends hδ hLN hLends
      (fun i => t i.rev) (ht 1).1 hgt (ht 0).2
      (by change J ∩ L = {γ (t 1), γ (t 0)}; simpa only [pair_comm] using htrace)
      (fun i => e i.rev) (fun i => ε i.rev)
      (fun i => hε i.rev) (fun i => hsource i.rev) (fun i => hcenter i.rev)
      (fun i => hcurve i.rev) (fun i => haxis i.rev)

theorem IsCombinatorialManifold.exists_raw_bigon_slide
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {B Ω J L : Set E}
    (hB : IsPLBall 2 B) (hBK : B ⊆ K.space) (hΩ : IsOpen Ω) (hBΩ : B ⊆ Ω)
    (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L) (hJK : J ⊆ K.space) (hLK : L ⊆ K.space)
    (hBJ : IsPLBall 1 (B ∩ J)) (hBL : IsPLBall 1 (B ∩ L))
    (c : Fin 2 → E) (hc : Function.Injective c) (htrace : B ∩ (J ∩ L) = {c 0, c 1})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) K.space) (ε : Fin 2 → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, (e i (0, 0) : E) = c i)
    (hfirst : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      (e i p : E) ∈ J ↔ p.1 = 0)
    (hsecond : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      (e i p : E) ∈ L ↔ p.2 = 0) :
    ∃ (N : Set E) (r : (Fin 3 → ℝ) → E) (H : E → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) N ∧ N ⊆ K.space ∩ Ω ∧
      B ⊆ r '' openSimplex (stdVertices 1) ∧ IsPLHomeomorphOn H K.space K.space ∧
      EqOn H id (closure (K.space \ N)) ∧ H '' N = N ∧
      H '' J ∩ L = (J ∩ L) \ {c 0, c 1} ∧
      N ∩ (J ∩ L) = {c 0, c 1} ∧ H '' J ∩ L = (J \ N) ∩ L := by
  have hiso (i : Fin 2) : ∀ᶠ y in 𝓝[K.space] (c i), y ∈ J ∩ L → y = c i := by
    have h := Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes
      (e i) (hε i) (hsource i) (hfirst i) (hsecond i)
    rw [hcenter i] at h
    exact h.mono fun _ hy => hy.mp
  obtain ⟨N, r, α, β, hr, hNKΩ, hBint, hα, hαbd, hβ, hβbd, hNtrace⟩ :=
    hK.exists_disk_neighborhood_with_isolated_crossings K hB hBK hΩ hBΩ hJ hL hJK hLK
      hBJ hBL htrace (by
        rintro x (rfl | rfl)
        · exact hiso 0
        · exact hiso 1)
  have hNK : N ⊆ K.space := hNKΩ.trans inter_subset_left
  have hBN : B ⊆ N := by
    rw [hr.image_openSimplex_stdVertices] at hBint
    exact hBint.trans sdiff_subset
  have hcB (i : Fin 2) : c i ∈ B := by
    apply (htrace.symm.subset ?_).1
    fin_cases i <;> simp
  have hcJ (i : Fin 2) : c i ∈ J := by
    apply (htrace.symm.subset ?_).2.1
    fin_cases i <;> simp
  have hcN (i : Fin 2) : c i ∈ N := hBN (hcB i)
  have hα' : IsPLHomeomorphOn α (stdSimplex ℝ (Fin 2)) (J ∩ N) := by
    simpa only [inter_comm] using hα
  have hβ' : IsPLHomeomorphOn β (stdSimplex ℝ (Fin 2)) (L ∩ N) := by
    simpa only [inter_comm] using hβ
  obtain ⟨γ, hγ, hγbd⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hα'
    (W := r '' stdSimplexBoundary 2) (by rw [← hαbd, inter_comm N J])
  obtain ⟨δ, hδ, hδbd⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hβ'
    (W := r '' stdSimplexBoundary 2) (by rw [← hβbd, inter_comm N L])
  have hγpoly : IsPolyhedron (J ∩ N) :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron
  have hδpoly : IsPolyhedron (L ∩ N) :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ).isPolyhedron
  obtain ⟨C, σ, hC, hσ⟩ := exists_planar_coordinates_of_isPLBall_two ⟨r, hr⟩
  let D := closure (Schoenflies.inside C)
  have hD : IsPLBall 2 D := isPLBall_closure_inside_of_isPLSphere_one hC
  let Γ := σ ∘ γ
  let Δ := σ ∘ δ
  have hΓ : IsPLHomeomorphOn Γ (Icc 0 1) (σ '' (J ∩ N)) :=
    hγ.trans (hσ.restrict hγpoly inter_subset_right)
  have hΔ : IsPLHomeomorphOn Δ (Icc 0 1) (σ '' (L ∩ N)) :=
    hδ.trans (hσ.restrict hδpoly inter_subset_right)
  have hrbdN : r '' stdSimplexBoundary 2 ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact hr.bijOn.mapsTo hz.1
  have hσbd : σ '' (r '' stdSimplexBoundary 2) = frontier D := by
    rw [← image_comp]
    exact (hr.trans hσ).image_stdSimplexBoundary
  have hΓbd : σ '' (J ∩ N) ∩ frontier D = {Γ 0, Γ 1} := by
    rw [← hσbd, ← hσ.bijOn.injOn.image_inter inter_subset_right hrbdN,
      ← hγbd, image_pair]
    rfl
  have hΔbd : σ '' (L ∩ N) ∩ frontier D = {Δ 0, Δ 1} := by
    rw [← hσbd, ← hσ.bijOn.injOn.image_inter inter_subset_right hrbdN,
      ← hδbd, image_pair]
    rfl
  have hparam : ∀ i, ∃ s ∈ Icc (0 : ℝ) 1, γ s = c i :=
    fun i => hγ.bijOn.surjOn ⟨hcJ i, hcN i⟩
  choose t ht htc using hparam
  have htopen : ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
    intro i
    have hcnot : c i ∉ r '' stdSimplexBoundary 2 := by
      have h := hBint (hcB i)
      rw [hr.image_openSimplex_stdVertices] at h
      exact h.2
    have hnot0 : t i ≠ 0 := by
      intro h
      apply hcnot
      rw [← htc i, h]
      exact (hγbd.subset (by simp)).2
    have hnot1 : t i ≠ 1 := by
      intro h
      apply hcnot
      rw [← htc i, h]
      exact (hγbd.subset (by simp)).2
    exact ⟨lt_of_le_of_ne (ht i).1 hnot0.symm, lt_of_le_of_ne (ht i).2 hnot1⟩
  have htne : t 0 ≠ t 1 := by
    intro h
    have heq : c 0 = c 1 := (htc 0).symm.trans ((congrArg γ h).trans (htc 1))
    exact (by decide : (0 : Fin 2) ≠ 1) (hc heq)
  have hΓtrace : σ '' (J ∩ N) ∩ σ '' (L ∩ N) = {Γ (t 0), Γ (t 1)} := by
    rw [← hσ.bijOn.injOn.image_inter inter_subset_right inter_subset_right]
    have heq : (J ∩ N) ∩ (L ∩ N) = N ∩ (J ∩ L) := by ext x; simp only [mem_inter_iff]; tauto
    rw [heq, hNtrace, image_pair]
    simp only [Γ, Function.comp_apply, htc]
  have hsmall : ∀ i, ∃ η : ℝ, 0 < η ∧ η ≤ ε i ∧
      (fun p => (e i p : E)) '' (Ioo (-η) η ×ˢ Ioo (-η) η) ⊆ N := by
    intro i
    apply Topology.OpenPartialHomeomorph.exists_square_image_subset_of_nhdsWithin
      (e i) (hε i) (hsource i)
    rw [hcenter i]
    exact hK.mem_nhdsWithin_of_mem_image_openSimplex K hr hNK (hBint (hcB i))
  choose η hη hηε hηN using hsmall
  have hbox (i : Fin 2) : Ioo (-η i) (η i) ⊆ Ioo (-ε i) (ε i) := fun s hs =>
    ⟨lt_of_le_of_lt (neg_le_neg (hηε i)) hs.1, lt_of_lt_of_le hs.2 (hηε i)⟩
  have hflat : ∀ i, ∃ d : OpenPartialHomeomorph (ℝ × ℝ) E2,
      d.source = Ioo (-η i) (η i) ×ˢ Ioo (-η i) (η i) ∧
      (∀ p, d p = σ (e i p)) ∧
      ∀ p ∈ Ioo (-η i) (η i) ×ˢ Ioo (-η i) (η i), ∀ A ⊆ N,
        d p ∈ σ '' A ↔ (e i p : E) ∈ A := by
    intro i
    exact hσ.exists_surface_chart_in_planar_coordinates (e i) (isOpen_Ioo.prod isOpen_Ioo)
      (fun p hp => hsource i ⟨hbox i hp.1, hbox i hp.2⟩) (hηN i)
  choose d hd hdeq hdmem using hflat
  have hdcenter : ∀ i, d i (0, 0) = Γ (t i) := by
    intro i
    rw [hdeq i, hcenter i]
    simp only [Γ, Function.comp_apply, htc]
  have hdcurve : ∀ i, ∀ p ∈ Ioo (-η i) (η i) ×ˢ Ioo (-η i) (η i),
      d i p ∈ σ '' (L ∩ N) ↔ p.2 = 0 := by
    intro i p hp
    rw [hdmem i p hp (L ∩ N) inter_subset_right]
    exact (and_iff_left (hηN i ⟨p, hp, rfl⟩)).trans
      (hsecond i p ⟨hbox i hp.1, hbox i hp.2⟩)
  have hdaxis : ∀ i, ∀ s ∈ Ioo (-η i) (η i), d i (0, s) ∈ σ '' (J ∩ N) := by
    intro i s hs
    have hzero : (0 : ℝ) ∈ Ioo (-η i) (η i) := ⟨neg_neg_of_pos (hη i), hη i⟩
    rw [hdmem i (0, s) ⟨hzero, hs⟩ (J ∩ N) inter_subset_right]
    exact ⟨(hfirst i (0, s) ⟨hbox i hzero, hbox i hs⟩).mpr rfl,
      hηN i ⟨(0, s), ⟨hzero, hs⟩, rfl⟩⟩
  obtain ⟨A, hA, hAD, hAside, hA₀, hA₁, h₀L, h₁L⟩ :=
    exists_side_disk_of_unordered_charts hD hΓ
      ((image_mono inter_subset_right).trans hσ.image_eq.subset) hΓbd hΔ
      ((image_mono inter_subset_right).trans hσ.image_eq.subset) hΔbd t htopen htne hΓtrace
      d η hη (fun i => (hd i).symm.subset) hdcenter hdcurve hdaxis
  let g := Function.invFunOn σ N
  have hg : IsPLHomeomorphOn g A (g '' A) := hσ.symm.restrict hA.isPolyhedron hAD
  obtain ⟨a, ha⟩ := hA
  have hga : IsPLHomeomorphOn (g ∘ a) (stdSimplex ℝ (Fin 3)) (g '' A) := ha.trans hg
  have hgAN : g '' A ⊆ N := (image_mono hAD).trans hσ.symm.image_eq.subset
  have hgabd : (g ∘ a) '' stdSimplexBoundary 2 = g '' frontier A := by
    rw [image_comp, ha.image_stdSimplexBoundary]
  have hinv (x : E) (hx : x ∈ N) : g (σ x) = x := hσ.bijOn.invOn_invFunOn.1 hx
  have hγN (s : ℝ) (hs : s ∈ Icc 0 1) : γ s ∈ N := (hγ.bijOn.mapsTo hs).2
  have hbackside : (g '' A) ∩ (L ∪ r '' stdSimplexBoundary 2) ⊆
      (g ∘ a) '' stdSimplexBoundary 2 := by
    rintro x ⟨hxA, hx⟩
    obtain ⟨y, hy, rfl⟩ := hxA
    rw [hgabd]
    refine ⟨y, hAside ⟨hy, ?_⟩, rfl⟩
    have hgyN : g y ∈ N := hgAN ⟨y, hy, rfl⟩
    have hσgy : σ (g y) = y := hσ.bijOn.invOn_invFunOn.2 (hAD hy)
    rcases hx with hxL | hxBd
    · exact Or.inl ⟨g y, ⟨hxL, hgyN⟩, hσgy⟩
    · exact Or.inr (hσbd.subset ⟨g y, hxBd, hσgy⟩)
  have hback₀ : γ 0 ∈ (g ∘ a) '' stdSimplexBoundary 2 := by
    rw [hgabd]
    exact ⟨Γ 0, hA₀, hinv _ (hγN 0 (by norm_num))⟩
  have hback₁ : γ 1 ∈ (g ∘ a) '' stdSimplexBoundary 2 := by
    rw [hgabd]
    exact ⟨Γ 1, hA₁, hinv _ (hγN 1 (by norm_num))⟩
  have hγ₀L : γ 0 ∉ L := fun h => h₀L ⟨γ 0, ⟨h, hγN 0 (by norm_num)⟩, rfl⟩
  have hγ₁L : γ 1 ∉ L := fun h => h₁L ⟨γ 1, ⟨h, hγN 1 (by norm_num)⟩, rfl⟩
  obtain ⟨H, hH, hfix, hHN, hafter⟩ := hK.exists_crosscut_slide_of_side_disk K hr hNK hJK
    hγ hγbd.symm hga hgAN hbackside hback₀ hback₁ hγ₀L hγ₁L
  refine ⟨N, r, H, hr, hNKΩ, hBint, hH, hfix, hHN, hafter.trans ?_, hNtrace, hafter⟩
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxN⟩, hxL⟩
    exact ⟨⟨hxJ, hxL⟩, fun h => hxN (hNtrace.symm.subset h).1⟩
  · rintro ⟨⟨hxJ, hxL⟩, hx⟩
    exact ⟨⟨hxJ, fun hxN => hx (hNtrace.subset ⟨hxN, hxJ, hxL⟩)⟩, hxL⟩

end DifferentialGeometry.Topology.PiecewiseLinear
