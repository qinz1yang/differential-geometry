import DifferentialGeometry.Topology.Handle.HalfBallCornerRoof
import DifferentialGeometry.Topology.Handle.HalfBallCylinderCollar
import DifferentialGeometry.Topology.MetricSpace.SphereNeighborhood
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.AmbientCornerRounding

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

theorem exists_halfBall_attachment_corner_coordinates
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P]
    (Ψ G : (E × ℝ) ≃ₘ[ℝ] F)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {σ : ℝ} (hσ : σ ≠ 0)
    (hP : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source)
    (hc : ∀ p, c p = G (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p))
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hGU : EqOn G (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U)
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, (e (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, -σ * p.2)) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∀ p : E × ℝ,
      |‖p.1‖ ^ 2 - 1| < r → |p.2| < r →
      p ∈ (PartialDiffeomorph.halfBallShear.symm.trans c).source ∧
      c (PartialDiffeomorph.halfBallShear.symm p) ∈ e.source ∧
      (e (c (PartialDiffeomorph.halfBallShear.symm p))).2 =
        ((halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1,
          -(halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).2) := by
  let J := PartialDiffeomorph.halfBallInversion (E := E) 1 one_ne_zero
  let L := PartialDiffeomorph.halfBallShear (E := E)
  let φ := L.symm.trans J
  let d := L.symm.trans c
  let V := U ∩ {p : E × ℝ | 3 / 4 < ‖p.1‖ ^ 2}
  have hV : IsOpen V := hU.inter (isOpen_lt continuous_const (continuous_fst.norm.pow 2))
  let N := (φ.source ∩ φ ⁻¹' V) ∩ (d.source ∩ d ⁻¹' e.source)
  have hN : IsOpen N :=
    (φ.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage φ.open_source hV).inter
      (d.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage d.open_source e.open_source)
  have hSN : sphere (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ N := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht' : t = 0 := ht
    subst t
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hL : L.symm (x, 0) = (x, 0) := by
      rw [show L = PartialDiffeomorph.halfBallShear from rfl,
        PartialDiffeomorph.halfBallShear_symm_apply]
      simp
    have hJ : J (x, 0) = (x, 0) := PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq
      one_ne_zero (by simpa only [abs_one] using hn)
    have hpL : (x, (0 : ℝ)) ∈ L.target := by change (0 : ℝ) < 2; norm_num
    have hpJ : (x, (0 : ℝ)) ∈ J.source :=
      PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg zero_lt_one le_rfl
    have hpP : (x, (0 : ℝ)) ∈ {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} := by
      simp only [hn, one_pow, zero_pow (by decide : 2 ≠ 0), add_zero, le_refl, and_self, mem_ofPred_eq]
    have hpU : (x, (0 : ℝ)) ∈ U := hDU ⟨sphere_subset_closedBall hx, rfl⟩
    have hφ : φ (x, 0) = (x, 0) := by change J (L.symm (x, 0)) = _; rw [hL, hJ]
    have hd : d (x, 0) = Ψ (x, 0) := by
      change c (L.symm (x, 0)) = _
      rw [hL, hc, show PartialDiffeomorph.halfBallInversion 1 one_ne_zero (x, 0) = (x, 0) from hJ,
        hGU hpU]
      change Ψ ((EuclideanGeometry.halfBallCylinderMap (x, 0)).1, σ⁻¹ * 0) = Ψ (x, 0)
      rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
    refine ⟨⟨⟨hpL, ?_⟩, ?_⟩, ⟨⟨hpL, ?_⟩, ?_⟩⟩
    · change L.symm (x, 0) ∈ J.source
      rwa [hL]
    · change φ (x, 0) ∈ V
      rw [hφ]
      exact ⟨hpU, by change 3 / 4 < ‖x‖ ^ 2; rw [hn]; norm_num⟩
    · change L.symm (x, 0) ∈ c.source
      rw [hL]
      exact hP hpP
    · change d (x, 0) ∈ e.source
      rw [hd]
      exact hsource ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  obtain ⟨r, hr, hrN⟩ := Metric.exists_norm_sq_sphere_prod_subset hN hSN
  refine ⟨r, hr, ?_⟩
  intro p hp ht
  have hpN := hrN ⟨hp, ht⟩
  let z := J (L.symm p)
  have hzU : z ∈ U := hpN.1.2.1
  have hzlarge : 3 / 4 ≤ ‖z.1‖ ^ 2 := le_of_lt hpN.1.2.2
  have hcoord := halfBallShearCornerCoordinates_eq_inversion
    (show p.2 < 2 from (lt_of_le_of_lt (le_abs_self p.2) ht).trans (hr.2.trans (by norm_num))) hpN.1.1.2
  have hnorm : ‖(EuclideanGeometry.halfBallCylinderMap z).1‖ ^ 2 = ‖z.1‖ ^ 2 + z.2 ^ 2 := by
    have hs : 0 < ‖z.1‖ ^ 2 := by linarith
    rw [EuclideanGeometry.halfBallCylinderMap_eq_of_norm_sq_ge hzlarge,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by have := div_nonneg (sq_nonneg z.2) hs.le; linarith),
      add_mul, one_mul, div_mul_cancel₀ _ hs.ne']
  refine ⟨hpN.2.1, hpN.2.2, ?_⟩
  rw [hc]
  change (e (G z)).2 = _
  rw [hGU hzU, he, hnorm]
  change (_, -σ * (σ⁻¹ * z.2)) = _
  have hmul : -σ * (σ⁻¹ * z.2) = -z.2 := by rw [neg_mul, mul_inv_cancel_left₀ hσ]
  rw [hmul]
  change halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2 =
    (1 - ‖z.1‖ ^ 2 - z.2 ^ 2, z.2) at hcoord
  rw [hcoord]
  congr 1
  ring

private theorem exists_corner_rounding_support_subset
    {X P : Type*} [TopologicalSpace X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (hzero : (univ : Set P) ×ˢ {(0 : ℝ × ℝ)} ⊆ e.target)
    {W : Set X} (hW : IsOpen W)
    (hKW : e.symm '' ((univ : Set P) ×ˢ {(0 : ℝ × ℝ)}) ⊆ W) :
    ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target ∧
      e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε) ⊆ W := by
  let N := e.target ∩ e.symm ⁻¹' W
  have hN : IsOpen N := e.continuousOn_symm.isOpen_inter_preimage e.open_target hW
  have hzeroN : (univ : Set P) ×ˢ {(0 : ℝ × ℝ)} ⊆ N := by
    intro p hp
    exact ⟨hzero hp, hKW (mem_image_of_mem _ hp)⟩
  obtain ⟨A, B, _, hB, hA, hB0, hAB⟩ := generalized_tube_lemma
    (isCompact_univ (X := P)) (isCompact_singleton (x := (0 : ℝ × ℝ))) hN hzeroN
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.mp hB 0 (hB0 (mem_singleton _))
  have hbox {ε : ℝ} (hε : ε ∈ Ioo 0 δ) :
      (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ N := by
    intro p hp
    apply hAB
    refine ⟨hA hp.1, hδB ?_⟩
    exact (closedBall_subset_ball hε.2) hp.2
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  refine ⟨fun p hp => (hbox hε hp).1, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact (hbox hε hp).2

private theorem exists_halfBall_attachment_roof
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O)
    {w : ℝ} (hw : 0 < w) :
    ∃ r ∈ Ioo 0 (min (w / 4) (1 / 16)), ∃ a ∈ Ico (-w) 0, ∃ b ∈ Ioc 0 w, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
        (∀ x, halfBallShearRoof x ≤ f x) ∧
        (∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → f x ∈ Ioo a b) ∧
        (∀ x, ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) → f x = halfBallShearRoof x) ∧
        (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
        ({p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 + r ∧ p.2 ∈ Icc 0 (f p.1)} ⊆ O) ∧
        ∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε (‖x‖ ^ 2) t = 0 ↔ t = f x) ∧
          (0 ≤ roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t ≤ f x) ∧
          (0 < roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t < f x) := by
  obtain ⟨η₀, hη₀, hband⟩ := exists_halfBallShearRoof_band_subset hO hP
  have h1 := Icc_subset_halfBallShearHeight_domain (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hg : ContinuousAt halfBallShearHeight 1 :=
    (contDiffOn_halfBallShearHeight.contDiffAt (isOpen_Ioo.mem_nhds h1)).continuousAt
  have hnear : ∀ᶠ s in 𝓝 (1 : ℝ), halfBallShearHeight s < w / 4 :=
    hg.eventually (isOpen_Iio.mem_nhds (show halfBallShearHeight 1 < w / 4 by
      rw [halfBallShearHeight_one]; positivity))
  obtain ⟨τ, hτ, hτsub⟩ := Metric.eventually_nhds_iff.mp hnear
  let η := min η₀ (w / 4)
  let ρ := min (τ / 4) (min (w / 4) η₀)
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨r, hr, a₀, ha₀, b₀, hb₀, δ, hδ, hroof⟩ :=
    exists_roundedHalfBallCornerRoof_graph (E := E) hρ hη
  have hrρ : r < ρ := hr.2.trans_le (min_le_left _ _)
  have hrw : r < w / 4 := hrρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrτ : 2 * r < τ := by have hh := hrρ.trans_le (min_le_left _ _); linarith
  have hrη : r < η₀ := hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let a := max a₀ (-w)
  let b := min b₀ w
  have ha : a ∈ Ico (-w) 0 := ⟨le_max_right _ _, max_lt ha₀ (neg_neg_of_pos hw)⟩
  have hb : b ∈ Ioc 0 w := ⟨lt_min hb₀ hw, min_le_right _ _⟩
  refine ⟨r, ⟨hr.1, lt_min hrw (hr.2.trans_le (min_le_right _ _))⟩, a, ha, b, hb, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨f, hf, hbound, hroot, heq, hzero, hsign⟩ := hroof ε hε
  have hraw (x : E) (hx : ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r)) : halfBallShearRoof x < w / 4 := by
    by_cases hh : ‖x‖ ^ 2 ≤ 1
    · rw [halfBallShearRoof, if_pos hh]
      apply hτsub
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    · rw [halfBallShearRoof, if_neg hh]
      positivity
  refine ⟨f, hf, fun x => (hbound x).1, ?_, heq, hzero, ?_, ?_⟩
  · intro x hx
    have hheight := (hroot x hx).1
    have hnonneg : 0 ≤ f x := (halfBallShearRoof_nonneg x).trans (hbound x).1
    have hfw : f x < w := by
      have hηw : η ≤ w / 4 := min_le_right _ _
      linarith [hraw x hx, (hbound x).2]
    exact ⟨max_lt hheight.1 (lt_of_lt_of_le (neg_neg_of_pos hw) hnonneg),
      lt_min hheight.2 hfw⟩
  · intro p hp
    apply hband
    refine ⟨by linarith [hp.1], hp.2.1, ?_⟩
    have hηle : η ≤ η₀ := min_le_left _ _
    linarith [hp.2.2, (hbound p.1).2]
  · intro x hx t ht
    exact hsign x hx t ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩

private theorem exists_halfBall_corner_rounding_roof
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P] [CompactSpace P]
    (Ψ G : (E × ℝ) ≃ₘ[ℝ] F)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {B : Set F} {σ : ℝ} (hσ : σ ≠ 0)
    (hP : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source)
    (hc : ∀ p, c p = G (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p))
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hGU : EqOn G (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U)
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, (e (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, -σ * p.2))
    (hzero : (univ : Set P) ×ˢ {(0 : ℝ × ℝ)} ⊆ e.target)
    (hraw : ∀ q ∈ e.target, e.symm q ∈ B ↔ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2)
    (hBc : ∀ p ∈ c.source, c p ∈ B ↔ 0 ≤ p.2 ∧ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2) :
    let d := PartialDiffeomorph.halfBallShear.symm.trans c
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∃ (H : F ≃ₜ F) (f : E → ℝ) (r : ℝ),
      0 < r ∧ ContDiff ℝ ∞ f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
      ({p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 + r ∧ p.2 ∈ Icc 0 (f p.1)} ⊆ d.source) ∧
      d.toOpenPartialHomeomorph.IsImage {p : E × ℝ | f p.1 ≤ p.2} (H '' B) ∧
      H '' B = e.smoothAbsQuadrantSet B ε ∧
      ∃ C : Set F, IsCompact C ∧ C ⊆ d.target ∧ EqOn H id Cᶜ ∧ EqOn H.symm id Cᶜ := by
  let L := PartialDiffeomorph.halfBallShear (E := E)
  let d := L.symm.trans c
  have hLP : L '' {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ d.source := by
    rintro p ⟨q, hq, rfl⟩
    have hqL := PartialDiffeomorph.halfBall_subset_halfBallShear_source hq
    refine ⟨L.map_source hqL, ?_⟩
    change L.symm (L q) ∈ c.source
    have hleft : L.symm (L q) = q := L.left_inv hqL
    rw [hleft]
    exact hP hq
  obtain ⟨w, hw, hcoord⟩ := exists_halfBall_attachment_corner_coordinates Ψ G c e hσ hP hc hU hDU hGU hsource he
  obtain ⟨r, hr, a, ha, b, hb, δ₀, hδ₀, hroof⟩ :=
    exists_halfBall_attachment_roof d.open_source hLP (div_pos hw.1 (by norm_num) : 0 < w / 2)
  let V := {p : E × ℝ | ‖p.1‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) ∧ p.2 ∈ Ioo a b}
  have hV : IsOpen V := ((continuous_fst.norm.pow 2).isOpen_preimage _ isOpen_Ioo).inter
    (continuous_snd.isOpen_preimage _ isOpen_Ioo)
  have hVcoord (p : E × ℝ) (hp : p ∈ V) :
      p ∈ d.source ∧ d p ∈ e.source ∧
      (e (d p)).2 = ((halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1,
        -(halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).2) := by
    apply hcoord
    · rw [abs_lt]
      have hh := hr.2.trans_le (min_le_left _ _)
      constructor <;> linarith [hp.1.1, hp.1.2]
    · rw [abs_lt]
      constructor <;> linarith [hp.2.1, hp.2.2, ha.1, hb.2, hw.1]
  have hVs : V ⊆ d.source := fun p hp => (hVcoord p hp).1
  let W := d '' V
  have hW : IsOpen W := d.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVs
  have hzeroW : e.symm '' ((univ : Set P) ×ˢ {(0 : ℝ × ℝ)}) ⊆ W := by
    rintro y ⟨q, hq, rfl⟩
    let p := Ψ.symm (e.symm q)
    have hp : Ψ p = e.symm q := Ψ.apply_symm_apply _
    have hq0 : q.2 = 0 := hq.2
    have hcq := he p
    rw [hp, e.right_inv (hzero hq), hq0] at hcq
    have ht : p.2 = 0 := by
      have hh : -σ * p.2 = 0 := (congrArg Prod.snd hcq).symm
      exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hσ)
    have hn : ‖p.1‖ = 1 := by
      have hh : 1 - ‖p.1‖ ^ 2 = 0 := (congrArg Prod.fst hcq).symm
      nlinarith [norm_nonneg p.1]
    have hmem : (p.1, (0 : ℝ)) ∈ V := by
      refine ⟨?_, ha.2, hb.1⟩
      change 1 - 2 * r < ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 < 1 + 2 * r
      rw [hn]
      constructor <;> nlinarith [hr.1]
    have hpU : (p.1, (0 : ℝ)) ∈ U := hDU ⟨mem_closedBall_zero_iff.mpr hn.le, rfl⟩
    refine ⟨(p.1, 0), hmem, ?_⟩
    change c (L.symm (p.1, 0)) = e.symm q
    rw [show L.symm (p.1, 0) = (p.1, 0) by
      simp only [L, PartialDiffeomorph.halfBallShear_symm_apply, zero_div, sub_zero,
        inv_one, one_smul], hc,
      PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq one_ne_zero (by simpa only [abs_one] using hn),
      hGU hpU]
    change Ψ ((EuclideanGeometry.halfBallCylinderMap (p.1, 0)).1, σ⁻¹ * 0) = _
    rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
    have hpp : (p.1, (0 : ℝ)) = p := Prod.ext rfl ht.symm
    exact (congrArg Ψ hpp).trans hp
  obtain ⟨δ₁, hδ₁, hsupport⟩ := exists_corner_rounding_support_subset e hzero hW hzeroW
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro ε hε
  have hε₀ : ε ∈ Ioo 0 δ₀ := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hε₁ : ε ∈ Ioo 0 δ₁ := ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  obtain ⟨f, hf, hlower, hheight, heq, hzeroF, hband, hsign⟩ := hroof ε hε₀
  obtain ⟨H, _, _, hC, hCs, hfix, hfixi, hquad, _⟩ :=
    e.exists_homeomorph_smoothAbs_corner hε.1 (hsupport ε hε₁).1
  let C := e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε)
  have hCW : C ⊆ W := (hsupport ε hε₁).2
  have hH : H '' B = e.smoothAbsQuadrantSet B ε := hquad B hraw
  have hinside (p : E × ℝ) (hp : p ∈ V) : d p ∈ H '' B ↔ f p.1 ≤ p.2 := by
    have hpc := hVcoord p hp
    rw [hH, e.mem_smoothAbsQuadrantSet_iff B ε hpc.2.1, hpc.2.2]
    change Real.smoothAbs ε ((halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1 -
      -(halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).2) ≤
      (halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1 +
        -(halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).2 ↔ _
    rw [sub_neg_eq_add, ← sub_eq_add_neg,
      ← roundedHalfBallShearCorner_nonpos_iff hε.1.ne']
    simpa only [not_lt] using not_congr (hsign p.1 hp.1 p.2 (Ioo_subset_Icc_self hp.2)).2.2
  have houtside (p : E × ℝ) (hp : p ∉ V) : f p.1 ≤ p.2 ↔ halfBallShearRoof p.1 ≤ p.2 := by
    by_cases hx : ‖p.1‖ ^ 2 ∈ Ioo (1 - r) (1 + r)
    · have hx' : ‖p.1‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) :=
        ⟨by linarith [hx.1, hr.1], by linarith [hx.2, hr.1]⟩
      have ht : p.2 ∉ Ioo a b := fun hh => hp ⟨hx', hh⟩
      have hfheight := hheight p.1 hx'
      have hrawnonneg := halfBallShearRoof_nonneg p.1
      have hlow := hlower p.1
      constructor
      · exact le_trans hlow
      · intro hh
        have htp : a < p.2 := ha.2.trans_le (hrawnonneg.trans hh)
        have htb : b ≤ p.2 := le_of_not_gt (fun hb => ht ⟨htp, hb⟩)
        exact hfheight.2.le.trans htb
    · rw [heq p.1 hx]
  have hBmodel (p : E × ℝ) (hp : p ∈ d.source) : d p ∈ B ↔ halfBallShearRoof p.1 ≤ p.2 := by
    change c (L.symm p) ∈ B ↔ _
    rw [hBc (L.symm p) hp.2]
    exact (halfBallShearRoof_le_iff_symm hp.1).symm
  refine ⟨H, f, r, hr.1, hf, fun x => (halfBallShearRoof_nonneg x).trans (hlower x),
    hzeroF, hband, ?_, hH, C, hC, ?_, hfix, hfixi⟩
  · intro p hp
    change d p ∈ H '' B ↔ f p.1 ≤ p.2
    by_cases hV : p ∈ V
    · exact hinside p hV
    · have hnotC : d p ∉ C := by
        intro hh
        obtain ⟨q, hq, hqp⟩ := hCW hh
        exact hV ((d.toOpenPartialHomeomorph.injOn (hVs hq) hp hqp) ▸ hq)
      have hmem : d p ∈ H '' B ↔ d p ∈ B := by
        have hh := H.injective.mem_set_image (a := d p) (s := B)
        simpa only [hfix hnotC, id_eq] using hh
      rw [hmem, hBmodel p hp]
      exact (houtside p hV).symm
  · rintro x hx
    obtain ⟨p, hp, rfl⟩ := hCW hx
    exact d.map_source (hVs hp)

theorem exists_diffeomorph_image_halfBall_rounding
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P] [CompactSpace P]
    (Ψ G : (E × ℝ) ≃ₘ[ℝ] F)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {K B : Set F} {σ : ℝ} (hσ : σ ≠ 0)
    (hP : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source)
    (hc : ∀ p, c p = G (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p))
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hGU : EqOn G (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U)
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, (e (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, -σ * p.2))
    (hzero : (univ : Set P) ×ˢ {(0 : ℝ × ℝ)} ⊆ e.target)
    (hraw : ∀ q ∈ e.target, e.symm q ∈ B ↔ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2)
    (hKc : ∀ p ∈ c.source, c p ∈ K ↔ 0 ≤ p.2)
    (hBc : ∀ p ∈ c.source, c p ∈ B ↔ 0 ≤ p.2 ∧ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2)
    (houtside : ∀ x ∉ c.target, x ∈ B ↔ x ∈ K) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∃ D : F ≃ₘ[ℝ] F,
      D '' e.smoothAbsQuadrantSet B ε = K ∧
      ∃ C : Set F, IsCompact C ∧ C ⊆ c.target ∧ EqOn D id Cᶜ ∧ EqOn D.symm id Cᶜ := by
  let L := PartialDiffeomorph.halfBallShear (E := E)
  let d := L.symm.trans c
  obtain ⟨δ, hδ, hroof⟩ := exists_halfBall_corner_rounding_roof Ψ G c e hσ hP hc hU hDU hGU
    hsource he hzero hraw hBc
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨H, f, r, hr, hf, hnonneg, hzeroF, hband, hBimage, hH, C, hC, hCt, hHfix, _⟩ := hroof ε hε
  have hKimage : d.toOpenPartialHomeomorph.IsImage {p : E × ℝ | 0 ≤ p.2} K := by
    intro p hp
    exact hKc (L.symm p) hp.2
  have hout (x : F) (hx : x ∉ d.target) : x ∈ H '' B ↔ x ∈ K := by
    have hnotC : x ∉ C := fun hh => hx (hCt hh)
    have hmem : x ∈ H '' B ↔ x ∈ B := by
      have hh := H.injective.mem_set_image (a := x) (s := B)
      simpa only [hHfix hnotC, id_eq] using hh
    rw [hmem]
    by_cases hxc : x ∈ c.target
    · let p := c.symm x
      have hps : p ∈ c.source := c.map_target hxc
      have hcx : c p = x := c.right_inv hxc
      have ht : 2 ≤ p.2 := by
        apply le_of_not_gt
        intro hh
        exact hx ⟨hxc, hh⟩
      have hpK : c p ∈ K := (hKc p hps).mpr (by linarith)
      have hpB : c p ∈ B := (hBc p hps).mpr ⟨by linarith, by nlinarith [sq_nonneg ‖p.1‖]⟩
      exact iff_of_true (hcx ▸ hpB) (hcx ▸ hpK)
    · exact houtside x hxc
  let R := Real.sqrt (1 + r)
  have hR : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hzero' (x : E) (hx : x ∉ closedBall 0 R) : f x = 0 := by
    have hn : R < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))
    have hsq : R ^ 2 = 1 + r := Real.sq_sqrt (by linarith)
    exact hzeroF x (by nlinarith)
  let g : ℝ × E → ℝ := fun p => (1 - p.1) * f p.2
  have hg : ContDiff ℝ ∞ g := (contDiff_const.sub contDiff_fst).mul (hf.comp contDiff_snd)
  obtain ⟨Φ, hΦ, hΦi, _, _, _, hepi, _, C₀, hC₀, hC₀s, hfix⟩ :=
    Diffeomorph.exists_isotopy_graphOn_endpoints_in_open hg
      (isCompact_closedBall (0 : E) R)
      (by intro t _ x hx; simp only [g, hzero' x hx, mul_zero]) d.open_source (by
        intro t ht x hx
        apply hband
        have hn := mem_closedBall_zero_iff.mp hx
        have hsq : R ^ 2 = 1 + r := Real.sq_sqrt (by linarith)
        refine ⟨by nlinarith [norm_nonneg x], mul_nonneg (sub_nonneg.mpr ht.2) (hnonneg x), ?_⟩
        change (1 - t) * f x ≤ f x
        nlinarith [ht.1, hnonneg x])
  have hepi' : Φ 1 '' {p : E × ℝ | f p.1 ≤ p.2} = {p | 0 ≤ p.2} := by
    simpa only [mem_univ, true_and, g, sub_zero, one_mul, sub_self, zero_mul] using hepi univ
  obtain ⟨J, _, _, hJe, hJC, hJCs, hJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      d.symm.toOpenPartialHomeomorph d.contMDiffOn_invFun d.contMDiffOn_toFun Φ hΦ hΦi hC₀ hC₀s
      (fun t z hz => ⟨(hfix t).1 hz, (hfix t).2 hz⟩)
  have hmap : MapsTo (Φ 1) d.source d.source := by
    intro p hp
    by_contra hh
    have hnot : Φ 1 p ∉ C₀ := fun h => hh (hC₀s h)
    have hid : Φ 1 (Φ 1 p) = Φ 1 p := (hfix 1).1 hnot
    have heq : Φ 1 p = p := (Φ 1).injective hid
    exact hh (heq.symm ▸ hp)
  have hmem (x : F) : J 1 x ∈ K ↔ x ∈ H '' B := by
    rw [(hJe 1 x).1]
    apply DifferentialGeometry.Topology.Manifold.extendChartById_mem_iff
      d.symm.toOpenPartialHomeomorph (Φ 1) hmap hBimage.symm hKimage.symm hout _ x
    intro p _
    rw [← hepi']
    exact (Φ 1).injective.mem_set_image
  have himage : J 1 '' (H '' B) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mpr hy
    · intro hx
      refine ⟨(J 1).symm x, (hmem _).mp ?_, (J 1).apply_symm_apply x⟩
      simpa only [(J 1).apply_symm_apply] using hx
  refine ⟨J 1, hH ▸ himage, d '' C₀, hJC, ?_, ?_, ?_⟩
  · intro x hx
    exact (hJCs hx).1
  · intro x hx
    exact (hJfix 1 x hx).1
  · intro x hx
    exact (hJfix 1 x hx).2

private theorem compl_interior_halfSpace {E : Type*} [TopologicalSpace E] :
    (interior {p : E × ℝ | p.2 ≤ 0})ᶜ = {p | 0 ≤ p.2} := by
  rw [← closure_compl]
  have hh : {p : E × ℝ | p.2 ≤ 0}ᶜ = univ ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp
  rw [hh, closure_prod_eq, closure_univ, closure_Ioi]
  ext p
  simp

private theorem compl_interior_reflex {P : Type*} [TopologicalSpace P] :
    (interior {p : P × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0})ᶜ =
      {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by
  rw [← closure_compl]
  have hh : {p : P × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0}ᶜ =
      univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext p
    simp
  rw [hh, closure_prod_eq, closure_prod_eq, closure_univ, closure_Ioi]
  ext p
  simp [Prod.le_def]

private theorem compl_interior_halfBall_union_halfSpace
    {E : Type*} [NormedAddCommGroup E] :
    (interior {p : E × ℝ | p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1})ᶜ =
      {p | 0 ≤ p.2 ∧ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2} := by
  rw [← closure_compl]
  have hh : {p : E × ℝ | p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1}ᶜ =
      {p | 0 < p.2 ∧ 1 < ‖p.1‖ ^ 2 + p.2 ^ 2} := by
    ext p
    simp
  rw [hh]
  apply Subset.antisymm
  · exact closure_minimal (fun p hp => ⟨hp.1.le, hp.2.le⟩)
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_const ((continuous_fst.norm.pow 2).add (continuous_snd.pow 2))))
  · intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(p.1, p.2 + ε / 2), ⟨by dsimp; linarith [hp.1], ?_⟩, ?_⟩
    · dsimp
      nlinarith [hp.1, hp.2, sq_pos_of_pos hε]
    · rw [Prod.dist_eq, dist_self, Real.dist_eq]
      have heq : p.2 - (p.2 + ε / 2) = -(ε / 2) := by ring
      rw [heq, abs_neg, abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
      linarith

private theorem isCompact_halfBall {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    IsCompact {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} := by
  apply ((isCompact_closedBall (0 : E) 1).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
  · exact (isClosed_le ((continuous_fst.norm.pow 2).add (continuous_snd.pow 2))
      continuous_const).inter (isClosed_le continuous_const continuous_snd)
  · intro p hp
    refine ⟨mem_closedBall_zero_iff.mpr ?_, hp.2, ?_⟩
    · nlinarith [hp.1, sq_nonneg p.2, norm_nonneg p.1]
    · nlinarith [hp.1, sq_nonneg ‖p.1‖]

theorem exists_diffeomorph_image_halfBall_reflex_rounding
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P] [CompactSpace P]
    (Ψ G : (E × ℝ) ≃ₘ[ℝ] F)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {K B : Set F} {σ : ℝ} (hσ : σ ≠ 0)
    (hP : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source)
    (hc : ∀ p, c p = G (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p))
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hGU : EqOn G (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U)
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, (e (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, -σ * p.2))
    (hzero : (univ : Set P) ×ˢ {(0 : ℝ × ℝ)} ⊆ e.target)
    (hraw : ∀ q ∈ e.target, e.symm q ∈ B ↔ q.2.1 ≤ 0 ∨ q.2.2 ≤ 0)
    (hKc : ∀ p ∈ c.source, c p ∈ K ↔ p.2 ≤ 0)
    (hBc : ∀ p ∈ c.source, c p ∈ B ↔ p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1)
    (houtside : ∀ x ∉ c.target, x ∈ B ↔ x ∈ K)
    (hBregular : closure (interior B) = B) (hKregular : closure (interior K) = K) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∃ D : F ≃ₘ[ℝ] F,
      D '' ((B \ e.source) ∪ e.symm ''
        (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)})) = K ∧
      ∃ C : Set F, IsCompact C ∧ C ⊆ c.target ∧ EqOn D id Cᶜ ∧ EqOn D.symm id Cᶜ := by
  let A := {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
  have hA : IsCompact (c '' A) := isCompact_halfBall.image_of_continuousOn
    (c.toOpenPartialHomeomorph.continuousOn.mono hP)
  have hAt : c '' A ⊆ c.target := image_subset_iff.mpr (fun _ hp => c.map_source (hP hp))
  have heq (x : F) (hx : x ∉ c '' A) : x ∈ B ↔ x ∈ K := by
    by_cases ht : x ∈ c.target
    · let p := c.symm x
      have hp : p ∈ c.source := c.map_target ht
      have hcx : c p = x := c.right_inv ht
      rw [← hcx, hBc p hp, hKc p hp]
      constructor
      · rintro (hh | hh)
        · exact hh
        · by_contra hn
          exact hx ⟨p, ⟨hh, (lt_of_not_ge hn).le⟩, hcx⟩
      · exact Or.inl
    · exact houtside x ht
  have heqext (x : F) (hx : x ∉ c.target) : x ∈ (interior B)ᶜ ↔ x ∈ (interior K)ᶜ := by
    let j := OpenPartialHomeomorph.ofSet (c '' A)ᶜ hA.isClosed.isOpen_compl
    have himg : j.IsImage B K := by
      intro y hy
      exact (heq y hy).symm
    exact not_congr (himg.interior (fun hh => hx (hAt hh))).symm
  have hKimage : c.toOpenPartialHomeomorph.IsImage {p : E × ℝ | p.2 ≤ 0} K := by
    intro p hp
    exact hKc p hp
  have hBimage : c.toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1} B := by
    intro p hp
    exact hBc p hp
  have heraw : e.symm.IsImage {p : P × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0} B := by
    intro q hq
    exact hraw q hq
  have hKext := hKimage.interior.compl
  have hBext := hBimage.interior.compl
  have hext := heraw.interior.compl
  rw [compl_interior_halfSpace] at hKext
  rw [compl_interior_halfBall_union_halfSpace] at hBext
  rw [compl_interior_reflex] at hext
  obtain ⟨δ₀, hδ₀, hD⟩ := exists_diffeomorph_image_halfBall_rounding Ψ G c e hσ hP hc hU hDU hGU
    hsource he hzero (fun q hq => hext hq) (fun p hp => hKext hp) (fun p hp => hBext hp) heqext
  obtain ⟨δ₁, hδ₁, hstrip⟩ := exists_corner_rounding_support_subset e hzero isOpen_univ
    (subset_univ _)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro ε hε
  obtain ⟨D, hDimage, C, hC, hCt, hfix, hfixi⟩ := hD ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  obtain ⟨H, _, _, _, _, _, _, hquad, hreflex⟩ := e.exists_homeomorph_smoothAbs_corner hε.1
    (hstrip ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩).1
  have hHext := hquad (interior B)ᶜ (fun q hq => hext hq)
  let J := H.trans D.toHomeomorph
  have hJext : J '' (interior B)ᶜ = (interior K)ᶜ := by
    rw [show (J : F → F) = D ∘ H from rfl, image_comp, hHext, hDimage]
  have hJint : J '' interior B = interior K := by
    rw [J.image_compl] at hJext
    exact compl_injective hJext
  have hJB : J '' B = K := by
    rw [← hBregular, J.image_closure, hJint, hKregular]
  refine ⟨D, ?_, C, hC, hCt, hfix, hfixi⟩
  rw [show (J : F → F) = D ∘ H from rfl, image_comp, hreflex B hraw] at hJB
  exact hJB

end DifferentialGeometry.Topology.Handle
