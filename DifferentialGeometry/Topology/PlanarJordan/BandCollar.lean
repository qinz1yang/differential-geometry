import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.AddCircle
import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import Mathlib.Topology.MetricSpace.Thickening

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_open_band_edge_neighborhood
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {U : Set ℝ} (hU : IsOpen U) (a : ℝ)
    (hedge : (fun u => B (a, u)) '' U ⊆ range γ) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ {a} ×ˢ U ⊆ V ∧ V ⊆ univ ×ˢ U ∧
      ∀ z ∈ V, B z ∈ range γ ↔ z.1 = a := by
  let O : TopologicalSpace.Opens ℝ := ⟨U, hU⟩
  let f : O → Schoenflies.Plane := fun u => B (a, u)
  let A : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph
  have hf₀ := ((_root_.Manifold.IsSmoothEmbedding.of_opens (I := 𝓘(ℝ, ℝ)) (n := ∞) O).graph
    (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => a))).diffeomorph_comp A
  have hf : _root_.Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ f :=
    hf₀.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun x => B.isLocalDiffeomorph x) (by simp)
  have hfsub : range f ⊆ range γ := by
    rintro y ⟨u, rfl⟩
    exact hedge ⟨u, u.property, rfl⟩
  have ho := hf.isOpen_preimage_range_of_range_subset hγ (by simp) rfl hfsub
  obtain ⟨W, hW, hWeq⟩ := hγ.isEmbedding.isInducing.image_eq_isOpen_inter_range ho
  rw [image_preimage_eq_inter_range, inter_eq_left.mpr hfsub] at hWeq
  have hWf : range f ⊆ W := hWeq ▸ inter_subset_left
  refine ⟨B ⁻¹' W ∩ (univ ×ˢ U), (hW.preimage B.continuous).inter (isOpen_univ.prod hU), ?_,
    inter_subset_right, ?_⟩
  · rintro ⟨x, u⟩ ⟨rfl, hu⟩
    exact ⟨hWf ⟨⟨u, hu⟩, rfl⟩, mem_univ _, hu⟩
  · intro z hz
    constructor
    · intro hzg
      have hzf : B z ∈ range f := hWeq.symm ▸ ⟨hz.1, hzg⟩
      obtain ⟨u, hu⟩ := hzf
      exact (congrArg Prod.fst (B.injective hu)).symm
    · intro hza
      exact hedge ⟨z.2, hz.2.2, by rw [← hza]⟩

theorem exists_band_edge_collar
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {U : Set ℝ} (hU : IsOpen U) (a : ℝ)
    (hedge : (fun u => B (a, u)) '' U ⊆ range γ)
    {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Ioo (a - ε) (a + ε) ×ˢ K,
      B z ∈ range γ ↔ z.1 = a := by
  obtain ⟨V, hV, hUV, _, heq⟩ := exists_open_band_edge_neighborhood hγ B hU a hedge
  obtain ⟨ε, hε, hεV⟩ := (isCompact_singleton.prod hK).exists_thickening_subset_open
    hV ((prod_mono Subset.rfl hKU).trans hUV)
  refine ⟨ε, hε, fun z hz => heq z (hεV ?_)⟩
  refine Metric.mem_thickening_iff.mpr ⟨(a, z.2), ⟨rfl, hz.2⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, abs_lt]
  constructor <;> linarith [hz.1.1, hz.1.2]

theorem exists_band_edge_region_collar
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {a h k : ℝ} (hk : 0 < k) (hkh : k < h)
    (hedge : (fun u => B (a, u)) '' Ioo (-h) h ⊆ range γ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Ioo (a - ε) (a + ε) ×ˢ Ioo (-k) k,
        B z ∈ range γ ↔ z.1 = a) ∧
      ((∀ z ∈ Ioo (a - ε) (a + ε) ×ˢ Ioo (-k) k,
        B z ∈ Schoenflies.inside (range γ) ↔ a < z.1) ∨
      (∀ z ∈ Ioo (a - ε) (a + ε) ×ˢ Ioo (-k) k,
        B z ∈ Schoenflies.inside (range γ) ↔ z.1 < a)) := by
  obtain ⟨ε, hε, hcurve⟩ := exists_band_edge_collar hγ B isOpen_Ioo a hedge
    (isCompact_Icc (a := -k) (b := k)) (by
      intro u hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  let R : Set (ℝ × ℝ) := Ioo (a - ε) (a + ε) ×ˢ Ioo (-k) k
  let W := B '' R
  let g : Schoenflies.Plane → ℝ := fun q => (B.symm q).1 - a
  have hW : IsOpen W := B.toHomeomorph.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)
  have heq (z : ℝ × ℝ) (hz : z ∈ R) : B z ∈ range γ ↔ z.1 = a :=
    hcurve z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hzero (q : Schoenflies.Plane) (hq : q ∈ W) : q ∈ range γ ↔ g q = 0 := by
    obtain ⟨z, hz, rfl⟩ := hq
    simpa only [g, B.symm_apply_apply, sub_eq_zero] using heq z hz
  have hpos : W ∩ {q | 0 < g q} = B '' (Ioo a (a + ε) ×ˢ Ioo (-k) k) := by
    ext q
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hp⟩
      have hp' : a < z.1 := by simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_pos] using hp
      exact ⟨z, ⟨⟨hp', hz.1.2⟩, hz.2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩, rfl⟩, ?_⟩
      simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_pos] using hz.1.1
  have hneg : W ∩ {q | g q < 0} = B '' (Ioo (a - ε) a ×ˢ Ioo (-k) k) := by
    ext q
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hp⟩
      have hp' : z.1 < a := by simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_neg] using hp
      exact ⟨z, ⟨⟨hz.1.1, hp'⟩, hz.2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩, rfl⟩, ?_⟩
      simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_neg] using hz.1.2
  have hposconn : IsPreconnected (W ∩ {q | 0 < g q}) := by
    rw [hpos]
    exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ B.continuous.continuousOn
  have hnegconn : IsPreconnected (W ∩ {q | g q < 0}) := by
    rw [hneg]
    exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ B.continuous.continuousOn
  have hpR : (a, 0) ∈ R :=
    ⟨⟨by dsimp [R]; linarith, by dsimp [R]; linarith⟩, neg_neg_of_pos hk, hk⟩
  have hC := Schoenflies.jordan_curve_theorem
    (isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hγ.isEmbedding)
  obtain hs | hs := hC.local_side_sign hW ((heq _ hpR).mpr rfl) ⟨(a, 0), hpR, rfl⟩
    g hzero hposconn hnegconn
  · refine ⟨ε, hε, heq, Or.inl ?_⟩
    intro z hz
    simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_pos] using hs (B z) ⟨z, hz, rfl⟩
  · refine ⟨ε, hε, heq, Or.inr ?_⟩
    intro z hz
    simpa only [mem_ofPred_eq, g, B.symm_apply_apply, sub_neg] using hs (B z) ⟨z, hz, rfl⟩


theorem exists_band_attaching_collars
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {h k : ℝ} (hk : 0 < k) (hkh : k < h)
    (hleft : (fun u => B (-1, u)) '' Ioo (-h) h ⊆ range γ)
    (hright : (fun u => B (1, u)) '' Ioo (-h) h ⊆ range γ)
    (havoid : ∀ z ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h, B z ∉ range γ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
        B z ∈ range γ ↔ z.1 = -1) ∧
      (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
        B z ∈ range γ ↔ z.1 = 1) ∧
      (((∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
          B z ∈ Schoenflies.inside (range γ) ↔ -1 < z.1) ∧
        (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
          B z ∈ Schoenflies.inside (range γ) ↔ z.1 < 1)) ∨
       ((∀ z ∈ Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k,
          B z ∈ Schoenflies.inside (range γ) ↔ z.1 < -1) ∧
        (∀ z ∈ Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k,
          B z ∈ Schoenflies.inside (range γ) ↔ 1 < z.1))) := by
  obtain ⟨ε₀, hε₀, hc₀, hs₀⟩ := exists_band_edge_region_collar hγ B hk hkh hleft
  obtain ⟨ε₁, hε₁, hc₁, hs₁⟩ := exists_band_edge_region_collar hγ B hk hkh hright
  let ε := min (min ε₀ ε₁) 1 / 2
  have hε : 0 < ε := half_pos (lt_min (lt_min hε₀ hε₁) zero_lt_one)
  have hεlt : ε < 1 := by dsimp [ε]; have := min_le_right (min ε₀ ε₁) 1; linarith
  have hεle₀ : ε ≤ ε₀ := by
    have h₀ := (min_le_left (min ε₀ ε₁) 1).trans (min_le_left ε₀ ε₁)
    dsimp [ε]
    linarith
  have hεle₁ : ε ≤ ε₁ := by
    have h₁ := (min_le_left (min ε₀ ε₁) 1).trans (min_le_right ε₀ ε₁)
    dsimp [ε]
    linarith
  have hsub₀ : Ioo (-1 - ε) (-1 + ε) ×ˢ Ioo (-k) k ⊆
      Ioo (-1 - ε₀) (-1 + ε₀) ×ˢ Ioo (-k) k := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hsub₁ : Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-k) k ⊆
      Ioo (1 - ε₁) (1 + ε₁) ×ˢ Ioo (-k) k := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  refine ⟨ε, hε, hεlt, fun z hz => hc₀ z (hsub₀ hz), fun z hz => hc₁ z (hsub₁ hz), ?_⟩
  let R : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h
  have hS : IsPreconnected (B '' R) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ B.continuous.continuousOn
  have hC := Schoenflies.jordan_curve_theorem
    (isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hγ.isEmbedding)
  have hcover : B '' R ⊆ Schoenflies.inside (range γ) ∪ Schoenflies.outside (range γ) := by
    rw [Schoenflies.inside_union_outside]
    rintro _ ⟨z, hz, rfl⟩
    exact havoid z hz
  have hconst (x y : ℝ × ℝ) (hx : x ∈ R) (hy : y ∈ R) :
      B x ∈ Schoenflies.inside (range γ) ↔ B y ∈ Schoenflies.inside (range γ) := by
    rcases hS.subset_or_subset hC.isOpen_inside hC.isOpen_outside
      Schoenflies.disjoint_inside_outside hcover with hi | ho
    · exact iff_of_true (hi ⟨x, hx, rfl⟩) (hi ⟨y, hy, rfl⟩)
    · exact iff_of_false
        (fun hxI => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hxI (ho ⟨x, hx, rfl⟩))
        (fun hyI => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyI (ho ⟨y, hy, rfl⟩))
  let x : ℝ × ℝ := (-1 + ε / 2, 0)
  let y : ℝ × ℝ := (1 - ε / 2, 0)
  have hx₀ : x ∈ Ioo (-1 - ε₀) (-1 + ε₀) ×ˢ Ioo (-k) k := by
    apply hsub₀
    exact ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, neg_neg_of_pos hk, hk⟩
  have hy₁ : y ∈ Ioo (1 - ε₁) (1 + ε₁) ×ˢ Ioo (-k) k := by
    apply hsub₁
    exact ⟨⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩, neg_neg_of_pos hk, hk⟩
  have hxR : x ∈ R := by
    exact ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩,
      by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hyR : y ∈ R := by
    exact ⟨⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩,
      by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  have hxy := hconst x y hxR hyR
  rcases hs₀ with hp₀ | hn₀ <;> rcases hs₁ with hp₁ | hn₁
  · have hxI := (hp₀ x hx₀).mpr (by dsimp [x]; linarith)
    have hygt := (hp₁ y hy₁).mp (hxy.mp hxI)
    dsimp [y] at hygt
    linarith
  · exact Or.inl ⟨fun z hz => hp₀ z (hsub₀ hz), fun z hz => hn₁ z (hsub₁ hz)⟩
  · exact Or.inr ⟨fun z hz => hn₀ z (hsub₀ hz), fun z hz => hp₁ z (hsub₁ hz)⟩
  · have hyI := (hn₁ y hy₁).mpr (by dsimp [y]; linarith)
    have hxlt := (hn₀ x hx₀).mp (hxy.mpr hyI)
    dsimp [x] at hxlt
    linarith

end DifferentialGeometry.Topology.PlanarJordan
