import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ConnectingCylinder

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

universe u v

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

def outerPunctured : Set c.toBallChart.Punctured :=
  {x | x.val ∉ c.chart '' ball (0 : E3) (5 / 4)}

theorem isClosed_outerPunctured : IsClosed (outerPunctured c) := by
  have hs : ball (0 : E3) (5 / 4) ⊆ c.chart.source := by
    intro x hx
    apply c.closedBall_subset_source
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hx
  have h := c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hs
  exact h.isClosed_compl.preimage continuous_subtype_val

private theorem radialMap_mem_outerPunctured_iff
    (z : S2) {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) :
    c.toBallChart.radialMap z r hr ∈ outerPunctured c ↔ 5 / 4 ≤ r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr.1
  have hsrc : r • z.val ∈ c.chart.source := by
    apply c.closedBall_subset_source
    simpa only [mem_closedBall_zero_iff, BallChart.norm_radial z hr0] using hr.2
  constructor
  · intro h
    by_contra hn
    have hx : r • z.val ∈ ball (0 : E3) (5 / 4) := by
      rw [mem_ball_zero_iff, BallChart.norm_radial z hr0]
      exact lt_of_not_ge hn
    exact h ⟨r • z.val, hx, rfl⟩
  · intro h ⟨x, hx, heq⟩
    have hxs : x ∈ c.chart.source := c.closedBall_subset_source
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hx)
    have he := c.chart.injOn hxs hsrc heq
    rw [he, mem_ball_zero_iff, BallChart.norm_radial z hr0] at hx
    exact (not_lt_of_ge h) hx

def outerLeft (x : outerPunctured c) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  inl c.toBallChart d.toBallChart a.val.toHomeomorph x.val

def outerRight (x : outerPunctured d) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  inr c.toBallChart d.toBallChart a.val.toHomeomorph x.val

theorem isClosedEmbedding_outerLeft : _root_.Topology.IsClosedEmbedding (outerLeft c d a) := by
  let : CompactSpace (outerPunctured c) :=
    isCompact_iff_compactSpace.mp (isClosed_outerPunctured c).isCompact
  have hcont : Continuous (outerLeft c d a) :=
    (continuous_inl c.toBallChart d.toBallChart a.val.toHomeomorph).comp continuous_subtype_val
  exact hcont.isClosedEmbedding ((inl_injective _ _ _).comp Subtype.val_injective)

theorem isClosedEmbedding_outerRight : _root_.Topology.IsClosedEmbedding (outerRight c d a) := by
  let : CompactSpace (outerPunctured d) :=
    isCompact_iff_compactSpace.mp (isClosed_outerPunctured d).isCompact
  have hcont : Continuous (outerRight c d a) :=
    (continuous_inr c.toBallChart d.toBallChart a.val.toHomeomorph).comp continuous_subtype_val
  exact hcont.isClosedEmbedding ((inr_injective _ _ _).comp Subtype.val_injective)

private theorem punctured_radial_of_not_outer (x : c.toBallChart.Punctured)
    (hx : x ∉ outerPunctured c) :
    ∃ z : S2, ∃ r : ℝ, ∃ hr : r ∈ Icc (1 : ℝ) 2,
      r < 5 / 4 ∧ c.toBallChart.radialMap z r hr = x := by
  classical
  have hin : x.val ∈ c.chart '' ball (0 : E3) (5 / 4) := not_not.mp hx
  obtain ⟨y, hy, heq⟩ := hin
  have hy1 : 1 ≤ ‖y‖ := by
    by_contra h
    exact x.property ⟨y, mem_ball_zero_iff.mpr (lt_of_not_ge h), heq⟩
  have hyn : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hy1))
  let z : S2 := ⟨‖y‖⁻¹ • y, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hyn)]⟩
  have hz : ‖y‖ • z.val = y := by
    change ‖y‖ • (‖y‖⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hyn), one_smul]
  have hy2 : ‖y‖ < 5 / 4 := mem_ball_zero_iff.mp hy
  refine ⟨z, ‖y‖, ⟨hy1, by linarith⟩, hy2, ?_⟩
  apply Subtype.ext
  exact (congrArg c.chart hz).trans heq

theorem outer_caps_connectingCylinder_cover :
    range (outerLeft c d a) ∪ range (outerRight c d a) ∪
      range (connectingCylinder c d a) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := jointly_surjective c.toBallChart d.toBallChart a.val.toHomeomorph q
  · by_cases hx : x ∈ outerPunctured c
    · exact Or.inl (Or.inl ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨z, r, hr, hrlt, rfl⟩ := punctured_radial_of_not_outer c x hx
      let t : unitInterval := ⟨(5 - 4 * r) / 2, by constructor <;> linarith [hr.1]⟩
      refine Or.inr ⟨(z, t), ?_⟩
      unfold connectingCylinder
      have ht : 0 ≤ (1 - 2 * t.val) / 4 := by dsimp [t]; linarith [hr.1]
      rw [collarMap_of_nonneg _ _ _ _ ht]
      apply congrArg (inl _ _ _)
      apply Subtype.ext
      change c.chart ((1 + (1 - 2 * t.val) / 4) • z.val) = c.chart (r • z.val)
      congr 2
      dsimp [t]
      ring
  · by_cases hx : x ∈ outerPunctured d
    · exact Or.inl (Or.inr ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨z, r, hr, hrlt, rfl⟩ := punctured_radial_of_not_outer d x hx
      let t : unitInterval := ⟨(4 * r - 3) / 2, by constructor <;> linarith [hr.1]⟩
      refine Or.inr ⟨(a.val.symm z, t), ?_⟩
      by_cases he : r = 1
      · have htt : t = ⟨1 / 2, by constructor <;> norm_num⟩ := by
          apply Subtype.ext
          dsimp [t]
          rw [he]
          norm_num
        rw [htt, connectingCylinder_half, boundary_eq]
        change inr _ _ _ (d.toBallChart.boundaryMap (a.val (a.val.symm z))) = _
        rw [a.val.apply_symm_apply]
        apply congrArg (inr _ _ _)
        apply Subtype.ext
        change d.chart z.val = d.chart (r • z.val)
        rw [he, one_smul]
      · unfold connectingCylinder
        have hrg : 1 < r := lt_of_le_of_ne hr.1 (Ne.symm he)
        have ht : (1 - 2 * t.val) / 4 < 0 := by dsimp [t]; linarith
        rw [collarMap_of_neg _ _ _ _ ht, a.val.apply_symm_apply]
        apply congrArg (inr _ _ _)
        apply Subtype.ext
        change d.chart ((1 - (1 - 2 * t.val) / 4) • z.val) = d.chart (r • z.val)
        congr 2
        dsimp [t]
        ring

private theorem boundary_not_mem_outer (z : S2) :
    c.toBallChart.boundaryMap z ∉ outerPunctured c := by
  intro hx
  exact hx ⟨z.val, mem_ball_zero_iff.mpr (by rw [norm_eq_of_mem_sphere]; norm_num), rfl⟩

theorem disjoint_outer_caps : Disjoint (range (outerLeft c d a)) (range (outerRight c d a)) := by
  apply disjoint_left.mpr
  rintro q ⟨x, rfl⟩ ⟨y, hy⟩
  obtain ⟨z, hz, _⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart a.val.toHomeomorph
    x.val y.val).mp hy.symm
  exact boundary_not_mem_outer c z (hz.symm ▸ x.property)

def outerLeftBoundary (z : S2) : outerPunctured c :=
  ⟨c.toBallChart.radialMap z (5 / 4) (by constructor <;> norm_num),
    (radialMap_mem_outerPunctured_iff c z (by constructor <;> norm_num)).mpr le_rfl⟩

def outerRightBoundary (z : S2) : outerPunctured d := outerLeftBoundary d (a.val z)

theorem connectingCylinder_eq_outerLeft_iff (q : S2 × unitInterval) (x : outerPunctured c) :
    connectingCylinder c d a q = outerLeft c d a x ↔
      q.2 = 0 ∧ outerLeftBoundary c q.1 = x := by
  have hin (p : c.toBallChart.Punctured) :
      inl c.toBallChart d.toBallChart a.val.toHomeomorph p = outerLeft c d a x →
        p ∈ outerPunctured c := by
    intro h
    have he := inl_injective _ _ _ h
    exact he.symm ▸ x.property
  constructor
  · intro h
    by_cases hpos : 0 ≤ (1 - 2 * q.2.val) / 4
    · have heq := h
      unfold connectingCylinder at heq
      rw [collarMap_of_nonneg _ _ _ _ hpos] at heq
      have hout := hin _ heq
      have hrad := (radialMap_mem_outerPunctured_iff c q.1 _).mp hout
      have ht : q.2 = 0 := by
        apply Subtype.ext
        change q.2.val = 0
        linarith [q.2.property.1]
      refine ⟨ht, ?_⟩
      rw [show q = (q.1, (0 : unitInterval)) from Prod.ext rfl ht,
        connectingCylinder_zero] at h
      apply Subtype.ext
      exact inl_injective _ _ _ h
    · unfold connectingCylinder at h
      rw [collarMap_of_neg _ _ _ _ (lt_of_not_ge hpos)] at h
      obtain ⟨z, hz, _⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart a.val.toHomeomorph
        x.val _).mp h.symm
      exact False.elim (boundary_not_mem_outer c z (hz.symm ▸ x.property))
  · rintro ⟨ht, hx⟩
    rw [show q = (q.1, (0 : unitInterval)) from Prod.ext rfl ht, connectingCylinder_zero]
    exact congrArg (inl c.toBallChart d.toBallChart a.val.toHomeomorph) (congrArg Subtype.val hx)

theorem connectingCylinder_eq_outerRight_iff (q : S2 × unitInterval) (x : outerPunctured d) :
    connectingCylinder c d a q = outerRight c d a x ↔
      q.2 = 1 ∧ outerRightBoundary d a q.1 = x := by
  constructor
  · intro h
    by_cases hpos : 0 ≤ (1 - 2 * q.2.val) / 4
    · unfold connectingCylinder at h
      rw [collarMap_of_nonneg _ _ _ _ hpos] at h
      obtain ⟨z, _, hz⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart a.val.toHomeomorph
        _ x.val).mp h
      exact False.elim (boundary_not_mem_outer d (a.val z) (hz.symm ▸ x.property))
    · have heq := h
      unfold connectingCylinder at heq
      rw [collarMap_of_neg _ _ _ _ (lt_of_not_ge hpos)] at heq
      have hrad := inr_injective _ _ _ heq
      have hout := hrad.symm ▸ x.property
      have hlow := (radialMap_mem_outerPunctured_iff d (a.val q.1) _).mp hout
      have ht : q.2 = 1 := by
        apply Subtype.ext
        change q.2.val = 1
        linarith [q.2.property.2]
      refine ⟨ht, ?_⟩
      rw [show q = (q.1, (1 : unitInterval)) from Prod.ext rfl ht,
        connectingCylinder_one] at h
      apply Subtype.ext
      exact inr_injective _ _ _ h
  · rintro ⟨ht, hx⟩
    rw [show q = (q.1, (1 : unitInterval)) from Prod.ext rfl ht, connectingCylinder_one]
    exact congrArg (inr c.toBallChart d.toBallChart a.val.toHomeomorph) (congrArg Subtype.val hx)

end DifferentialGeometry.Topology.ConnectedSumQuotient
