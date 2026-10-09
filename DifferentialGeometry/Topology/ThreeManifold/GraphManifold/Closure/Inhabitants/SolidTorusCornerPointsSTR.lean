import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusNonemptySTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 9: the two corner points and their actual rim fibres

`qRim_zero_STR : qRim 0 = 4/5 + i √119/20` and `qRim_one_STR : qRim 1 = 4/5 - i √119/20` (the two
corner points `q±` of `C₁`, `‖q±‖² = 15/16`, `Re q± = 4/5`, `Im q± ≠ 0`), the active labels at the
rim base point of an endpoint (`corner_labels_STR`: ball and vertical face active, cusp face not,
the whole fibre in both faces) and `corner_incidences_STR` (two incidences on the same ball face).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CornerPointsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CornerPointsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- The corner points `q± = 4/5 ± i √119/20`. -/
def qPlus_STR : ℂ := ⟨4 / 5, √119 / 20⟩

def qMinus_STR : ℂ := ⟨4 / 5, -(√119 / 20)⟩

theorem zRim_sq_STR {τ : ℝ} (hτ : τ = 0 ∨ τ = 1) :
    zRim_STR τ ^ 2 = (rr_STR + kap_STR) / (rr_STR - kap_STR) := by
  have h : (1 - 2 * τ) ^ 2 = 1 := by rcases hτ with rfl | rfl <;> norm_num
  rw [zRim_STR, mul_pow, h, one_mul]
  exact cR_sq_STR kap_lt_rr_STR

theorem re_qRim_STR {τ : ℝ} (hτ : τ = 0 ∨ τ = 1) : (qRim_STR τ).re = 4 / 5 := by
  rw [qRim_STR, qOf_re_STR, zRim_sq_STR hτ]
  have h1 : 0 < rr_STR - kap_STR := sub_pos.2 kap_lt_rr_STR
  have hk : kap_STR = 4 / 5 := rfl
  have h2 : 0 < rr_STR + kap_STR := by rw [hk]; linarith [rr_pos_STR]
  field_simp
  rw [hk]
  ring

theorem norm_sq_qRim_STR (τ : ℝ) : ‖qRim_STR τ‖ ^ 2 = 15 / 16 := by
  rw [norm_qRim_STR, rr_sq_STR]

theorem im_sq_qRim_STR {τ : ℝ} (hτ : τ = 0 ∨ τ = 1) : (qRim_STR τ).im ^ 2 = 119 / 400 := by
  have h := norm_sq_qRim_STR τ
  rw [Complex.sq_norm, Complex.normSq_apply, re_qRim_STR hτ] at h
  nlinarith

theorem sqrt119_STR : (√119 / 20) ^ 2 = (119 / 400 : ℝ) := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem im_qRim_zero_STR : (qRim_STR 0).im = √119 / 20 := by
  have hc := cR_pos_STR kap_lt_rr_STR
  have hpos : 0 < (qRim_STR 0).im := by
    rw [qRim_STR, qOf_im_STR, zRim_STR]
    have this : 0 < (1 - 2 * (0 : ℝ)) * cR_STR rr_STR := by simpa using hc
    exact div_pos (mul_pos (mul_pos two_pos rr_pos_STR) this) (by positivity)
  have h := im_sq_qRim_STR (Or.inl rfl : (0 : ℝ) = 0 ∨ (0 : ℝ) = 1)
  have hs : 0 ≤ √119 / 20 := by positivity
  nlinarith [sqrt119_STR]

theorem im_qRim_one_STR : (qRim_STR 1).im = -(√119 / 20) := by
  have hc := cR_pos_STR kap_lt_rr_STR
  have hneg : (qRim_STR 1).im < 0 := by
    rw [qRim_STR, qOf_im_STR, zRim_STR]
    have : (1 - 2 * (1 : ℝ)) * cR_STR rr_STR < 0 := by nlinarith
    have h2 : 0 < rr_STR := rr_pos_STR
    have h3 : 0 < ((1 - 2 * (1 : ℝ)) * cR_STR rr_STR) ^ 2 + 1 := by positivity
    rw [div_neg_iff]
    right
    exact ⟨by nlinarith, h3⟩
  have h := im_sq_qRim_STR (Or.inr rfl : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1)
  have hs : 0 ≤ √119 / 20 := by positivity
  nlinarith [sqrt119_STR]

theorem qRim_zero_STR : qRim_STR 0 = qPlus_STR :=
  Complex.ext (re_qRim_STR (Or.inl rfl)) im_qRim_zero_STR

theorem qRim_one_STR : qRim_STR 1 = qMinus_STR :=
  Complex.ext (re_qRim_STR (Or.inr rfl)) im_qRim_one_STR

theorem qPlus_ne_qMinus_STR : qPlus_STR ≠ qMinus_STR := by
  intro h
  have h1 : √119 / 20 = -(√119 / 20) := congrArg Complex.im h
  have h2 : 0 < √119 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-! ## The corner fibres -/

theorem corner_labels_STR (e : rows_STR.edge.EdgeEnd) :
    phiL_STR labBall_STR (rimBase_STR e.1) = 0 ∧ phiL_STR labVert_STR (rimBase_STR e.1) = 0 ∧
      phiL_STR labCusp_STR (rimBase_STR e.1) < 0 ∧
      rows_STR.circle.fibre (rimBase_STR e.1) ⊆
        circleFaceSet rows_STR.slimPieces rows_STR.edge (.horizontal (faces_STR.horizontal e)) ∧
      rows_STR.circle.fibre (rimBase_STR e.1) ⊆
        circleFaceSet rows_STR.slimPieces rows_STR.edge (.vertical e.component) ∧
      rows_STR.edge.rim e.1 = rows_STR.circle.fibre (rimBase_STR e.1) := by
  have hτ := edgeEnd_val_STR e
  have hq := qOfBase_rimBase_STR e.1
  have hn := norm_q_sq_STR (rimBase_STR e.1)
  have hr := re_q_STR (rimBase_STR e.1)
  have hB : phiBall_STR (rimBase_STR e.1) = 0 := by
    simp only [phiBall_STR, gBall_STR]
    rw [← hr, hq, re_qRim_STR hτ]
    norm_num
  have hV : phiVert_STR (rimBase_STR e.1) = 0 := by
    simp only [phiVert_STR, gVert_STR]
    rw [← hn, hq, norm_sq_qRim_STR]
    norm_num
  have hA : phiCusp_STR (rimBase_STR e.1) < 0 := by
    simp only [phiCusp_STR, gCusp_STR]
    rw [← hn, hq, norm_sq_qRim_STR]
    norm_num
  have hcb : rimBase_STR e.1 ∈ rows_STR.circle.cbase :=
    mem_cbase_STR.2 ⟨hA.le, hV.le, hB.le⟩
  refine ⟨hB, hV, hA, ?_, ?_, rim_fibre_STR e.1⟩
  · have h := (fibre_iff_STR (f := labBall_STR) hcb).2 hB
    exact h
  · have hc : e.component = cbaseComp_STR := actualComponent_eq_STR _
    rw [hc]
    exact (fibre_iff_STR (f := labVert_STR) hcb).2 hV

/-- Two incidences: the two endpoints `t = 0, 1` have distinct rim base points `q±` and disjoint
whole rims, and both are attached to the same ball face. -/
theorem corner_incidences_STR : ∃ e₀ e₁ : rows_STR.edge.EdgeEnd, e₀ ≠ e₁ ∧
    faces_STR.horizontal e₀ = faces_STR.horizontal e₁ ∧
    qOfBase_STR (rimBase_STR e₀.1).1 = qPlus_STR ∧ qOfBase_STR (rimBase_STR e₁.1).1 = qMinus_STR ∧
    rimBase_STR e₀.1 ≠ rimBase_STR e₁.1 ∧
    Disjoint (rows_STR.edge.rim e₀.1) (rows_STR.edge.rim e₁.1) ∧
    (rows_STR.edge.rim e₀.1).Nonempty ∧ (rows_STR.edge.rim e₁.1).Nonempty := by
  refine ⟨endAt_STR 0 (Or.inl rfl), endAt_STR 1 (Or.inr rfl), ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun e : rows_STR.edge.EdgeEnd => coordE_STR e.1) h
    simp [endAt_STR, coordE_STR] at h1
  · rw [qOfBase_rimBase_STR]
    exact qRim_zero_STR
  · rw [qOfBase_rimBase_STR]
    exact qRim_one_STR
  · intro h
    have h1 := congrArg (fun b : rows_STR.circle.Base => qOfBase_STR b.1) h
    change qOfBase_STR (rimBase_STR (endAt_STR 0 (Or.inl rfl)).1).1 =
      qOfBase_STR (rimBase_STR (endAt_STR 1 (Or.inr rfl)).1).1 at h1
    rw [qOfBase_rimBase_STR, qOfBase_rimBase_STR] at h1
    have h2 : qRim_STR (coordE_STR (endAt_STR 0 (Or.inl rfl)).1) =
        qRim_STR (coordE_STR (endAt_STR 1 (Or.inr rfl)).1) := h1
    have e0 : coordE_STR (endAt_STR 0 (Or.inl rfl)).1 = 0 := by simp [endAt_STR, coordE_STR]
    have e1 : coordE_STR (endAt_STR 1 (Or.inr rfl)).1 = 1 := by simp [endAt_STR, coordE_STR]
    rw [e0, e1, qRim_zero_STR, qRim_one_STR] at h2
    exact qPlus_ne_qMinus_STR h2
  · rw [Set.disjoint_left]
    intro y hy0 hy1
    have h0 := rim_eq_STR ballZeroDomainsL_STR (endAt_STR 0 (Or.inl rfl)).1
    have h1 := rim_eq_STR ballZeroDomainsL_STR (endAt_STR 1 (Or.inr rfl)).1
    have a0 := (Set.ext_iff.1 h0 y).1 hy0
    have a1 := (Set.ext_iff.1 h1 y).1 hy1
    obtain ⟨hp, ht0, -⟩ := a0
    obtain ⟨hp', ht1, -⟩ := a1
    have e0 : coordE_STR (endAt_STR 0 (Or.inl rfl)).1 = 0 := by simp [endAt_STR, coordE_STR]
    have e1 : coordE_STR (endAt_STR 1 (Or.inr rfl)).1 = 1 := by simp [endAt_STR, coordE_STR]
    have c0 : tOf_STR (sphereSecond y.val) = 0 := ht0.trans e0
    have c1 : tOf_STR (sphereSecond y.val) = 1 := ht1.trans e1
    rw [c0] at c1
    norm_num at c1
  · obtain ⟨-, -, -, -, -, h⟩ := corner_labels_STR (endAt_STR 0 (Or.inl rfl))
    rw [h]
    exact fibre_nonempty_STR _
  · obtain ⟨-, -, -, -, -, h⟩ := corner_labels_STR (endAt_STR 1 (Or.inr rfl))
    rw [h]
    exact fibre_nonempty_STR _

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
