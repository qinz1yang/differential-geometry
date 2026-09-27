import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import DifferentialGeometry.Topology.Manifold.BallChartPalaisTransport
import DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_diffeomorph_straightening_embedded_closedBall_scale_le
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ φ.source)
    {V : Set E} (hV : IsOpen V) (himage : φ '' closedBall 0 r ⊆ V)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ (A : E ≃L[ℝ] E) (ε : ℝ) (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞),
      (A : E →L[ℝ] E) = fderiv ℝ φ 0 ∧ 0 < ε ∧ ε ≤ μ ∧
      (∀ x ∈ closedBall 0 r, F (φ x) = ε • A x + φ 0) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
        ∀ y, y ∉ K → F y = y ∧ F.symm y = y := by
  have h0B : (0 : E) ∈ closedBall 0 r := mem_closedBall_self hr.le
  obtain ⟨A, hA, L, hgerm, K₀, hK₀, hK₀V, hLfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_straightening_partialDiffeomorph
      φ (hrs h0B) hV (himage ⟨0, h0B, rfl⟩)
  obtain ⟨δ, hδ, hδeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let ε := min μ (min 1 (δ / r))
  have hε : 0 < ε := lt_min hμ (lt_min zero_lt_one (div_pos hδ hr))
  have hεμ : ε ≤ μ := min_le_left _ _
  have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεr : ε * r ≤ δ := by
    have h1 : ε ≤ δ / r := le_trans (min_le_right _ _) (min_le_right _ _)
    exact (le_div_iff₀ hr).mp h1
  let t := -Real.log ε
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hε.le hε1)
  have hexp : Real.exp (-t) = ε := by simp only [t, neg_neg, Real.exp_log hε]
  obtain ⟨D, _, _, _, hrad, K₁, hK₁, hK₁V, _, hDfix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall φ hr hrs hV himage
  let F := (D t).trans L.symm
  have hFfix (y : E) (hy : y ∉ K₀ ∪ K₁) : F y = y := by
    have h₀ : y ∉ K₀ := fun h ↦ hy (Or.inl h)
    have h₁ : y ∉ K₁ := fun h ↦ hy (Or.inr h)
    change L.symm (D t y) = y
    rw [(hDfix t y h₁).1, (hLfix y h₀).2]
  refine ⟨A, ε, F, hA, hε, hεμ, ?_, K₀ ∪ K₁, hK₀.union hK₁,
    union_subset hK₀V hK₁V, ?_⟩
  · intro x hx
    have hεx : ε • x ∈ closedBall 0 δ := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hε.le).trans hεr
    have heq : L (A (ε • x) + φ 0) = φ (ε • x) := hδeq hεx
    change L.symm (D t (φ x)) = _
    rw [hrad t x ht hx, hexp, ← heq, L.symm_apply_apply, map_smul]
  · intro y hy
    refine ⟨hFfix y hy, ?_⟩
    apply F.injective
    exact (F.apply_symm_apply y).trans (hFfix y hy).symm

theorem exists_compact_diffeomorph_eqOn_closedBall_of_same_germ_of_subset
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (h₀ : closedBall (0 : E) 2 ⊆ φ₀.source) (h₁ : closedBall (0 : E) 2 ⊆ φ₁.source)
    (hc : φ₀ 0 = φ₁ 0) (hd : fderiv ℝ (φ₀ : E → E) 0 = fderiv ℝ (φ₁ : E → E) 0)
    {V : Set E} (hV : IsOpen V) (hV₀ : φ₀ '' closedBall 0 2 ⊆ V)
    (hV₁ : φ₁ '' closedBall 0 2 ⊆ V) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x ∈ closedBall (0 : E) 2, F (φ₀ x) = φ₁ x) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧ ∀ y ∉ K, F y = y ∧ F.symm y = y := by
  have hb0 : (0 : E) ∈ closedBall (0 : E) 2 := mem_closedBall_self (by norm_num)
  have hpV : φ₀ 0 ∈ V := hV₀ ⟨0, hb0, rfl⟩
  obtain ⟨ρ₀, hρ₀pos, hρ₀V⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  set ρ : ℝ := ρ₀ / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρV : closedBall (φ₀ 0) ρ ⊆ V := fun y hy ↦
    hρ₀V (closedBall_subset_ball (by rw [hρdef]; linarith) hy)
  set n : ℝ := ‖(fderiv ℝ (φ₀ : E → E) 0)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  set μ : ℝ := min 1 (ρ / (4 * (n + 1))) with hμ
  have hμpos : 0 < μ := lt_min zero_lt_one (div_pos hρpos (by positivity))
  obtain ⟨A₀, ε₀, F₀, hA₀, hε₀, hε₀μ, hF₀, K₀, hK₀c, hK₀V, hK₀fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := μ) φ₀ (by norm_num)
      h₀ hV hV₀ hμpos
  obtain ⟨A₁, ε₁, F₁, hA₁, hε₁, hε₁μ, hF₁, K₁, hK₁c, hK₁V, hK₁fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := μ) φ₁ (by norm_num)
      h₁ hV hV₁ hμpos
  have hAeq : (A₀ : E →L[ℝ] E) = (A₁ : E →L[ℝ] E) := by rw [hA₀, hA₁, hd]
  have hA₁x : ∀ x : E, A₁ x = A₀ x := fun x ↦ by
    have := congrArg (fun f : E →L[ℝ] E ↦ f x) hAeq
    exact this.symm
  have hn₀ : ‖(A₀ : E →L[ℝ] E)‖ = n := by rw [hA₀, hn]
  have hμn : μ * n ≤ ρ / 4 := by
    have h1 : μ ≤ ρ / (4 * (n + 1)) := min_le_right _ _
    have h3 : μ * n ≤ ρ / (4 * (n + 1)) * n := mul_le_mul_of_nonneg_right h1 hn0
    have h4 : ρ / (4 * (n + 1)) * n ≤ ρ / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    linarith
  have hb₀ : 2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖ ≤ ρ / 2 := by
    calc 2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖ = 2 * ε₀ * n := by rw [hn₀]
      _ ≤ 2 * μ * n := by nlinarith [hε₀μ, hn0]
      _ ≤ 2 * (ρ / 4) := by nlinarith [hμn]
      _ = ρ / 2 := by ring
  have hb₁ : 2 * ε₁ * ‖(A₀ : E →L[ℝ] E)‖ ≤ ρ / 2 := by
    calc 2 * ε₁ * ‖(A₀ : E →L[ℝ] E)‖ = 2 * ε₁ * n := by rw [hn₀]
      _ ≤ 2 * μ * n := by nlinarith [hε₁μ, hn0]
      _ ≤ 2 * (ρ / 4) := by nlinarith [hμn]
      _ = ρ / 2 := by ring
  set c : ℝ := ε₁ / ε₀ with hcdef
  have hcpos : 0 < c := div_pos hε₁ hε₀
  have hcmul : c * ε₀ = ε₁ := by rw [hcdef, div_mul_cancel₀ _ hε₀.ne']
  set η : ℝ := ρ / (4 * (c + 1)) with hηdef
  have hηpos : 0 < η := div_pos hρpos (by positivity)
  have hηle : η ≤ ρ / 4 := by
    rw [hηdef]
    exact div_le_div_of_nonneg_left hρpos.le (by norm_num) (by linarith [hcpos])
  have hcη : c * η ≤ ρ / 4 := by
    have h1 : c * η = ρ / 4 * (c / (c + 1)) := by rw [hηdef]; field_simp
    have h2 : c / (c + 1) ≤ 1 := (div_le_one (by linarith [hcpos])).mpr (by linarith)
    rw [h1]
    nlinarith [hρpos.le, h2]
  set r : ℝ := 2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖ + η with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    have h : 0 ≤ 2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖ := by positivity
    linarith
  have hRr : r < ρ := by rw [hrdef]; linarith [hb₀, hηle]
  have hcr : c * r < ρ := by
    have h1 : c * r = c * (2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖) + c * η := by rw [hrdef]; ring
    have h2 : c * (2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖) =
        2 * ε₁ * ‖(A₀ : E →L[ℝ] E)‖ := by
      rw [← hcmul]; ring
    rw [h1, h2]
    linarith [hb₁, hcη]
  obtain ⟨H, hHexact, hHfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_scale_at (φ₀ 0) hrpos hcpos hRr hcr
  have hkey : ∀ x ∈ closedBall (0 : E) 2,
      H (ε₀ • A₀ x + φ₀ 0) = ε₁ • A₁ x + φ₁ 0 := by
    intro x hx
    have hmem : ε₀ • A₀ x + φ₀ 0 ∈ closedBall (φ₀ 0) r := by
      have hsub : ε₀ • A₀ x + φ₀ 0 - φ₀ 0 = ε₀ • A₀ x := by abel
      rw [mem_closedBall, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε₀]
      have hop : ‖A₀ x‖ ≤ ‖(A₀ : E →L[ℝ] E)‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm (A₀ : E →L[ℝ] E) x
      have hx2 : ‖x‖ ≤ 2 := by simpa using hx
      have h1 : ε₀ * ‖A₀ x‖ ≤ ε₀ * (‖(A₀ : E →L[ℝ] E)‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left hop hε₀.le
      have h2 : ε₀ * (‖(A₀ : E →L[ℝ] E)‖ * ‖x‖) ≤
          ε₀ * (‖(A₀ : E →L[ℝ] E)‖ * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx2 (norm_nonneg _)) hε₀.le
      have h3 : ε₀ * (‖(A₀ : E →L[ℝ] E)‖ * 2) =
          2 * ε₀ * ‖(A₀ : E →L[ℝ] E)‖ := by ring
      rw [hrdef]
      linarith [h1, h2, h3, hηpos]
    rw [hHexact _ hmem]
    have hsub : ε₀ • A₀ x + φ₀ 0 - φ₀ 0 = ε₀ • A₀ x := by abel
    rw [hsub, smul_smul, hA₁x x, hcmul, hc, add_comm]
  refine ⟨F₀.trans (H.trans F₁.symm), ?_, ?_⟩
  · intro x hx
    rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
      hF₀ x hx, hkey x hx, ← hF₁ x hx, Diffeomorph.symm_apply_apply]
  · refine ⟨K₀ ∪ closedBall (φ₀ 0) ρ ∪ K₁,
      (hK₀c.union (isCompact_closedBall _ _)).union hK₁c, ?_, ?_⟩
    · intro y hy
      rcases hy with (hy | hy) | hy
      · exact hK₀V hy
      · exact hρV hy
      · exact hK₁V hy
    · intro y hy
      have hy₀ : y ∉ K₀ := fun h ↦ hy (Or.inl (Or.inl h))
      have hyH : y ∉ closedBall (φ₀ 0) ρ := fun h ↦ hy (Or.inl (Or.inr h))
      have hy₁ : y ∉ K₁ := fun h ↦ hy (Or.inr h)
      have hcomp : (F₀.trans (H.trans F₁.symm)) y = y := by
        rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
          (hK₀fix y hy₀).1, (hHfix y hyH).1, (hK₁fix y hy₁).2]
      refine ⟨hcomp, ?_⟩
      have hs := Diffeomorph.symm_apply_apply (F₀.trans (H.trans F₁.symm)) y
      rw [hcomp] at hs
      exact hs

omit [FiniteDimensional ℝ E] in
theorem image_subset_union_of_diffeomorph_eqOn_closedBall
    {φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞}
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K : Set E}
    (hF : ∀ x ∈ closedBall (0 : E) 2, F (φ₀ x) = φ₁ x)
    (hfix : ∀ y ∉ K, F y = y) :
    φ₁ '' closedBall (0 : E) 2 ⊆ K ∪ φ₀ '' closedBall (0 : E) 2 := by
  rintro z ⟨x, hx, rfl⟩
  by_cases hz : φ₁ x ∈ K
  · exact Or.inl hz
  · exact Or.inr ⟨x, hx, F.injective ((hF x hx).trans (hfix _ hz).symm)⟩

end DifferentialGeometry.Topology.Manifold
