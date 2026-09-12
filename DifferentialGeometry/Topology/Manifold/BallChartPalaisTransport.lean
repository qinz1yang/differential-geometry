import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactPointMotion
import DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_compact_diffeomorph_translate_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a b : E) {r R : ℝ} (hr : 0 ≤ r) (hR : r + ‖b - a‖ < R) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x ∈ closedBall a r, D x = x + (b - a)) ∧
      (∀ x ∉ closedBall a R, D x = x ∧ D.symm x = x) := by
  obtain ⟨rIn, hrIn₁, hrIn₂⟩ := exists_between hR
  have hrIn_pos : 0 < rIn := lt_of_le_of_lt (add_nonneg hr (norm_nonneg _)) hrIn₁
  let β : ContDiffBump a := ⟨rIn, R, hrIn_pos, hrIn₂⟩
  let v : E → E := fun x ↦ β x • (b - a)
  have hv : ContDiff ℝ ∞ v := β.contDiff.smul contDiff_const
  have hvc : HasCompactSupport v := β.hasCompactSupport.smul_right
  obtain ⟨D, _hD, hderiv, hzero, _hadd, hinv⟩ :=
    exists_smoothFlow_of_eq_const_off_compact hv 0 (by simpa using hvc)
  have hv_on : ∀ x ∈ closedBall a rIn, v x = b - a := fun x hx =>
    by simp only [v, β.one_of_mem_closedBall hx, one_smul]
  have hsupport : tsupport v ⊆ closedBall a R := by
    have h1 : tsupport v ⊆ tsupport (β : E → ℝ) := tsupport_smul_subset_left (β : E → ℝ) (fun _ : E ↦ b - a)
    rw [β.tsupport_eq] at h1
    exact h1
  have hpoint : ∀ (x : E) (t : ℝ), x ∉ closedBall a R → D t x = x := by
    intro x t hx
    by_contra hne
    have hs := tsupport_integralCurveFamily_sub_subset (v := v) (hv.of_le (by simp))
      (Γ := fun y s ↦ D s y) (fun y ↦ by rw [hzero]; rfl) hderiv t
    exact hx (hsupport (hs (subset_closure (Function.mem_support.mpr (sub_ne_zero.mpr hne)))))
  have hclosed : ∀ x ∈ closedBall a r, D 1 x = x + (b - a) := by
    intro x hx
    have hxr : ‖x - a‖ ≤ r := by simpa [dist_eq_norm] using hx
    have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : x + t • (b - a) ∈ closedBall a rIn := by
      rw [mem_closedBall, dist_eq_norm]
      have hsplit : x + t • (b - a) - a = (x - a) + t • (b - a) := by abel
      rw [hsplit]
      have h1 : ‖(x - a) + t • (b - a)‖ ≤ ‖x - a‖ + ‖t • (b - a)‖ := norm_add_le _ _
      have h2 : ‖t • (b - a)‖ = t * ‖b - a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h3 : t * ‖b - a‖ ≤ ‖b - a‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith
    have hγ : IsIntegralCurveOn (fun t : ℝ ↦ x + t • (b - a)) (fun _ : ℝ ↦ v) (Icc 0 1) := by
      intro t ht
      have hder : HasDerivAt (fun s : ℝ ↦ x + s • (b - a)) (v (x + t • (b - a))) t := by
        rw [hv_on _ (hmem t ht)]
        simpa using (((hasDerivAt_id t).smul_const (b - a)).const_add x)
      exact hder.hasDerivWithinAt
    have hDcur : IsIntegralCurveOn (fun t : ℝ ↦ D t x) (fun _ : ℝ ↦ v) (Icc 0 1) :=
      fun t ht ↦ (hderiv x t).hasDerivWithinAt
    have hinit : (fun t : ℝ ↦ D t x) 0 = (fun t : ℝ ↦ x + t • (b - a)) 0 := by
      simp only [hzero, Diffeomorph.coe_refl, id_eq, zero_smul, add_zero]
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hv
      (a := 0) (b := 1) hDcur hγ hinit
    have h1 := he ⟨zero_le_one, le_refl (1:ℝ)⟩
    simpa using h1
  refine ⟨D 1, hclosed, ?_⟩
  intro x hx
  refine ⟨hpoint x 1 hx, ?_⟩
  rw [hinv 1]
  exact hpoint x (-1) hx

section ModelTranslation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def modelTranslation (t : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toEquiv :=
    { toFun := fun x ↦ x + t
      invFun := fun x ↦ x - t
      left_inv := fun x ↦ by simp
      right_inv := fun x ↦ by simp }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private theorem modelTranslation_apply (t x : E) : modelTranslation t x = x + t := rfl

private def translateConjugate (p : E) (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  (modelTranslation (-p)).trans (F.trans (modelTranslation p))

private theorem translateConjugate_apply (p : E) (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (x : E) :
    translateConjugate p F x = p + F (x - p) := by
  rw [translateConjugate, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans,
    Function.comp_apply, modelTranslation_apply, modelTranslation_apply, add_comm]
  simp only [sub_eq_add_neg]

private theorem translateConjugate_symm_apply (p : E)
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (x : E) :
    (translateConjugate p F).symm x = p + F.symm (x - p) := by
  have h : translateConjugate p F (p + F.symm (x - p)) = x := by
    rw [translateConjugate_apply]
    have h2 : p + F.symm (x - p) - p = F.symm (x - p) := by abel
    rw [h2, Diffeomorph.apply_symm_apply]
    abel
  have hsymm := Diffeomorph.symm_apply_apply (translateConjugate p F) (p + F.symm (x - p))
  rw [h] at hsymm
  exact hsymm

end ModelTranslation

theorem exists_compact_diffeomorph_scale_at
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) {r R c : ℝ} (hr : 0 < r) (hc : 0 < c) (hRr : r < R) (hcr : c * r < R) :
    ∃ H : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x ∈ closedBall p r, H x = p + c • (x - p)) ∧
      (∀ x ∉ closedBall p R, H x = x ∧ H.symm x = x) := by
  have hmem : ∀ x : E, x ∈ closedBall p r ↔ x - p ∈ closedBall (0 : E) r := by
    intro x
    rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm]
    constructor <;> intro h <;> simpa using h
  have hmemR : ∀ x : E, x ∉ closedBall p R ↔ x - p ∉ closedBall (0 : E) R := by
    intro x
    rw [← not_iff_not, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm]
    constructor <;> intro h <;> simpa using h
  by_cases hle : c ≤ 1
  · obtain ⟨D, -, -, -, -, hrad, hfix⟩ :=
      exists_compact_flow_contracting_closedBall (E := E) (r := r) (R := R) hr hRr
    let t : ℝ := -Real.log c
    have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hc.le hle)
    have hexp : Real.exp (-t) = c := by simp only [t, neg_neg, Real.exp_log hc]
    have hfix' : ∀ x : E, x ∉ closedBall p R →
        translateConjugate p (D t) x = x ∧ (translateConjugate p (D t)).symm x = x := by
      intro x hx
      have hxp : x - p ∉ closedBall (0 : E) R := (hmemR x).mp hx
      have h1 := (hfix t (x - p) hxp).1
      have h2 := (hfix t (x - p) hxp).2
      refine ⟨?_, ?_⟩
      · rw [translateConjugate_apply, h1]
        abel
      · rw [translateConjugate_symm_apply, h2]
        abel
    refine ⟨translateConjugate p (D t), ?_, hfix'⟩
    intro x hx
    have hxp : x - p ∈ closedBall (0 : E) r := (hmem x).mp hx
    rw [translateConjugate_apply, hrad t (x - p) ht hxp, hexp]
  · obtain ⟨D, -, -, -, -, hrad, hfix⟩ :=
      exists_compact_flow_contracting_closedBall (E := E) (r := c * r) (R := R)
        (by positivity) hcr
    let t : ℝ := Real.log c
    have ht : 0 ≤ t := Real.log_nonneg (le_of_lt (not_le.mp hle))
    have hexp : Real.exp (-t) = c⁻¹ := by
      simp only [t, Real.exp_neg, Real.exp_log hc]
    have hfix' : ∀ x : E, x ∉ closedBall p R →
        (translateConjugate p (D t)).symm x = x ∧
          (translateConjugate p (D t)).symm.symm x = x := by
      intro x hx
      have hxp : x - p ∉ closedBall (0 : E) R := (hmemR x).mp hx
      have h1 := (hfix t (x - p) hxp).1
      have h2 := (hfix t (x - p) hxp).2
      refine ⟨?_, ?_⟩
      · rw [translateConjugate_symm_apply, h2]
        abel
      · change translateConjugate p (D t) x = x
        rw [translateConjugate_apply, h1]
        abel
    refine ⟨(translateConjugate p (D t)).symm, ?_, hfix'⟩
    intro x hx
    have hxp : x - p ∈ closedBall (0 : E) r := (hmem x).mp hx
    have hcxp : c • (x - p) ∈ closedBall (0 : E) (c * r) := by
      rw [mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have h3 : ‖x - p‖ ≤ r := by simpa using hxp
      nlinarith
    have hstep : translateConjugate p (D t) (p + c • (x - p)) = x := by
      rw [translateConjugate_apply]
      have h4 : p + c • (x - p) - p = c • (x - p) := by abel
      rw [h4, hrad t (c • (x - p)) ht hcxp, hexp]
      simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      abel
    have hsymm := Diffeomorph.symm_apply_apply (translateConjugate p (D t)) (p + c • (x - p))
    rw [hstep] at hsymm
    exact hsymm

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_diffeomorph_apply_eq_of_mem_nhds (x : M) :
    ∃ t ∈ 𝓝 x, ∀ z ∈ t, ∃ Φ : Diffeomorph I I M M ∞, Φ x = z := by
  let φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ x
  let e : OpenPartialHomeomorph M E := φ.toOpenPartialHomeomorph
  have hxsrc : x ∈ e.source := by
    dsimp only [e, φ, DifferentialGeometry.PartialDiffeomorph.extChartAt]
    exact mem_extChartAt_source x
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ closedBall (e x) R ⊆ e.target := by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hxsrc))
    exact ⟨ρ / 2, by linarith, fun y hy => hρsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  let t : Set M := e.source ∩ e ⁻¹' ball (e x) R
  have htopen : IsOpen t := by
    simpa only [t] using e.isOpen_inter_preimage isOpen_ball
  have hxt : x ∈ t := ⟨hxsrc, mem_ball_self hRpos⟩
  refine ⟨t, htopen.mem_nhds hxt, ?_⟩
  rintro z ⟨hzsrc, hzball⟩
  · have hznorm : ‖e z - e x‖ < R := by
      simpa only [Set.mem_preimage, mem_ball, dist_eq_norm] using hzball
    obtain ⟨D, hmove, hfix⟩ :=
      DifferentialGeometry.Analysis.exists_compact_diffeomorph_translate_on_closedBall
        (e x) (e z) (r := 0) (R := R) le_rfl (by simpa using hznorm)
    have hD0 : D (e x) = e z := by
      have h := hmove (e x) (mem_closedBall_self le_rfl)
      simpa using h
    obtain ⟨J, -, -, hJ, -, -, -⟩ :=
      exists_diffeomorph_extension_of_partial_chart_family e φ.contMDiffOn_toFun
        φ.contMDiffOn_invFun (fun _ : ℝ => D)
        (D.contDiff.comp contDiff_snd) (D.symm.contDiff.comp contDiff_snd)
        (isCompact_closedBall (e x) R) hRsub (fun _ y hy => hfix y hy)
    refine ⟨J 1, ?_⟩
    rw [(hJ 1 x).1]
    rw [extendChartById, if_pos hxsrc, hD0, e.left_inv hzsrc]

theorem exists_diffeomorph_apply_eq_of_connectedSpace [ConnectedSpace M] (a b : M) :
    ∃ Φ : Diffeomorph I I M M ∞, Φ a = b := by
  let S : Set M := {y | ∃ Φ : Diffeomorph I I M M ∞, Φ a = y}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨t, ht, ht'⟩ := exists_diffeomorph_apply_eq_of_mem_nhds (I := I) y
    refine Filter.mem_of_superset ht ?_
    rintro z hz
    obtain ⟨Ψ, hΨ⟩ := ht' z hz
    obtain ⟨Φ, hΦ⟩ := hy
    exact ⟨Φ.trans Ψ, by rw [Diffeomorph.coe_trans, Function.comp_apply, hΦ, hΨ]⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨t, ht, ht'⟩ := exists_diffeomorph_apply_eq_of_mem_nhds (I := I) y
    refine Filter.mem_of_superset ht ?_
    rintro z hz hzS
    obtain ⟨Ψ, hΨ⟩ := ht' z hz
    obtain ⟨Φ, hΦ⟩ := hzS
    exact hy ⟨Φ.trans Ψ.symm, by
      rw [Diffeomorph.coe_trans, Function.comp_apply, hΦ, ← hΨ, Diffeomorph.symm_apply_apply]⟩
  have huniv : S = Set.univ := by
    rcases isClopen_iff.mp (⟨hSclosed, hSopen⟩ : IsClopen S) with h | h
    · exfalso
      have ha : a ∈ S := ⟨Diffeomorph.refl I M ∞, rfl⟩
      rw [h] at ha
      exact ha
    · exact h
  have hb : b ∈ S := huniv ▸ Set.mem_univ b
  exact hb

theorem exists_compact_diffeomorph_eqOn_closedBall_of_same_germ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (h₀ : closedBall (0 : E) 2 ⊆ φ₀.source) (h₁ : closedBall (0 : E) 2 ⊆ φ₁.source)
    (hc : φ₀ 0 = φ₁ 0) (hd : fderiv ℝ (φ₀ : E → E) 0 = fderiv ℝ (φ₁ : E → E) 0) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x ∈ closedBall (0 : E) 2, F (φ₀ x) = φ₁ x) ∧
      ∃ K : Set E, IsCompact K ∧ ∀ y ∉ K, F y = y ∧ F.symm y = y := by
  obtain ⟨A₀, ε₀, F₀, hA₀, hε₀, -, hF₀, K₀, hK₀, -, hK₀fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₀ (by norm_num) h₀
      isOpen_univ (subset_univ _)
  obtain ⟨A₁, ε₁, F₁, hA₁, hε₁, -, hF₁, K₁, hK₁, -, hK₁fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₁ (by norm_num) h₁
      isOpen_univ (subset_univ _)
  have hAeq : (A₀ : E →L[ℝ] E) = (A₁ : E →L[ℝ] E) := by rw [hA₀, hA₁, hd]
  have hA₁x : ∀ x : E, A₁ x = A₀ x := fun x => by
    have := congrArg (fun f : E →L[ℝ] E ↦ f x) hAeq
    exact this.symm
  set c : ℝ := ε₁ / ε₀ with hcdef
  have hcpos : 0 < c := div_pos hε₁ hε₀
  set r : ℝ := 2 * (ε₀ * ‖(A₀ : E →L[ℝ] E)‖) + 1 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  set R : ℝ := max r (c * r) + 1 with hRdef
  have hRr : r < R := by rw [hRdef]; linarith [le_max_left r (c * r)]
  have hcr : c * r < R := by rw [hRdef]; linarith [le_max_right r (c * r)]
  obtain ⟨H, hHexact, hHfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_scale_at (φ₀ 0) hrpos hcpos hRr hcr
  have hkey : ∀ x ∈ closedBall (0 : E) 2, H (ε₀ • A₀ x + φ₀ 0) = ε₁ • A₁ x + φ₁ 0 := by
    intro x hx
    have hmem : ε₀ • A₀ x + φ₀ 0 ∈ closedBall (φ₀ 0) r := by
      rw [mem_closedBall, dist_eq_norm]
      have hsub : ε₀ • A₀ x + φ₀ 0 - φ₀ 0 = ε₀ • A₀ x := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε₀]
      have hop : ‖A₀ x‖ ≤ ‖(A₀ : E →L[ℝ] E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A₀ : E →L[ℝ] E) x
      have hx2 : ‖x‖ ≤ 2 := by simpa using hx
      have hnorm : 0 ≤ ‖(A₀ : E →L[ℝ] E)‖ := norm_nonneg _
      have hxnn : 0 ≤ ‖x‖ := norm_nonneg _
      rw [hrdef]
      nlinarith [hop, hx2, hnorm, hε₀]
    rw [hHexact _ hmem]
    have hsub : ε₀ • A₀ x + φ₀ 0 - φ₀ 0 = ε₀ • A₀ x := by abel
    rw [hsub, smul_smul, hA₁x x, hc, div_mul_cancel₀ ε₁ hε₀.ne']
    exact add_comm _ _
  refine ⟨F₀.trans (H.trans F₁.symm), ?_, ?_⟩
  · intro x hx
    rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
      hF₀ x hx, hkey x hx, ← hF₁ x hx, Diffeomorph.symm_apply_apply]
  · refine ⟨K₀ ∪ closedBall (φ₀ 0) R ∪ K₁, hK₀.union (isCompact_closedBall _ _) |>.union hK₁, ?_⟩
    intro y hy
    have hy₀ : y ∉ K₀ := fun h => hy (Or.inl (Or.inl h))
    have hyH : y ∉ closedBall (φ₀ 0) R := fun h => hy (Or.inl (Or.inr h))
    have hy₁ : y ∉ K₁ := fun h => hy (Or.inr h)
    have hfix₀ := hK₀fix y hy₀
    have hfixH := hHfix y hyH
    have hfix₁ := hK₁fix y hy₁
    have hcomp : (F₀.trans (H.trans F₁.symm)) y = y := by
      rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
        hfix₀.1, hfixH.1, hfix₁.2]
    refine ⟨hcomp, ?_⟩
    have hs := Diffeomorph.symm_apply_apply (F₀.trans (H.trans F₁.symm)) y
    rw [hcomp] at hs
    exact hs

end DifferentialGeometry.Topology.Manifold
