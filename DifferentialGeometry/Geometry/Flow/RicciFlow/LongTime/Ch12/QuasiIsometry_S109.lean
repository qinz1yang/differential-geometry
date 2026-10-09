import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HCX3ExtNoSpeed_S109
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyCalc_S15
import DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity

set_option autoImplicit false

/-! # CH12-S109 G2: quasi-isometry of `exp(μ X)` for `C¹`-small compactly supported `X`

`∃ ε₀ > 0, K ≥ 1, ∀ X (smooth, = 0 off D2, C¹-ε₀-small), |μ| ≤ 2, q, w :
g_q(w,w) ≤ K · g_{E_μ q}(dE_μ w, dE_μ w)` where `E_μ = scaledExp X μ`.  Proof: Lebesgue puts `q` and
`E_μ q` into one atlas ball; in that chart `D(ext ∘ E_μ ∘ ext⁻¹) = L` with `‖L - id‖ ≤ 1/2`, and the
metric is comparable to the Euclidean one on the finitely many compact chart balls (S15 recipe).  Stated for
`I = 𝓘(ℝ, E)` (the compact-source ellipticity lemma of the tree is for that model). -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Coord
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

omit [LocallyCompactSpace M] in
/-- coordinate expression of `d(exp(μ X))`: `d ext_{F p} ∘ dF = L ∘ d ext_p` (the identity inside
`scaledExp_immersion_S15`). -/
theorem mfderiv_scaledExp_coord_S109 (c : M) (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) (μ : ℝ) {p : M}
    (hp : p ∈ (extChartAt I c).source) (hFp : scaledExp_S15 g hEnorm X μ p ∈ (extChartAt I c).source)
    {L : E →L[ℝ] E}
    (hL : HasFDerivAt (fun y => chartPsi_S15 g hEnorm c (y, μ • coordSec_S15 c X y)) L
      (extChartAt I c p)) (w : TangentSpace I p) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I c) (scaledExp_S15 g hEnorm X μ p)
      (mfderiv I I (scaledExp_S15 g hEnorm X μ) p w) : E) =
      L (mfderiv I 𝓘(ℝ, E) (extChartAt I c) p w) := by
  set F := scaledExp_S15 g hEnorm X μ with hF
  have hFd : MDifferentiableAt I I F p :=
    ((contMDiff_scaledExp_fam_S15 g hEnorm X hX μ) p).mdifferentiableAt (by simp)
  have hqS : F p ∈ (chartAt H c).source := by rwa [extChartAt_source] at hFp
  have hpS : p ∈ (chartAt H c).source := by rwa [extChartAt_source] at hp
  have hextq : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) (F p) := mdifferentiableAt_extChartAt hqS
  have hextp : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) p := mdifferentiableAt_extChartAt hpS
  set G : E → E := fun y => chartPsi_S15 g hEnorm c (y, μ • coordSec_S15 c X y) with hG
  have hGd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p) :=
    hL.differentiableAt.mdifferentiableAt
  have h1 : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I c (F y)) p =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I c) (F p)).comp (mfderiv I I F p) :=
    mfderiv_comp p hextq hFd
  have hev : (fun y => extChartAt I c (F y)) =ᶠ[𝓝 p] (G ∘ extChartAt I c) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) c).mem_nhds hp] with y hy
    have := scaledExp_ext_S15 g hEnorm c X μ (x := extChartAt I c y) ((extChartAt I c).map_source hy)
    rw [(extChartAt I c).left_inv hy] at this
    exact this
  have h2 : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I c (F y)) p =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p)).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I c) p) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp p hGd hextp
  have hGm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p) = L := by
    rw [mfderiv_eq_fderiv]; exact hL.fderiv
  have key := h1.symm.trans h2
  rw [hGm] at key
  exact congrArg (fun T => (T w : E)) key

end Coord

section Ell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem mfderiv_symm_cancel_S109 (c : M) {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, E) c).source)
    (w : TangentSpace 𝓘(ℝ, E) p) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c).symm (extChartAt 𝓘(ℝ, E) c p)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c) p w) : E) = (w : E) := by
  have := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℝ, E)) hp
  have h2 := congrArg (fun L => (L w : E)) this
  simp only [mfderivWithin_univ, ModelWithCorners.range_eq_univ, ContinuousLinearMap.comp_apply] at h2
  exact h2

/-- chart coordinates of a tangent vector: `d ext_c (w)`. -/
def coordVec_S109 (c : M) {p : M} (w : TangentSpace 𝓘(ℝ, E) p) : E :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c) p w

/-- the metric is comparable to the Euclidean norm of the chart coordinates on a compact chart ball. -/
theorem chart_ellipticity_S109 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (c : M) {r : ℝ}
    (hr : closedBall (extChartAt 𝓘(ℝ, E) c c) r ⊆ (extChartAt 𝓘(ℝ, E) c).target) :
    ∃ m Am : ℝ, 0 < m ∧ m ≤ Am ∧ ∀ p ∈ (extChartAt 𝓘(ℝ, E) c).source,
      extChartAt 𝓘(ℝ, E) c p ∈ closedBall (extChartAt 𝓘(ℝ, E) c c) r →
      ∀ w : TangentSpace 𝓘(ℝ, E) p,
        m * ‖coordVec_S109 c w‖ ^ 2 ≤ g.inner p w w ∧ g.inner p w w ≤ Am * ‖coordVec_S109 c w‖ ^ 2 := by
  obtain ⟨m, Am, hm, hmA, hb⟩ := exists_compact_source_metric_ellipticity g (V := E)
    (f := (extChartAt 𝓘(ℝ, E) c).symm) (U := (extChartAt 𝓘(ℝ, E) c).target)
    (K := closedBall (extChartAt 𝓘(ℝ, E) c c) r) (isOpen_extChartAt_target c)
    ((contMDiffOn_extChartAt_symm (n := ∞) c).of_le (by exact_mod_cast le_top)) (isCompact_closedBall _ _) hr
    (fun x hx => by
      have := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) (x := c) (hr hx)).bijective.1
      simpa only [mfderivWithin_univ, ModelWithCorners.range_eq_univ] using this)
  refine ⟨m, Am, hm, hmA, fun p hp hpb w => ?_⟩
  have hb' := hb (extChartAt 𝓘(ℝ, E) c p) hpb
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c) p w)
  have h1 : g.inner ((extChartAt 𝓘(ℝ, E) c).symm (extChartAt 𝓘(ℝ, E) c p))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c).symm (extChartAt 𝓘(ℝ, E) c p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c) p w))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c).symm (extChartAt 𝓘(ℝ, E) c p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) c) p w)) = g.inner p w w :=
    congrArg₂ (fun (x : M) (v : E) => g.inner x v v) ((extChartAt 𝓘(ℝ, E) c).left_inv hp)
      (mfderiv_symm_cancel_S109 c hp w)
  rw [h1] at hb'
  exact hb'


section Main
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold 𝓘(ℝ, E) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hEnorm : IsMetricNorm g)

/-- **QI lemma.**  `E_μ = exp(μ X)` is a uniform quasi-isometry of the metric (at the level of
differentials) for `C¹`-small compactly supported `X`: `g_q(w,w) ≤ K g_{E_μ q}(dE_μ w, dE_μ w)`. -/
theorem quasi_isometry_S109 (A : CkAtlas_S15 𝓘(ℝ, E) M) {D2 : Set M} (hD2 : IsCompact D2)
    (hD2A : D2 ⊆ A.cover) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ K : ℝ, 1 ≤ K ∧ ∀ X : (∀ y : M, TangentSpace 𝓘(ℝ, E) y),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (secBundle_S15 X) → (∀ p, p ∉ D2 → X p = 0) →
      CkSmall_S15 g A X 1 ε₀ → ∀ μ : ℝ, |μ| ≤ 2 → ∀ (q : M) (w : TangentSpace 𝓘(ℝ, E) q),
        g.inner q w w ≤ K * g.inner (scaledExp_S15 g hEnorm X μ q)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q w)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q w) := by
  have hcalc : ∀ i : Fin A.n, ∃ e : ℝ, 0 < e ∧ ∀ cc : E → E,
      ContDiffOn ℝ 1 cc (extChartAt 𝓘(ℝ, E) (A.ctr i)).target →
      (∀ x ∈ closedBall (extChartAt 𝓘(ℝ, E) (A.ctr i) (A.ctr i)) (A.rad i),
        ‖cc x‖ ≤ e ∧ ‖fderiv ℝ cc x‖ ≤ e) → ∀ μ : ℝ, |μ| ≤ 2 →
      ∀ x ∈ closedBall (extChartAt 𝓘(ℝ, E) (A.ctr i) (A.ctr i)) (A.rad i), ∃ L : E →L[ℝ] E,
        HasFDerivAt (fun y => chartPsi_S15 g hEnorm (A.ctr i) (y, μ • cc y)) L x ∧
          ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := fun i => by
    obtain ⟨e, he, h⟩ := calc_C1_small_S15 (chartDom_isOpen_S15 g hEnorm (A.ctr i))
      (isOpen_extChartAt_target (A.ctr i))
      ((chartPsi_contDiffOn_S15 g hEnorm (A.ctr i)).of_le (by exact_mod_cast le_top))
      (A.closedBall_sub i) (fun x hx => chartPsi_zero_S15 g hEnorm (A.ctr i) hx)
      (fun x hx => chartDom_zero_S15 g hEnorm (A.ctr i) hx)
    exact ⟨e, he, fun cc h1 h2 μ hμ => (h cc h1 h2 μ hμ).2.1⟩
  choose e he hcalc using hcalc
  have hell := fun i : Fin A.n => chart_ellipticity_S109 g (A.ctr i) (A.closedBall_sub i)
  choose m Am hm hmA hell using hell
  obtain ⟨m₀, hm₀, hm₀le⟩ := exists_pos_forall_le_fin_S15 A.n m hm
  set Asum : ℝ := ∑ i, Am i with hAsum
  have hAle : ∀ i, Am i ≤ Asum := fun i =>
    Finset.single_le_sum (f := Am) (fun j _ => (hm j).le.trans (hmA j)) (Finset.mem_univ i)
  have hAsum0 : 0 ≤ Asum := Finset.sum_nonneg (fun j _ => (hm j).le.trans (hmA j))
  obtain ⟨ε0, hε0, hε0le⟩ := exists_pos_forall_le_fin_S15 A.n e he
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_riemannian_S15 (I := 𝓘(ℝ, E)) hD2 (fun i => A.isOpen_U i)
    (by simpa [CkAtlas_S15.cover] using hD2A)
  obtain ⟨δ0, hδ0, hδ0le⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ ENNReal.ofReal δ0 ≤ δ := by
    rcases eq_top_or_lt_top δ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  refine ⟨min ε0 (δ0 / 8), lt_min hε0 (by linarith), max 1 (4 * Asum / m₀), le_max_left _ _, ?_⟩
  intro X hX hX0 hsmall μ hμ q w
  set F := scaledExp_S15 g hEnorm X μ with hF
  have hg0 : ∀ (y : M) (v : TangentSpace 𝓘(ℝ, E) y), 0 ≤ g.inner y v v := by
    intro y v
    by_cases hz : v = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  by_cases hqD : q ∈ D2
  · set ε := min ε0 (δ0 / 8) with hε
    have hε1 : ε ≤ ε0 := min_le_left _ _
    have hε2 : ε ≤ δ0 / 8 := min_le_right _ _
    obtain ⟨j, hqj⟩ := mem_iUnion.mp (hD2A hqD)
    have hxj : extChartAt 𝓘(ℝ, E) (A.ctr j) q ∈
        closedBall (extChartAt 𝓘(ℝ, E) (A.ctr j) (A.ctr j)) (A.rad j) :=
      ball_subset_closedBall hqj.2
    have h1 := (hsmall j _ hxj).1
    rw [(extChartAt 𝓘(ℝ, E) (A.ctr j)).left_inv hqj.1] at h1
    have hm' : |μ| * tanLen_S15 g (secBundle_S15 X q) ≤ 2 * ε :=
      mul_le_mul hμ h1.le (Real.sqrt_nonneg _) (by norm_num)
    have hlen := (edist_scaledExp_le_S15 g hEnorm X μ q).trans (ENNReal.ofReal_le_ofReal hm')
    have hd : Manifold.riemannianEDist 𝓘(ℝ, E) q (F q) < δ :=
      lt_of_le_of_lt hlen
        (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ0).mpr (by linarith)) hδ0le)
    obtain ⟨i, hqi, hFqi⟩ := hleb q hqD (F q) hd
    have hxb : extChartAt 𝓘(ℝ, E) (A.ctr i) q ∈
        closedBall (extChartAt 𝓘(ℝ, E) (A.ctr i) (A.ctr i)) (A.rad i) :=
      ball_subset_closedBall hqi.2
    have hxb' : extChartAt 𝓘(ℝ, E) (A.ctr i) (F q) ∈
        closedBall (extChartAt 𝓘(ℝ, E) (A.ctr i) (A.ctr i)) (A.rad i) :=
      ball_subset_closedBall hFqi.2
    have hcoord : ∀ x ∈ closedBall (extChartAt 𝓘(ℝ, E) (A.ctr i) (A.ctr i)) (A.rad i),
        ‖coordSec_S15 (A.ctr i) X x‖ ≤ e i ∧ ‖fderiv ℝ (coordSec_S15 (A.ctr i) X) x‖ ≤ e i := by
      intro x hx
      have h0 := (hsmall i x hx).2 0 (by norm_num)
      have h1 := (hsmall i x hx).2 1 le_rfl
      rw [norm_iteratedFDeriv_zero] at h0
      have h1' : ‖fderiv ℝ (coordSec_S15 (A.ctr i) X) x‖ < ε := by
        have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := coordSec_S15 (A.ctr i) X) (x := x) (n := 0)
        rw [norm_iteratedFDeriv_zero] at this
        rw [this]; exact h1
      exact ⟨(h0.trans_le (hε1.trans (hε0le i))).le, (h1'.trans_le (hε1.trans (hε0le i))).le⟩
    obtain ⟨L, hL, hLb⟩ := hcalc i (coordSec_S15 (A.ctr i) X)
      ((coordSec_contDiffOn_S15 (A.ctr i) X hX).of_le (by exact_mod_cast le_top)) hcoord μ hμ _ hxb
    have hC : coordVec_S109 (A.ctr i) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w) =
        L (coordVec_S109 (A.ctr i) w) :=
      mfderiv_scaledExp_coord_S109 g hEnorm (A.ctr i) X hX μ hqi.1 hFqi.1 hL w
    obtain ⟨-, hup⟩ := hell i q hqi.1 hxb w
    obtain ⟨hlow, -⟩ := hell i (F q) hFqi.1 hxb' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w)
    rw [hC] at hlow
    set w' := coordVec_S109 (A.ctr i) w with hw'
    have h4 : ‖w'‖ ≤ ‖L w'‖ + ‖(L - ContinuousLinearMap.id ℝ E) w'‖ := by
      have h3 : w' = L w' - (L - ContinuousLinearMap.id ℝ E) w' := by simp
      conv_lhs => rw [h3]
      exact norm_sub_le _ _
    have h5 : ‖(L - ContinuousLinearMap.id ℝ E) w'‖ ≤ 1 / 2 * ‖w'‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hLb (norm_nonneg _))
    have hnorm : ‖w'‖ ≤ 2 * ‖L w'‖ := by linarith
    set g' := g.inner (F q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w) with hg'
    have hlow' : m₀ * ‖L w'‖ ^ 2 ≤ g' :=
      (mul_le_mul_of_nonneg_right (hm₀le i) (sq_nonneg _)).trans hlow
    have hg'0 : 0 ≤ g' := (mul_nonneg hm₀.le (sq_nonneg _)).trans hlow'
    have hK : 4 * Asum / m₀ ≤ max 1 (4 * Asum / m₀) := le_max_right _ _
    calc g.inner q w w ≤ Am i * ‖w'‖ ^ 2 := hup
      _ ≤ Asum * ‖w'‖ ^ 2 := mul_le_mul_of_nonneg_right (hAle i) (sq_nonneg _)
      _ ≤ Asum * (2 * ‖L w'‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hAsum0
      _ = (4 * Asum / m₀) * (m₀ * ‖L w'‖ ^ 2) := by field_simp; ring
      _ ≤ (4 * Asum / m₀) * g' := mul_le_mul_of_nonneg_left hlow' (by positivity)
      _ ≤ max 1 (4 * Asum / m₀) * g' := mul_le_mul_of_nonneg_right hK hg'0
  · have hopen : IsOpen D2ᶜ := hD2.isClosed.isOpen_compl
    have hev : F =ᶠ[𝓝 q] id := by
      filter_upwards [hopen.mem_nhds hqD] with y hy
      exact scaledExp_zero_field_S102 g hEnorm X μ (hX0 y hy)
    have hFq : F q = q := hev.eq_of_nhds
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : M → M) q :=
      hev.mfderiv_eq
    have hw : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w : E) = (w : E) := by
      rw [hd, mfderiv_id]; rfl
    have h2 : g.inner (F q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F q w) =
        g.inner q w w :=
      congrArg₂ (fun (x : M) (v : E) => g.inner x v v) hFq hw
    rw [h2]
    have h0 := hg0 q w
    have h1 : (1 : ℝ) ≤ max 1 (4 * Asum / m₀) := le_max_left _ _
    nlinarith

end Main

end Ell

end GC.LongTime.Ch12
