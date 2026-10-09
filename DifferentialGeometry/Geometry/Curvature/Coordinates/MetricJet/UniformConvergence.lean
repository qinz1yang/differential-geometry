import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalPlane
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn mapDerivNorm
  tendstoUniformlyOn_of_cPConvergence)
namespace DifferentialGeometry.Analysis

section General

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem mapCPConvergenceOn_comp_clm' {U D : Set E} (hU : IsOpen U) (hDU : D ⊆ U)
    {p : ℕ} {f : ℕ → E → F} {f₀ : E → F} (hf : ∀ i, ContDiffOn ℝ p (f i) U)
    (hf₀ : ContDiffOn ℝ p f₀ U) (L : F →L[ℝ] G) (h : MapCPConvergenceOn D p f f₀) :
    MapCPConvergenceOn D p (fun i y => L (f i y)) (fun y => L (f₀ y)) := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / (‖L‖ + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hd : ContDiffAt ℝ p (fun y => f k y - f₀ y) x :=
    ((hf k).sub hf₀).contDiffAt (hU.mem_nhds (hDU hx))
  have hb : ‖iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x‖ ≤ ε / (‖L‖ + 1) :=
    hk0 k hk r hr x hx
  have heq : (fun y => L (f k y) - L (f₀ y)) = L ∘ (fun y => f k y - f₀ y) := by
    funext y
    simp only [Function.comp_apply, map_sub]
  have hcomp : iteratedFDeriv ℝ r (fun y => L (f k y) - L (f₀ y)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x) := by
    rw [heq]
    exact L.iteratedFDeriv_comp_left hd (by exact_mod_cast hr)
  have hbound : ‖iteratedFDeriv ℝ r (fun y => L (f k y) - L (f₀ y)) x‖ ≤ ε := by
    rw [hcomp]
    have hL := norm_nonneg L
    calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x)‖
        ≤ ‖L‖ * ‖iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x‖ :=
          L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * (ε / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hb hL
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  exact hbound

/-- `C²` convergence on `D` gives uniform convergence of the second jets on `D`. -/
theorem tendstoUniformlyOn_jet2_of_mapCPConvergenceOn {U D : Set E} (hU : IsOpen U)
    (hDU : D ⊆ U) {f : ℕ → E → F} {f₀ : E → F} (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hf₀ : ContDiffOn ℝ 2 f₀ U) (hconv : MapCPConvergenceOn D 2 f f₀) :
    TendstoUniformlyOn (fun i w => jet2 (f i) w) (fun w => jet2 f₀ w) atTop D := by
  refine (Metric.tendstoUniformlyOn_iff (α := F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))).mpr
    fun ε hε => ?_
  obtain ⟨k0, hk0⟩ := hconv (ε / 2) (by positivity)
  rw [eventually_atTop]
  refine ⟨k0, fun k hk w hw => ?_⟩
  have hwU : U ∈ 𝓝 w := hU.mem_nhds (hDU hw)
  have hdU (y : E) (hy : y ∈ U) : DifferentiableAt ℝ (f k) y :=
    ((hf k).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdU₀ (y : E) (hy : y ∈ U) : DifferentiableAt ℝ f₀ y :=
    (hf₀.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fun y => fderiv ℝ (f k) y) w :=
    (((hf k).contDiffAt hwU).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdd₀ : DifferentiableAt ℝ (fun y => fderiv ℝ f₀ y) w :=
    ((hf₀.contDiffAt hwU).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 : ‖f k w - f₀ w‖ ≤ ε / 2 := by
    have hb := hk0 k hk 0 (Nat.zero_le 2) w hw
    rwa [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  have h1 : ‖fderiv ℝ (f k) w - fderiv ℝ f₀ w‖ ≤ ε / 2 := by
    have hb := hk0 k hk 1 (by norm_num) w hw
    rwa [mapDerivNorm, norm_iteratedFDeriv_one,
      fderiv_fun_sub (hdU w (hDU hw)) (hdU₀ w (hDU hw))] at hb
  have h2 : ‖fderiv ℝ (fun y => fderiv ℝ (f k) y) w - fderiv ℝ (fun y => fderiv ℝ f₀ y) w‖
      ≤ ε / 2 := by
    have hb := hk0 k hk 2 le_rfl w hw
    have hev : (fderiv ℝ (fun y => f k y - f₀ y)) =ᶠ[𝓝 w]
        (fun y => fderiv ℝ (f k) y - fderiv ℝ f₀ y) := by
      filter_upwards [hwU] with y hy
      exact fderiv_fun_sub (hdU y hy) (hdU₀ y hy)
    have hsec : fderiv ℝ (fderiv ℝ (fun y => f k y - f₀ y)) w =
        fderiv ℝ (fun y => fderiv ℝ (f k) y) w - fderiv ℝ (fun y => fderiv ℝ f₀ y) w :=
      hev.fderiv_eq.trans (fderiv_fun_sub hdd hdd₀)
    have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := fun y => f k y - f₀ y)
      (x := w)
    rw [norm_iteratedFDeriv_one, hsec] at hn
    rw [mapDerivNorm] at hb
    rw [hn]
    exact hb
  rw [dist_comm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine Prod.dist_eq.trans_le (max_le ?_ (Prod.dist_eq.trans_le (max_le ?_ ?_)))
  · exact (dist_eq_norm (E := F) _ _).trans_le h0
  · exact (dist_eq_norm (E := E →L[ℝ] F) _ _).trans_le h1
  · exact (dist_eq_norm (E := E →L[ℝ] E →L[ℝ] F) _ _).trans_le h2

end General

section Coercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous positive-definite family of bilinear forms on a compact set is uniformly
coercive. -/
theorem exists_uniform_coercive_of_continuousOn {L : Set E} (hL : IsCompact L)
    {c₀ : E → E →L[ℝ] E →L[ℝ] ℝ} (hcont : ContinuousOn c₀ L)
    (hpos : ∀ y ∈ L, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ L, ∀ v : E, lam * ‖v‖ ^ 2 ≤ c₀ y v v := by
  obtain ⟨C, hC, hb⟩ := hcont.exists_uniform_bilin_quadratic_bounds hL hpos
  exact ⟨C⁻¹, inv_pos.mpr (zero_lt_one.trans_le hC), fun y hy v => (hb y hy v).1⟩

end Coercive

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U L : Set E} {c : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {c₀ : E → E →L[ℝ] E →L[ℝ] ℝ}

private theorem det_coefficientGram_ne_zero' {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hpos : ∀ v : E, v ≠ 0 → 0 < b w v v) :
    (Matrix.of (coefficientGram b w)).det ≠ 0 := by
  intro hdet0
  obtain ⟨a, ha0, hav⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of (coefficientGram b w))).2 hdet0
  set v : E := ∑ i, a i • chartModelBasis E i with hv
  have hrow0 : ∀ i, (b w (chartModelBasis E i)) v = 0 := by
    intro i
    have h1 : (b w (chartModelBasis E i)) v =
        ∑ j, Matrix.of (coefficientGram b w) i j * a j := by
      rw [hv, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      simp only [coefficientGram_apply, Matrix.of_apply]
    have h2 : (∑ j, Matrix.of (coefficientGram b w) i j * a j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hav i
    rw [h1, h2]
  have hinner : b w v v = 0 := by
    have hout : (b w) v = ∑ i, a i • ((b w) (chartModelBasis E i)) := by
      rw [hv, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    calc b w v v = (∑ i, a i • ((b w) (chartModelBasis E i))) v := by rw [hout]
      _ = ∑ i, a i • ((b w (chartModelBasis E i)) v) := by
          rw [_root_.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [_root_.smul_apply]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hrow0 i, smul_zero]
  have hvne : v ≠ 0 := by
    intro hv0
    apply ha0
    have hz : ∑ i, a i • chartModelBasis E i = 0 := hv.symm.trans hv0
    have hall := Fintype.linearIndependent_iff.1 (chartModelBasis E).linearIndependent a hz
    funext i
    exact hall i
  exact absurd hinner (ne_of_gt (hpos v hvne))

private theorem contDiff_repr_apply (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ fun X : E => (chartModelBasis E).repr X i :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)
    ((chartModelBasis E).coord i)).contDiff

/-- `jetRm04`, as a function of the jet and the four vectors jointly, is continuous at every
jet with invertible Gram matrix. -/
private theorem continuousAt_jetRm04_uncurry
    {P₀ : MatJet E (Module.finrank ℝ E) × E × E × E × E}
    (hP₀ : (Matrix.of P₀.1.1).det ≠ 0) :
    ContinuousAt (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E =>
      jetRm04 P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2) P₀ := by
  have h1 : ContDiff ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.2.1) :=
    contDiff_fst.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h3 : ContDiff ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.2.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  have h4 : ContDiff ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.2.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  have h0 : ContDiff ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.1) :=
    contDiff_fst
  have hR : ∀ a b d e : Fin (Module.finrank ℝ E), ContDiffAt ℝ ∞
      (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E =>
        jetRiemann (chartModelBasis E) P.1 a b d e) P₀ := fun a b d e =>
    (contDiffAt_jetRiemann (chartModelBasis E) hP₀ a b d e).comp P₀ h0.contDiffAt
  have hV : ∀ a b : Fin (Module.finrank ℝ E), ContDiffAt ℝ ∞
      (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E => P.1.1 a b) P₀ := fun a b =>
    ((contDiff_jetVal a b).comp h0).contDiffAt
  suffices hcd : ContDiffAt ℝ ∞ (fun P : MatJet E (Module.finrank ℝ E) × E × E × E × E =>
      jetRm04 P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2) P₀ from hcd.continuousAt
  unfold jetRm04
  refine ContDiffAt.sum (fun i _ => ?_)
  refine ContDiffAt.sum (fun j _ => ?_)
  refine ContDiffAt.sum (fun k _ => ?_)
  refine ContDiffAt.sum (fun l _ => ?_)
  exact (((((contDiff_repr_apply i).comp h1).contDiffAt.mul
    ((contDiff_repr_apply j).comp h2).contDiffAt).mul
    ((contDiff_repr_apply k).comp h3).contDiffAt).mul
    ((contDiff_repr_apply l).comp h4).contDiffAt).mul
    (ContDiffAt.sum fun l' _ => (hV l l').mul (hR k i j l'))

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_jet2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) :
    ContinuousOn (fun y => jet2 g y) U :=
  hg.continuousOn.prodMk ((hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).prodMk
    ((hg.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU
      (by norm_num)))

private theorem continuousOn_coefficientRm04_limit (hU : IsOpen U) (hLU : L ⊆ U)
    (hc₀ : ContDiffOn ℝ 2 c₀ U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) :
    ContinuousOn (fun q : E × E × E × E × E =>
      coefficientRm04 c₀ q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) (L ×ˢ univ) := by
  have hG : ContinuousOn (fun q : E × E × E × E × E =>
      ((jet2 (coefficientGram c₀) q.1, q.2) : MatJet E (Module.finrank ℝ E) × E × E × E × E))
      (L ×ˢ univ) :=
    (((continuousOn_jet2 hU (contDiffOn_coefficientGram hc₀)).mono hLU).comp
      continuousOn_fst fun q hq => hq.1).prodMk continuousOn_snd
  intro q hq
  exact ContinuousAt.comp_continuousWithinAt (x := q)
    (f := fun q : E × E × E × E × E =>
      ((jet2 (coefficientGram c₀) q.1, q.2) : MatJet E (Module.finrank ℝ E) × E × E × E × E))
    (continuousAt_jetRm04_uncurry (det_coefficientGram_ne_zero' (hpos q.1 (hLU hq.1))))
    (hG q hq)

/-- Item 1: `C²` convergence of the metric coefficients gives uniform convergence of the second
jets of their Gram matrices. -/
theorem tendstoUniformlyOn_jet2_coefficientGram (hU : IsOpen U) (hLU : L ⊆ U)
    (hc : ∀ k, ContDiffOn ℝ 2 (c k) U) (hc₀ : ContDiffOn ℝ 2 c₀ U)
    (hconv : MapCPConvergenceOn L 2 c c₀) :
    TendstoUniformlyOn (fun k y => jet2 (coefficientGram (c k)) y)
      (fun y => jet2 (coefficientGram c₀) y) atTop L :=
  tendstoUniformlyOn_jet2_of_mapCPConvergenceOn hU hLU
    (fun k => contDiffOn_coefficientGram (hc k)) (contDiffOn_coefficientGram hc₀)
    (mapCPConvergenceOn_comp_clm' hU hLU hc hc₀ (coefficientGramCLM E) hconv)

/-- Item 2: a uniform coercivity constant for the limit and, eventually, for the sequence. -/
theorem exists_eventually_coercive (hL : IsCompact L) (hLU : L ⊆ U)
    (hc₀ : ContDiffOn ℝ 2 c₀ U) (hconv : MapCPConvergenceOn L 2 c c₀)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) :
    ∃ lam : ℝ, 0 < lam ∧ (∀ y ∈ L, ∀ v : E, 2 * lam * ‖v‖ ^ 2 ≤ c₀ y v v) ∧
      ∀ᶠ k in atTop, ∀ y ∈ L, ∀ v : E, lam * ‖v‖ ^ 2 ≤ c k y v v := by
  obtain ⟨m, hm, hmb⟩ := exists_uniform_coercive_of_continuousOn hL
    (hc₀.continuousOn.mono hLU) (fun y hy => hpos y (hLU hy))
  refine ⟨m / 2, by positivity, fun y hy v => by linarith [hmb y hy v], ?_⟩
  have hu := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_of_cPConvergence (hconv.mono_order (Nat.zero_le 2))) (m / 2)
    (by positivity)
  filter_upwards [hu] with k hk y hy v
  have hd : ‖c k y - c₀ y‖ < m / 2 := by
    have h := hk y hy
    rwa [dist_comm, dist_eq_norm] at h
  have hb : |c k y v v - c₀ y v v| ≤ m / 2 * ‖v‖ ^ 2 := by
    have h1 : c k y v v - c₀ y v v = (c k y - c₀ y) v v := by
      simp only [_root_.sub_apply]
    rw [h1, ← Real.norm_eq_abs]
    calc ‖(c k y - c₀ y) v v‖ ≤ ‖c k y - c₀ y‖ * ‖v‖ * ‖v‖ := (c k y - c₀ y).le_opNorm₂ v v
      _ = ‖c k y - c₀ y‖ * ‖v‖ ^ 2 := by ring
      _ ≤ m / 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖v‖)
  linarith [hmb y hy v, neg_abs_le (c k y v v - c₀ y v v)]

/-- Item 3: uniform convergence of the `(0,4)` curvature coefficients on `L` times unit balls. -/
theorem tendstoUniformlyOn_coefficientRm04 (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U)
    (hc : ∀ k, ContDiffOn ℝ 2 (c k) U) (hc₀ : ContDiffOn ℝ 2 c₀ U)
    (hconv : MapCPConvergenceOn L 2 c c₀) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) :
    TendstoUniformlyOn (fun k (q : E × E × E × E × E) =>
        coefficientRm04 (c k) q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (fun q => coefficientRm04 c₀ q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) atTop
      (L ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ (Metric.closedBall 0 1 ×ˢ
        (Metric.closedBall 0 1 ×ˢ Metric.closedBall 0 1)))) := by
  set D : Set (E × E × E × E × E) := L ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ
    (Metric.closedBall 0 1 ×ˢ (Metric.closedBall 0 1 ×ˢ Metric.closedBall 0 1)))
  let G₀ : E × E × E × E × E → MatJet E (Module.finrank ℝ E) × E × E × E × E :=
    fun q => (jet2 (coefficientGram c₀) q.1, q.2)
  let Φ : MatJet E (Module.finrank ℝ E) × E × E × E × E → ℝ :=
    fun P => jetRm04 P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2
  have hD : IsCompact D := hL.prod ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  have hG₀ : ContinuousOn G₀ D :=
    (((continuousOn_jet2 hU (contDiffOn_coefficientGram hc₀)).mono hLU).comp
      continuousOn_fst fun q hq => hq.1).prodMk continuousOn_snd
  have hK : IsCompact (G₀ '' D) := hD.image_of_continuousOn hG₀
  have hΦ : ∀ P ∈ G₀ '' D, ContinuousAt Φ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact continuousAt_jetRm04_uncurry (P₀ := G₀ q)
      (det_coefficientGram_ne_zero' (hpos q.1 (hLU hq.1)))
  have hJ := tendstoUniformlyOn_jet2_coefficientGram hU hLU hc hc₀ hconv
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  have hr := hK.uniformContinuousAt_of_continuousAt Φ hΦ (Metric.dist_mem_uniformity hε)
  obtain ⟨η, hη, hηr⟩ :=
    (Metric.mem_uniformity_dist (α := MatJet E (Module.finrank ℝ E) × E × E × E × E)).1 hr
  filter_upwards [(Metric.tendstoUniformlyOn_iff (α := MatJet E (Module.finrank ℝ E))).mp hJ η hη]
    with k hk q hq
  have hdist : dist (G₀ q)
      ((jet2 (coefficientGram (c k)) q.1, q.2) : MatJet E (Module.finrank ℝ E) × E × E × E × E)
      < η := by
    simp only [G₀, Prod.dist_eq, dist_self]
    exact max_lt (hk q.1 hq.1) hη
  have key := hηr hdist (mem_image_of_mem G₀ hq)
  rw [mem_ofPred_eq] at key
  exact key

private theorem coefficientRm04_smul_smul (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (a t : ℝ)
    (V W : E) :
    coefficientRm04 b x (a • V) (t • W) (t • W) (a • V) =
      (a * t) ^ 2 * coefficientRm04 b x V W W V := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
private theorem exists_unit_smul (v : E) : ∃ V : E, ‖V‖ ≤ 1 ∧ ‖v‖ • V = v := by
  rcases eq_or_ne v 0 with h | h
  · exact ⟨0, by simp, by simp [h]⟩
  · refine ⟨‖v‖⁻¹ • v, ?_, smul_inv_smul₀ (norm_ne_zero_iff.2 h) v⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

private theorem lower_transfer {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) {δ : ℝ}
    {V W : E} (h : -δ * (b x V V * b x W W - (b x V W) ^ 2) ≤ coefficientRm04 b x V W W V)
    {v w : E} (α β γ η : ℝ) (hv : α • V + β • W = v) (hw : γ • V + η • W = w) :
    -δ * (b x v v * b x w w - (b x v w) ^ 2) ≤ coefficientRm04 b x v w w v := by
  subst hv hw
  rw [bilin_gram_change_of_basis hsymm.self_of_nhds,
    coefficientRm04_change_of_basis hb hsymm hco, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- Item 4: an almost-nonnegative lower bound for the curvature of the approximating metrics,
uniform on `L`, when the limit curvature is nonnegative. -/
theorem eventually_coefficientRm04_lower (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U)
    (hc : ∀ k, ContDiffOn ℝ 2 (c k) U) (hc₀ : ContDiffOn ℝ 2 c₀ U)
    (hsymm : ∀ k, ∀ y ∈ U, ∀ v w : E, c k y v w = c k y w v)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) (hconv : MapCPConvergenceOn L 2 c c₀)
    (hnonneg : ∀ y ∈ L, ∀ v w : E, 0 ≤ coefficientRm04 c₀ y v w w v) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ y ∈ L, ∀ v w : E,
      -δ * (c k y v v * c k y w w - (c k y v w) ^ 2) ≤ coefficientRm04 (c k) y v w w v := by
  intro δ hδ
  obtain ⟨lam, hlam, -, hco⟩ := exists_eventually_coercive hL hLU hc₀ hconv hpos
  have hR := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_coefficientRm04 hU hL hLU hc hc₀ hconv hpos) (δ * lam ^ 2)
    (by positivity)
  filter_upwards [hco, hR] with k hk1 hk2 y hy v w
  have hyU : U ∈ 𝓝 y := hU.mem_nhds (hLU hy)
  have hb : ContDiffAt ℝ 2 (c k) y := (hc k).contDiffAt hyU
  have hs : ∀ᶠ z in 𝓝 y, ∀ u t : E, c k z u t = c k z t u :=
    Filter.eventually_of_mem hyU fun z hz => hsymm k z hz
  have hcoer : IsCoercive (c k y) := ⟨lam, hlam, fun u => by linarith [hk1 y hy u]⟩
  have hdeg : ∀ V : E, -δ * (c k y V V * c k y V V - (c k y V V) ^ 2) ≤
      coefficientRm04 (c k) y V V V V := by
    intro V
    have h := coefficientRm04_swap_left (c k) y V V V V
    have h0 : c k y V V * c k y V V - (c k y V V) ^ 2 = 0 := by ring
    rw [h0, mul_zero]
    linarith
  have horth : ∀ V W : E, ‖V‖ = 1 → ‖W‖ = 1 → inner ℝ V W = 0 →
      -δ * (c k y V V * c k y W W - (c k y V W) ^ 2) ≤ coefficientRm04 (c k) y V W W V := by
    intro V W hV hW hVW
    have hWV : c k y W V = c k y V W := hsymm k y (hLU hy) W V
    have ha := hk1 y hy V
    rw [hV, one_pow, mul_one] at ha
    have hq := hk1 y hy (c k y V W • V - c k y V V • W)
    have hn : ‖c k y V W • V - c k y V V • W‖ ^ 2 = (c k y V W) ^ 2 + (c k y V V) ^ 2 := by
      simp only [norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right, hVW,
        hV, hW, Real.norm_eq_abs, mul_one, mul_zero, sq_abs]
      ring
    have hexp : c k y (c k y V W • V - c k y V V • W) (c k y V W • V - c k y V V • W) =
        c k y V V * (c k y V V * c k y W W - (c k y V W) ^ 2) := by
      simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul, hWV]
      ring
    rw [hn, hexp] at hq
    have hapos : 0 < c k y V V := lt_of_lt_of_le hlam ha
    have hX : lam * c k y V V ≤ c k y V V * c k y W W - (c k y V W) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hapos
      nlinarith [mul_nonneg hlam.le (sq_nonneg (c k y V W))]
    have hG : lam ^ 2 ≤ c k y V V * c k y W W - (c k y V W) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ha hlam.le]
    have hVb : V ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hV.le
    have hWb : W ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hW.le
    have h1 := hk2 (y, V, W, W, V) ⟨hy, hVb, hWb, hWb, hVb⟩
    have h0 := hnonneg y hy V W
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    nlinarith [mul_le_mul_of_nonneg_left hG hδ.le]
  by_cases hv0 : v = 0
  · exact lower_transfer hb hs hcoer (hdeg w) 0 0 1 0 (by simp [hv0]) (by simp)
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    set V : E := ‖v‖⁻¹ • v with hVdef
    have hV1 : ‖V‖ = 1 := by rw [hVdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
    have hvV : ‖v‖ • V + (0 : ℝ) • V = v := by
      rw [zero_smul, add_zero, hVdef, smul_inv_smul₀ hnv]
    set w' : E := w - inner ℝ V w • V with hw'def
    by_cases hw0 : w' = 0
    · refine lower_transfer hb hs hcoer (hdeg V) ‖v‖ 0 (inner ℝ V w) 0 hvV ?_
      rw [zero_smul, add_zero]
      exact (sub_eq_zero.1 hw0).symm
    · have hnw : ‖w'‖ ≠ 0 := norm_ne_zero_iff.2 hw0
      set W : E := ‖w'‖⁻¹ • w' with hWdef
      have hW1 : ‖W‖ = 1 := by rw [hWdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw]
      have hVW : inner ℝ V W = 0 := by
        rw [hWdef, real_inner_smul_right, hw'def, inner_sub_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hV1]
        ring
      refine lower_transfer hb hs hcoer (horth V W hV1 hW1 hVW) ‖v‖ 0 (inner ℝ V w) ‖w'‖
        (by rw [zero_smul, add_zero, hVdef, smul_inv_smul₀ hnv]) ?_
      rw [hWdef, smul_inv_smul₀ hnw, hw'def, add_sub_cancel]

/-- Item 5: a uniform upper bound for the curvature of the approximating metrics on `L`. -/
theorem exists_eventually_abs_coefficientRm04_le (hU : IsOpen U) (hL : IsCompact L)
    (hLU : L ⊆ U) (hc : ∀ k, ContDiffOn ℝ 2 (c k) U) (hc₀ : ContDiffOn ℝ 2 c₀ U)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) (hconv : MapCPConvergenceOn L 2 c c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ y ∈ L, ∀ v w : E,
      |coefficientRm04 (c k) y v w w v| ≤ C * ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  have hD : IsCompact (L ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ
      (Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 1)))) :=
    hL.prod ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  obtain ⟨C₀, hC₀⟩ := hD.exists_bound_of_continuousOn
    ((continuousOn_coefficientRm04_limit hU hLU hc₀ hpos).mono
      (prod_mono subset_rfl (subset_univ _)))
  refine ⟨max C₀ 0 + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_coefficientRm04 hU hL hLU hc hc₀ hconv hpos) 1 one_pos]
    with k hk y hy v w
  obtain ⟨V, hV, hvV⟩ := exists_unit_smul v
  obtain ⟨W, hW, hwW⟩ := exists_unit_smul w
  have hVb : V ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hV
  have hWb : W ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hW
  have h1 := hk (y, V, W, W, V) ⟨hy, hVb, hWb, hWb, hVb⟩
  have h2 := hC₀ (y, V, W, W, V) ⟨hy, hVb, hWb, hWb, hVb⟩
  rw [Real.dist_eq] at h1
  rw [Real.norm_eq_abs] at h2
  have h3 : |coefficientRm04 (c k) y V W W V| ≤ max C₀ 0 + 1 := by
    have h4 := abs_sub_abs_le_abs_sub (coefficientRm04 (c k) y V W W V)
      (coefficientRm04 c₀ y V W W V)
    rw [abs_sub_comm] at h4
    linarith [le_max_left C₀ 0]
  have hR : coefficientRm04 (c k) y v w w v =
      (‖v‖ * ‖w‖) ^ 2 * coefficientRm04 (c k) y V W W V := by
    rw [← coefficientRm04_smul_smul, hvV, hwW]
  rw [hR, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc (‖v‖ * ‖w‖) ^ 2 * |coefficientRm04 (c k) y V W W V|
      ≤ (‖v‖ * ‖w‖) ^ 2 * (max C₀ 0 + 1) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = (max C₀ 0 + 1) * ‖v‖ ^ 2 * ‖w‖ ^ 2 := by ring

end Metric

end DifferentialGeometry.Analysis
