import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts

/-!
# Short geodesic interpolation near the diagonal (shared interface D5 of the finite soul package)

For a metric `g` of class `C^{r+1}` (`1 ≤ r`) and a point `x₀`, read everything in the chart
`κ = extChartAt I x₀`. Near `(κ x₀, κ x₀)` there is a `C^r` map `L : E × E → E` (the chart reading
of `log_x y`) with `exp_x (dκ⁻¹ (L (κ x, κ y))) = y`, and the short geodesic interpolation
`J(x, y, s) = exp_x (s · log_x y)`, read in the chart, is `C^r` with derivative
`(1 - s) · fst + s · snd` at the diagonal point (`exists_shortInterpolation_chart`):
`D J_s |(q, q) = (1 - s) I ⊕ s I`.

With the length distance of `g` (`hnorm`, `2 ≤ r`), the interpolation is minimizing:
`d(x, J_s) = s d(x, y)` and `d(J_s, y) = (1 - s) d(x, y)` (`exists_shortInterpolation_chart_dist`).

Route: the two-point map `F(a, ξ) = (a, κ(exp(T⁻¹(a, ξ))))` (`expChartPair`) has derivative
`(a, b) ↦ (a, a + b)` at `(κ x₀, 0)`; `L = (F⁻¹).2` for its local inverse, and
`κ(J_s) = (F(a, s L(a, b))).2`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

omit [T2Space M] in
/-- The second component of the two-point map, read through the base point of the chart. -/
theorem expChartPair_snd_eq {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x₀ : M) {w : E × E}
    (hw : w.1 ∈ (extChartAt I x₀).target) :
    (g.expChartPair x₀ w).2 = extChartAt I x₀ (g.expMap (⟨(extChartAt I x₀).symm w.1,
      mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm w.1 w.2⟩ : TangentBundle I M)) := by
  have hxs : (extChartAt I x₀).symm w.1 ∈ (chartAt H x₀).source := by
    have h := (extChartAt I x₀).map_target hw
    rwa [extChartAt_source] at h
  have hκ : extChartAt I x₀ ((extChartAt I x₀).symm w.1) = w.1 := (extChartAt I x₀).right_inv hw
  have hT : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm w =
      (⟨(extChartAt I x₀).symm w.1, mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm w.1 w.2⟩ :
        TangentBundle I M) := by
    have hw' : w = ((extChartAt I x₀ ((extChartAt I x₀).symm w.1), w.2) : E × E) := by
      rw [hκ]
    rw [hw', extChartAt_tangent_symm_mk x₀ hxs, hκ]
  change extChartAt I x₀ (g.expMap ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm w))
    = _
  rw [hT]

/-- **Short geodesic interpolation (shared interface D5).** Near `(κ x₀, κ x₀)` (`κ` the chart at
`x₀`), with `x = κ⁻¹ z.1`, `v_z = dκ⁻¹(L z) ∈ T_x M`:
* `L` is `C^r`, vanishes on the diagonal, and `D L = snd - fst` at `(κ x₀, κ x₀)`;
* `exp_x v_z = κ⁻¹ z.2`, and the whole arc `exp_x (s v_z)`, `s ∈ [0, 1]`, stays in the chart;
* `z ↦ κ(exp_x (s v_z))` is `C^r` for `s ∈ [0, 1]` and has derivative `(1 - s) fst + s snd` at the
  diagonal point, for every `s`. -/
theorem exists_shortInterpolation_chart
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (x₀ : M) :
    ∃ W : Set (E × E), IsOpen W ∧ ((extChartAt I x₀ x₀, extChartAt I x₀ x₀) : E × E) ∈ W ∧
      W ⊆ (extChartAt I x₀).target ×ˢ (extChartAt I x₀).target ∧
      ∃ L : E × E → E, ContDiffOn ℝ r L W ∧
        L (extChartAt I x₀ x₀, extChartAt I x₀ x₀) = 0 ∧
        HasFDerivAt L (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E)
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) ∧
        (∀ z ∈ W, z.1 = z.2 → L z = 0) ∧
        (∀ z ∈ W, g.expMap (⟨(extChartAt I x₀).symm z.1,
          mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) =
            (extChartAt I x₀).symm z.2) ∧
        (∀ z ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, g.expMap (⟨(extChartAt I x₀).symm z.1,
          s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) ∈
            (extChartAt I x₀).source) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ r (fun z : E × E => extChartAt I x₀
          (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M))) W) ∧
        ∀ s : ℝ, HasFDerivAt (fun z : E × E => extChartAt I x₀
          (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M)))
          ((1 - s) • ContinuousLinearMap.fst ℝ E E + s • ContinuousLinearMap.snd ℝ E E)
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  have hr1 : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  set κ := extChartAt I x₀ with hκ
  set F := g.expChartPair x₀ with hFdef
  set a₀ : E := κ x₀ with ha₀
  set z₀ : E × E := (a₀, (0 : E)) with hz₀
  set U₀ := g.expChartPairDomain x₀ with hU₀def
  have hU₀ : IsOpen U₀ := g.isOpen_expChartPairDomain hr x₀
  have hz₀U : z₀ ∈ U₀ := g.mem_expChartPairDomain_zero hr x₀
  let Lq : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))
    (fun z => by simp) (fun z => by simp)
  have hFd : HasFDerivAt F (Lq : E × E →L[ℝ] E × E) z₀ := g.hasFDerivAt_expChartPair hr x₀
  have hFc : ∀ w ∈ U₀, ContDiffAt ℝ r F w := fun w hw => g.contDiffAt_expChartPair hr x₀ hw
  set Ψ := (hFc z₀ hz₀U).toOpenPartialHomeomorph F hFd hr0 with hΨ
  have hΨF : ∀ w, Ψ w = F w := fun _ => rfl
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have ha₀t : a₀ ∈ κ.target := mem_extChartAt_target x₀
  -- the two-point map preserves the first coordinate and fixes the zero section
  have hF1 : ∀ w, (F w).1 = w.1 := fun _ => rfl
  have hFzero : ∀ a ∈ κ.target, F (a, 0) = (a, a) := by
    intro a ha
    refine Prod.ext rfl ?_
    rw [expChartPair_snd_eq g x₀ (w := (a, 0)) ha]
    have h0 : (⟨κ.symm a, mfderiv 𝓘(ℝ, E) I κ.symm a (0 : E)⟩ : TangentBundle I M) =
        ⟨κ.symm a, 0⟩ := by
      congr 1
      exact map_zero _
    change κ (g.expMap (⟨κ.symm a, mfderiv 𝓘(ℝ, E) I κ.symm a (0 : E)⟩ : TangentBundle I M)) = a
    rw [h0, g.expMap_zero hr]
    exact κ.right_inv ha
  set w₀ : E × E := (a₀, a₀) with hw₀
  have hFz₀ : F z₀ = w₀ := hFzero a₀ ha₀t
  have hz₀src : z₀ ∈ Ψ.source := (hFc z₀ hz₀U).mem_toOpenPartialHomeomorph_source hFd hr0
  have hw₀tgt : w₀ ∈ Ψ.target := by
    rw [← hFz₀]
    exact (hFc z₀ hz₀U).image_mem_toOpenPartialHomeomorph_target hFd hr0
  have hΨw₀ : Ψ.symm w₀ = z₀ := by
    rw [← hFz₀]
    exact Ψ.left_inv hz₀src
  -- the locus of invertible derivative
  have hFC1 : ContDiffOn ℝ 1 F U₀ := fun w hw => ((hFc w hw).of_le hr1).contDiffWithinAt
  set S₁ := Ψ.source ∩ (U₀ ∩ fderiv ℝ F ⁻¹'
    range ((↑) : ((E × E) ≃L[ℝ] (E × E)) → (E × E →L[ℝ] E × E))) with hS₁
  have hS₁o : IsOpen S₁ := Ψ.open_source.inter
    ((hFC1.continuousOn_fderiv_of_isOpen hU₀ le_rfl).isOpen_inter_preimage hU₀
      ContinuousLinearEquiv.isOpen)
  have hz₀S₁ : z₀ ∈ S₁ := ⟨hz₀src, hz₀U, ⟨Lq, hFd.fderiv.symm⟩⟩
  obtain ⟨β, hβ, hβU⟩ := Metric.isOpen_iff.mp hU₀ z₀ hz₀U
  -- the neighbourhood
  set W : Set (E × E) := (Ψ.target ∩ Ψ.symm ⁻¹' (S₁ ∩ ball z₀ β)) ∩
    ((κ.target ×ˢ κ.target) ∩ ((fun z : E × E => ((z.1, (0 : E)) : E × E)) ⁻¹' Ψ.source ∩
      {z : E × E | z.1 ∈ ball a₀ β})) with hW
  have hWo : IsOpen W := by
    refine (Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target
      (hS₁o.inter isOpen_ball)).inter ?_
    refine ((isOpen_extChartAt_target x₀).prod (isOpen_extChartAt_target x₀)).inter ?_
    exact (Ψ.open_source.preimage (continuous_fst.prodMk continuous_const)).inter
      (isOpen_ball.preimage continuous_fst)
  have hw₀W : w₀ ∈ W := by
    refine ⟨⟨hw₀tgt, ?_⟩, ⟨ha₀t, ha₀t⟩, ?_, mem_ball_self hβ⟩
    · change Ψ.symm w₀ ∈ S₁ ∩ ball z₀ β
      rw [hΨw₀]
      exact ⟨hz₀S₁, mem_ball_self hβ⟩
    · exact hz₀src
  set L : E × E → E := fun z => (Ψ.symm z).2 with hLdef
  -- basic facts on `W`
  have hsymm1 : ∀ z ∈ W, (Ψ.symm z).1 = z.1 := by
    intro z hz
    have h := congrArg Prod.fst (Ψ.right_inv hz.1.1)
    rw [hΨF] at h
    exact h
  have hsymmform : ∀ z ∈ W, Ψ.symm z = ((z.1, L z) : E × E) := fun z hz =>
    Prod.ext (hsymm1 z hz) rfl
  have hseg : ∀ z ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, ((z.1, s • L z) : E × E) ∈ U₀ := by
    intro z hz s hs
    apply hβU
    have h1 : ((z.1, (0 : E)) : E × E) ∈ ball z₀ β := by
      rw [mem_ball, hz₀, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hz.2.2.2
    have h2 : ((z.1, L z) : E × E) ∈ ball z₀ β := by
      rw [← hsymmform z hz]
      exact hz.1.2.2
    have h := (convex_ball z₀ β) h1 h2 (sub_nonneg.2 hs.2) hs.1 (by ring)
    convert h using 1
    ext
    · simp only [Prod.fst_add, Prod.smul_fst]
      module
    · simp
  have hJF : ∀ s : ℝ, ∀ z : E × E, z.1 ∈ κ.target →
      κ (g.expMap (⟨κ.symm z.1, s • mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M)) =
        (F (z.1, s • L z)).2 := by
    intro s z hz
    rw [expChartPair_snd_eq g x₀ (w := (z.1, s • L z)) hz]
    exact congrArg (fun v : TangentSpace I (κ.symm z.1) =>
      κ (g.expMap (⟨κ.symm z.1, v⟩ : TangentBundle I M)))
      (map_smul (mfderiv 𝓘(ℝ, E) I κ.symm z.1) s (L z)).symm
  have hsrc : ∀ z ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, g.expMap (⟨κ.symm z.1,
      s • mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M) ∈ κ.source := by
    intro z hz s hs
    have hU := (hseg z hz s hs).2
    have hxs : κ.symm z.1 ∈ (chartAt H x₀).source := by
      have h := κ.map_target hz.2.1.1
      rwa [hκ, extChartAt_source] at h
    have hT : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm ((z.1, s • L z) : E × E) =
        (⟨κ.symm z.1, s • mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M) := by
      have hκz : κ (κ.symm z.1) = z.1 := κ.right_inv hz.2.1.1
      have hw' : ((z.1, s • L z) : E × E) = ((κ (κ.symm z.1), s • L z) : E × E) := by rw [hκz]
      rw [hw', extChartAt_tangent_symm_mk x₀ hxs, hκz]
      exact congrArg (fun v : TangentSpace I (κ.symm z.1) => (⟨κ.symm z.1, v⟩ : TangentBundle I M))
        (map_smul (mfderiv 𝓘(ℝ, E) I κ.symm z.1) s (L z))
    have hU' : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm ((z.1, s • L z) : E × E) ∈
        g.expDomain ∩ g.expMap ⁻¹' (extChartAt I x₀).source := hU
    rw [hT] at hU'
    exact hU'.2
  -- `L` is `C^r` on `W`
  have hLc : ∀ z ∈ W, ContDiffAt ℝ r L z := by
    intro z hz
    obtain ⟨⟨hzt, hzS, -⟩, -⟩ := hz
    obtain ⟨-, hU, e, he⟩ := hzS
    have hdiff : HasFDerivAt F (e : E × E →L[ℝ] E × E) (Ψ.symm z) := by
      rw [he]
      exact ((hFc _ hU).differentiableAt hr0).hasFDerivAt
    have hsymm : ContDiffAt ℝ r Ψ.symm z :=
      Ψ.contDiffAt_symm hzt (f₀' := e) hdiff (hFc _ hU)
    exact contDiffAt_snd.comp z hsymm
  have hLd : HasFDerivAt L (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E) w₀ := by
    have h := Ψ.hasFDerivAt_symm hw₀tgt (f' := Lq) (by rw [hΨw₀]; exact hFd)
    have h2 : HasFDerivAt L ((ContinuousLinearMap.snd ℝ E E).comp
        (Lq.symm : E × E →L[ℝ] E × E)) w₀ :=
      (hasFDerivAt_snd (p := Ψ.symm w₀)).comp w₀ h
    refine h2.congr_fderiv ?_
    ext v <;> simp [Lq]
  refine ⟨W, hWo, hw₀W, fun z hz => hz.2.1, L, fun z hz => (hLc z hz).contDiffWithinAt, ?_, hLd,
    ?_, ?_, ?_, ?_, ?_⟩
  · change (Ψ.symm w₀).2 = 0
    rw [hΨw₀]
  · intro z hz hzz
    have hsrc0 : ((z.1, (0 : E)) : E × E) ∈ Ψ.source := hz.2.2.1
    have hF0 : Ψ ((z.1, (0 : E)) : E × E) = z := by
      rw [hΨF, hFzero z.1 hz.2.1.1]
      exact Prod.ext rfl hzz
    change (Ψ.symm z).2 = 0
    rw [← hF0, Ψ.left_inv hsrc0]
  · intro z hz
    have h1 := hsrc z hz 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul] at h1
    have h2 := congrArg Prod.snd (Ψ.right_inv hz.1.1)
    rw [hΨF, hsymmform z hz, expChartPair_snd_eq g x₀ (w := (z.1, L z)) hz.2.1.1] at h2
    rw [← h2, κ.left_inv h1]
  · exact hsrc
  · intro s hs z hz
    have hcd : ContDiffAt ℝ r (fun z : E × E => (F (z.1, s • L z)).2) z := by
      have hin : ContDiffAt ℝ r (fun z : E × E => ((z.1, s • L z) : E × E)) z :=
        contDiffAt_fst.prodMk ((hLc z hz).const_smul s)
      have hF' : ContDiffAt ℝ r F ((z.1, s • L z) : E × E) := hFc _ (hseg z hz s hs)
      have h : ContDiffAt ℝ r (F ∘ fun z : E × E => ((z.1, s • L z) : E × E)) z := hF'.comp z hin
      exact contDiffAt_snd.comp z h
    refine (hcd.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hWo.mem_nhds hz] with y hy
    exact hJF s y hy.2.1.1
  · intro s
    have hin : HasFDerivAt (fun z : E × E => ((z.1, s • L z) : E × E))
        ((ContinuousLinearMap.fst ℝ E E).prod
          (s • (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))) w₀ :=
      hasFDerivAt_fst.prodMk (hLd.const_smul s)
    have hin0 : ((w₀.1, s • L w₀) : E × E) = z₀ := by
      change ((a₀, s • (Ψ.symm w₀).2) : E × E) = z₀
      rw [hΨw₀, hz₀, smul_zero]
    have hFd' : HasFDerivAt F (Lq : E × E →L[ℝ] E × E) ((w₀.1, s • L w₀) : E × E) := by
      rw [hin0]; exact hFd
    have hcomp : HasFDerivAt (fun z : E × E => (F (z.1, s • L z)).2)
        ((ContinuousLinearMap.snd ℝ E E).comp ((Lq : E × E →L[ℝ] E × E).comp
          ((ContinuousLinearMap.fst ℝ E E).prod
            (s • (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))))) w₀ :=
      (hasFDerivAt_snd (p := F (w₀.1, s • L w₀))).comp w₀
        (HasFDerivAt.comp (g := F) (f := fun z : E × E => ((z.1, s • L z) : E × E)) w₀ hFd' hin)
    have hcomp' : HasFDerivAt (fun z : E × E => (F (z.1, s • L z)).2)
        ((1 - s) • ContinuousLinearMap.fst ℝ E E + s • ContinuousLinearMap.snd ℝ E E) w₀ := by
      refine hcomp.congr_fderiv ?_
      ext v
      · simp [Lq]
        module
      · simp [Lq]
    refine hcomp'.congr_of_eventuallyEq ?_
    filter_upwards [hWo.mem_nhds hw₀W] with y hy
    exact hJF s y hy.2.1.1

end Bundle.ContMDiffRiemannianMetric
