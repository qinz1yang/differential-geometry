import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.OppositeBusemann

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

section ScalarSandwich

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivAt_of_support_sandwich
    {f l u : F → ℝ} {x : F}
    (hl : DifferentiableAt ℝ l x) (hu : DifferentiableAt ℝ u x)
    (hlx : l x = f x) (hux : u x = f x)
    (hbound : ∀ᶠ y in 𝓝 x, l y ≤ f y ∧ f y ≤ u y) :
    HasFDerivAt f (fderiv ℝ l x) x := by
  have hmin : IsLocalMin (fun y => u y - l y) x := by
    filter_upwards [hbound] with y hy
    rw [hux, hlx, sub_self]
    exact sub_nonneg.mpr (hy.1.trans hy.2)
  have hderiv := hu.hasFDerivAt.sub hl.hasFDerivAt
  have hzero := hmin.hasFDerivAt_eq_zero hderiv
  rw [hzero] at hderiv
  have hgap : (fun y => u y - l y) =o[𝓝 x] (fun y => y - x) := by
    simpa only [Pi.sub_apply, hux, hlx, sub_self, zero_apply, sub_zero] using hderiv.isLittleO
  have hsmall : (fun y => f y - l y) =o[𝓝 x] (fun y => y - x) := by
    apply (Asymptotics.IsBigO.of_bound' ?_).trans_isLittleO hgap
    filter_upwards [hbound] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hy.1),
      abs_of_nonneg (sub_nonneg.mpr (hy.1.trans hy.2))]
    exact sub_le_sub_right hy.2 _
  have hdiff : HasFDerivAt (fun y => f y - l y) (0 : F →L[ℝ] ℝ) x := by
    apply HasFDerivAt.of_isLittleO
    simpa only [hlx, sub_self, zero_apply, sub_zero] using hsmall
  have hadd := hdiff.add hl.hasFDerivAt
  have heq : (fun y => f y - l y) + l = f := by
    funext y
    exact sub_add_cancel (f y) (l y)
  simpa only [heq, zero_add] using hadd

end ScalarSandwich

section ManifoldSandwich

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem mdifferentiableAt_of_support_sandwich
    {f l u : M → ℝ} {x : M}
    (hl : MDifferentiableAt I 𝓘(ℝ, ℝ) l x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hlx : l x = f x) (hux : u x = f x)
    (hbound : ∀ᶠ y in 𝓝 x, l y ≤ f y ∧ f y ≤ u y) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
  have hchart (k : M → ℝ) : MDifferentiableAt I 𝓘(ℝ, ℝ) k x ↔
      DifferentiableAt ℝ (k ∘ (extChartAt I x).symm) ((extChartAt I x) x) := by
    rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source H x),
      I.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt]
  apply (hchart f).mpr
  apply (hasFDerivAt_of_support_sandwich ((hchart l).mp hl) ((hchart u).mp hu)
    ?_ ?_ ?_).differentiableAt
  · simpa only [Function.comp_apply, extChartAt_to_inv] using hlx
  · simpa only [Function.comp_apply, extChartAt_to_inv] using hux
  · have hlim : Tendsto (extChartAt I x).symm (𝓝 ((extChartAt I x) x)) (𝓝 x) := by
      simpa only [ContinuousAt, extChartAt_to_inv] using
        (continuousAt_extChartAt_symm (I := I) x)
    exact hlim.eventually hbound

end ManifoldSandwich

section SupportGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem gradientFun_eq_of_differentiable_lower_support
    (g : SmoothRiemannianMetric I M) {f φ : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : MDifferentiableAt I 𝓘(ℝ, ℝ) φ x)
    (hcontact : φ x = f x) (hbelow : ∀ᶠ y in 𝓝 x, φ y ≤ f y) :
    gradientFun (I := I) g f x = gradientFun (I := I) g φ x := by
  have hmin : IsLocalMin (fun y => f y - φ y) x := by
    filter_upwards [hbelow] with y hy
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hy
  have hz := gradientFun_eq_zero_of_isLocalMin (I := I) g hmin (hf.sub hφ)
  rw [gradientFun_sub (I := I) g hf hφ] at hz
  exact sub_eq_zero.mp hz

end SupportGradient

section OppositeBusemann

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem opposite_busemann_mdifferentiable
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) :
    MDifferentiable I 𝓘(ℝ, ℝ) (busemann (fun t : ℝ≥0 => γ t)) ∧
      MDifferentiable I 𝓘(ℝ, ℝ) (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) := by
  let cp : ℝ≥0 → M := fun t => γ t
  let cn : ℝ≥0 → M := fun t => γ (-(t : ℝ))
  have hp : Isometry cp := by
    apply Isometry.of_dist_eq
    intro s t
    exact hγ.dist_eq s t
  have hn : Isometry cn := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hγ.dist_eq, dist_neg_neg]
    rfl
  have hsum (y : M) : busemann cp y + busemann cn y = 0 :=
    opposite_busemann_sum_eq_zero (I := I) g hEnorm hRic hγ y
  have hpos : MDifferentiable I 𝓘(ℝ, ℝ) (busemann cp) := by
    intro p
    obtain ⟨vp, hvp, hip, hcap, hsp⟩ :=
      exists_smooth_intrinsic_coray_support (I := I) g hEnorm cp hp p
    obtain ⟨vn, hvn, hin, hcan, hsn⟩ :=
      exists_smooth_intrinsic_coray_support (I := I) g hEnorm cn hn p
    obtain ⟨Up, hUp, hpUp, hfp, hbp, hep⟩ := hsp 1 zero_lt_one
    obtain ⟨Un, hUn, hpUn, hfn, hbn, hen⟩ := hsn 1 zero_lt_one
    have hpa := ((hfp p hpUp).contMDiffAt (hUp.mem_nhds hpUp)).mdifferentiableAt (by simp)
    have hna := ((hfn p hpUn).contMDiffAt (hUn.mem_nhds hpUn)).mdifferentiableAt (by simp)
    apply mdifferentiableAt_of_support_sandwich (I := I) hpa hna.neg hep
    · rw [Pi.neg_apply, hen]
      linarith [hsum p]
    · apply Eventually.of_forall
      intro y
      refine ⟨hbp y, ?_⟩
      rw [Pi.neg_apply]
      linarith [hbn y, hsum y]
  have hneg : busemann cn = -busemann cp := by
    funext y
    change busemann cn y = -busemann cp y
    linarith [hsum y]
  refine ⟨hpos, ?_⟩
  change MDifferentiable I 𝓘(ℝ, ℝ) (busemann cn)
  rw [hneg]
  exact hpos.neg

theorem opposite_busemann_gradient_neg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (x : M) :
    gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) x =
      -gradientFun (I := I) g (busemann (fun t : ℝ≥0 => γ t)) x := by
  have heq : busemann (fun t : ℝ≥0 => γ (-(t : ℝ))) =
      -busemann (fun t : ℝ≥0 => γ t) := by
    funext y
    change busemann (fun t : ℝ≥0 => γ (-(t : ℝ))) y =
      -busemann (fun t : ℝ≥0 => γ t) y
    linarith [opposite_busemann_sum_eq_zero (I := I) g hEnorm hRic hγ y]
  rw [heq]
  exact gradientFun_neg (I := I) g
    ((opposite_busemann_mdifferentiable (I := I) g hEnorm hRic hγ).1 x)

end OppositeBusemann

end DifferentialGeometry.Geometry.Topology

end
