import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLiftInvariants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveShortTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem continuous_height_slice (c : ProductCurve M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    Continuous (fun x => c.y x t) :=
  (contDiffOn_univ.mp (hc.2.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun x _ => ⟨mem_univ x, ht⟩))).continuous

theorem angle_eq_of_map_eq (c d : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hd : d.SmoothOn (I := I) {t})
    (hmap : ∀ z, c.map z t = d.map z t) (x : ℝ) :
    c.angle g lambda x t = d.angle g lambda x t := by
  have hy (y : ℝ) : deriv (fun z => c.y z t) y = deriv (fun z => d.y z t) y :=
    c.deriv_y_eq_of_snd_map_eq d (fun z => congrArg Prod.snd (hmap z)) y
      (continuous_height_slice c hc (mem_singleton t)).continuousAt
      (continuous_height_slice d hd (mem_singleton t)).continuousAt
  have hM : (fun y : ℝ => (c.map (y : Surgery.Topology.Circle) t).1) =
      fun y : ℝ => (d.map (y : Surgery.Topology.Circle) t).1 := by
    funext y
    exact congrArg Prod.fst (hmap (y : Surgery.Topology.Circle))
  have hxM := congrArg Prod.fst (hmap (x : Surgery.Topology.Circle))
  have hs : c.speed g lambda x t = d.speed g lambda x t := by
    simp only [speed, inner, X, projection, CurveMap.lift, CurveMap.X]
    rw [hM, hxM, hy x]
    rfl
  rw [c.angle_eq, d.angle_eq, hs, hy x]

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] [I.Boundaryless]
  {D : RealTimeInterval} {a b : ℝ}

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [I.Boundaryless] in
private theorem smoothOn_singleton (c : ProductCurve M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    c.SmoothOn (I := I) {t} :=
  ⟨hc.1.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht)),
    hc.2.mono (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ht))⟩

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem initial_angle_lower_bound (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hc : c.SmoothOn (I := I) (Ico a T))
    (hramp : c.IsRampOn g lambda (Ico a T)) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ x, u₀ ≤ c.angle g lambda x a := by
  have ha : a ∈ Ico a T := ⟨le_rfl, haT⟩
  have hcont := (c.angle_contDiff_of_immersedOn g lambda hlambda hc hramp.1 a ha).continuous
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨(0 : ℝ), by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) hcont.continuousOn
  refine ⟨c.angle g lambda y a, hramp.2 y a ha, ?_⟩
  intro x
  have hper : Function.Periodic (fun x => c.angle g lambda x a) 1 :=
    c.angle_add_period g lambda hc a ha
  obtain ⟨z, hz, hxz⟩ := hper.exists_mem_Ico₀ zero_lt_one x
  rw [hxz]
  exact hmin ⟨hz.1, hz.2.le⟩

private theorem angle_lower_bound_Ico
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (hTb : T ≤ b)
    (hc : c.IsSolutionOn B.family.metric lambda (Ico a T))
    (hramp : c.IsRampOn B.family.metric lambda (Ico a T))
    (u₀ : ℝ) (hinit : ∀ x, u₀ ≤ c.angle B.family.metric lambda x a)
    (x t : ℝ) (ht : t ∈ Ico a T) :
    u₀ * Real.exp (-B.B₀ * (t - a)) ≤ c.angle B.family.metric lambda x t := by
  let u := (t + T) / 2
  have hau : a < u := by dsimp [u]; linarith [ht.1, ht.2]
  have huT : u < T := by dsimp [u]; linarith [ht.2]
  have htu : t ≤ u := by dsimp [u]; linarith [ht.2]
  have hsub : Icc a u ⊆ Ico a T := fun τ hτ => ⟨hτ.1, hτ.2.trans_lt huT⟩
  exact c.angle_lower_bound_of_isRampOn B lambda hlambda hau
    (Icc_subset_Icc le_rfl (huT.le.trans hTb))
    (hc.mono hsub (fun τ hτ => ((uniqueDiffOn_Icc hau) τ hτ).uniqueMDiffWithinAt))
    (hramp.mono hsub) u₀ hinit x t ⟨ht.1, htu⟩

theorem exists_isSolutionOn_Icc_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (hc : c.IsSolutionOn B.family.metric lambda (Ico a T))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric lambda x t ≤ K) :
    ∃ closed : ProductCurve M,
      closed.IsSolutionOn B.family.metric lambda (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed.map z t = c.map z t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Ico a T) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Ico a T) hc
  have hbound : ∀ x t, t ∈ Ico a T → c.map.curvature Bhat.family.metric x t ≤ K := by
    intro x t ht
    dsimp only [CurveMap.curvature, ProductCurve.curvature] at hcurv ⊢
    rw [hm, c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x t ht]
    exact hcurv x t ht
  obtain ⟨q, hq, hqeq⟩ := curveShorteningTerminalClosure_of_ricciBackground Bhat
    T haT hTb c.map K hK hsol hbound
  obtain ⟨closed, hclosed, heq⟩ := product_solution_lift A B.family.metric lambda hlambda q
    haT (Icc a T) (Or.inr rfl) (by rw [← hm]; exact hq)
  exact ⟨closed, hclosed, fun z t ht =>
    (heq z t ⟨ht.1, ht.2.le⟩).trans (hqeq z t ht)⟩

theorem isRampOn_Icc_of_isRampOn_Ico
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a T))
    (hramp : c.IsRampOn B.family.metric lambda (Ico a T)) :
    c.IsRampOn B.family.metric lambda (Icc a T) := by
  have hsub : Ico a T ⊆ Icc a T := Ico_subset_Icc_self
  have hco : c.IsSolutionOn B.family.metric lambda (Ico a T) :=
    hc.mono hsub (fun t ht => ((uniqueDiffOn_Ico a T) t ht).uniqueMDiffWithinAt)
  obtain ⟨u₀, hu₀, hinit⟩ := initial_angle_lower_bound c B.family.metric lambda hlambda haT
    hco.smooth hramp
  have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.angle B.family.metric lambda p.1 p.2)
      (univ ×ˢ Icc a T) :=
    c.angle_contDiffOn B.family.metric B.smooth lambda hlambda
      (uniqueDiffOn_Icc haT) (fun τ hτ => B.regular ⟨hτ.1, hτ.2.trans hTb⟩)
      hc.smooth hc.immersed
  refine ⟨hc.immersed, ?_⟩
  intro x t ht
  have hcont : ContinuousOn (fun τ => c.angle B.family.metric lambda x τ) (Icc a T) :=
    hsm.continuousOn.comp (f := fun τ : ℝ => (x, τ))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun τ hτ => ⟨mem_univ x, hτ⟩)
  have hle : u₀ * Real.exp (-B.B₀ * (t - a)) ≤ c.angle B.family.metric lambda x t := by
    have hb : ∀ τ ∈ Ico a T, u₀ * Real.exp (-B.B₀ * (τ - a)) ≤
        c.angle B.family.metric lambda x τ :=
      fun τ hτ => angle_lower_bound_Ico B c lambda hlambda hTb hco hramp u₀ hinit x τ hτ
    have hc' : ContinuousOn (fun τ => c.angle B.family.metric lambda x τ)
        (closure (Ico a T)) := by rwa [closure_Ico haT.ne]
    have he' : ContinuousOn (fun τ => u₀ * Real.exp (-B.B₀ * (τ - a)))
        (closure (Ico a T)) :=
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const)))).continuousOn
    have ht' : t ∈ closure (Ico a T) := by rwa [closure_Ico haT.ne]
    exact le_on_closure hb he' hc' ht'
  exact (mul_pos hu₀ (Real.exp_pos _)).trans_le hle

theorem exists_isSolutionOn_Icc_isRampOn_of_isRampOn_Ico
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (hc : c.IsSolutionOn B.family.metric lambda (Ico a T))
    (hramp : c.IsRampOn B.family.metric lambda (Ico a T)) :
    ∃ closed : ProductCurve M,
      closed.IsSolutionOn B.family.metric lambda (Icc a T) ∧
      closed.IsRampOn B.family.metric lambda (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed.map z t = c.map z t := by
  obtain ⟨K, hK, hcurv⟩ := c.exists_curvature_bound_on_Ico_of_isRampOn B lambda hlambda hTb hc hramp
  obtain ⟨closed, hclosed, hagree⟩ :=
    c.exists_isSolutionOn_Icc_of_curvature_le B lambda hlambda haT hTb hc hK hcurv
  have hr : closed.IsRampOn B.family.metric lambda (Ico a T) := by
    refine ⟨fun x t ht => hclosed.immersed x t ⟨ht.1, ht.2.le⟩, ?_⟩
    intro x t ht
    rw [closed.angle_eq_of_map_eq c B.family.metric lambda t
      (smoothOn_singleton closed hclosed.smooth ⟨ht.1, ht.2.le⟩)
      (smoothOn_singleton c hc.smooth ht) (fun z => hagree z t ht) x]
    exact hramp.2 x t ht
  exact ⟨closed, hclosed,
    closed.isRampOn_Icc_of_isRampOn_Ico B lambda hlambda haT hTb hclosed hr, hagree⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
