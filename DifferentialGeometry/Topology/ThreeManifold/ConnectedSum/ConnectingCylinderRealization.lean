import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ConnectingCylinderQuotient
import DifferentialGeometry.Topology.Manifold.BallChartRadialCollar
import DifferentialGeometry.Topology.Manifold.CylinderCollar.DoubleSlabMatching

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

universe u v w

section OuterCaps

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

private theorem outerPunctured_mem_interior (x : outerPunctured c) :
    x.val.val ∈ c.toBallChart.interior := by
  rintro ⟨y, hy, hyx⟩
  exact x.property ⟨y, (closedBall_subset_ball (by norm_num : (1 : ℝ) < 5 / 4)) hy, hyx⟩

private theorem outerPunctured_not_mem_closedBall_image_iff (x : outerPunctured c) :
    x.val.val ∉ c.chart '' closedBall (0 : E3) (5 / 4) ↔
      x ∉ range (outerLeftBoundary c) := by
  constructor
  · rintro hx ⟨z, rfl⟩
    apply hx
    refine ⟨(5 / 4 : ℝ) • z.val, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, BallChart.norm_radial z (by norm_num)]
  · intro hx hmem
    obtain ⟨y, hy, heq⟩ := hmem
    have hyn : ‖y‖ = 5 / 4 := by
      apply le_antisymm (mem_closedBall_zero_iff.mp hy)
      by_contra h
      exact x.property ⟨y, mem_ball_zero_iff.mpr (lt_of_not_ge h), heq⟩
    have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hyn]; norm_num)
    let z : S2 := ⟨‖y‖⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]⟩
    apply hx
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change c.chart ((5 / 4 : ℝ) • (‖y‖⁻¹ • y)) = x.val.val
    rw [← hyn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul]
    exact heq

private theorem isClosed_outer_closedBall_image :
    IsClosed (c.chart '' closedBall (0 : E3) (5 / 4)) := by
  apply IsCompact.isClosed
  apply (isCompact_closedBall (0 : E3) (5 / 4)).image_of_continuousOn
  apply c.chart.contMDiffOn_toFun.continuousOn.mono
  exact (closedBall_subset_closedBall (by norm_num)).trans c.closedBall_subset_source

private theorem eventually_outerPunctured (x : outerPunctured c)
    (hx : x ∉ range (outerLeftBoundary c)) :
    ∀ᶠ y : c.toBallChart.interior in 𝓝 ⟨x.val.val, outerPunctured_mem_interior c x⟩,
      c.toBallChart.interiorToPunctured y ∈ outerPunctured c := by
  have hmem := (outerPunctured_not_mem_closedBall_image_iff c x).mpr hx
  have hopen := (isClosed_outer_closedBall_image c).isOpen_compl
  have hcont : ContinuousAt (fun y : c.toBallChart.interior => y.val)
      ⟨x.val.val, outerPunctured_mem_interior c x⟩ := continuous_subtype_val.continuousAt
  have hnhds : ∀ᶠ y : c.toBallChart.interior in 𝓝 ⟨x.val.val, outerPunctured_mem_interior c x⟩,
      y.val ∉ c.chart '' closedBall (0 : E3) (5 / 4) :=
    hcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hnhds] with y hy
  rintro ⟨z, hz, heq⟩
  exact hy ⟨z, ball_subset_closedBall hz, heq⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {P : Type w} [TopologicalSpace P] [ChartedSpace H' P]

private theorem isLocalDiffeomorphAt_outerLeft_of_not_mem_boundary
    (H : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier → P)
    (f : M.Carrier → P)
    (hH : ∀ x : outerPunctured c, H (outerLeft c d a x) = f x.val.val)
    (x : outerPunctured c) (hx : x ∉ range (outerLeftBoundary c))
    (hf : IsLocalDiffeomorphAt (𝓡 3) J ∞ f x.val.val) :
    IsLocalDiffeomorphAt (𝓡 3) J ∞ H (outerLeft c d a x) := by
  let u : c.toBallChart.interior := ⟨x.val.val, outerPunctured_mem_interior c x⟩
  have heq : (H ∘ interiorLeft c.toBallChart d.toBallChart a.val) =ᶠ[𝓝 u]
      (fun y : c.toBallChart.interior => f y.val) := by
    filter_upwards [eventually_outerPunctured c x hx] with y hy
    exact hH ⟨c.toBallChart.interiorToPunctured y, hy⟩
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) J ∞
      (H ∘ interiorLeft c.toBallChart d.toBallChart a.val) u :=
    DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq
      ((DifferentialGeometry.isLocalDiffeomorph_subtype_val c.toBallChart.interior u).comp
        J P hf)
  have hlocal := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (I := 𝓡 3) (J := 𝓡 3) (K := J)
    (N := (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier)
    (f := interiorLeft c.toBallChart d.toBallChart a.val) (g := H) (x := u)
    hcomp ((smoothConnectedSum M N c d a).interiorLeft_localDiffeomorph u)
  exact hlocal

private theorem isLocalDiffeomorphAt_outerRight_of_not_mem_boundary
    (H : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier → P)
    (f : N.Carrier → P)
    (hH : ∀ x : outerPunctured d, H (outerRight c d a x) = f x.val.val)
    (x : outerPunctured d) (hx : x ∉ range (outerRightBoundary d a))
    (hf : IsLocalDiffeomorphAt (𝓡 3) J ∞ f x.val.val) :
    IsLocalDiffeomorphAt (𝓡 3) J ∞ H (outerRight c d a x) := by
  have hx' : x ∉ range (outerLeftBoundary d) := by
    rintro ⟨z, rfl⟩
    apply hx
    refine ⟨a.val.symm z, ?_⟩
    change outerLeftBoundary d (a.val (a.val.symm z)) = outerLeftBoundary d z
    rw [a.val.apply_symm_apply]
  let u : d.toBallChart.interior := ⟨x.val.val, outerPunctured_mem_interior d x⟩
  have heq : (H ∘ interiorRight c.toBallChart d.toBallChart a.val) =ᶠ[𝓝 u]
      (fun y : d.toBallChart.interior => f y.val) := by
    filter_upwards [eventually_outerPunctured d x hx'] with y hy
    exact hH ⟨d.toBallChart.interiorToPunctured y, hy⟩
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) J ∞
      (H ∘ interiorRight c.toBallChart d.toBallChart a.val) u :=
    DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq
      ((DifferentialGeometry.isLocalDiffeomorph_subtype_val d.toBallChart.interior u).comp
        J P hf)
  have hlocal := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (I := 𝓡 3) (J := 𝓡 3) (K := J)
    (N := (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier)
    (f := interiorRight c.toBallChart d.toBallChart a.val) (g := H) (x := u)
    hcomp ((smoothConnectedSum M N c d a).interiorRight_localDiffeomorph u)
  exact hlocal


end OuterCaps

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
  {E K P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K] {I : ModelWithCorners ℝ E K}
  [TopologicalSpace P] [ChartedSpace K P]

private theorem radial_outer (z : S2) {r : ℝ} (hlo : 5 / 4 ≤ r) (hhi : r ≤ 2) :
    c.toBallChart.radialMap z r ⟨by linarith, hhi⟩ ∈ outerPunctured c := by
  intro hx
  obtain ⟨y,hy,he⟩ := hx
  have hys : y ∈ c.chart.source := c.closedBall_subset_source
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hy)
  have hrs : r • z.val ∈ c.chart.source := by
    apply c.closedBall_subset_source
    simpa only [mem_closedBall_zero_iff, BallChart.norm_radial z (by linarith : 0 ≤ r)] using hhi
  have he' : y = r • z.val := c.chart.injOn hys hrs he
  rw [he', mem_ball_zero_iff, BallChart.norm_radial z (by linarith : 0 ≤ r)] at hy
  linarith

private theorem connectingCylinderOpen_left (q : connectingCylinderDomain) (hq : q.val.2 ≤ 0) :
    ∃ x : outerPunctured c,
      connectingCylinderOpen c d a q = outerLeft c d a x ∧
      x.val.val = c.chart ((5 / 4 - q.val.2 / 2) • q.val.1.val) := by
  have hr : (5 / 4 - q.val.2 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 := by
    constructor <;> linarith [q.property.2.1]
  let x : outerPunctured c := ⟨c.toBallChart.radialMap q.val.1 _ hr,
    radial_outer c q.val.1 (by linarith) hr.2⟩
  refine ⟨x, ?_, rfl⟩
  unfold connectingCylinderOpen
  rw [collarMap_of_nonneg _ _ _ _ (by linarith)]
  apply congrArg (inl c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change c.chart ((1 + (1 - 2 * q.val.2) / 4) • q.val.1.val) =
    c.chart ((5 / 4 - q.val.2 / 2) • q.val.1.val)
  congr 2
  ring

private theorem connectingCylinderOpen_right (q : connectingCylinderDomain) (hq : 1 ≤ q.val.2) :
    ∃ x : outerPunctured d,
      connectingCylinderOpen c d a q = outerRight c d a x ∧
      x.val.val = d.chart ((3 / 4 + q.val.2 / 2) • (a.val q.val.1).val) := by
  have hr : (3 / 4 + q.val.2 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 := by
    constructor <;> linarith [q.property.2.2]
  let x : outerPunctured d := ⟨d.toBallChart.radialMap (a.val q.val.1) _ hr,
    radial_outer d (a.val q.val.1) (by linarith) hr.2⟩
  refine ⟨x, ?_, rfl⟩
  unfold connectingCylinderOpen
  rw [collarMap_of_neg _ _ _ _ (by linarith)]
  apply congrArg (inr c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change d.chart ((1 - (1 - 2 * q.val.2) / 4) • (a.val q.val.1).val) =
    d.chart ((3 / 4 + q.val.2 / 2) • (a.val q.val.1).val)
  congr 2
  ring

omit [TopologicalSpace P] in
private theorem connectingCylinderOpen_local_equation
    (H : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier → P)
    (f₀ : M.Carrier → P) (f₁ : N.Carrier → P) (T : S2 × ℝ → P)
    (hT : ∀ q : S2 × unitInterval, H (connectingCylinder c d a q) = T (q.1,q.2.val))
    (hL : ∀ x, H (outerLeft c d a x) = f₀ x.val.val)
    (hR : ∀ x, H (outerRight c d a x) = f₁ x.val.val)
    (hzero : ∀ z : S2, T =ᶠ[𝓝 (z,0)]
      (fun q => f₀ (c.chart ((5 / 4 - q.2 / 2) • q.1.val))))
    (hone : ∀ z : S2, T =ᶠ[𝓝 (z,1)]
      (fun q => f₁ (d.chart ((3 / 4 + q.2 / 2) • (a.val q.1).val))))
    (q : S2 × unitInterval) :
    let p : connectingCylinderDomain := ⟨(q.1,q.2.val), mem_univ _, by
      constructor <;> linarith [q.2.property.1,q.2.property.2]⟩
    (H ∘ connectingCylinderOpen c d a) =ᶠ[𝓝 p] (fun r => T r.val) := by
  let p : connectingCylinderDomain := ⟨(q.1,q.2.val), mem_univ _, by
      constructor <;> linarith [q.2.property.1,q.2.property.2]⟩
  have hslab (r : connectingCylinderDomain) (hr : r.val.2 ∈ Icc (0 : ℝ) 1) :
      H (connectingCylinderOpen c d a r) = T r.val := hT (r.val.1,⟨r.val.2,hr⟩)
  by_cases hz : q.2.val = 0
  · have ht : Tendsto (Subtype.val : connectingCylinderDomain → S2 × ℝ) (𝓝 p) (𝓝 (q.1,0)) := by
      simpa only [p,hz] using continuous_subtype_val.tendsto p
    have hn : ∀ᶠ r : connectingCylinderDomain in 𝓝 p, r.val.2 < 1 :=
      (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const).mem_nhds (by
        change q.2.val < 1
        rw [hz]
        norm_num)
    filter_upwards [(hzero q.1).comp_tendsto ht,hn] with r hr hrt
    change H (connectingCylinderOpen c d a r) = T r.val
    by_cases hpos : 0 ≤ r.val.2
    · exact hslab r ⟨hpos,hrt.le⟩
    · obtain ⟨x,hx,hxr⟩ := connectingCylinderOpen_left c d a r (le_of_not_ge hpos)
      rw [hx,hL,hxr]
      exact hr.symm
  · by_cases ho : q.2.val = 1
    · have ht : Tendsto (Subtype.val : connectingCylinderDomain → S2 × ℝ) (𝓝 p) (𝓝 (q.1,1)) := by
        simpa only [p,ho] using continuous_subtype_val.tendsto p
      have hn : ∀ᶠ r : connectingCylinderDomain in 𝓝 p, 0 < r.val.2 :=
        (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)).mem_nhds (by
          change 0 < q.2.val
          rw [ho]
          norm_num)
      filter_upwards [(hone q.1).comp_tendsto ht,hn] with r hr hrt
      change H (connectingCylinderOpen c d a r) = T r.val
      by_cases hpos : r.val.2 ≤ 1
      · exact hslab r ⟨hrt.le,hpos⟩
      · obtain ⟨x,hx,hxr⟩ := connectingCylinderOpen_right c d a r (le_of_not_ge hpos)
        rw [hx,hR,hxr]
        exact hr.symm
    · have hn : ∀ᶠ r : connectingCylinderDomain in 𝓝 p, r.val.2 ∈ Ioo (0 : ℝ) 1 :=
        (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)).mem_nhds
          ⟨lt_of_le_of_ne q.2.property.1 (Ne.symm hz),lt_of_le_of_ne q.2.property.2 ho⟩
      filter_upwards [hn] with r hr
      exact hslab r ⟨hr.1.le,hr.2.le⟩

private theorem isLocalDiffeomorphAt_cylinder_of_germs
    (H : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier → P)
    (f₀ : M.Carrier → P) (f₁ : N.Carrier → P)
    (T : PartialDiffeomorph CI I (S2 × ℝ) P ∞)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hT : ∀ q : S2 × unitInterval, H (connectingCylinder c d a q) = T (q.1,q.2.val))
    (hL : ∀ x, H (outerLeft c d a x) = f₀ x.val.val)
    (hR : ∀ x, H (outerRight c d a x) = f₁ x.val.val)
    (hzero : ∀ z : S2, (T : S2 × ℝ → P) =ᶠ[𝓝 (z,0)]
      (fun q => f₀ (c.chart ((5 / 4 - q.2 / 2) • q.1.val))))
    (hone : ∀ z : S2, (T : S2 × ℝ → P) =ᶠ[𝓝 (z,1)]
      (fun q => f₁ (d.chart ((3 / 4 + q.2 / 2) • (a.val q.1).val))))
    (q : S2 × unitInterval) :
    IsLocalDiffeomorphAt (𝓡 3) I ∞ H (connectingCylinder c d a q) := by
  let p : connectingCylinderDomain := ⟨(q.1,q.2.val), mem_univ _, by
      constructor <;> linarith [q.2.property.1,q.2.property.2]⟩
  have hloc : IsLocalDiffeomorphAt CI I ∞ (fun r : connectingCylinderDomain => T r.val) p :=
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val connectingCylinderDomain p).comp I P
      (T.isLocalDiffeomorphAt _ _ ∞ (hTs ⟨mem_univ _,q.2.property⟩))
  have hcomp : IsLocalDiffeomorphAt CI I ∞ (H ∘ connectingCylinderOpen c d a) p :=
    DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
      (connectingCylinderOpen_local_equation c d a H f₀ f₁ T hT hL hR hzero hone q) hloc
  have hh := DifferentialGeometry.isLocalDiffeomorphAt_of_comp hcomp
    (isLocalDiffeomorph_connectingCylinderOpen c d a p)
  simpa only [p, connectingCylinderOpen_restrict] using hh

theorem exists_diffeomorph_of_outer_caps_cylinder_collar_equations
    [T2Space P]
    (F₀ : PartialDiffeomorph (𝓡 3) I M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) I N.Carrier P ∞)
    (T : PartialDiffeomorph CI I (S2 × ℝ) P ∞)
    (hF₀ : ∀ x : outerPunctured c, x.val.val ∈ F₀.source)
    (hF₁ : ∀ x : outerPunctured d, x.val.val ∈ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (range (fun x : outerPunctured c => F₀ x.val.val))
      (range (fun x : outerPunctured d => F₁ x.val.val)))
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = F₀ x.val.val → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = F₁ x.val.val → q.2 = 1 ∧ outerRightBoundary d a q.1 = x)
    (hcover : range (fun q : S2 × unitInterval => T (q.1,q.2.val)) ∪
      (range (fun x : outerPunctured c => F₀ x.val.val) ∪
        range (fun x : outerPunctured d => F₁ x.val.val)) = univ)
    (hzero : ∀ z : S2, (T : S2 × ℝ → P) =ᶠ[𝓝 (z,0)]
      (fun q => F₀ (c.chart ((5 / 4 - q.2 / 2) • q.1.val))))
    (hone : ∀ z : S2, (T : S2 × ℝ → P) =ᶠ[𝓝 (z,1)]
      (fun q => F₁ (d.chart ((3 / 4 + q.2 / 2) • (a.val q.1).val)))) :
    ∃ D : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, I⟯ P,
      (∀ q, D (connectingCylinder c d a q) = T (q.1,q.2.val)) ∧
      (∀ x, D (outerLeft c d a x) = F₀ x.val.val) ∧
      (∀ x, D (outerRight c d a x) = F₁ x.val.val) ∧
      (∀ q : S2 × unitInterval, D.symm (T (q.1,q.2.val)) = connectingCylinder c d a q) ∧
      (∀ x : outerPunctured c, D.symm (F₀ x.val.val) = outerLeft c d a x) ∧
      ∀ x : outerPunctured d, D.symm (F₁ x.val.val) = outerRight c d a x := by
  let f₀ : C(outerPunctured c, P) := ⟨fun x => F₀ x.val.val,
    continuousOn_univ.mp (F₀.contMDiffOn_toFun.continuousOn.comp
      (continuous_subtype_val.comp continuous_subtype_val).continuousOn (fun x _ => hF₀ x))⟩
  let f₁ : C(outerPunctured d, P) := ⟨fun x => F₁ x.val.val,
    continuousOn_univ.mp (F₁.contMDiffOn_toFun.continuousOn.comp
      (continuous_subtype_val.comp continuous_subtype_val).continuousOn (fun x _ => hF₁ x))⟩
  let t : C(S2 × unitInterval, P) := ⟨fun q => T (q.1,q.2.val),
    continuousOn_univ.mp (T.contMDiffOn_toFun.continuousOn.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun q _ => hTs ⟨mem_univ _,q.2.property⟩))⟩
  let : CompactSpace (outerPunctured c) :=
    isCompact_iff_compactSpace.mp (isClosed_outerPunctured c).isCompact
  let : CompactSpace (outerPunctured d) :=
    isCompact_iff_compactSpace.mp (isClosed_outerPunctured d).isCompact
  have hf₀ : _root_.Topology.IsClosedEmbedding f₀ := f₀.continuous.isClosedEmbedding (by
    intro x y h
    exact Subtype.ext (Subtype.ext (F₀.injOn (hF₀ x) (hF₀ y) h)))
  have hf₁ : _root_.Topology.IsClosedEmbedding f₁ := f₁.continuous.isClosedEmbedding (by
    intro x y h
    exact Subtype.ext (Subtype.ext (F₁.injOn (hF₁ x) (hF₁ y) h)))
  have ht : _root_.Topology.IsClosedEmbedding t := t.continuous.isClosedEmbedding (by
    intro x y h
    have he := T.injOn (hTs ⟨mem_univ _,x.2.property⟩) (hTs ⟨mem_univ _,y.2.property⟩) h
    exact Prod.ext (congrArg (fun q : S2 × ℝ => q.1) he) (Subtype.ext (congrArg (fun q : S2 × ℝ => q.2) he)))
  have hz (z : S2) : t (z,0) = f₀ (outerLeftBoundary c z) := by
    have hh := (hzero z).eq_of_nhds
    change T (z,0) = F₀ (c.chart ((5 / 4 : ℝ) • z.val))
    simpa only [sub_zero,zero_div] using hh
  have ho (z : S2) : t (z,1) = f₁ (outerRightBoundary d a z) := by
    have hh := (hone z).eq_of_nhds
    convert hh using 1 <;> norm_num [t,f₁,outerRightBoundary,outerLeftBoundary,BallChart.radialMap]
  obtain ⟨H,hHT,hHL,hHR,_,_,_⟩ :=
    exists_homeomorph_of_outer_caps_cylinder_cover c d a f₀ f₁ t hf₀ hf₁ ht hdisj hz ho
      hcross₀ hcross₁ hcover
  have hloc : IsLocalDiffeomorph (𝓡 3) I ∞ H := by
    intro p
    have hmem : p ∈ range (outerLeft c d a) ∪ range (outerRight c d a) ∪
        range (connectingCylinder c d a) := by
      rw [outer_caps_connectingCylinder_cover]
      exact mem_univ _
    rcases hmem with (⟨x,rfl⟩ | ⟨x,rfl⟩) | ⟨q,rfl⟩
    · by_cases hx : x ∈ range (outerLeftBoundary c)
      · obtain ⟨z,rfl⟩ := hx
        have he := (connectingCylinder_eq_outerLeft_iff c d a (z,0) (outerLeftBoundary c z)).mpr ⟨rfl,rfl⟩
        rw [← he]
        exact isLocalDiffeomorphAt_cylinder_of_germs c d a H F₀ F₁ T hTs hHT hHL hHR hzero hone _
      · exact isLocalDiffeomorphAt_outerLeft_of_not_mem_boundary c d a H F₀ hHL x hx
          (F₀.isLocalDiffeomorphAt _ _ ∞ (hF₀ x))
    · by_cases hx : x ∈ range (outerRightBoundary d a)
      · obtain ⟨z,rfl⟩ := hx
        have he := (connectingCylinder_eq_outerRight_iff c d a (z,1) (outerRightBoundary d a z)).mpr ⟨rfl,rfl⟩
        rw [← he]
        exact isLocalDiffeomorphAt_cylinder_of_germs c d a H F₀ F₁ T hTs hHT hHL hHR hzero hone _
      · exact isLocalDiffeomorphAt_outerRight_of_not_mem_boundary c d a H F₁ hHR x hx
          (F₁.isLocalDiffeomorphAt _ _ ∞ (hF₁ x))
    · exact isLocalDiffeomorphAt_cylinder_of_germs c d a H F₀ F₁ T hTs hHT hHL hHR hzero hone q
  let D := hloc.diffeomorphOfBijective H.bijective
  refine ⟨D,hHT,hHL,hHR,?_,?_,?_⟩
  · intro q
    exact D.symm_apply_eq.mpr (hHT q).symm
  · intro x
    exact D.symm_apply_eq.mpr (hHL x).symm
  · intro x
    exact D.symm_apply_eq.mpr (hHR x).symm

private theorem exists_outerPunctured_of_not_mem_ball_image (x : M.Carrier)
    (hx : x ∉ c.chart '' ball (0 : E3) (5 / 4)) :
    ∃ y : outerPunctured c, y.val.val = x := by
  refine ⟨⟨⟨x, ?_⟩, hx⟩, rfl⟩
  exact fun h => hx ((image_mono (ball_subset_ball (by norm_num))) h)

private theorem exists_outer_caps_cylinder_germ_matching
    (F₀ : PartialDiffeomorph (𝓡 3) I M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) I N.Carrier P ∞)
    (T : PartialDiffeomorph CI I (S2 × ℝ) P ∞)
    (hF₀ : ∀ x : outerPunctured c, x.val.val ∈ F₀.source)
    (hF₁ : ∀ x : outerPunctured d, x.val.val ∈ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hzero : ∀ z : S2, T (z,0) = F₀ (outerLeftBoundary c z).val.val)
    (hone : ∀ z : S2, T (z,1) = F₁ (outerRightBoundary d a z).val.val)
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = F₀ x.val.val → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = F₁ x.val.val → q.2 = 1 ∧ outerRightBoundary d a q.1 = x) :
    ∃ G : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ),
      G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : S2, G (z,0) = (z,0)) ∧ (∀ z : S2, G (z,1) = (z,1)) ∧
      (∀ z : S2, (fun q => T (G q)) =ᶠ[𝓝 (z,0)]
        (fun q => F₀ (c.chart ((5 / 4 - q.2 / 2) • q.1.val)))) ∧
      ∀ z : S2, (fun q => T (G q)) =ᶠ[𝓝 (z,1)]
        (fun q => F₁ (d.chart ((3 / 4 + q.2 / 2) • (a.val q.1).val))) := by
  have hF₀' : (c.chart '' ball (0 : E3) (5 / 4))ᶜ ⊆ F₀.source := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_outerPunctured_of_not_mem_ball_image c x hx
    exact hF₀ y
  have hF₁' : (d.chart '' ball (0 : E3) (5 / 4))ᶜ ⊆ F₁.source := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_outerPunctured_of_not_mem_ball_image d x hx
    exact hF₁ y
  obtain ⟨P₀,hP₀,hP₀eq,hP₀one,hP₀im⟩ :=
    BallChart.exists_outer_ball_complement_radial_collar c.toBallChart F₀ hF₀'
  obtain ⟨R₁,hR₁,hR₁eq,hR₁one,hR₁im⟩ :=
    BallChart.exists_outer_ball_complement_radial_collar d.toBallChart F₁ hF₁'
  let A := a.val.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let P₁ := A.toPartialDiffeomorph.trans R₁
  have hP₁ : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P₁.source := by
    intro q hq
    exact ⟨mem_univ _,hR₁ ⟨mem_univ _,hq.2⟩⟩
  have hP₁eq (q : S2 × ℝ) :
      P₁ q = F₁ (d.chart ((7 / 4 - q.2 / 2) • (a.val q.1).val)) := by
    exact hR₁eq (A q)
  have hP₁one (z : S2) : P₁ (z,1) = F₁ (d.chart ((5 / 4 : ℝ) • (a.val z).val)) :=
    hR₁one (a.val z)
  have hzero' (z : S2) : T (z,0) = P₀ (z,1) := by
    rw [hP₀one]
    exact hzero z
  have hone' (z : S2) : T (z,1) = P₁ (z,1) := by
    rw [hP₁one]
    exact hone z
  have hmeet₀ : P₀ '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P₀ '' (univ ×ˢ ({0} : Set ℝ)) ∪ P₀ '' (univ ×ˢ ({1} : Set ℝ)) := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := hP₀im hy.1
    obtain ⟨v,hv,rfl⟩ := exists_outerPunctured_of_not_mem_ball_image c x hx
    obtain ⟨q,hq,hqy⟩ := hy.2
    have hcross := hcross₀ (q.1,⟨q.2,hq.2⟩) v (hqy.trans hxy.symm)
    have hqt : q.2 = 0 := congrArg Subtype.val hcross.1
    apply Or.inr
    refine ⟨(q.1,1),⟨mem_univ _,rfl⟩,?_⟩
    rw [← hzero']
    have he : q = (q.1,0) := Prod.ext rfl hqt
    rw [← he]
    exact hqy
  have hmeet₁ : P₁ '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ T '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P₁ '' (univ ×ˢ ({0} : Set ℝ)) ∪ P₁ '' (univ ×ˢ ({1} : Set ℝ)) := by
    intro y hy
    obtain ⟨p,hp,hpy⟩ := hy.1
    have hRmem : R₁ (A p) ∈ R₁ '' (univ ×ˢ Icc (0 : ℝ) 1) :=
      mem_image_of_mem R₁ ⟨mem_univ _,hp.2⟩
    obtain ⟨x,hx,hxR⟩ := hR₁im hRmem
    obtain ⟨v,hv,rfl⟩ := exists_outerPunctured_of_not_mem_ball_image d x hx
    obtain ⟨q,hq,hqy⟩ := hy.2
    have hxy : F₁ v.val.val = y := hxR.trans hpy
    have hcross := hcross₁ (q.1,⟨q.2,hq.2⟩) v (hqy.trans hxy.symm)
    have hqt : q.2 = 1 := congrArg Subtype.val hcross.1
    apply Or.inr
    refine ⟨(q.1,1),⟨mem_univ _,rfl⟩,?_⟩
    rw [← hone']
    have he : q = (q.1,1) := Prod.ext rfl hqt
    rw [← he]
    exact hqy
  obtain ⟨G,hGb,hG0,hG1,hGlo,hGhi⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_two_ended_slab_collar_matching
      P₀ P₁ T hP₀ hP₁ hTs hzero' hone' hmeet₀ hmeet₁
  refine ⟨G,hGb,hG0,hG1,?_,?_⟩
  · intro z
    filter_upwards [hGlo z] with q hq
    rw [hP₀eq] at hq
    change T (G q) = F₀ (c.chart ((7 / 4 - (1 + q.2) / 2) • q.1.val)) at hq
    rw [show (7 / 4 : ℝ) - (1 + q.2) / 2 = 5 / 4 - q.2 / 2 by ring] at hq
    exact hq
  · intro z
    filter_upwards [hGhi z] with q hq
    rw [hP₁eq] at hq
    change T (G q) = F₁ (d.chart ((7 / 4 - (2 - q.2) / 2) • (a.val q.1).val)) at hq
    rw [show (7 / 4 : ℝ) - (2 - q.2) / 2 = 3 / 4 + q.2 / 2 by ring] at hq
    exact hq


omit [TopologicalSpace P] in
private theorem cylinder_cross_reparametrization
    (G : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ))
    (hGb : G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1)
    (hG0 : ∀ z : S2, G (z,0) = (z,0))
    (hG1 : ∀ z : S2, G (z,1) = (z,1))
    (T : S2 × ℝ → P)
    (f₀ : outerPunctured c → P) (f₁ : outerPunctured d → P)
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = f₀ x → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = f₁ x → q.2 = 1 ∧ outerRightBoundary d a q.1 = x) :
    (∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (G (q.1,q.2.val)) = f₀ x → q.2 = 0 ∧ outerLeftBoundary c q.1 = x) ∧
    (∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (G (q.1,q.2.val)) = f₁ x → q.2 = 1 ∧ outerRightBoundary d a q.1 = x) := by
  have hmem (q : S2 × unitInterval) : G (q.1,q.2.val) ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
    rw [← hGb]
    exact mem_image_of_mem G ⟨mem_univ _,q.2.property⟩
  constructor
  · intro q x h
    obtain ⟨ht,hx⟩ := hcross₀ ((G (q.1,q.2.val)).1,
      ⟨(G (q.1,q.2.val)).2,(hmem q).2⟩) x h
    have he : G (q.1,q.2.val) = G ((G (q.1,q.2.val)).1,0) := by
      rw [hG0]
      exact Prod.ext rfl (congrArg Subtype.val ht)
    have hg := G.injective he
    have hz : q.2 = 0 := Subtype.ext (congrArg Prod.snd hg)
    exact ⟨hz,(congrArg (outerLeftBoundary c) (congrArg Prod.fst hg)).trans hx⟩
  · intro q x h
    obtain ⟨ht,hx⟩ := hcross₁ ((G (q.1,q.2.val)).1,
      ⟨(G (q.1,q.2.val)).2,(hmem q).2⟩) x h
    have he : G (q.1,q.2.val) = G ((G (q.1,q.2.val)).1,1) := by
      rw [hG1]
      exact Prod.ext rfl (congrArg Subtype.val ht)
    have hg := G.injective he
    have hz : q.2 = 1 := Subtype.ext (congrArg Prod.snd hg)
    exact ⟨hz,(congrArg (outerRightBoundary d a) (congrArg Prod.fst hg)).trans hx⟩

omit [TopologicalSpace P] in
private theorem range_cylinder_reparametrization
    (G : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ))
    (hGb : G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1)
    (T : S2 × ℝ → P) :
    range (fun q : S2 × unitInterval => T (G (q.1,q.2.val))) =
      range (fun q : S2 × unitInterval => T (q.1,q.2.val)) := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    have hmem : G (q.1,q.2.val) ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
      rw [← hGb]
      exact mem_image_of_mem G ⟨mem_univ _,q.2.property⟩
    exact ⟨((G (q.1,q.2.val)).1,⟨(G (q.1,q.2.val)).2,hmem.2⟩),rfl⟩
  · rintro ⟨q,rfl⟩
    have hmem : (q.1,q.2.val) ∈ G '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [hGb]
      exact ⟨mem_univ _,q.2.property⟩
    obtain ⟨r,hr,he⟩ := hmem
    exact ⟨(r.1,⟨r.2,hr.2⟩),congrArg T he⟩

private theorem exists_diffeomorph_of_reparametrized_cylinder
    [T2Space P]
    (F₀ : PartialDiffeomorph (𝓡 3) I M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) I N.Carrier P ∞)
    (T : PartialDiffeomorph CI I (S2 × ℝ) P ∞)
    (hF₀ : ∀ x : outerPunctured c, x.val.val ∈ F₀.source)
    (hF₁ : ∀ x : outerPunctured d, x.val.val ∈ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (range (fun x : outerPunctured c => F₀ x.val.val))
      (range (fun x : outerPunctured d => F₁ x.val.val)))
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = F₀ x.val.val → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = F₁ x.val.val → q.2 = 1 ∧ outerRightBoundary d a q.1 = x)
    (hcover : range (fun q : S2 × unitInterval => T (q.1,q.2.val)) ∪
      (range (fun x : outerPunctured c => F₀ x.val.val) ∪
        range (fun x : outerPunctured d => F₁ x.val.val)) = univ)
    (G : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ))
    (hGb : G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1)
    (hG0 : ∀ z : S2, G (z,0) = (z,0))
    (hG1 : ∀ z : S2, G (z,1) = (z,1))
    (hzero : ∀ z : S2, (fun q => T (G q)) =ᶠ[𝓝 (z,0)]
      (fun q => F₀ (c.chart ((5 / 4 - q.2 / 2) • q.1.val))))
    (hone : ∀ z : S2, (fun q => T (G q)) =ᶠ[𝓝 (z,1)]
      (fun q => F₁ (d.chart ((3 / 4 + q.2 / 2) • (a.val q.1).val)))) :
    ∃ D : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, I⟯ P,
      (∀ q, D (connectingCylinder c d a q) = T (G (q.1,q.2.val))) ∧
      (∀ x, D (outerLeft c d a x) = F₀ x.val.val) ∧
      (∀ x, D (outerRight c d a x) = F₁ x.val.val) ∧
      (∀ q : S2 × unitInterval, D.symm (T (G (q.1,q.2.val))) = connectingCylinder c d a q) ∧
      (∀ x : outerPunctured c, D.symm (F₀ x.val.val) = outerLeft c d a x) ∧
      ∀ x : outerPunctured d, D.symm (F₁ x.val.val) = outerRight c d a x := by
  let t := G.toPartialDiffeomorph.trans T
  have ht : univ ×ˢ Icc (0 : ℝ) 1 ⊆ t.source := by
    intro q hq
    refine ⟨mem_univ _,hTs ?_⟩
    change G q ∈ univ ×ˢ Icc (0 : ℝ) 1
    rw [← hGb]
    exact mem_image_of_mem G hq
  obtain ⟨hc₀,hc₁⟩ := cylinder_cross_reparametrization c d a G hGb hG0 hG1 T
    (fun x : outerPunctured c => F₀ x.val.val) (fun x : outerPunctured d => F₁ x.val.val)
    hcross₀ hcross₁
  have hcov : range (fun q : S2 × unitInterval => t (q.1,q.2.val)) ∪
      (range (fun x : outerPunctured c => F₀ x.val.val) ∪
        range (fun x : outerPunctured d => F₁ x.val.val)) = univ := by
    change range (fun q : S2 × unitInterval => T (G (q.1,q.2.val))) ∪ _ = _
    rw [range_cylinder_reparametrization G hGb T,hcover]
  exact exists_diffeomorph_of_outer_caps_cylinder_collar_equations c d a F₀ F₁ t hF₀ hF₁ ht
    hdisj hc₀ hc₁ hcov hzero hone

theorem exists_diffeomorph_of_outer_caps_cylinder_cover
    [T2Space P]
    (F₀ : PartialDiffeomorph (𝓡 3) I M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) I N.Carrier P ∞)
    (T : PartialDiffeomorph CI I (S2 × ℝ) P ∞)
    (hF₀ : ∀ x : outerPunctured c, x.val.val ∈ F₀.source)
    (hF₁ : ∀ x : outerPunctured d, x.val.val ∈ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (range (fun x : outerPunctured c => F₀ x.val.val))
      (range (fun x : outerPunctured d => F₁ x.val.val)))
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = F₀ x.val.val → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = F₁ x.val.val → q.2 = 1 ∧ outerRightBoundary d a q.1 = x)
    (hcover : range (fun q : S2 × unitInterval => T (q.1,q.2.val)) ∪
      (range (fun x : outerPunctured c => F₀ x.val.val) ∪
        range (fun x : outerPunctured d => F₁ x.val.val)) = univ)
    (hzero : ∀ z : S2, T (z,0) = F₀ (outerLeftBoundary c z).val.val)
    (hone : ∀ z : S2, T (z,1) = F₁ (outerRightBoundary d a z).val.val) :
    ∃ G : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ),
      G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : S2, G (z,0) = (z,0)) ∧ (∀ z : S2, G (z,1) = (z,1)) ∧
    ∃ D : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, I⟯ P,
      (∀ q, D (connectingCylinder c d a q) = T (G (q.1,q.2.val))) ∧
      (∀ x, D (outerLeft c d a x) = F₀ x.val.val) ∧
      (∀ x, D (outerRight c d a x) = F₁ x.val.val) ∧
      (∀ q : S2 × unitInterval, D.symm (T (G (q.1,q.2.val))) = connectingCylinder c d a q) ∧
      (∀ x : outerPunctured c, D.symm (F₀ x.val.val) = outerLeft c d a x) ∧
      ∀ x : outerPunctured d, D.symm (F₁ x.val.val) = outerRight c d a x := by
  obtain ⟨G,hGb,hG0,hG1,hGlo,hGhi⟩ :=
    exists_outer_caps_cylinder_germ_matching c d a F₀ F₁ T hF₀ hF₁ hTs hzero hone hcross₀ hcross₁
  exact ⟨G,hGb,hG0,hG1,
    exists_diffeomorph_of_reparametrized_cylinder c d a F₀ F₁ T hF₀ hF₁ hTs
      hdisj hcross₀ hcross₁ hcover G hGb hG0 hG1 hGlo hGhi⟩


end DifferentialGeometry.Topology.ConnectedSumQuotient
