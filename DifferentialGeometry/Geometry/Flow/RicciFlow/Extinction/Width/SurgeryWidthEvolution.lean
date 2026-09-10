import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OrientationDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.CanonicalClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import Mathlib.Topology.Instances.ENNReal.Lemmas
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

noncomputable section

universe u v

open Bundle Manifold Set Filter MeasureTheory CategoryTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDist_le_of_metric_pullback
    {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (f : M → N) (hf : ContMDiff ThreeModel ThreeModel ∞ f)
    (hmetric : ∀ x v w, h.inner (f x)
      (mfderiv ThreeModel ThreeModel f x v) (mfderiv ThreeModel ThreeModel f x w) =
        g.inner x v w) (x y : M) :
    riemannianEDistOf h (f x) (f y) ≤ riemannianEDistOf g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  have hmap : ContMDiff (𝓡∂ 1) ThreeModel 1 (γ.map hf.continuous) := by
    change ContMDiff (𝓡∂ 1) ThreeModel 1 (f ∘ γ)
    exact (hf.of_le (by simp)).comp hγ
  refine iInf_le_of_le (γ.map hf.continuous) (iInf_le_of_le hmap ?_)
  apply le_of_eq
  apply lintegral_congr
  intro t
  have hderiv : mfderiv (𝓡∂ 1) ThreeModel (γ.map hf.continuous) t 1 =
      mfderiv ThreeModel ThreeModel f (γ t) (mfderiv (𝓡∂ 1) ThreeModel γ t 1) := by
    change mfderiv (𝓡∂ 1) ThreeModel (f ∘ γ) t 1 = _
    exact mfderiv_comp_apply t ((hf.mdifferentiable (by simp)) (γ t))
      ((hγ.mdifferentiable one_ne_zero) t) 1
  change ENNReal.ofReal (Real.sqrt (h.inner (f (γ t))
    (mfderiv (𝓡∂ 1) ThreeModel (γ.map hf.continuous) t 1) (mfderiv (𝓡∂ 1) ThreeModel (γ.map hf.continuous) t 1))) = _
  rw [hderiv, hmetric]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDist_eq_of_diffeomorph_metric_pullback
    {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (e : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N)
    (hmetric : ∀ x v w, h.inner (e x)
      (mfderiv ThreeModel ThreeModel e x v) (mfderiv ThreeModel ThreeModel e x w) =
        g.inner x v w) (x y : M) :
    riemannianEDistOf h (e x) (e y) = riemannianEDistOf g x y := by
  have hsymm : ∀ z v w, g.inner (e.symm z)
      (mfderiv ThreeModel ThreeModel e.symm z v)
      (mfderiv ThreeModel ThreeModel e.symm z w) = h.inner z v w := by
    intro z v w
    have hd := (e.toOpenPartialHomeomorph_mdifferentiable (by simp)).comp_symm_deriv
      (x := z) (by trivial)
    have hdv := congrArg (fun L => L v) hd
    have hdw := congrArg (fun L => L w) hd
    change mfderiv ThreeModel ThreeModel e (e.symm z)
      (mfderiv ThreeModel ThreeModel e.symm z v) = v at hdv
    change mfderiv ThreeModel ThreeModel e (e.symm z)
      (mfderiv ThreeModel ThreeModel e.symm z w) = w at hdw
    have hh := hmetric (e.symm z)
      (mfderiv ThreeModel ThreeModel e.symm z v)
      (mfderiv ThreeModel ThreeModel e.symm z w)
    calc
      g.inner (e.symm z) (mfderiv ThreeModel ThreeModel e.symm z v)
          (mfderiv ThreeModel ThreeModel e.symm z w) = h.inner (e (e.symm z)) v w := by
        simpa only [hdv, hdw] using hh.symm
      _ = h.inner z v w := congrArg
        (fun q => (h.inner q : ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ) v w)
        (e.apply_symm_apply z)
  apply le_antisymm
  · exact riemannianEDist_le_of_metric_pullback g h e e.contMDiff hmetric x y
  · simpa only [e.symm_apply_apply] using
      riemannianEDist_le_of_metric_pullback h g e.symm e.symm.contMDiff hsymm (e x) (e y)

private theorem integralHomologyMap_comp_apply {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) (a : IntegralHomology X n) :
    integralHomologyMap n g (integralHomologyMap n f a) =
      integralHomologyMap n (g.comp f) a := by
  have h := (integralHomologyFunctor n).map_comp (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg (fun F => F a) h.symm

private theorem integralHomologyMap_id_apply {X : Type u} [TopologicalSpace X]
    (n : ℕ) (a : IntegralHomology X n) :
    integralHomologyMap n (ContinuousMap.id X) a = a := by
  have h := (integralHomologyFunctor n).map_id (TopCat.of X)
  exact congrArg (fun F => F a) h

theorem canonicalWidth_eq_of_isometry
    {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]
    (g : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₜ N)
    (he : ∀ x y, riemannianEDistOf h (e x) (e y) = riemannianEDistOf g x y)
    (horient : integralHomologyMap 3 (e : C(M, N)) (fundamentalClass oM) =
      fundamentalClass oN) : canonicalWidth h oN = canonicalWidth g oM := by
  have hcomp : (e.symm : C(N, M)).comp (e : C(M, N)) = ContinuousMap.id M := by
    ext x
    exact e.symm_apply_apply x
  have hinverse : integralHomologyMap 3 (e.symm : C(N, M)) (fundamentalClass oN) =
      fundamentalClass oM := by
    rw [← horient, integralHomologyMap_comp_apply, hcomp, integralHomologyMap_id_apply]
  have hdegree : orientedDegree oM oN (e : C(M, N)) = 1 :=
    (orientedDegree_eq_iff oM oN (e : C(M, N)) 1).mpr (by simpa using horient)
  have hdegreeSymm : orientedDegree oN oM (e.symm : C(N, M)) = 1 :=
    (orientedDegree_eq_iff oN oM (e.symm : C(N, M)) 1).mpr (by simpa using hinverse)
  have hforward := rfs_canonical_width_lipschitz g h oM oN (e : C(M, N)) hdegree 1
    (fun x y => calc
      riemannianEDistOf h ((e : C(M, N)) x) ((e : C(M, N)) y) =
          riemannianEDistOf g x y := he x y
      _ ≤ (1 : ℝ≥0∞) * riemannianEDistOf g x y := by simp only [one_mul, le_refl])
  have hbackward := rfs_canonical_width_lipschitz h g oN oM (e.symm : C(N, M)) hdegreeSymm 1
    (fun x y => calc
      riemannianEDistOf g ((e.symm : C(N, M)) x) ((e.symm : C(N, M)) y) =
          riemannianEDistOf h x y := by
        convert! (he (e.symm x) (e.symm y)).symm using 1;
          simp only [e.apply_symm_apply]
      _ ≤ (1 : ℝ≥0∞) * riemannianEDistOf h x y := by simp only [one_mul, le_refl])
  exact le_antisymm (by simpa using hforward) (by simpa using hbackward)

def componentDiffeomorph (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    (c : ConnectedComponents P.Carrier) :
    (P.component c).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ P.Carrier where
  toFun := Subtype.val
  invFun x := ⟨x, Subsingleton.elim _ _⟩
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    intro x
    exact codRestr_contMDiffAt (V := P.componentOpen c)
      (f := id) (fun _ => Subsingleton.elim _ _) contMDiffAt_id


theorem componentDiffeomorph_metric (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    (g : P.Metric) (c : ConnectedComponents P.Carrier)
    (x : (P.component c).Carrier) (v w : TangentSpace ThreeModel x) :
    g.inner (componentDiffeomorph P c x)
      (mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x v)
      (mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x w) =
      (P.componentMetric g c).inner x v w := by
  have hv := mfderiv_subtype_val_apply (I := ThreeModel) (P.componentOpen c) x v
  have hw := mfderiv_subtype_val_apply (I := ThreeModel) (P.componentOpen c) x w
  exact congrArg₂ (fun a b : ThreeSpace =>
    (g.inner x.1 : ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ) a b) hv hw


theorem componentDiffeomorph_positive (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    (c : ConnectedComponents P.Carrier) :
    PreservesTangentOrientation (P.component c).orientation P.orientation
      (componentDiffeomorph P c) := by
  refine ⟨(componentDiffeomorph P c).contMDiff, ?_⟩
  intro x
  have hd : mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x =
      ContinuousLinearMap.id ℝ ThreeSpace :=
    mfderiv_subtype_val (P.componentOpen c) x
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x) := by
    rw [hd]
    exact Function.bijective_id
  refine ⟨hbij, ?_⟩
  unfold PreservesTangentOrientationAt
  have he : LinearEquiv.ofBijective
      (mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x).toLinearMap hbij =
      LinearEquiv.refl ℝ ThreeSpace := by
    ext v
    change mfderiv ThreeModel ThreeModel (componentDiffeomorph P c) x v = v
    rw [hd]
    rfl
  have hm := congrArg (fun e : ThreeSpace ≃ₗ[ℝ] ThreeSpace =>
    Orientation.map (Fin 3) e (P.orientation.orientation x.1)) he
  have hr := congrArg (fun e : Orientation ℝ ThreeSpace (Fin 3) ≃
      Orientation ℝ ThreeSpace (Fin 3) => e (P.orientation.orientation x.1))
    (Orientation.map_refl (R := ℝ) (M := ThreeSpace) (Fin 3))
  exact hm.trans hr

private theorem le_liminf_of_eventually_le_mul {a : ℝ≥0∞} {t : ℝ}
    {v : ℝ → ℝ≥0∞} {ell : ℝ → ℝ}
    (hell : Tendsto ell (𝓝[<] t) (𝓝 1))
    (h : ∀ᶠ s in 𝓝[<] t, a ≤ ENNReal.ofReal ((ell s) ^ 2) * v s) :
    a ≤ liminf v (𝓝[<] t) := by
  let m : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((ell s) ^ 2)
  have hm : Tendsto m (𝓝[<] t) (𝓝 1) := by
    simpa only [m, Function.comp_def, one_pow, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hell.pow 2)
  have hsup : limsup m (𝓝[<] t) = 1 := hm.limsup_eq
  have hprod : liminf (m * v) (𝓝[<] t) ≤ liminf v (𝓝[<] t) := by
    have hmul := ENNReal.liminf_mul_le (u := m) (v := v) (f := 𝓝[<] t)
      (Or.inl (by rw [hsup]; exact one_ne_zero))
      (Or.inl (by rw [hsup]; exact ENNReal.one_ne_top))
    simpa only [hsup, one_mul] using hmul
  exact (Filter.le_liminf_of_le (by isBoundedDefault) h).trans hprod

section FixedCarriers

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N]

theorem rfs_comparison_width_transition
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (hcomposition : ∀ (g : SmoothRiemannianMetric ThreeModel M)
      (h : SmoothRiemannianMetric ThreeModel N) (f : C(M, N)) (L : ℝ≥0),
      FreeHomotopyClass.map (contractibleLoopPostcompose f)
        (positiveFreeContractibleClass oM) = positiveFreeContractibleClass oN →
      (∀ x y, riemannianEDistOf h (f x) (f y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf g x y) →
      canonicalWidth h oN ≤ (L : ℝ) ^ 2 * canonicalWidth g oM)
    (g : ℝ → SmoothRiemannianMetric ThreeModel M)
    (h : SmoothRiemannianMetric ThreeModel N) (f : C(M, N))
    (hclass : FreeHomotopyClass.map (contractibleLoopPostcompose f)
      (positiveFreeContractibleClass oM) = positiveFreeContractibleClass oN)
    {t : ℝ} (ell : ℝ → ℝ) (hell : Tendsto ell (𝓝[<] t) (𝓝 1))
    (hlip : ∀ᶠ s in 𝓝[<] t, 0 ≤ ell s ∧
      ∀ x y, riemannianEDistOf h (f x) (f y) ≤
        ENNReal.ofReal (ell s) * riemannianEDistOf (g s) x y) :
    ENNReal.ofReal (canonicalWidth h oN) ≤
      liminf (fun s => ENNReal.ofReal (canonicalWidth (g s) oM)) (𝓝[<] t) := by
  apply le_liminf_of_eventually_le_mul hell
  filter_upwards [hlip] with s hs
  let L : ℝ≥0 := ⟨ell s, hs.1⟩
  have hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (g s) x y := by
    have hcast : (L : ℝ≥0∞) = ENNReal.ofReal (ell s) := ENNReal.coe_nnreal_eq L
    intro x y
    calc
      riemannianEDistOf h (f x) (f y) ≤
          ENNReal.ofReal (ell s) * riemannianEDistOf (g s) x y := hs.2 x y
      _ = (L : ℝ≥0∞) * riemannianEDistOf (g s) x y :=
        congrArg (fun z : ℝ≥0∞ => z * riemannianEDistOf (g s) x y) hcast.symm
  have hw := hcomposition (g s) h f L hclass hf
  have he := ENNReal.ofReal_le_ofReal hw
  change ENNReal.ofReal (canonicalWidth h oN) ≤
    ENNReal.ofReal ((ell s) ^ 2 * canonicalWidth (g s) oM) at he
  simpa only [ENNReal.ofReal_mul (sq_nonneg (ell s))] using he

end FixedCarriers

def componentWidth (P : OrientedThreeStage.{u}) (g : P.Metric)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) : ℝ :=
  let := P.component_connected c
  let := hSC
  canonicalWidth (P.componentMetric g c) (P.component c).orientation

theorem componentWidth_nonneg (P : OrientedThreeStage.{u}) (g : P.Metric)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    0 ≤ componentWidth P g c hSC := by
  let := P.component_connected c
  let := hSC
  exact canonicalWidth_nonneg (P.componentMetric g c) (P.component c).orientation

theorem continuousOn_componentWidth_metricFamily (P : OrientedThreeStage.{u})
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → P.Metric)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    ContinuousOn (fun t => componentWidth P (g t) c hSC) D.carrier := by
  let := P.component_connected c
  let := hSC
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := componentWidth P (g t₀) c hSC
  have hA : 0 ≤ A := componentWidth_nonneg P (g t₀) c hSC
  let δ := min (1 / 2 : ℝ) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp
      (show δ ≤ ε / (A + 1) from min_le_right _ _)
    nlinarith
  filter_upwards [eventually_uniform_relative_metric_bound D g hg t₀ hδ] with t ht
  have hrestrict : ∀ q (v : TangentSpace ThreeModel q),
      |(P.componentMetric (g t) c).inner q v v -
        (P.componentMetric (g t₀) c).inner q v v| ≤
      δ * (P.componentMetric (g t₀) c).inner q v v := by
    intro q v
    exact ht q.1 v
  rw [Real.dist_eq]
  exact (classWidth_relative_metric_bound (P.componentMetric (g t₀) c)
    (P.componentMetric (g t) c) hδ.le hδone hrestrict
    (positiveFreeContractibleClass (P.component c).orientation)).trans_lt hδA

theorem rfs_actual_width_jump {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    letI := hSC (G.transition.childParent c)
    ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
      (G.transition.child_simplyConnected c)) ≤
      liminf (fun s => ENNReal.ofReal
        (componentWidth (H.stage i.castSucc) ((H.event i).incoming.flow.base.metric s)
          (G.transition.childParent c) (hSC (G.transition.childParent c))))
        (𝓝[<] (H.time i.succ)) := by
  let := (H.stage i.castSucc).component_connected (G.transition.childParent c)
  let := (H.stage i.succ).component_connected c
  let := hSC (G.transition.childParent c)
  let := G.transition.child_simplyConnected c
  obtain ⟨f, _hsupport, hdegree, s₀, hs₀, ell, hell, hlim, hlip⟩ :=
    G.rfs_child_comparison hSC
  have hdeg : orientedDegree (G.Parent c).orientation (G.Child c).orientation (f c) = 1 := by
    apply (orientedDegree_eq_iff _ _ _ 1).mpr
    simpa only [one_smul] using hdegree c
  have hcomp : ∀ (g : (G.Parent c).Metric) (h : (G.Child c).Metric)
      (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) (L : ℝ≥0),
      FreeHomotopyClass.map (contractibleLoopPostcompose f)
          (positiveFreeContractibleClass (G.Parent c).orientation) =
        positiveFreeContractibleClass (G.Child c).orientation →
      (∀ x y, riemannianEDistOf h (f x) (f y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf g x y) →
      canonicalWidth h (G.Child c).orientation ≤
        (L : ℝ) ^ 2 * canonicalWidth g (G.Parent c).orientation := by
    intro g h f L hclass hf
    have hw := rfs_width_lipschitz g h f L hf
      (positiveFreeContractibleClass (G.Parent c).orientation)
    rw [hclass] at hw
    exact hw
  apply rfs_comparison_width_transition (G.Parent c).orientation (G.Child c).orientation
    hcomp _ _ (f c)
    (positiveFreeContractibleClass_natural _ _ (f c) hdeg) ell hlim
  filter_upwards [Ioo_mem_nhdsLT hs₀.2] with s hs
  exact ⟨le_trans zero_le_one (hell s hs), hlip c s hs⟩

def historyStageAt (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) :
    Fin (H.eventCount + 1) :=
  (Finset.univ.filter (fun j => H.time j ≤ t.1)).max' (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [H.time_zero] using t.2.1)


def historyStageTime (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) :
    Icc (0 : ℝ) H.horizon :=
  ⟨H.time j, by
    constructor
    · rw [← H.time_zero]
      exact H.time_strictMono.monotone (Fin.zero_le j)
    · exact (H.time_strictMono.monotone (Fin.le_last j)).trans H.time_le_horizon⟩

theorem historyStageAt_stageTime (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) : historyStageAt H (historyStageTime H j) = j := by
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    exact H.time_strictMono.le_iff_le.mp (Finset.mem_filter.mp hk).2
  · apply Finset.le_max'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩

def historyStageMetric (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) :
    ℝ → (H.stage j).Metric :=
  Fin.lastCases
    (if h : H.time (Fin.last H.eventCount) < H.horizon then
      (H.finalSlab h).flow.base.metric
    else fun _ => H.initialMetric (Fin.last H.eventCount))
    (fun i => (H.event i).incoming.flow.base.metric) j

def historyWidth (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : Icc (0 : ℝ) H.horizon) : ℝ :=
  let j := historyStageAt H t
  let c := (rfs_finite_ancestor_chain H terminal).component j
  componentWidth (H.stage j) (historyStageMetric H j t.1) c
    (rfs_simply_connected_history H h0 j c)

theorem historyWidth_nonneg (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : Icc (0 : ℝ) H.horizon) : 0 ≤ historyWidth H h0 terminal t := by
  exact componentWidth_nonneg _ _ _ _

section InitialData

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N]

theorem isometry_fundamentalClass_iff_preservesTangentOrientation
    (g : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (e : M ≃ₜ N)
    (he : ∀ x y, riemannianEDistOf h (e x) (e y) = riemannianEDistOf g x y) :
    integralHomologyMap 3 (e : C(M, N)) (fundamentalClass oM) = fundamentalClass oN ↔
      PreservesTangentOrientation oM oN e := by
  sorry

omit [SimplyConnectedSpace M] in
theorem familyMaximum_scale (g : SmoothRiemannianMetric ThreeModel M)
    (Γ : RegularFamily (I := ThreeModel) (Q := M) (Sphere 2)) {c : ℝ} (hc : 0 < c) :
    familyMaximum (scaleMetric c hc g) Γ = c * familyMaximum g Γ := by
  have hpoint (k : Sphere 2) :
      regularLeastArea (scaleMetric c hc g) (Γ k) = c * regularLeastArea g (Γ k) :=
    leastArea_scale g hc (Γ k).1.toContinuousLoop (Γ k).2 ((Γ k).1.isLipschitz g)
  apply le_antisymm
  · exact familyMaximum_le_mul g (scaleMetric c hc g) hc.le Γ (fun k => (hpoint k).le)
  · obtain ⟨k, hk⟩ := familyMaximum_attained g Γ
    rw [hk, ← hpoint k]
    exact regularLeastArea_le_familyMaximum (scaleMetric c hc g) Γ k

theorem initial_regular_width_data (g₀ : SmoothRiemannianMetric ThreeModel M)
    (o : TangentOrientationSection M) :
    ∃ Γ₀ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o),
      0 ≤ canonicalWidth g₀ o ∧ canonicalWidth g₀ o ≤ familyMaximum g₀ Γ₀.1 ∧
      ∀ (lam : ℝ) (hlam : 0 < lam),
        familyMaximum (scaleMetric lam hlam g₀) Γ₀.1 = lam * familyMaximum g₀ Γ₀.1 := by
  obtain ⟨Γ₀⟩ := canonical_regularRepresentative_nonempty o
  exact ⟨Γ₀, canonicalWidth_nonneg g₀ o,
    classWidth_le_familyMaximum g₀ (positiveFreeContractibleClass o) Γ₀,
    fun _ hlam => familyMaximum_scale g₀ Γ₀.1 hlam⟩

end InitialData

theorem historyStageAt_of_mem_incoming (H : ObservedHistory.{u})
    (i : Fin H.eventCount) (t : Icc (0 : ℝ) H.horizon)
    (ht : t.1 ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    historyStageAt H t = i.castSucc := by
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    have hkt : H.time k < H.time i.succ := (Finset.mem_filter.mp hk).2.trans_lt ht.2
    have hki : k < i.succ := H.time_strictMono.lt_iff_lt.mp hkt
    have hcast : i.castSucc.val = i.val := rfl
    have hsucc : i.succ.val = i.val + 1 := rfl
    have hval : k.val < i.succ.val := hki
    change k.val ≤ i.castSucc.val
    omega
  · apply Finset.le_max'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.1⟩

theorem historyStageAt_of_mem_final (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (Fin.last H.eventCount) ≤ t.1) :
    historyStageAt H t = Fin.last H.eventCount := by
  apply le_antisymm (Fin.le_last _)
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩

theorem historyStageMetric_initial (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) :
    historyStageMetric H j (H.time j) = H.initialMetric j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [historyStageMetric, Fin.lastCases_last]
    split_ifs with h
    · exact H.final_initial h
    · rfl
  | cast i =>
    simpa only [historyStageMetric, Fin.lastCases_castSucc] using H.event_initial i

theorem historyWidth_stageTime (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (j : Fin (H.eventCount + 1)) :
    historyWidth H h0 terminal (historyStageTime H j) =
      componentWidth (H.stage j) (H.initialMetric j)
        ((rfs_finite_ancestor_chain H terminal).component j)
        (rfs_simply_connected_history H h0 j _) := by
  let W : Fin (H.eventCount + 1) → ℝ → ℝ := fun k s =>
    componentWidth (H.stage k) (historyStageMetric H k s)
      ((rfs_finite_ancestor_chain H terminal).component k)
      (rfs_simply_connected_history H h0 k _)
  change W (historyStageAt H (historyStageTime H j)) (H.time j) = _
  rw [historyStageAt_stageTime]
  exact congrArg (fun g : (H.stage j).Metric => componentWidth (H.stage j) g
    ((rfs_finite_ancestor_chain H terminal).component j)
    (rfs_simply_connected_history H h0 j _)) (historyStageMetric_initial H j)

theorem historyWidth_incoming (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (i : Fin H.eventCount) (t : Icc (0 : ℝ) H.horizon)
    (ht : t.1 ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    historyWidth H h0 terminal t =
      componentWidth (H.stage i.castSucc) ((H.event i).incoming.flow.base.metric t.1)
        ((rfs_finite_ancestor_chain H terminal).component i.castSucc)
        (rfs_simply_connected_history H h0 i.castSucc _) := by
  let W : Fin (H.eventCount + 1) → ℝ → ℝ := fun k s =>
    componentWidth (H.stage k) (historyStageMetric H k s)
      ((rfs_finite_ancestor_chain H terminal).component k)
      (rfs_simply_connected_history H h0 k _)
  change W (historyStageAt H t) t.1 = _
  rw [historyStageAt_of_mem_incoming H i t ht]
  simp only [W, historyStageMetric, Fin.lastCases_castSucc]

def historyStageDomain (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) : Set ℝ :=
  Fin.lastCases (Icc (H.time (Fin.last H.eventCount)) H.horizon)
    (fun i => Ico (H.time i.castSucc) (H.time i.succ)) j

theorem historyStageAt_mem (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) :
    t.1 ∈ historyStageDomain H (historyStageAt H t) := by
  have hmem : historyStageAt H t ∈ Finset.univ.filter (fun k => H.time k ≤ t.1) := by
    unfold historyStageAt
    exact Finset.max'_mem _ _
  have hstart : H.time (historyStageAt H t) ≤ t.1 := (Finset.mem_filter.mp hmem).2
  generalize hj : historyStageAt H t = j at *
  cases j using Fin.lastCases with
  | last =>
    simp only [historyStageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨hstart, t.2.2⟩
  | cast i =>
    simp only [historyStageDomain, Fin.lastCases_castSucc, Set.mem_Ico]
    refine ⟨hstart, ?_⟩
    by_contra h
    have hmem : i.succ ∈ Finset.univ.filter (fun k => H.time k ≤ t.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
    have hle : i.succ ≤ historyStageAt H t := Finset.le_max' _ _ hmem
    rw [hj] at hle
    have hcast : i.castSucc.val = i.val := rfl
    have hsucc : i.succ.val = i.val + 1 := rfl
    have hval : i.succ.val ≤ i.castSucc.val := hle
    omega

theorem historyStageAt_eventually_eq_of_not_event (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon)
    (ht : ∀ i : Fin H.eventCount, t.1 ≠ H.time i.succ) :
    ∀ᶠ s in 𝓝 t, historyStageAt H s = historyStageAt H t := by
  have hall : ∀ᶠ s in 𝓝 t, ∀ k : Fin (H.eventCount + 1),
      H.time k ≤ s.1 ↔ H.time k ≤ t.1 := by
    apply eventually_all.mpr
    intro k
    by_cases hk : k = 0
    · subst k
      exact Eventually.of_forall fun s => by simp [H.time_zero, s.2.1, t.2.1]
    have hne : H.time k ≠ t.1 := by
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk
      exact (ht i).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · filter_upwards [(continuous_subtype_val.tendsto t).eventually (eventually_gt_nhds hlt)]
        with s hs
      simp [hs.le, hlt.le]
    · filter_upwards [(continuous_subtype_val.tendsto t).eventually (eventually_lt_nhds hgt)]
        with s hs
      simp [not_le.mpr hs, not_le.mpr hgt]
  filter_upwards [hall] with s hs
  have he : Finset.univ.filter (fun k => H.time k ≤ s.1) =
      Finset.univ.filter (fun k => H.time k ≤ t.1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs k]
  unfold historyStageAt
  simp only [he]

theorem historyStageAt_eventually_eq_right (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) :
    ∀ᶠ s in 𝓝[Ici t] t, historyStageAt H s = historyStageAt H t := by
  have hall : ∀ᶠ s in 𝓝[Ici t] t, ∀ k : Fin (H.eventCount + 1),
      H.time k ≤ s.1 ↔ H.time k ≤ t.1 := by
    apply eventually_all.mpr
    intro k
    by_cases hk : H.time k ≤ t.1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact iff_of_true (hk.trans hs) hk
    · have hlt : t.1 < H.time k := lt_of_not_ge hk
      have he := (continuous_subtype_val.tendsto t).eventually (eventually_lt_nhds hlt)
      filter_upwards [he.filter_mono inf_le_left] with s hs
      exact iff_of_false (not_le.mpr hs) hk
  filter_upwards [hall] with s hs
  have he : Finset.univ.filter (fun k => H.time k ≤ s.1) =
      Finset.univ.filter (fun k => H.time k ≤ t.1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs k]
  unfold historyStageAt
  simp only [he]

theorem continuousOn_historyStageComponentWidth (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) (c : ConnectedComponents (H.stage j).Carrier)
    (hSC : SimplyConnectedSpace ((H.stage j).component c).Carrier) :
    ContinuousOn (fun t => componentWidth (H.stage j) (historyStageMetric H j t) c hSC)
      (historyStageDomain H j) := by
  cases j using Fin.lastCases with
  | last =>
    simp only [historyStageMetric, historyStageDomain, Fin.lastCases_last]
    split_ifs with h
    · exact continuousOn_componentWidth_metricFamily _ _ _ (H.finalSlab h).equation.smoothMetric c hSC
    · exact continuous_const.continuousOn
  | cast i =>
    have hc := continuousOn_componentWidth_metricFamily _ _ _
      (H.event i).incoming.equation.smoothMetric c hSC
    change ContinuousOn (fun s => componentWidth (H.stage i.castSucc)
      ((H.event i).incoming.flow.base.metric s) c hSC)
      (Ico (H.time i.castSucc) (H.time i.succ)) at hc
    simpa only [historyStageMetric, historyStageDomain, Fin.lastCases_castSucc] using hc

private theorem historyWidth_tendsto_of_stage_eventually_constant (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : Icc (0 : ℝ) H.horizon) (F : Filter (Icc (0 : ℝ) H.horizon))
    (hF : F ≤ 𝓝 t)
    (hstage : ∀ᶠ s in F, historyStageAt H s = historyStageAt H t) :
    Tendsto (historyWidth H h0 terminal) F (𝓝 (historyWidth H h0 terminal t)) := by
  let j := historyStageAt H t
  let c := (rfs_finite_ancestor_chain H terminal).component j
  let hSC := rfs_simply_connected_history H h0 j c
  let f : ℝ → ℝ := fun s => componentWidth (H.stage j) (historyStageMetric H j s) c hSC
  have hc : ContinuousWithinAt f (historyStageDomain H j) t.1 :=
    continuousOn_historyStageComponentWidth H j c hSC t.1 (historyStageAt_mem H t)
  have hcoe : Tendsto (fun s : Icc (0 : ℝ) H.horizon => s.1) F
      (𝓝[historyStageDomain H j] t.1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_subtype_val.tendsto t).mono_left hF, ?_⟩
    filter_upwards [hstage] with s hs
    simpa only [hs] using historyStageAt_mem H s
  have heq : (fun s : Icc (0 : ℝ) H.horizon => f s.1) =ᶠ[F]
      historyWidth H h0 terminal := by
    filter_upwards [hstage] with s hs
    let W : Fin (H.eventCount + 1) → ℝ := fun k =>
      componentWidth (H.stage k) (historyStageMetric H k s.1)
        ((rfs_finite_ancestor_chain H terminal).component k)
        (rfs_simply_connected_history H h0 k _)
    change W (historyStageAt H t) = W (historyStageAt H s)
    exact congrArg W hs.symm
  exact (Filter.Tendsto.comp hc hcoe).congr' heq

theorem historyWidth_initial_eq_of_isometry
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (g₀ : SmoothRiemannianMetric ThreeModel M) (o : TangentOrientationSection M)
    (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (e : M ≃ₜ (H.stage 0).Carrier)
    (he : ∀ x y, riemannianEDistOf (H.initialMetric 0) (e x) (e y) =
      riemannianEDistOf g₀ x y)
    (horient : integralHomologyMap 3 (e : C(M, (H.stage 0).Carrier)) (fundamentalClass o) =
      fundamentalClass (H.stage 0).orientation)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    historyWidth H h0 terminal (historyStageTime H 0) = canonicalWidth g₀ o := by
  let : ConnectedSpace (H.stage 0).Carrier := e.connectedSpace_iff.mp inferInstance
  let : SimplyConnectedSpace (H.stage 0).Carrier :=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  let c := (rfs_finite_ancestor_chain H terminal).component 0
  let := (H.stage 0).component_connected c
  let := h0 c
  let d := componentDiffeomorph (H.stage 0) c
  have hd : ∀ x y, riemannianEDistOf (H.initialMetric 0) (d x) (d y) =
      riemannianEDistOf ((H.stage 0).componentMetric (H.initialMetric 0) c) x y :=
    riemannianEDist_eq_of_diffeomorph_metric_pullback _ _ d
      (componentDiffeomorph_metric (H.stage 0) (H.initialMetric 0) c)
  have hpositive : integralHomologyMap 3
      (d : C(((H.stage 0).component c).Carrier, (H.stage 0).Carrier))
      (fundamentalClass ((H.stage 0).component c).orientation) =
        fundamentalClass (H.stage 0).orientation :=
    fundamentalClass_natural_diffeomorph ((H.stage 0).component c).orientation
      (H.stage 0).orientation d (componentDiffeomorph_positive (H.stage 0) c)
  have hw := canonicalWidth_eq_of_isometry _ _ _ _ d.toHomeomorph hd hpositive
  rw [historyWidth_stageTime]
  change canonicalWidth ((H.stage 0).componentMetric (H.initialMetric 0) c)
    ((H.stage 0).component c).orientation = canonicalWidth g₀ o
  exact hw.symm.trans (canonicalWidth_eq_of_isometry g₀ (H.initialMetric 0)
    o (H.stage 0).orientation e he horient)

theorem historyWidth_continuousAt_of_not_event (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (t : Icc (0 : ℝ) H.horizon)
    (ht : ∀ i : Fin H.eventCount, t.1 ≠ H.time i.succ) :
    ContinuousAt (historyWidth H h0 terminal) t := by
  exact historyWidth_tendsto_of_stage_eventually_constant H h0 terminal t (𝓝 t) le_rfl
    (historyStageAt_eventually_eq_of_not_event H t ht)

theorem historyWidth_rightContinuousAt_event (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (i : Fin H.eventCount) (_hi : H.time i.succ < H.horizon) :
    ContinuousWithinAt (historyWidth H h0 terminal)
      (Ici (historyStageTime H i.succ)) (historyStageTime H i.succ) := by
  exact historyWidth_tendsto_of_stage_eventually_constant H h0 terminal _ _ inf_le_left
    (historyStageAt_eventually_eq_right H _)

theorem historyWidth_event_jump (H : ObservedHistory.{u})
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (i : Fin H.eventCount) :
    ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) ≤
      liminf (fun t => ENNReal.ofReal (historyWidth H h0 terminal t))
        (𝓝[<] (historyStageTime H i.succ)) := by
  let chain := rfs_finite_ancestor_chain H terminal
  let SC := rfs_simply_connected_history H h0
  let G := cutoff i
  let c := chain.component i.succ
  let p := G.transition.childParent c
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal
    (componentWidth (H.stage i.castSucc) ((H.event i).incoming.flow.base.metric s) p
      (SC i.castSucc p))
  have hleft : ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) =
      ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
        (SC i.succ c)) := by
    rw [historyWidth_stageTime, ← H.event_output i]
  rw [hleft]
  have h₁ : ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
      (SC i.succ c)) ≤ liminf w (𝓝[<] (H.time i.succ)) :=
    rfs_actual_width_jump G (SC i.castSucc) c
  have hcoe : Tendsto (fun t : Icc (0 : ℝ) H.horizon => t.1)
      (𝓝[<] (historyStageTime H i.succ)) (𝓝[<] (H.time i.succ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(continuous_subtype_val.tendsto (historyStageTime H i.succ)).mono_left inf_le_left,
      self_mem_nhdsWithin⟩
  have h₂ := hcoe.liminf_le_liminf_comp (u := w)
  have heq : (w ∘ fun t : Icc (0 : ℝ) H.horizon => t.1) =ᶠ[𝓝[<] (historyStageTime H i.succ)]
      (fun t => ENNReal.ofReal (historyWidth H h0 terminal t)) := by
    filter_upwards [hcoe.eventually (Ioo_mem_nhdsLT (H.event i).incoming.lt)] with t ht
    rw [historyWidth_incoming H h0 terminal i t ⟨ht.1.le, ht.2⟩]
    change w t.1 = ENNReal.ofReal (componentWidth (H.stage i.castSucc)
      ((H.event i).incoming.flow.base.metric t.1) (chain.component i.castSucc)
      (SC i.castSucc _))
    rw [chain.parent_eq i]
  exact h₁.trans (h₂.trans_eq (liminf_congr heq))

theorem rfs_initial_width_data_of_homeomorph
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (g₀ : SmoothRiemannianMetric ThreeModel M) (o : TangentOrientationSection M) :
    ∃ Γ₀ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass o),
      let A := familyMaximum g₀ Γ₀.1
      (0 ≤ canonicalWidth g₀ o ∧ canonicalWidth g₀ o ≤ A ∧ ENNReal.ofReal A < ⊤) ∧
      (∀ (lam : ℝ) (hlam : 0 < lam),
        familyMaximum (scaleMetric lam hlam g₀) Γ₀.1 = lam * A ∧
          canonicalWidth (scaleMetric lam hlam g₀) o ≤ lam * A) ∧
      ∀ (H : ObservedHistory.{u})
        (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
          SimplyConnectedSpace ((H.stage 0).component c).Carrier)
        (e : M ≃ₜ (H.stage 0).Carrier),
        (∀ x y, riemannianEDistOf (H.initialMetric 0) (e x) (e y) =
          riemannianEDistOf g₀ x y) →
        integralHomologyMap 3 (e : C(M, (H.stage 0).Carrier)) (fundamentalClass o) =
          fundamentalClass (H.stage 0).orientation →
        ∀ (parameters : CutoffParameters)
          (_cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
          (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier),
          (∀ t, 0 ≤ historyWidth H h0 terminal t ∧
            ENNReal.ofReal (historyWidth H h0 terminal t) < ⊤) ∧
          historyWidth H h0 terminal (historyStageTime H 0) ≤ A ∧
          (∀ t, (∀ i : Fin H.eventCount, t.1 ≠ H.time i.succ) →
            ContinuousAt (historyWidth H h0 terminal) t) ∧
          (∀ i : Fin H.eventCount,
            ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) ≤
              liminf (fun t => ENNReal.ofReal (historyWidth H h0 terminal t))
                (𝓝[<] (historyStageTime H i.succ))) ∧
          ∀ i : Fin H.eventCount, H.time i.succ < H.horizon →
            ContinuousWithinAt (historyWidth H h0 terminal)
              (Ici (historyStageTime H i.succ)) (historyStageTime H i.succ) := by
  obtain ⟨Γ₀, hnonneg, hbound, hscale⟩ := initial_regular_width_data g₀ o
  refine ⟨Γ₀, ⟨hnonneg, hbound, ENNReal.ofReal_lt_top⟩, ?_, ?_⟩
  · intro lam hlam
    refine ⟨hscale lam hlam, ?_⟩
    rw [canonicalWidth_scale g₀ o hlam]
    exact mul_le_mul_of_nonneg_left hbound hlam.le
  · intro H h0 e he horient parameters cutoff terminal
    refine ⟨fun t => ⟨historyWidth_nonneg H h0 terminal t, ENNReal.ofReal_lt_top⟩,
      ?_, ?_, ?_, ?_⟩
    · rw [historyWidth_initial_eq_of_isometry g₀ o H h0 e he horient terminal]
      exact hbound
    · exact fun t ht => historyWidth_continuousAt_of_not_event H h0 terminal t ht
    · exact fun i => historyWidth_event_jump H parameters cutoff h0 terminal i
    · exact fun i hi => historyWidth_rightContinuousAt_event H h0 terminal i hi

theorem initialIdentification_riemannianEDist_eq (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : ObservedHistory.{u}) (d : InitialIdentification P g H) (x y : P.Carrier) :
    riemannianEDistOf (H.initialMetric 0) (d.map x) (d.map y) =
      riemannianEDistOf g x y := by
  exact riemannianEDist_eq_of_diffeomorph_metric_pullback g (H.initialMetric 0)
    d.map d.metric_eq x y

theorem initialIdentification_fundamentalClass (P : OrientedThreeStage.{u})
    [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier] (g : P.Metric)
    (H : ObservedHistory.{u}) (d : InitialIdentification P g H) :
    integralHomologyMap 3 (d.map : C(P.Carrier, (H.stage 0).Carrier))
      (fundamentalClass P.orientation) = fundamentalClass (H.stage 0).orientation := by
  exact fundamentalClass_natural_diffeomorph P.orientation (H.stage 0).orientation d.map d.positive

theorem initialIdentification_components_simplyConnected
    (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (g : P.Metric)
    (H : ObservedHistory.{u}) (d : InitialIdentification P g H)
    (c : ConnectedComponents (H.stage 0).Carrier) :
    SimplyConnectedSpace ((H.stage 0).component c).Carrier := by
  let : ConnectedSpace (H.stage 0).Carrier :=
    d.map.toHomeomorph.connectedSpace_iff.mp inferInstance
  let : SimplyConnectedSpace (H.stage 0).Carrier :=
    d.map.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  exact (componentDiffeomorph (H.stage 0) c).toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem rfs_initial_width_data (P : OrientedThreeStage.{u})
    [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier] (g₀ : P.Metric) :
    ∃ Γ₀ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass P.orientation),
      let A := familyMaximum g₀ Γ₀.1
      (0 ≤ canonicalWidth g₀ P.orientation ∧ canonicalWidth g₀ P.orientation ≤ A ∧
        ENNReal.ofReal A < ⊤) ∧
      (∀ (lam : ℝ) (hlam : 0 < lam),
        familyMaximum (scaleMetric lam hlam g₀) Γ₀.1 = lam * A ∧
        canonicalWidth (scaleMetric lam hlam g₀) P.orientation ≤ lam * A ∧
        ∀ (H : ObservedHistory.{u}) (d : InitialIdentification P (scaleMetric lam hlam g₀) H)
          (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier),
          historyWidth H
            (initialIdentification_components_simplyConnected P (scaleMetric lam hlam g₀) H d)
            terminal (historyStageTime H 0) ≤ lam * A) ∧
      ∀ (H : ObservedHistory.{u}) (d : InitialIdentification P g₀ H),
        let h0 := initialIdentification_components_simplyConnected P g₀ H d
        ∀ (parameters : CutoffParameters)
          (_cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
          (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier),
          (∀ t, 0 ≤ historyWidth H h0 terminal t ∧
            ENNReal.ofReal (historyWidth H h0 terminal t) < ⊤) ∧
          historyWidth H h0 terminal (historyStageTime H 0) ≤ A ∧
          (∀ t, (∀ i : Fin H.eventCount, t.1 ≠ H.time i.succ) →
            ContinuousAt (historyWidth H h0 terminal) t) ∧
          (∀ i : Fin H.eventCount,
            ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) ≤
              liminf (fun t => ENNReal.ofReal (historyWidth H h0 terminal t))
                (𝓝[<] (historyStageTime H i.succ))) ∧
          ∀ i : Fin H.eventCount, H.time i.succ < H.horizon →
            ContinuousWithinAt (historyWidth H h0 terminal)
              (Ici (historyStageTime H i.succ)) (historyStageTime H i.succ) := by
  obtain ⟨Γ₀, hbound, hscale, hhistory⟩ := rfs_initial_width_data_of_homeomorph g₀ P.orientation
  refine ⟨Γ₀, hbound, ?_, ?_⟩
  · intro lam hlam
    refine ⟨(hscale lam hlam).1, (hscale lam hlam).2, ?_⟩
    intro H d terminal
    rw [historyWidth_initial_eq_of_isometry (scaleMetric lam hlam g₀) P.orientation H
      (initialIdentification_components_simplyConnected P (scaleMetric lam hlam g₀) H d)
      d.map.toHomeomorph
      (initialIdentification_riemannianEDist_eq P (scaleMetric lam hlam g₀) H d)
      (initialIdentification_fundamentalClass P (scaleMetric lam hlam g₀) H d) terminal]
    exact (hscale lam hlam).2
  · intro H d
    dsimp only
    intro parameters cutoff terminal
    exact hhistory H (initialIdentification_components_simplyConnected P g₀ H d)
      d.map.toHomeomorph (initialIdentification_riemannianEDist_eq P g₀ H d)
      (initialIdentification_fundamentalClass P g₀ H d) parameters cutoff terminal

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
