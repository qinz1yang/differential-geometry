import DifferentialGeometry.Geometry.Exponential.BranchEnergyBounds
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import Mathlib.Topology.VectorBundle.Riemannian
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section
open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem branch_source_tube
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∃ A ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) < r → (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source := by
  let e := trivializationAt E (TangentSpace I) p
  let O : Set (M × E) := e '' (e.source ∩ B.hom.source)
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hO : IsOpen O := e.toOpenPartialHomeomorph.isOpen_image_source_inter B.hom.open_source
  have hpO : (p, (0 : E)) ∈ O := by
    refine ⟨⟨p, 0⟩, ⟨?_, B.zero_mem⟩, e.zeroSection ℝ hpbase⟩
    rwa [e.mem_source]
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds hpO)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt E (fun x : M => TangentSpace I x) p
  change ∀ᶠ y in 𝓝 p, ‖e.continuousLinearMapAt ℝ y‖ < C at hbound
  let A := (U ∩ {y | ‖e.continuousLinearMapAt ℝ y‖ < C}) ∩ e.baseSet
  have hA : A ∈ 𝓝 p := inter_mem (inter_mem hU hbound) (e.open_baseSet.mem_nhds hpbase)
  refine ⟨A, hA, r / C, div_pos hr hC, ?_⟩
  intro y hy v hv
  have hnorm : ‖v‖ = Real.sqrt (g.inner y v v) := by
    have h := hEnorm y v
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).1 h
  let w := e.continuousLinearMapAt ℝ y v
  have hw : ‖w‖ < r := by
    calc
      ‖w‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ := (e.continuousLinearMapAt ℝ y).le_opNorm v
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hy.1.2.le (norm_nonneg v)
      _ < C * (r / C) := mul_lt_mul_of_pos_left (by rwa [hnorm]) hC
      _ = r := mul_div_cancel₀ r hC.ne'
  have hwV : w ∈ V := hrV (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  obtain ⟨z, hz, hez⟩ := hUV (Set.mk_mem_prod hy.1.1 hwV)
  have hvsource : (⟨y, v⟩ : TangentBundle I M) ∈ e.source := by
    rw [e.mem_source]
    exact hy.2
  have hev : e (⟨y, v⟩ : TangentBundle I M) = (y, w) := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy.2 v]
    exact congrArg (fun a : E => (y, a)) (congrFun (e.coe_continuousLinearEquivAt_eq hy.2) v)
  have hzv := e.toOpenPartialHomeomorph.injOn hz.1 hvsource (hez.trans hev.symm)
  exact hzv ▸ hz.2

private theorem diagonalInverseBranch_eventually_branchEnergy_eq_half_dist_sq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p), (yz ∈ B.dom) ∧
      branchEnergy g (B.fixed yz.1) yz.2 = (1 / 2 : ℝ) * (riemannianEDist I yz.1 yz.2).toReal ^ 2 := by
  obtain ⟨A, hA, r, hr, hsource⟩ := branch_source_tube B
  have hdist : {yz : M × M | edist yz.1 yz.2 < ENNReal.ofReal r} ∈ 𝓝 (p, p) :=
    (isOpen_lt (continuous_fst.edist continuous_snd) continuous_const).mem_nhds
      (by simpa using ENNReal.ofReal_pos.mpr hr)
  filter_upwards [continuous_fst.continuousAt hA, hdist] with yz hyA hyd
  have hyd' : riemannianEDist I yz.1 yz.2 < ENNReal.ofReal r := by
    rwa [← IsRiemannianManifold.out (I := I)]
  have hfin : riemannianEDist I yz.1 yz.2 ≠ ⊤ := ne_top_of_lt hyd'
  have hydreal : (riemannianEDist I yz.1 yz.2).toReal < r := by
    simpa only [ENNReal.toReal_ofReal hr.le] using
      (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hyd'
  obtain ⟨v, hvexp, hvlen⟩ := minExp_of_ne_top (I := I) g hEnorm yz.1 yz.2 hfin
  have hvdist : Real.sqrt (g.inner yz.1 v v) = (riemannianEDist I yz.1 yz.2).toReal := by
    exact hvlen
  have hvsource : (⟨yz.1, v⟩ : TangentBundle I M) ∈ B.hom.source :=
    hsource yz.1 hyA v (hvdist.trans_lt hydreal)
  have hvfixed : tangentSpaceModelContinuousLinearEquiv (I := I) yz.1 v ∈
      (B.fixed yz.1).hom.source := by
    change (⟨yz.1, v⟩ : TangentBundle I M) ∈ B.hom.source
    exact hvsource
  have henergy : branchEnergy g (B.fixed yz.1) yz.2 =
      (1 / 2 : ℝ) * g.inner yz.1 v v := by
    rw [← hvexp]
    exact branchEnergy_exp (B.fixed yz.1) hvfixed
  have htarget : yz ∈ B.dom := by
    have hh := B.hom.map_source hvsource
    have heq : B.hom (⟨yz.1, v⟩ : TangentBundle I M) = yz := by
      exact (B.hom_eq hvsource).trans (by simp only [diagExp, hvexp, Prod.mk.eta])
    exact heq ▸ hh
  have hsq : (riemannianEDist I yz.1 yz.2).toReal ^ 2 = g.inner yz.1 v v := by
    rw [← hvdist]
    exact Real.sq_sqrt (metric_inner_self_nonneg g yz.1 v)
  exact ⟨htarget, henergy.trans (congrArg (fun a : ℝ => (1 / 2 : ℝ) * a) hsq.symm)⟩

private theorem exists_open_contMDiff_riemannianEDist_sq_of_complete
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (x : M) :
    ∃ U : Set (M × M), IsOpen U ∧ (x, x) ∈ U ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun yz : M × M => (riemannianEDist I yz.1 yz.2).toReal ^ 2) U := by
  let B := standardDiagonalInverseBranch (I := I) g hEnorm x
  have hnear := diagonalInverseBranch_eventually_branchEnergy_eq_half_dist_sq B
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  have hUB : U ⊆ B.dom := fun yz hyz => (hUsub hyz).1
  have he : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
      (fun yz : M × M => 2 * branchEnergy g (B.fixed yz.1) yz.2) U :=
    contMDiffOn_const.mul (B.contMDiffOn_branchEnergy_fixed.mono hUB)
  refine ⟨U, hU, hxU, he.congr ?_⟩
  intro yz hyz
  rw [(hUsub hyz).2]
  ring

end DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_riemannianMetricComplete_local_distance_eq
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (g' : SmoothRiemannianMetric I M) (U : Set M),
      RiemannianMetricComplete g' ∧ IsOpen U ∧ p ∈ U ∧
      (∀ x ∈ U, g'.inner x = g.inner x) ∧
      ∀ x ∈ U, ∀ y ∈ U, riemannianEDistOf g' x y = riemannianEDistOf g x y ∧
        riemannianEDistOf g x y ≠ ⊤ := by
  obtain ⟨g', W, hcomplete, hW, hpW, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g (isCompact_singleton (x := p))
  have hpW' : p ∈ W := hpW (mem_singleton p)
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  have hlocal : ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, ∀ y ∈ V, g'.inner x = g.inner x ∧
        riemannianEDistOf g' x y = riemannianEDistOf g x y ∧
        riemannianEDistOf g x y ≠ ⊤ := by
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    obtain ⟨ε, hε, hεW⟩ := EMetric.mem_nhds_iff.mp (hW.mem_nhds hpW')
    obtain ⟨R, hR, hR0, hRε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    have hRpos : 0 < R := ENNReal.ofReal_pos.mp hR0
    refine ⟨Metric.eball p (ENNReal.ofReal (R / 4)), Metric.isOpen_eball,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr (by positivity)), ?_⟩
    intro x hx y hy
    have hxp : edist x p < ENNReal.ofReal (R / 4) := hx
    have hyp : edist y p < ENNReal.ofReal (R / 4) := hy
    have hxy : edist x y < ENNReal.ofReal (R / 2) := by
      calc
        edist x y ≤ edist x p + edist p y := edist_triangle _ _ _
        _ < ENNReal.ofReal (R / 4) + ENNReal.ofReal (R / 4) :=
          ENNReal.add_lt_add hxp (by simpa only [edist_comm p y] using hyp)
        _ = ENNReal.ofReal (R / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    have hball : {z : M | riemannianEDistOf g x z ≤ ENNReal.ofReal (R / 2)} ⊆ W := by
      intro z hz
      apply hεW
      change edist z p < ε
      have hxz : edist x z ≤ ENNReal.ofReal (R / 2) := hz
      calc
        edist z p ≤ edist z x + edist x p := edist_triangle _ _ _
        _ ≤ ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 4) :=
          add_le_add (by simpa only [edist_comm z x] using hxz) hxp.le
        _ ≤ ENNReal.ofReal R := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        _ < ε := hRε
    have hxW : x ∈ W := hball (by
      change riemannianEDistOf g x x ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le)
    exact ⟨heq x hxW, riemannianEDistOf_eq_of_eqOn_ball g g' hball heq hle hxy,
      ne_top_of_lt hxy⟩
  obtain ⟨V, hV, hpV, hdV⟩ := hlocal
  exact ⟨g', V, hcomplete, hV, hpV, fun x hx => (hdV x hx x hx).1,
    fun x hx y hy => (hdV x hx y hy).2⟩

private theorem exists_open_contMDiff_riemannianEDistOf_sq_of_nonzero_finrank
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun yz : M × M => (riemannianEDistOf g yz.1 yz.2).toReal ^ 2) (U ×ˢ U) := by
  obtain ⟨g', V, hcomplete, hV, hpV, _heq, hdV⟩ :=
    exists_riemannianMetricComplete_local_distance_eq g p
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  obtain ⟨Z, hZ, hpZ, hdZ⟩ := exists_open_contMDiff_riemannianEDist_sq_of_complete g' hEnorm p
  obtain ⟨A, B, hA, hpA, hB, hpB, hAB⟩ := mem_nhds_prod_iff'.mp (hZ.mem_nhds hpZ)
  let U : Set M := (A ∩ B) ∩ V
  have hUZ : U ×ˢ U ⊆ Z := fun yz hyz => hAB ⟨hyz.1.1.1, hyz.2.1.2⟩
  refine ⟨U, (hA.inter hB).inter hV, ⟨⟨hpA, hpB⟩, hpV⟩, (hdZ.mono hUZ).congr ?_⟩
  intro yz hyz
  rw [← riemannianEDistOf_eq_riemannianEDist g' hEnorm, (hdV yz.1 hyz.1.2 yz.2 hyz.2.2).1]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_open_contMDiff_riemannianEDistOf_sq
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun yz : M × M => (riemannianEDistOf g yz.1 yz.2).toReal ^ 2) (U ×ˢ U) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : DiscreteTopology M := DifferentialGeometry.discrete_topology_of_finrank_eq_zero I hdim
    exact ⟨univ, isOpen_univ, mem_univ p, contMDiff_of_discreteTopology.contMDiffOn⟩
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact exists_open_contMDiff_riemannianEDistOf_sq_of_nonzero_finrank g p

end DifferentialGeometry.Geometry.Riemannian
