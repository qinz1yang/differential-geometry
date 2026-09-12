import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SpanningArea
import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaWeakBoundary
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaHomeomorphism
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Topology.StandardModel

noncomputable section

universe uK

open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def competitorAreas (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) : Set ℝ :=
  Set.range (fun u : DiskCompetitor g γ => diskArea g u.1.map)

theorem competitorAreas_bddBelow (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) : BddBelow (competitorAreas g γ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact diskArea_nonneg g u.1.map

variable [finiteDimensionalE : FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q]

theorem competitorAreas_nonempty (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    (competitorAreas g γ).Nonempty := by
  obtain ⟨u⟩ := rfs_disk_competitor_exists g γ hctr hlip
  exact ⟨diskArea g u.1.map, u, rfl⟩

def leastArea (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (_hctr : IsContractibleLoop γ) (_hlip : IsLipschitzLoop g γ) : ℝ :=
  sInf (competitorAreas g γ)

theorem leastArea_nonneg (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    0 ≤ leastArea g γ hctr hlip := by
  apply le_csInf (competitorAreas_nonempty g γ hctr hlip)
  rintro _ ⟨u, rfl⟩
  exact diskArea_nonneg g u.1.map

omit finiteDimensionalE boundarylessI t2Q compactQ in
theorem leastArea_le_competitor (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (u : DiskCompetitor g γ) : leastArea g γ hctr hlip ≤ diskArea g u.1.map :=
  csInf_le (competitorAreas_bddBelow g γ) ⟨u, rfl⟩


theorem exists_competitor_area_lt (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : DiskCompetitor g γ, diskArea g u.1.map < leastArea g γ hctr hlip + ε := by
  obtain ⟨a, ⟨u, rfl⟩, hu⟩ := exists_lt_of_csInf_lt
    (competitorAreas_nonempty g γ hctr hlip)
    (show sInf (competitorAreas g γ) < leastArea g γ hctr hlip + ε by
      exact lt_add_of_pos_right _ hε)
  exact ⟨u, hu⟩

theorem leastArea_const (g : SmoothRiemannianMetric I Q) (q : Q) :
    leastArea g (constantLoops q) (isContractibleLoop_constant q)
      (isLipschitzLoop_constant g q) = 0 := by
  apply le_antisymm
  · exact (leastArea_le_competitor g (constantLoops q) (isContractibleLoop_constant q)
      (isLipschitzLoop_constant g q) (constantDiskCompetitor g q)).trans_eq (diskArea_const g q)
  · exact leastArea_nonneg _ _ _ _


def regularLeastArea (g : SmoothRiemannianMetric I Q)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) : ℝ :=
  leastArea g γ.1.toContinuousLoop γ.2 (γ.1.isLipschitz g)

theorem regularLeastArea_nonneg (g : SmoothRiemannianMetric I Q)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) : 0 ≤ regularLeastArea g γ :=
  leastArea_nonneg _ _ _ _

theorem leastArea_le_add_of_disk_attachment (g : SmoothRiemannianMetric I Q)
    (γ₀ γ₁ : ContinuousFreeLoop Q)
    (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
    (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁)
    (A : LipschitzAnnulus g)
    (hattach : ∀ u : DiskCompetitor g γ₀, ∃ v : DiskCompetitor g γ₁,
      diskArea g v.1.map = diskArea g u.1.map + annulusArea g A.map) :
    leastArea g γ₁ hctr₁ hlip₁ ≤ leastArea g γ₀ hctr₀ hlip₀ + annulusArea g A.map := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu⟩ := exists_competitor_area_lt g γ₀ hctr₀ hlip₀ hε
  obtain ⟨v, hv⟩ := hattach u
  have hvle := leastArea_le_competitor g γ₁ hctr₁ hlip₁ v
  rw [hv] at hvle
  linarith

omit finiteDimensionalE boundarylessI t2Q compactQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem parametricJacobian_eq_riemannianAreaDensity (g : SmoothRiemannianMetric I Q)
    (U : ℂ → Q) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    parametricJacobian g U (Metric.closedBall (0 : ℂ) 1) z =
      Geometry.riemannianAreaDensity g U z := by
  have hs : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) I U z
  · have hw : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      hd.mdifferentiableWithinAt
    rw [parametricJacobian, if_pos hw, mfderivWithin_of_mem_nhds (f := U) hs]
    have h0 : diskBasis (0 : Fin 2) = (1 : ℂ) := by simp [diskBasis]
    have h1 : diskBasis (1 : Fin 2) = Complex.I := by simp [diskBasis]
    rw [Matrix.det_fin_two, Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian]
    simp only [h0, h1]
    rw [g.symm (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
      (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))]
    ring_nf
  · have hw : ¬ MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      fun h => hd (h.mdifferentiableAt hs)
    rw [parametricJacobian, if_neg hw,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd]

omit finiteDimensionalE boundarylessI t2Q compactQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem diskArea_eq_riemannianDiskArea (g : SmoothRiemannianMetric I Q) (u : Disk → Q) :
    diskArea g u = Geometry.riemannianDiskArea g u := by
  simp only [diskArea, diskJacobian, Geometry.riemannianDiskArea, Geometry.riemannianArea]
  refine integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  refine (parametricJacobian_congr_on (s := Metric.closedBall (0 : ℂ) 1) g ?_
    (Metric.ball_subset_closedBall hz)).trans
    (parametricJacobian_eq_riemannianAreaDensity g (Geometry.diskExtension u) z hz)
  intro w hw
  simp only [diskExtension, dif_pos hw, Geometry.diskExtension, Function.comp_apply]
  rw [Geometry.diskRetraction_coe ⟨w, hw⟩]

section Pullback

variable {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [t2A : T2Space A]

omit boundarylessI t2Q compactQ in
private theorem riemannianAreaDensity_pullbackMetricCross (g : SmoothRiemannianMetric I Q)
    (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (U : ℂ → A) (z : ℂ) :
    Geometry.riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      Geometry.riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z =
        (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

omit boundarylessI t2Q compactQ in
private theorem riemannianDiskArea_pullbackMetricCross (g : SmoothRiemannianMetric I Q)
    (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    Geometry.riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) u =
      Geometry.riemannianDiskArea g (fun z => Ψ (u z)) := by
  rw [Geometry.riemannianDiskArea, Geometry.riemannianDiskArea]
  refine integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  rw [riemannianAreaDensity_pullbackMetricCross]
  refine Geometry.riemannianAreaDensity_congr g ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [Geometry.diskExtension, Function.comp_apply]

omit finiteDimensionalE t2Q t2A in
private theorem mem_spanningDiskCompetitors_iff (g : SmoothRiemannianMetric 𝓘(ℝ, E) A)
    (γ : C(DifferentialGeometry.Topology.loopCircle, A))
    (u : C(DifferentialGeometry.Topology.closedDisk, A)) :
    u ∈ Geometry.spanningDiskCompetitors g γ ↔
      (∀ θ : Surgery.Topology.Circle, u (diskBoundary θ) = γ θ) ∧
        ∃ L : ℝ≥0, ∀ z w : Disk,
          riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w := by
  rw [Geometry.spanningDiskCompetitors, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun θ => ?_, h.2⟩
    exact congrFun (congrArg DFunLike.coe h.1) θ
  · rintro ⟨h1, h2⟩
    refine ⟨ContinuousMap.ext fun θ => ?_, h2⟩
    exact h1 θ

end Pullback

abbrev standardModelLoop (c : Geometry.Topology.StandardModelCopy I Q E)
    (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    Geometry.lipschitzContractibleLoop (Diffeomorph.pullbackMetricCross g c.equiv.symm) :=
  ⟨⟨Surgery.Topology.loopPostcompose (⟨c.equiv, c.equiv.continuous⟩ : C(Q, c.Q)) γ,
      hctr.postcompose (⟨c.equiv, c.equiv.continuous⟩ : C(Q, c.Q))⟩, by
    obtain ⟨L, hL⟩ := hlip
    refine ⟨L, fun x y => ?_⟩
    rw [Geometry.Metric.edistOf_pullbackMetricCross]
    simpa only [Surgery.Topology.loopPostcompose_apply, ContinuousMap.coe_mk,
      Diffeomorph.symm_apply_apply] using hL x y⟩

omit boundarylessI compactQ in
private theorem leastArea_eq_leastSpanningArea_standardModelCopy
    (c : Geometry.Topology.StandardModelCopy I Q E)
    (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea g γ hctr hlip =
      Geometry.leastSpanningArea (Diffeomorph.pullbackMetricCross g c.equiv.symm)
        (standardModelLoop c g γ hctr hlip) := by
  let Φc : C(Q, c.Q) := ⟨c.equiv, c.equiv.continuous⟩
  have hset : competitorAreas g γ
      = Geometry.spanningDiskAreas (Diffeomorph.pullbackMetricCross g c.equiv.symm)
          (standardModelLoop c g γ hctr hlip) := by
    ext a
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Φc.comp u.1.map, ?_, ?_⟩
      · rw [mem_spanningDiskCompetitors_iff]
        refine ⟨fun θ => ?_, ?_⟩
        · simp only [ContinuousMap.comp_apply, u.2 θ]
          rfl
        · obtain ⟨L, hL⟩ := u.1.isLipschitz
          refine ⟨L, fun z w => ?_⟩
          rw [Geometry.Metric.edistOf_pullbackMetricCross]
          simpa only [Φc, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
            Diffeomorph.symm_apply_apply] using hL z w
      · beta_reduce
        rw [diskArea_eq_riemannianDiskArea g u.1.map]
        refine (riemannianDiskArea_pullbackMetricCross g c.equiv.symm
          (Φc.comp u.1.map)).trans ?_
        have harg : (fun z : Disk => c.equiv.symm ((Φc.comp u.1.map) z)) = u.1.map := by
          funext z
          simp only [Φc, ContinuousMap.coe_mk, ContinuousMap.comp_apply]
          exact Diffeomorph.symm_apply_apply c.equiv (u.1.map z)
        rw [harg]
    · rintro ⟨u', hu', rfl⟩
      rw [mem_spanningDiskCompetitors_iff] at hu'
      obtain ⟨htr, L, hL⟩ := hu'
      let vmap : C(Disk, Q) :=
        ⟨fun z => c.equiv.symm (u' z), c.equiv.symm.continuous.comp u'.continuous⟩
      have hv : ∃ L : ℝ≥0, ∀ z w : Disk, riemannianEDistOf g (vmap z) (vmap w)
          ≤ (L : ℝ≥0∞) * edist z w := by
        refine ⟨L, fun z w => ?_⟩
        simp only [vmap, ContinuousMap.coe_mk]
        rw [← Geometry.Metric.edistOf_pullbackMetricCross]
        exact hL z w
      refine ⟨⟨⟨vmap, hv⟩, ?_⟩, ?_⟩
      · intro θ
        simp only [vmap, ContinuousMap.coe_mk]
        rw [htr θ]
        exact Diffeomorph.symm_apply_apply c.equiv (γ θ)
      · simp only [vmap, ContinuousMap.coe_mk]
        exact (diskArea_eq_riemannianDiskArea g (fun z => c.equiv.symm (u' z))).trans
          (riemannianDiskArea_pullbackMetricCross g c.equiv.symm u').symm
  rw [leastArea, Geometry.leastSpanningArea, hset]

variable [connectedQ : ConnectedSpace Q]


theorem leastArea_nearby_upper_bound (g : SmoothRiemannianMetric I Q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : ContinuousFreeLoop Q)
        (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
        (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁),
        loopUniformDistance g γ₀ γ₁ < ρ →
        leastArea g γ₁ hctr₁ hlip₁ ≤ leastArea g γ₀ hctr₀ hlip₀ +
          C * loopUniformDistance g γ₀ γ₁ * (loopLength g γ₀ + loopLength g γ₁) := by
  obtain ⟨ρ, C, hρ, hC, hA⟩ := rfs_nearby_loop_annulus g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  obtain ⟨A, _, _, _, harea, hattach⟩ := hA γ₀ γ₁ hlip₀ hlip₁ hnear
  exact (leastArea_le_add_of_disk_attachment g γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ A
    hattach).trans (add_le_add le_rfl harea)

theorem leastArea_nearby_abs_bound (g : SmoothRiemannianMetric I Q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : ContinuousFreeLoop Q)
        (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
        (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁),
        loopUniformDistance g γ₀ γ₁ < ρ →
        |leastArea g γ₀ hctr₀ hlip₀ - leastArea g γ₁ hctr₁ hlip₁| ≤
          C * loopUniformDistance g γ₀ γ₁ * (loopLength g γ₀ + loopLength g γ₁) := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := leastArea_nearby_upper_bound g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  have h₁ := hbound γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  have hnear' : loopUniformDistance g γ₁ γ₀ < ρ := by
    rwa [loopUniformDistance_comm]
  have h₀ := hbound γ₁ γ₀ hctr₁ hctr₀ hlip₁ hlip₀ hnear'
  rw [loopUniformDistance_comm, add_comm (loopLength g γ₁)] at h₀
  exact abs_le.mpr ⟨by linarith, by linarith⟩

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem continuous_regularLeastArea (g : SmoothRiemannianMetric I Q) :
    Continuous (regularLeastArea g) := by
  sorry


def IsWeaklyMonotoneCircleMap (ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle)) : Prop :=
  ∃ φ : ℝ → ℝ, Continuous φ ∧ Monotone φ ∧
    (∀ t, φ (t + 1) = φ t + 1) ∧ ∀ t : ℝ, ψ (t : Surgery.Topology.Circle) = (φ t : Surgery.Topology.Circle)

theorem isWeaklyMonotoneCircleMap_id :
    IsWeaklyMonotoneCircleMap (ContinuousMap.id Surgery.Topology.Circle) :=
  ⟨id, continuous_id, monotone_id, fun _ => rfl, fun _ => rfl⟩


abbrev WeakDiskCompetitor (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) :=
  {u : LipschitzDisk g // ∃ ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle),
    IsWeaklyMonotoneCircleMap ψ ∧ ∀ θ, u.map (diskBoundary θ) = γ (ψ θ)}

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem rfs_weak_boundary_trace (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle))
    (hψ : IsWeaklyMonotoneCircleMap ψ)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ψ)) (hlip' : IsLipschitzLoop g (γ.comp ψ)) :
    leastArea g (γ.comp ψ) hctr' hlip' = leastArea g γ hctr hlip := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  obtain ⟨φ, hc, hm, hp, hlift⟩ := hψ
  rw [leastArea_eq_leastSpanningArea_standardModelCopy c g (γ.comp ψ) hctr' hlip',
    leastArea_eq_leastSpanningArea_standardModelCopy c g γ hctr hlip]
  exact Geometry.leastSpanningArea_comp_weak_boundary
    (Diffeomorph.pullbackMetricCross g c.equiv.symm)
    (standardModelLoop c g γ hctr hlip)
    (standardModelLoop c g (γ.comp ψ) hctr' hlip') ψ hc hm hp hlift rfl

theorem leastArea_eq_weak_boundary_infimum (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea g γ hctr hlip =
      sInf (Set.range (fun u : WeakDiskCompetitor g γ => diskArea g u.1.map)) := by
  let S := Set.range (fun u : WeakDiskCompetitor g γ => diskArea g u.1.map)
  have hS : S.Nonempty := by
    obtain ⟨u⟩ := rfs_disk_competitor_exists g γ hctr hlip
    exact ⟨diskArea g u.1.map,
      ⟨u.1, ContinuousMap.id _, isWeaklyMonotoneCircleMap_id, u.2⟩, rfl⟩
  have hb : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact diskArea_nonneg _ _
  apply le_antisymm
  · apply le_csInf hS
    rintro _ ⟨u, rfl⟩
    obtain ⟨ψ, hψ, hu⟩ := u.2
    have hctr' : IsContractibleLoop (γ.comp ψ) := by
      obtain ⟨q, hq⟩ := hctr
      exact ⟨q, hq.comp (ContinuousMap.Homotopic.refl ψ)⟩
    have hlip' := u.1.isLipschitz_trace g (γ.comp ψ) hu
    rw [← rfs_weak_boundary_trace g γ ψ hψ hctr hlip hctr' hlip']
    exact leastArea_le_competitor g (γ.comp ψ) hctr' hlip' ⟨u.1, hu⟩
  · apply le_csInf (competitorAreas_nonempty g γ hctr hlip)
    rintro _ ⟨u, rfl⟩
    exact csInf_le hb ⟨⟨u.1, ContinuousMap.id _, isWeaklyMonotoneCircleMap_id, u.2⟩, rfl⟩

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem leastArea_circle_homeomorph (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (ψ : Surgery.Topology.Circle ≃ₜ Surgery.Topology.Circle)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ⟨ψ, ψ.continuous⟩))
    (hlip' : IsLipschitzLoop g (γ.comp ⟨ψ, ψ.continuous⟩)) :
    leastArea g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip' = leastArea g γ hctr hlip := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  rw [leastArea_eq_leastSpanningArea_standardModelCopy c g (γ.comp ⟨ψ, ψ.continuous⟩)
      hctr' hlip',
    leastArea_eq_leastSpanningArea_standardModelCopy c g γ hctr hlip]
  exact Geometry.leastSpanningArea_comp_homeomorphism
    (Diffeomorph.pullbackMetricCross g c.equiv.symm)
    (standardModelLoop c g γ hctr hlip)
    (standardModelLoop c g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip') ψ rfl

omit connectedQ in
theorem leastArea_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ)
    (hlipg : IsLipschitzLoop g γ) (hliph : IsLipschitzLoop h γ) :
    a ^ 2 * leastArea g γ hctr hlipg ≤ leastArea h γ hctr hliph ∧
      leastArea h γ hctr hliph ≤ b ^ 2 * leastArea g γ hctr hlipg := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos (ha.trans_le hab)
  have hback : ∀ q (v : TangentSpace I q),
      g.inner q v v ≤ (a ^ 2)⁻¹ * h.inner q v v := by
    intro q v
    exact (le_inv_mul_iff₀ ha2).mpr (hmetric q v).1
  have hlower : a ^ 2 * leastArea g γ hctr hlipg ≤ leastArea h γ hctr hliph := by
    apply le_csInf (competitorAreas_nonempty h γ hctr hliph)
    rintro _ ⟨u, rfl⟩
    let v : DiskCompetitor g γ :=
      ⟨u.1.changeMetric h g (inv_pos.mpr ha2) hback, u.2⟩
    exact (mul_le_mul_of_nonneg_left (leastArea_le_competitor g γ hctr hlipg v)
      ha2.le).trans (diskArea_metric_comparison g h ha hab hmetric v.1).1
  have hupperDiv : leastArea h γ hctr hliph / b ^ 2 ≤ leastArea g γ hctr hlipg := by
    apply le_csInf (competitorAreas_nonempty g γ hctr hlipg)
    rintro _ ⟨u, rfl⟩
    let v : DiskCompetitor h γ :=
      ⟨u.1.changeMetric g h hb2 (fun q w => (hmetric q w).2), u.2⟩
    apply (div_le_iff₀ hb2).mpr
    have hv := (leastArea_le_competitor h γ hctr hliph v).trans
      (diskArea_metric_comparison g h ha hab hmetric u.1).2
    simpa only [mul_comm] using hv
  refine ⟨hlower, ?_⟩
  simpa only [mul_comm] using (div_le_iff₀ hb2).mp hupperDiv

omit connectedQ in
theorem regularLeastArea_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) :
    a ^ 2 * regularLeastArea g γ ≤ regularLeastArea h γ ∧
      regularLeastArea h γ ≤ b ^ 2 * regularLeastArea g γ :=
  leastArea_metric_comparison g h ha hab hmetric γ.1.toContinuousLoop γ.2
    (γ.1.isLipschitz g) (γ.1.isLipschitz h)

omit connectedQ in
theorem leastArea_scale (g : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea (scaleMetric c hc g) γ hctr
      ((isLipschitzLoop_metric_iff g (scaleMetric c hc g) γ).mp hlip) =
      c * leastArea g γ hctr hlip := by
  have hmetric : ∀ q (v : TangentSpace I q),
      (Real.sqrt c) ^ 2 * g.inner q v v ≤ (scaleMetric c hc g).inner q v v ∧
      (scaleMetric c hc g).inner q v v ≤ (Real.sqrt c) ^ 2 * g.inner q v v := by
    intro q v
    simp [Real.sq_sqrt hc.le]
  have h := leastArea_metric_comparison g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (le_refl (Real.sqrt c)) hmetric γ hctr hlip
    ((isLipschitzLoop_metric_iff g (scaleMetric c hc g) γ).mp hlip)
  simpa only [Real.sq_sqrt hc.le] using le_antisymm h.2 h.1

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem rfs_short_loop_fillings (g : SmoothRiemannianMetric I Q) :
    ∃ σ K₀ : ℝ, 0 < σ ∧ 0 ≤ K₀ ∧
      (∀ (γ : ContinuousFreeLoop Q), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K₀ * loopLength g γ ^ 2) ∧
      (∀ (K : Type uK) [TopologicalSpace K] [CompactSpace K]
        (Γ : RegularFamily (I := I) (Q := Q) K),
        (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
        ∃ F : C(Icc (0 : ℝ) 1 × K, ContractibleRegularLoop (I := I) (Q := Q)),
          (∀ k, F (⟨0, by simp⟩, k) = Γ k) ∧
          ∀ k, F (⟨1, by simp⟩, k) = constantContractibleRegularLoop ((Γ k).1 0)) ∧
      ((∀ q : Q, Subsingleton (HomotopyGroup (Fin 2) Q q)) →
        ∀ (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)),
          (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
          ∃ q : Q, ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ)
            (ContinuousMap.const (Sphere 2)
              (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q))) := by
  sorry

theorem short_loop_disk (g : SmoothRiemannianMetric I Q) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (γ : ContinuousFreeLoop Q), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K * loopLength g γ ^ 2 := by
  obtain ⟨σ, K, hσ, hK, hfill, _, _⟩ := rfs_short_loop_fillings.{0} g
  exact ⟨σ, hσ, K, hK, hfill⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
