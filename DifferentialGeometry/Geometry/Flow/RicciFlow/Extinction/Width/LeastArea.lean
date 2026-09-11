import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SpanningArea

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
  sorry

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
  sorry

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
