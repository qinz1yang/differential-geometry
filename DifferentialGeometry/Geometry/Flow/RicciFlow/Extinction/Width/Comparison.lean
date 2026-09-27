import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth

noncomputable section

open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace H P] [ChartedSpace G Q] [IsManifold I ∞ P] [IsManifold J ∞ Q]


theorem IsLipschitzLoop.postcompose (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : ContinuousFreeLoop P) (hγ : IsLipschitzLoop g γ) :
    IsLipschitzLoop h (f.comp γ) := by
  obtain ⟨V, hV⟩ := hγ
  refine ⟨L * V, fun x y => ?_⟩
  exact (hf (γ x) (γ y)).trans (by
    simpa only [ENNReal.coe_mul, mul_assoc] using
      mul_le_mul' (le_refl (L : ℝ≥0∞)) (hV x y))


def LipschitzDisk.postcompose (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (u : LipschitzDisk g) : LipschitzDisk h where
  map := f.comp u.map
  isLipschitz := by
    obtain ⟨V, hV⟩ := u.isLipschitz
    refine ⟨L * V, fun z w => ?_⟩
    exact (hf (u.map z) (u.map w)).trans (by
      simpa only [ENNReal.coe_mul, mul_assoc] using
        mul_le_mul' (le_refl (L : ℝ≥0∞)) (hV z w))


def DiskCompetitor.postcompose (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : ContinuousFreeLoop P) (u : DiskCompetitor g γ) :
    DiskCompetitor h (f.comp γ) := by
  refine ⟨u.1.postcompose g h f L hf, fun θ => ?_⟩
  exact congrArg f (u.2 θ)

variable [finiteDimensionalE : FiniteDimensional ℝ E]
  [finiteDimensionalF : FiniteDimensional ℝ F]
  [boundarylessI : I.Boundaryless] [boundarylessJ : J.Boundaryless]
  [t2P : T2Space P] [t2Q : T2Space Q]
  [compactP : CompactSpace P] [compactQ : CompactSpace Q]
  [connectedP : ConnectedSpace P] [connectedQ : ConnectedSpace Q]

omit connectedP connectedQ in
theorem loopLength_le_of_lipschitz (h : SmoothRiemannianMetric J Q)
    (γ : ContinuousFreeLoop Q) (V : ℝ≥0)
    (hV : ∀ x y, riemannianEDistOf h (γ x) (γ y) ≤ (V : ℝ≥0∞) * edist x y) :
    loopLength h γ ≤ (V : ℝ) := by
  apply (ENNReal.ofReal_le_ofReal_iff V.coe_nonneg).mp
  rw [loopLength_eq_riemannianCurveLength h γ ⟨V, hV⟩,
    ENNReal.ofReal_coe_nnreal]
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  have hstep (i : ℕ) : edist ((p.2.1 (i + 1) : ℝ) : Surgery.Topology.Circle)
      ((p.2.1 i : ℝ) : Surgery.Topology.Circle) ≤
        ENNReal.ofReal (p.2.1 (i + 1) - p.2.1 i) := by
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm.trans_eq
      (Real.norm_of_nonneg (sub_nonneg.mpr (p.2.2.1 (Nat.le_succ i))))
  calc
    _ ≤ ∑ i ∈ Finset.range p.1,
        (V : ℝ≥0∞) * ENNReal.ofReal (p.2.1 (i + 1) - p.2.1 i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (hV _ _).trans (mul_le_mul' le_rfl (hstep i))
    _ = (V : ℝ≥0∞) * ENNReal.ofReal (p.2.1 p.1 - p.2.1 0) := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => sub_nonneg.mpr (p.2.2.1 (Nat.le_succ i))), Finset.sum_range_sub]
    _ ≤ (V : ℝ≥0∞) * 1 := by
      apply mul_le_mul' le_rfl
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      linarith [(p.2.2.2 p.1).2, (p.2.2.2 0).1]
    _ = _ := mul_one _

omit connectedP connectedQ finiteDimensionalF boundarylessJ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_loopUniformDistance_lt {K α : Type*}
    [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
    (h : SmoothRiemannianMetric J Q) {p : Filter α}
    {S : α → C(K, ContinuousFreeLoop Q)} {Γ : C(K, ContinuousFreeLoop Q)}
    (hS : Filter.Tendsto S p (𝓝 Γ)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in p, ∀ k, loopUniformDistance h (Γ k) (S ε k) < δ := by
  let : RiemannianBundle (TangentSpace J : Q → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : Q → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace Q := PseudoEMetricSpace.ofRiemannianMetric J Q
  have hu := ContinuousMap.continuous_uncurry.tendsto Γ |>.comp hS
  have hv := (EMetric.tendstoUniformly_iff.mp
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp hu))
      (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [hv] with ε hε k
  apply lt_of_le_of_lt (show loopUniformDistance h (Γ k) (S ε k) ≤ δ / 2 from ?_)
    (by linarith)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨θ, rfl⟩
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hε (k, θ)).le

omit connectedP connectedQ in
theorem loopLength_postcompose_le (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : ContinuousFreeLoop P) (hlip : IsLipschitzLoop g γ) :
    loopLength h (f.comp γ) ≤ (L : ℝ) * loopLength g γ := by
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg L.coe_nonneg (loopLength_nonneg g γ))).mp
  rw [ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    loopLength_eq_riemannianCurveLength g γ hlip,
    loopLength_eq_riemannianCurveLength h (f.comp γ)
      (IsLipschitzLoop.postcompose g h f L hf γ hlip)]
  exact riemannianCurveLength_comp_le g h f L hf (loopLift γ) 0 1

omit connectedQ connectedP in
theorem leastArea_postcompose_le (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : ContinuousFreeLoop P) (hctr : IsContractibleLoop γ)
    (hlip : IsLipschitzLoop g γ) :
    leastArea h (f.comp γ) (hctr.postcompose f)
      (IsLipschitzLoop.postcompose g h f L hf γ hlip) ≤
        (L : ℝ) ^ 2 * leastArea g γ hctr hlip := by
  have hcomp (u : DiskCompetitor g γ) :
      leastArea h (f.comp γ) (hctr.postcompose f)
        (IsLipschitzLoop.postcompose g h f L hf γ hlip) ≤
          (L : ℝ) ^ 2 * diskArea g u.1.map := by
    exact (leastArea_le_competitor h (f.comp γ) (hctr.postcompose f)
      (IsLipschitzLoop.postcompose g h f L hf γ hlip)
      (DiskCompetitor.postcompose g h f L hf γ u)).trans
        (diskArea_lipschitz_comp g h f L hf u.1)
  by_cases hzero : (L : ℝ) = 0
  · obtain ⟨u⟩ := rfs_disk_competitor_exists g γ hctr hlip
    simpa only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using hcomp u
  · have hpos : 0 < (L : ℝ) ^ 2 := sq_pos_of_ne_zero hzero
    have hdiv : leastArea h (f.comp γ) (hctr.postcompose f)
        (IsLipschitzLoop.postcompose g h f L hf γ hlip) / (L : ℝ) ^ 2 ≤
          leastArea g γ hctr hlip := by
      apply le_csInf (competitorAreas_nonempty g γ hctr hlip)
      rintro _ ⟨u, rfl⟩
      apply (div_le_iff₀ hpos).mpr
      simpa only [mul_comm] using hcomp u
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

include finiteDimensionalE finiteDimensionalF boundarylessI boundarylessJ
  t2P t2Q compactP compactQ connectedQ in
omit connectedP in
theorem rfs_composed_family_regularization (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (ξ : FreeContractibleSphereClass P) (Γ : RegularRepresentative (I := I) ξ)
    {N : ℕ} (e : SmoothLoopEmbedding (I := J) (Q := Q) N) {η : ℝ} (hη : 0 < η) :
    ∃ Γ' : RegularRepresentative (I := J)
        (FreeHomotopyClass.map (contractibleLoopPostcompose f) ξ),
      (∀ k : Sphere 2, regularLeastArea h (Γ'.1 k) ≤
        (L : ℝ) ^ 2 * regularLeastArea g (Γ.1 k) + η) ∧
      HasContinuousSmoothLoopJets e Γ'.1 := by
  classical
  let Γc : C(Sphere 2, ContractibleContinuousLoop Q) :=
    (contractibleLoopPostcompose f).comp (contractibleRegularLoopInclusion.comp Γ.1)
  let Γ₀ : C(Sphere 2, ContinuousFreeLoop Q) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(ContractibleContinuousLoop Q,
      ContinuousFreeLoop Q)).comp Γc
  obtain ⟨V₀, hV₀, _⟩ := regularFamily_uniform_bounds g Γ.1
  let V := L * V₀
  have hV (k : Sphere 2) (x y : Surgery.Topology.Circle) :
      riemannianEDistOf h (Γ₀ k x) (Γ₀ k y) ≤ (V : ℝ≥0∞) * edist x y := by
    change riemannianEDistOf h (f ((Γ.1 k).1.toContinuousLoop x))
      (f ((Γ.1 k).1.toContinuousLoop y)) ≤ _
    exact (hf _ _).trans (by
      simpa only [V, ENNReal.coe_mul, mul_assoc] using
        mul_le_mul' (le_refl (L : ℝ≥0∞)) (hV₀ k x y))
  obtain ⟨Cq, _, hsmooth⟩ := rfs_loop_smoothing h e
  obtain ⟨ε₀, hε₀, S, hjets, hS, hhom, _, hSLip⟩ := hsmooth (Sphere 2) Γ₀
  obtain ⟨ρ, C, hρ, hC, hnearby⟩ := leastArea_nearby_upper_bound h
  let B : ℝ := (V : ℝ) + (Cq * V : ℝ≥0) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := min ρ (η / (C * B))
  have hδ : 0 < δ := lt_min hρ (div_pos hη (mul_pos hC hB))
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) ε₀ := Ioo_mem_nhdsGT hε₀
  obtain ⟨ε, hε, hclose⟩ :=
    (hevent.and (eventually_loopUniformDistance_lt h hS hδ)).exists
  obtain ⟨Fhom, _, hFhom⟩ := hhom ε hε
  have hctrS (k : Sphere 2) : IsContractibleLoop (S ε k).toContinuousLoop := by
    have hk := hFhom k (Γc k).2 1
    exact Eq.mp (congrArg IsContractibleLoop (Fhom.apply_one k)) hk
  let T : RegularFamily (I := J) (Q := Q) (Sphere 2) :=
    ⟨fun k => ⟨S ε k, hctrS k⟩, (S ε).continuous.subtype_mk _⟩
  have hhomT : ContinuousMap.Homotopic Γc (contractibleRegularLoopInclusion.comp T) := by
    refine ⟨{
      toFun := fun p => ⟨Fhom p, hFhom p.2 (Γc p.2).2 p.1⟩
      continuous_toFun := (map_continuous Fhom).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro k
      apply Subtype.ext
      exact Fhom.apply_zero k
    · intro k
      apply Subtype.ext
      exact Fhom.apply_one k
  have hclass : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp T) =
      FreeHomotopyClass.map (contractibleLoopPostcompose f) ξ := by
    refine ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhomT).symm.trans ?_
    simpa only [Γc, ← FreeHomotopyClass.map_mk] using
      congrArg (FreeHomotopyClass.map (contractibleLoopPostcompose f)) Γ.2
  refine ⟨⟨T, hclass⟩, ?_, ?_⟩
  · intro k
    have hlipS : IsLipschitzLoop h (S ε k).toContinuousLoop :=
      ⟨Cq * V, hSLip V hV ε hε k⟩
    have hlength : loopLength h (Γ₀ k) + loopLength h (S ε k).toContinuousLoop ≤ B := by
      have h₀ := loopLength_le_of_lipschitz h (Γ₀ k) V (hV k)
      have h₁ := loopLength_le_of_lipschitz h (S ε k).toContinuousLoop (Cq * V)
        (hSLip V hV ε hε k)
      exact (add_le_add h₀ h₁).trans (le_add_of_nonneg_right zero_le_one)
    have herror : C * loopUniformDistance h (Γ₀ k) (S ε k).toContinuousLoop *
        (loopLength h (Γ₀ k) + loopLength h (S ε k).toContinuousLoop) ≤ η := by
      calc
        _ ≤ C * δ * (loopLength h (Γ₀ k) + loopLength h (S ε k).toContinuousLoop) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hclose k).le hC.le)
            (add_nonneg (loopLength_nonneg h _) (loopLength_nonneg h _))
        _ ≤ C * δ * B := mul_le_mul_of_nonneg_left hlength (mul_nonneg hC.le hδ.le)
        _ ≤ η := by
          have hh := (le_div_iff₀ (mul_pos hC hB)).mp
            (show δ ≤ η / (C * B) from min_le_right _ _)
          nlinarith
    have harea := hnearby (Γ₀ k) (S ε k).toContinuousLoop (Γc k).2 (hctrS k)
      ⟨V, hV k⟩ hlipS ((hclose k).trans_le (min_le_left _ _))
    have hcomp := leastArea_postcompose_le g h f L hf (Γ.1 k).1.toContinuousLoop
      (Γ.1 k).2 ((Γ.1 k).1.isLipschitz g)
    exact harea.trans (add_le_add hcomp herror)
  · simpa only [HasContinuousSmoothLoopJets, HasContinuousSmoothJets, T,
      ContinuousMap.coe_mk] using hjets ε hε

theorem rfs_width_lipschitz (g : SmoothRiemannianMetric I P)
    (h : SmoothRiemannianMetric J Q) (f : C(P, Q)) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (ξ : FreeContractibleSphereClass P) :
    classWidth h (FreeHomotopyClass.map (contractibleLoopPostcompose f) ξ) ≤
      (L : ℝ) ^ 2 * classWidth g ξ := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := J) (Q := Q)
  have hfamily (Γ : RegularRepresentative (I := I) ξ) :
      classWidth h (FreeHomotopyClass.map (contractibleLoopPostcompose f) ξ) ≤
        (L : ℝ) ^ 2 * familyMaximum g Γ.1 := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨Γ', hpoint, _⟩ := rfs_composed_family_regularization g h f L hf ξ Γ e hη
    apply (classWidth_le_familyMaximum h _ Γ').trans
    obtain ⟨k, hk⟩ := familyMaximum_attained h Γ'.1
    rw [hk]
    exact (hpoint k).trans (add_le_add
      (mul_le_mul_of_nonneg_left (regularLeastArea_le_familyMaximum g Γ.1 k)
        (sq_nonneg (L : ℝ))) le_rfl)
  by_cases hzero : (L : ℝ) = 0
  · obtain ⟨Γ⟩ := regularRepresentative_nonempty (I := I) ξ
    simpa only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using hfamily Γ
  · have hpos : 0 < (L : ℝ) ^ 2 := sq_pos_of_ne_zero hzero
    have hdiv : classWidth h (FreeHomotopyClass.map (contractibleLoopPostcompose f) ξ) /
        (L : ℝ) ^ 2 ≤ classWidth g ξ := by
      apply le_csInf (representativeMaxima_nonempty g ξ)
      rintro _ ⟨Γ, rfl⟩
      apply (div_le_iff₀ hpos).mpr
      simpa only [mul_comm] using hfamily Γ
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
