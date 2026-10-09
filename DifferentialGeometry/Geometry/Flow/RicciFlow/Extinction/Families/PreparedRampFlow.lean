import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import DifferentialGeometry.Analysis.Calculus.TimeJet.Matching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductFamilyExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLiftInvariants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductHeightContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCylinderTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAngleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampCurvatureBound

section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  {P : Type*} [TopologicalSpace P]

private theorem continuous_initial_product_jets
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (γ : P → Surgery.Topology.Circle → Q)
    (hs : ∀ p, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => γ p x))
    (hj : ∀ m : ℕ, Continuous (fun q : P × ℝ =>
      iteratedDeriv m (fun x : ℝ => e.map (γ q.1 x)) q.2)) (a : ℝ) (m : ℕ) :
    Continuous (fun q : P × ℝ =>
      iteratedDeriv m (fun x => productEmbeddedCoordinates e (initialRamp (γ q.1)) x a) q.2) := by
  let cir : ℝ → ℂ := fun x => Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)
  have hcir : ContDiff ℝ ∞ cir :=
    Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
  have heq (p : P) : (fun x => productEmbeddedCoordinates e (initialRamp (γ p)) x a) =
      fun x : ℝ => (e.map (γ p x), cir x) := by
    funext x
    apply Prod.ext
    · rfl
    · simp only [productEmbeddedCoordinates, initialRamp, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, Circle.coe_exp, cir]
      congr 1
      push_cast
      ring
  have hjet (p : P) (x : ℝ) :
      iteratedDeriv m (fun x => productEmbeddedCoordinates e (initialRamp (γ p)) x a) x =
        (iteratedDeriv m (fun x : ℝ => e.map (γ p x)) x,
          iteratedDeriv m cir x) := by
    rw [heq]
    have hf := (e.smooth.comp (hs p)).contDiff
    simpa only [iteratedDerivWithin_univ, Function.comp_def] using
      DifferentialGeometry.Analysis.iteratedDerivWithin_prodMk
        (hf.of_le (by exact_mod_cast le_top)).contDiffAt.contDiffWithinAt
        (hcir.of_le (by exact_mod_cast le_top)).contDiffAt.contDiffWithinAt
        uniqueDiffOn_univ (mem_univ x) (n := m)
  exact ((hj m).prodMk
    ((hcir.continuous_iteratedDeriv m (by exact_mod_cast le_top)).comp continuous_snd)).congr
      (fun q => (hjet q.1 q.2).symm)

theorem continuous_initialRamp
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (γ : P → Surgery.Topology.Circle → Q)
    (hs : ∀ p, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => γ p x))
    (hj : ∀ m : ℕ, Continuous (fun q : P × ℝ =>
      iteratedDeriv m (fun x : ℝ => e.map (γ q.1 x)) q.2)) (a : ℝ) :
    @Continuous P (ProductCurve Q) inferInstance (smoothProductInitialTopology e a)
      (fun p => initialRamp (γ p)) := by
  let : TopologicalSpace (ProductCurve Q) := smoothProductInitialTopology e a
  apply continuous_iff_continuousAt.mpr
  intro p
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro U ⟨c, m, ε, hε, rfl⟩ ⟨ρ₀, hρ₀, hb₀⟩
  have hjet := continuous_initial_product_jets e γ hs hj a m
  let J : P → C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin d) × ℂ) := fun q =>
    ⟨fun x => iteratedDeriv m (fun y => productEmbeddedCoordinates e (initialRamp (γ q)) y a) x,
      hjet.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hJ : Continuous J := ContinuousMap.continuous_of_continuous_uncurry _
    (hjet.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hgap : 0 < ε - ρ₀ := sub_pos.mpr hρ₀
  have hnear := hJ.continuousAt.eventually (Metric.ball_mem_nhds (J p) hgap)
  filter_upwards [hnear] with q hq
  have hdist : dist (J q) (J p) < ε - ρ₀ := hq
  refine ⟨dist (J q) (J p) + ρ₀, by linarith, fun x hx => ?_⟩
  have hpoint : ‖J q ⟨x, hx⟩ - J p ⟨x, hx⟩‖ ≤ dist (J q) (J p) := by
    simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := J q) (g := J p) ⟨x, hx⟩
  have htriangle := norm_add_le
    (J q ⟨x, hx⟩ - J p ⟨x, hx⟩)
    (J p ⟨x, hx⟩ - iteratedDeriv m (fun y => productEmbeddedCoordinates e c y a) x)
  rw [sub_add_sub_cancel] at htriangle
  exact htriangle.trans (add_le_add hpoint (hb₀ x hx))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {a b : ℝ}

theorem exists_continuous_prepared_product_family
    (B : SmoothMetricWindow (I := I) (M := Q) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) P)
    (hsmooth : HasContinuousSmoothLoopJets e prepared) :
    ∃ dtime : ℝ, a < dtime ∧ dtime ≤ b ∧
      ∃ solutions : P → ProductCurve Q,
        @Continuous P (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a dtime)) solutions ∧
        ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a dtime) ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z) := by
  have hs : ∀ p, (initialRamp ((prepared p).1)).SmoothOn (I := I) {a} := by
    intro p
    have h := initialRamp_smoothOn (I := I) (Q := Q) (hsmooth.1 p)
    exact ⟨h.1.mono (prod_mono Subset.rfl (subset_univ _)),
      h.2.mono (prod_mono Subset.rfl (subset_univ _))⟩
  have hi : ∀ p, (initialRamp ((prepared p).1)).ImmersedOn (I := I) {a} := by
    intro p x t ht
    exact initialRamp_immersedOn ((prepared p).1) x t trivial
  obtain ⟨dtime, had, hdb, solutions, hcont, hsol⟩ :=
    exists_continuous_product_solution_family_of_compact
      B lambda hlambda e (fun p => initialRamp ((prepared p).1)) hs hi
      (fun m => continuous_initial_product_jets e
        (fun p => (prepared p).1.toContinuousLoop) hsmooth.1 hsmooth.2 a m)
  refine ⟨dtime, had, hdb, solutions, hcont, ?_⟩
  intro p
  exact ⟨hsol p |>.1, fun z => by simpa [initialRamp] using (hsol p).2 z⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]

theorem exists_uniform_initial_angle_lower_bound
    (g : ℝ → SmoothRiemannianMetric I Q) {lambda : ℝ} (hlambda : 0 < lambda)
    (a : ℝ) (prepared : RegularFamily (I := I) (Q := Q) P)
    (solutions : P → ProductCurve Q)
    (hsmooth : ∀ p, (solutions p).SmoothOn (I := I) {a})
    (hmap : ∀ p z, (solutions p).map z a = ((prepared p).1 z, z)) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ p x, u₀ ≤ (solutions p).angle g lambda x a := by
  obtain ⟨V, hV, hbound⟩ := regularFamily_uniform_speed (g a) prepared
  have hycont (p : P) : Continuous (fun x => (solutions p).y x a) :=
    (contDiffOn_univ.mp ((hsmooth p).2.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x _ => ⟨mem_univ x, mem_singleton a⟩))).continuous
  have hyderiv (p : P) (x : ℝ) : deriv (fun z => (solutions p).y z a) x = 1 := by
    have h := (solutions p).deriv_y_eq_of_snd_map_eq (t := a)
      (initialRamp ((prepared p).1)) (fun z => congrArg Prod.snd (hmap p z)) x
      (hycont p).continuousAt continuousAt_id
    simpa only [initialRamp, deriv_id''] using h
  have hspeed (p : P) (x : ℝ) :
      (solutions p).speed g lambda x a =
        (initialRamp ((prepared p).1)).speed (fun _ => g a) lambda x a := by
    have hM : (fun y : ℝ => ((solutions p).map (y : Surgery.Topology.Circle) a).1) =
        fun y : ℝ => ((initialRamp ((prepared p).1)).map (y : Surgery.Topology.Circle) a).1 := by
      funext y
      exact congrArg Prod.fst (hmap p (y : Surgery.Topology.Circle))
    have hxM : ((solutions p).map (x : Surgery.Topology.Circle) a).1 =
        ((initialRamp ((prepared p).1)).map (x : Surgery.Topology.Circle) a).1 :=
      congrArg Prod.fst (hmap p (x : Surgery.Topology.Circle))
    have hd : deriv (fun z => (solutions p).y z a) x =
        deriv (fun z => (initialRamp ((prepared p).1)).y z a) x := by
      simpa only [initialRamp, deriv_id''] using hyderiv p x
    simp only [ProductCurve.speed, ProductCurve.inner, ProductCurve.X,
      ProductCurve.projection, CurveMap.lift, CurveMap.X]
    rw [hM, hxM, hd]
    rfl
  have hspeed_pos (p : P) (x : ℝ) : 0 < (solutions p).speed g lambda x a := by
    rw [hspeed]
    exact initialRamp_speed_pos (g a) hlambda ((prepared p).1) x a
  have hspeed_bound (p : P) (x : ℝ) : (solutions p).speed g lambda x a ≤ V + lambda := by
    obtain ⟨y, hy, hxy⟩ := ((solutions p).speed_periodic g lambda
      (hsmooth p) a (mem_singleton a)).exists_mem_Ico₀ zero_lt_one x
    rw [hxy, hspeed]
    apply (initialRamp_speed_le (g a) (prepared p).1.toContinuousLoop lambda y a).trans
    rw [abs_of_pos hlambda]
    simpa only [add_comm] using add_le_add_right (hbound p ⟨y, hy.1, hy.2.le⟩) lambda
  refine ⟨lambda * (V + lambda)⁻¹, mul_pos hlambda (inv_pos.mpr (by linarith)), ?_⟩
  intro p x
  rw [ProductCurve.angle_eq, hyderiv, mul_one]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (hspeed_pos p x) (hspeed_bound p x)) hlambda.le

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompactSpace Q] {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_prepared_ramp_family
    (B : SmoothMetricWindow (I := I) (M := Q) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (prepared : RegularFamily (I := I) (Q := Q) P)
    (hsmooth : HasContinuousSmoothLoopJets e prepared) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → ProductCurve Q,
      @Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a d)) solutions ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a d) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a d) ∧
        (solutions p).degree = 1 ∧
        ∀ z, (solutions p).map z a = ((prepared p).1 z, z) := by
  let : T2Space Q := e.isClosedEmbedding.isEmbedding.t2Space
  obtain ⟨T, haT, hTb, solutions, hcont, hsol⟩ :=
    exists_continuous_prepared_product_family B lambda hlambda e prepared hsmooth
  have hycont (p : P) : Continuous (fun x => (solutions p).y x a) :=
    (contDiffOn_univ.mp ((hsol p).1.smooth.2.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x _ => ⟨mem_univ x, le_rfl, haT.le⟩))).continuous
  have hyderiv (p : P) (x : ℝ) : deriv (fun z => (solutions p).y z a) x = 1 := by
    have h := (solutions p).deriv_y_eq_of_snd_map_eq (t := a) (initialRamp ((prepared p).1))
      (fun z => congrArg Prod.snd ((hsol p).2 z)) x (hycont p).continuousAt continuousAt_id
    simpa only [initialRamp, deriv_id''] using h
  have hramp (p : P) : (solutions p).IsRampOn B.family.metric lambda {a} := by
    have hi : (solutions p).ImmersedOn (I := I) {a} := by
      intro x t ht
      rw [mem_singleton_iff.mp ht]
      exact (hsol p).1.immersed x a ⟨le_rfl, haT.le⟩
    refine ⟨hi, ?_⟩
    intro x t ht
    rw [mem_singleton_iff.mp ht, (solutions p).angle_eq, hyderiv]
    exact mul_pos (mul_pos hlambda (inv_pos.mpr
      ((solutions p).speed_pos_of_immersedOn B.family.metric lambda hlambda hi x a
        (mem_singleton a)))) zero_lt_one
  have hdegree (p : P) : (solutions p).degree = 1 := by
    have h := (solutions p).degree_eq_of_snd_map_eq (t := a) (initialRamp ((prepared p).1))
      (hycont p).continuousOn continuousOn_id (fun z => congrArg Prod.snd ((hsol p).2 z))
    exact h
  have hdy := ProductCurve.continuousOn_deriv_y_of_smoothProductCylinder e haT solutions
    hcont (fun p => (hsol p).1.smooth)
  obtain ⟨δ, hδ, hδT, hramps⟩ :=
    ProductCurve.exists_forall_isRampOn_Icc_of_continuousOn_deriv solutions
      B.family.metric hlambda haT hramp hdy
  have had : a < a + δ := lt_add_of_pos_right a hδ
  have hdT : a + δ ≤ T := by linarith
  refine ⟨a + δ, had, hdT.trans hTb, solutions, ?_, ?_⟩
  · exact smoothProductCylinderTopology_continuous_mono e
      (Icc_subset_Icc le_rfl hdT) (uniqueDiffOn_Icc had) (uniqueDiffOn_Icc haT)
      solutions hcont (fun p => (hsol p).1.smooth)
  · intro p
    exact ⟨(hsol p).1.mono_Icc le_rfl hdT had, hramps p, hdegree p, (hsol p).2⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_prepared_ramp_family_angle_lower_bound
    (B : RicciBackground (I := I) (M := Q) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (prepared : RegularFamily (I := I) (Q := Q) P)
    (hsmooth : HasContinuousSmoothLoopJets e prepared) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → ProductCurve Q,
      @Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a d)) solutions ∧
      (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a d) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a d) ∧
        (solutions p).degree = 1 ∧
        ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
      ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ p x t, t ∈ Icc a d →
        u₀ * Real.exp (-B.B₀ * (t - a)) ≤
          (solutions p).angle B.family.metric lambda x t := by
  obtain ⟨d, had, hdb, solutions, hcont, hsol⟩ :=
    exists_continuous_prepared_ramp_family B.toSmoothMetricWindow lambda hlambda e prepared hsmooth
  have hstart (p : P) : (solutions p).SmoothOn (I := I) {a} := by
    refine ⟨(hsol p).1.smooth.1.mono ?_, (hsol p).1.smooth.2.mono ?_⟩ <;>
      exact Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ⟨le_rfl, had.le⟩)
  obtain ⟨u₀, hu₀, hangle⟩ := exists_uniform_initial_angle_lower_bound
    B.family.metric hlambda a prepared solutions hstart (fun p => (hsol p).2.2.2)
  refine ⟨d, had, hdb, solutions, hcont, hsol, u₀, hu₀, ?_⟩
  intro p x t ht
  exact (solutions p).angle_lower_bound_of_isRampOn B lambda hlambda had
    (Icc_subset_Icc le_rfl hdb) (hsol p).1 (hsol p).2.1 u₀ (hangle p) x t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_prepared_ramp_family_curvature_bound
    (B : RicciBackground (I := I) (M := Q) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (prepared : RegularFamily (I := I) (Q := Q) P)
    (hsmooth : HasContinuousSmoothLoopJets e prepared) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → ProductCurve Q,
      @Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a d)) solutions ∧
      (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a d) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a d) ∧
        (solutions p).degree = 1 ∧
        ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
      (∃ u₀ : ℝ, 0 < u₀ ∧ ∀ p x t, t ∈ Icc a d →
        u₀ * Real.exp (-B.B₀ * (t - a)) ≤
          (solutions p).angle B.family.metric lambda x t) ∧
      ∀ p x t, t ∈ Icc a d →
        (solutions p).curvature B.family.metric lambda x t ≤
          (solutions p).curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t := by
  obtain ⟨d, had, hdb, solutions, hcont, hsol, hangle⟩ :=
    exists_continuous_prepared_ramp_family_angle_lower_bound B lambda hlambda e prepared hsmooth
  refine ⟨d, had, hdb, solutions, hcont, hsol, hangle, ?_⟩
  intro p x t ht
  exact (solutions p).curvature_le_curvatureEnvelope B lambda hlambda had
    (Icc_subset_Icc le_rfl hdb) (hsol p).1 (hsol p).2.1 x t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end
end
