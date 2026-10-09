import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftFrame
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftBound
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelTransportApplications
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Metric.LocalIsometryCovering
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative

/-!
# Euclidean covers of complete finite flat surfaces

The finite transverse Jacobi equation gives a globally Euclidean Fermi map. Completeness of its
Euclidean domain gives actual path lifts and the covering property without upgrading the metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteFlatSurface

private theorem scalarFlatJacobi_nonneg {j : ℝ → ℝ} (hc : Continuous j) (h0 : j 0 = 1)
    (hd0 : deriv j 0 = 0)
    (hd : ∀ s, 0 < j s → HasDerivAt j (deriv j s) s ∧
      HasDerivAt (deriv j) 0 s) {s : ℝ} (hs : 0 ≤ s) : j s = 1 := by
  have hpos : ∀ t ∈ Ico 0 (s + 1), 0 < j t := by
    have hb := DifferentialGeometry.Analysis.scalarJacobi_mem_Icc
      (k := fun t => 0) (Λ := 0) (ρ := s + 1) (by norm_num) (by simp)
      hc.continuousOn h0 hd0
      (fun t ht hp => by simpa using hd t hp) (by intro t ht; simp)
    intro t ht
    linarith [(hb t ht).1]
  have hb := DifferentialGeometry.Analysis.scalarJacobi_bounds_of_pos
    (k := fun t => 0) (Λ := 0) (T := s + 1) (by norm_num) h0 hd0
    (fun t ht => by simpa using hd t (hpos t ht)) (by intro t ht; simp) hpos
  have h := hb s ⟨hs, by linarith⟩
  simp only [zero_mul, zero_div, sub_zero] at h
  exact le_antisymm h.2 h.1

private theorem scalarFlatJacobi {j : ℝ → ℝ} (hc : Continuous j) (h0 : j 0 = 1)
    (hd0 : deriv j 0 = 0)
    (hd : ∀ s, 0 < j s → HasDerivAt j (deriv j s) s ∧
      HasDerivAt (deriv j) 0 s) (s : ℝ) : j s = 1 := by
  by_cases hs : 0 ≤ s
  · exact scalarFlatJacobi_nonneg hc h0 hd0 hd hs
  let k : ℝ → ℝ := fun t => j (-t)
  have hkD : ∀ t, 0 < k t → HasDerivAt k (-deriv j (-t)) t := by
    intro t ht
    simpa only [k, Function.comp_def, mul_neg_one] using
      (hd (-t) ht).1.comp t (hasDerivAt_neg t)
  have hk0 : deriv k 0 = 0 := by
    rw [(hkD 0 (by simp [k, h0])).deriv]
    simp [hd0]
  have hkDD : ∀ t, 0 < k t →
      HasDerivAt k (deriv k t) t ∧ HasDerivAt (deriv k) 0 t := by
    intro t ht
    have hkt := hkD t ht
    refine ⟨hkt.deriv ▸ hkt, ?_⟩
    have heq : deriv k =ᶠ[𝓝 t] fun u => -deriv j (-u) := by
      have hp : ∀ᶠ u in 𝓝 t, 0 < k u :=
        ((hc.comp continuous_neg).continuousAt).eventually (lt_mem_nhds ht)
      filter_upwards [hp] with u hu
      exact (hkD u hu).deriv
    have hh := ((hd (-t) ht).2.comp t (hasDerivAt_neg t)).neg
    simpa only [Function.comp_def, zero_mul, neg_zero] using hh.congr_of_eventuallyEq heq
  have h := scalarFlatJacobi_nonneg (hc.comp continuous_neg) (by simpa [k] using h0)
    hk0 hkDD (s := -s) (by linarith)
  simpa [k] using h

open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

variable (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E
  (TangentSpace I : M → Type _))

theorem transverseSpeedSq_eq_one_of_flat (hr : 3 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (hdom : g.geodesicFlowDomain = univ) (p : TangentBundle I M)
    (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E}
    (hcont : Continuous (fun t =>
      (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)))
    (hunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ξ t)
      (g.geodesicFlow p t).snd = 0)
    (hflat : ∀ x (v w : TangentSpace I x), g.sectionalCurvature x v w = 0)
    (t h : ℝ) : transverseSpeedSq g p ξ (t, h) = 1 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hV : ∀ t ∈ (univ : Set ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t := by
    intro u hu
    exact contMDiffAt_unitNormal_dim_two g hr1 hdim p
      (fun u => by rw [hdom]; exact mem_univ _) hp isOpen_univ hcont.continuousOn
      (fun u hu => hunit u) (fun u hu => hperp u) hu
  obtain ⟨hGc, hode⟩ := transverseShift_jacobi g hr hdim hdom p hp isOpen_univ
    hcont.continuousOn (fun u hu => hunit u) (fun u hu => hperp u) (mem_univ t)
  obtain ⟨hj0, hd0⟩ := deriv_sqrt_transverseSpeedSq_zero g hr2 hdom p hp isOpen_univ
    hV (fun u hu => hperp u) (mem_univ t)
  have hj : Real.sqrt (transverseSpeedSq g p ξ (t, h)) = 1 :=
    scalarFlatJacobi (Real.continuous_sqrt.comp hGc) hj0 hd0 (fun s hs => by
      obtain ⟨hd, hdd⟩ := hode s (Real.sqrt_pos.mp hs)
      refine ⟨hd, ?_⟩
      have hh := hflat (transverseShift g p ξ (t, s))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u => transverseShift g p ξ (u, s)) t 1)
        (g.geodesicFlow (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M) s).snd
      rw [hh, zero_mul, neg_zero] at hdd
      simpa only [Function.comp_def] using hdd) h
  have hpG : 0 ≤ transverseSpeedSq g p ξ (t, h) := by
    have hjpos : 0 < Real.sqrt (transverseSpeedSq g p ξ (t, h)) := by rw [hj]; norm_num
    exact (Real.sqrt_pos.mp hjpos).le
  have hs := Real.sq_sqrt hpG
  rw [hj, one_pow] at hs
  exact hs.symm

private theorem bilinear_eq_inner_of_basis {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i j, B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = if i = j then 1 else 0)
    (v w : EuclideanSpace ℝ (Fin n)) : B v w = inner ℝ v w := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : B.toLinearMap = (innerSL ℝ).toLinearMap := by
    apply b.ext
    intro i
    have hi : (B (b i)).toLinearMap = (innerSL ℝ (b i)).toLinearMap := by
      apply b.ext
      intro j
      exact (hB i j).trans ((EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j).symm
    exact DFunLike.ext _ _ fun x => congrArg (fun L => L x) hi
  exact congrArg (fun L => L v w) he

section Plane

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)]
  [IsRiemannianManifold (𝓡 2) Z] [CompleteSpace Z]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local instance planeDimension : NeZero (Module.finrank ℝ E2) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
  (TangentSpace (𝓡 2) : Z → Type _))

theorem exists_flatFermiMap (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    (hflat : ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0)
    (q : Z) : ∃ f : E2 → Z, f 0 = q ∧ ContMDiff (𝓡 2) (𝓡 2) r f ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) r f ∧
      ∀ x v w, k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
        (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdom := k.geodesicFlowDomain_eq_univ hr2 hnorm
  have hdq : Module.finrank ℝ (TangentSpace (𝓡 2) q) = 2 := by
    change Module.finrank ℝ E2 = 2
    exact finrank_euclideanSpace_fin
  obtain ⟨v₀, hv₀⟩ := exists_orthonormal_of_pos (k.inner q) (k.symm q) (k.pos q)
  let v : Fin 2 → E2 := fun i => v₀ (Fin.cast hdq.symm i)
  have hv : ∀ i j, k.inner q (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    simpa only [v, Fin.cast_inj] using hv₀ (Fin.cast hdq.symm i) (Fin.cast hdq.symm j)
  let p : TangentBundle (𝓡 2) Z := ⟨q, v 0⟩
  have hp : k.inner p.proj p.snd p.snd = 1 := by simp [p, hv]
  obtain ⟨ξ, hξ0, hξpar, hξc, hξ⟩ := exists_parallel_unit_normal_geodesicFlow k hr1 hnorm p
    (v 1) (by simp [p, hv]) (by simp [p, hv])
  have hV : ∀ t ∈ (univ : Set ℝ), ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2).tangent r
      (fun t => (⟨(k.geodesicFlow p t).proj, ξ t⟩ : TangentBundle (𝓡 2) Z)) t := by
    intro t ht
    exact contMDiffAt_unitNormal_dim_two k hr1 (by simp) p
      (fun t => by rw [hdom]; exact mem_univ _) hp isOpen_univ hξc.continuousOn
      (fun t ht => (hξ t).1) (fun t ht => (hξ t).2) ht
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let f : E2 → Z := shiftChart k p ξ b
  have hf : ContMDiff (𝓡 2) (𝓡 2) r f := by
    have hc := contMDiffOn_shiftChart k b hr1 hdom p hV
    simpa only [Set.prod_univ, Set.preimage_univ, contMDiffOn_univ] using hc
  have hf0 : f 0 = q := by
    change transverseShift k p ξ (finTwoCoords b 0) = q
    rw [map_zero]
    change (k.geodesicFlow
      (⟨(k.geodesicFlow p 0).proj, ξ 0⟩ : TangentBundle (𝓡 2) Z) 0).proj = q
    rw [k.geodesicFlow_zero hr1, k.geodesicFlow_zero hr1]
  have hi : ∀ x v w, k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
      (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w := by
    intro x u w
    apply bilinear_eq_inner_of_basis (shiftCoeff k p ξ b x) ?_ u w
    obtain ⟨h00, h01, h11⟩ := shiftCoeff_structure k b hr2 hdom p isOpen_univ hV
      (fun t ht => (hξ t).1) (fun t ht => (hξ t).2) (y := x) (by simp)
    have hG := transverseSpeedSq_eq_one_of_flat k hr (by simp) hdom p hp hξc
      (fun t => (hξ t).1) (fun t => (hξ t).2) hflat
      (finTwoCoords b x).1 (finTwoCoords b x).2
    rw [Prod.mk.eta] at hG
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00.trans hG
    · exact h01
    · exact (k.symm _ _ _).trans h01
    · exact h11
  have hinv : ∀ x, (mfderiv (𝓡 2) (𝓡 2) f x).IsInvertible := by
    intro x
    have hker : Function.Injective (mfderiv (𝓡 2) (𝓡 2) f x) := by
      apply LinearMap.ker_eq_bot.mp
      rw [LinearMap.ker_eq_bot']
      intro u hu
      have hh := hi x u u
      have hz : mfderiv (𝓡 2) (𝓡 2) f x u = 0 := hu
      have hzero : k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x u)
          (mfderiv (𝓡 2) (𝓡 2) f x u) = 0 :=
        (congrArg (fun v => k.inner (f x) v v) hz).trans (by simp)
      exact inner_self_eq_zero.mp (hh.symm.trans hzero)
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 2) (𝓡 2) f x).toLinearMap
      ⟨hker, LinearMap.injective_iff_surjective.mp hker⟩).toContinuousLinearEquiv, rfl⟩
  have hloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) r f := by
    have hc := hf.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv isOpen_univ
      (by exact_mod_cast hr1) (fun x hx => hinv x)
    exact fun x => hc ⟨x, mem_univ x⟩
  exact ⟨f, hf0, hf, hloc, hi⟩

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
omit [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] in
private theorem lift_contMDiff_one {f : E2 → Z}
    (hf : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f) {γ : ℝ → Z}
    {z : E2} {a t : ℝ} {η : ℝ → E2}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc a t))
    (hη : DifferentialGeometry.IsPathLiftOn f γ z a t η) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 η (Icc a t) := by
  intro s hs
  obtain ⟨d, hd, hfd⟩ := hf (η s)
  have hγd : γ s ∈ d.target := by
    rw [← hη.2.2 s hs, hfd hd]
    exact d.map_source hd
  have hnear : ∀ᶠ u in 𝓝[Icc a t] s, η u ∈ d.source :=
    (hη.1 s hs).preimage_mem_nhdsWithin (d.open_source.mem_nhds hd)
  have heq : η =ᶠ[𝓝[Icc a t] s] d.symm ∘ γ := by
    filter_upwards [hnear, self_mem_nhdsWithin] with u hu huc
    exact (d.left_inv hu).symm.trans
      (congrArg d.symm ((hfd hu).symm.trans (hη.2.2 u huc)))
  exact ((d.contMDiffOn_invFun.contMDiffAt (d.open_target.mem_nhds hγd)).comp_contMDiffWithinAt
    s (hγ s hs)).congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hs)

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
private theorem finite_pathELength_ne_top
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    {γ : ℝ → Z} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc 0 1)) :
    Manifold.pathELength (𝓡 2) γ 0 1 ≠ ⊤ := by
  let v : (t : ℝ) → TangentSpace (𝓡 2) (γ t) :=
    fun t => mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) γ (Icc 0 1) t 1
  have hc : ContinuousOn (fun t => Real.sqrt (k.inner (γ t) (v t) (v t))) (Icc 0 1) := by
    let cg := k.toContinuousRiemannianMetric
    let metricBundle : RiemannianBundle (TangentSpace (𝓡 2) : Z → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    have hv := continuousOn_velocityWithin_totalSpace_of_contMDiffOn zero_lt_one hγ
    exact (hv.inner_bundle hv).sqrt
  obtain ⟨s, hs, hbound⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hc
  let L : ℝ := Real.sqrt (k.inner (γ s) (v s) (v s))
  have hle : Manifold.pathELength (𝓡 2) γ 0 1 ≤ ENNReal.ofReal L := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    calc
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal L := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Ioo
        intro t ht
        have hv : v t = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 := by
          exact congrArg (fun A : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
              TangentSpace (𝓡 2) (γ t) => A 1)
            (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (f := γ)
              (Icc_mem_nhds ht.1 ht.2))
        rw [hnorm]
        exact ENNReal.ofReal_le_ofReal (by
          have hh := hbound (Ioo_subset_Icc_self ht)
          change Real.sqrt (k.inner (γ t) (v t) (v t)) ≤ L at hh
          exact (congrArg (fun w => Real.sqrt (k.inner (γ t) w w)) hv).symm.le.trans hh)
      _ = ENNReal.ofReal L := by simp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
omit [IsManifold (𝓡 2) ∞ Z] in
private theorem lifted_pathELength_eq {f : E2 → Z}
    (hf : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f)
    (hD : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ = ‖(v : E2)‖ₑ)
    {γ : ℝ → Z} {z : E2} {a t : ℝ} {η : ℝ → E2}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc a t))
    (hη : DifferentialGeometry.IsPathLiftOn f γ z a t η) :
    Manifold.pathELength (𝓡 2) η a t = Manifold.pathELength (𝓡 2) γ a t := by
  have hηc := lift_contMDiff_one hf hγ hη
  have hηD : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo a t),
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) η s :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
      ((hηc s (Ioo_subset_Icc_self hs)).mdifferentiableWithinAt one_ne_zero).mdifferentiableAt
        (Icc_mem_nhds hs.1 hs.2)
  rw [← Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f hηD
    (Eventually.of_forall fun s => (hf (η s)).mdifferentiableAt one_ne_zero)
    (Eventually.of_forall fun s => hD _ _)]
  exact Manifold.pathELength_congr fun s hs => hη.2.2 s hs

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
private theorem forall_finite_path_lift
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    {f : E2 → Z} (hf : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f)
    (hD : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ = ‖(v : E2)‖ₑ)
    (γ : ℝ → Z) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc 0 1))
    (z : E2) (hz : f z = γ 0) :
    ∃ η : ℝ → E2, ContinuousOn η (Icc 0 1) ∧ η 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f (η t) = γ t := by
  have hfin := finite_pathELength_ne_top k hnorm hγ
  let L := (Manifold.pathELength (𝓡 2) γ 0 1).toReal
  obtain ⟨η, hη⟩ := DifferentialGeometry.exists_isPathLiftOn_of_isCompact
    hf.isLocalHomeomorph zero_le_one hγ.continuousOn hz (isCompact_closedBall z L) (by
      intro t ht η hη
      have hγt := hγ.mono (Icc_subset_Icc le_rfl ht.2)
      have hηc := lift_contMDiff_one hf hγt hη
      have he : edist z (η t) ≤ ENNReal.ofReal L := by
        calc edist z (η t) = Manifold.riemannianEDist (𝓡 2) z (η t) :=
            IsRiemannianManifold.out z (η t)
          _ ≤ Manifold.pathELength (𝓡 2) η 0 t :=
            Manifold.riemannianEDist_le_pathELength hηc hη.2.1 rfl ht.1
          _ = Manifold.pathELength (𝓡 2) γ 0 t := lifted_pathELength_eq hf hD hγt hη
          _ ≤ Manifold.pathELength (𝓡 2) γ 0 1 := Manifold.pathELength_mono le_rfl ht.2
          _ = ENNReal.ofReal L := (ENNReal.ofReal_toReal hfin).symm
      exact (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).mp
        (by simpa only [edist_dist, dist_comm] using he))
  exact ⟨η, hη⟩

variable [ConnectedSpace Z]

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
private theorem surjective_finite_localIsometry
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    {f : E2 → Z} (hf : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f)
    (hD : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ = ‖(v : E2)‖ₑ) : Surjective f := by
  have hclosed : IsClosed (range f) := by
    apply closure_subset_iff_isClosed.mp
    intro q hq
    let c := extChartAt (𝓡 2) q
    obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target q)
      (c q) (mem_extChartAt_target q)
    let V := c.source ∩ c ⁻¹' Metric.ball (c q) a
    have hVo : IsOpen V := (continuousOn_extChartAt q).isOpen_inter_preimage
      (isOpen_extChartAt_source q) Metric.isOpen_ball
    have hqV : q ∈ V := ⟨mem_extChartAt_source q, Metric.mem_ball_self ha⟩
    obtain ⟨y, hy, p, rfl⟩ := mem_closure_iff.mp hq V hVo hqV
    let γ : ℝ → Z := fun s => c.symm (c (f p) + s • (c q - c (f p)))
    have hcγ : ∀ s ∈ Icc (0 : ℝ) 1, c (f p) + s • (c q - c (f p)) ∈ c.target := by
      intro s hs
      exact hball ((convex_ball (c q) a).add_smul_sub_mem hy.2
        (Metric.mem_ball_self ha) hs)
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc 0 1) := by
      have hline : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1
          (fun s : ℝ => c (f p) + s • (c q - c (f p))) :=
        (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
      exact (contMDiffOn_extChartAt_symm (I := 𝓡 2) (n := 1) q).comp
        hline.contMDiffOn hcγ
    have hγ0 : γ 0 = f p := by
      simpa only [γ, zero_smul, add_zero] using c.left_inv hy.1
    have hγ1 : γ 1 = q := by
      simpa only [γ, one_smul, add_sub_cancel] using extChartAt_to_inv q
    obtain ⟨η, hηc, hη0, hη⟩ := forall_finite_path_lift k hnorm hf hD γ hγ p hγ0.symm
    exact ⟨η 1, (hη 1 ⟨zero_le_one, le_rfl⟩).trans hγ1⟩
  have hc : IsClopen (range f) := ⟨hclosed, hf.isOpen_range⟩
  exact range_eq_univ.mp (hc.eq_univ ⟨f 0, mem_range_self 0⟩)

omit [CompleteSpace Z] [IsRiemannianManifold (𝓡 2) Z] in
theorem isCoveringMap_finite_localIsometry
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    {f : E2 → Z} (hf : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f)
    (hD : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ = ‖(v : E2)‖ₑ) :
    IsCoveringMap f ∧ Surjective f := by
  have hsurj := surjective_finite_localIsometry k hnorm hf hD
  refine ⟨DifferentialGeometry.isCoveringMap_of_forall_smooth_path_lift (I := 𝓡 2)
    hf.isLocalHomeomorph hsurj ?_, hsurj⟩
  intro γ hγ z hz
  exact forall_finite_path_lift k hnorm hf hD γ (hγ.of_le (by simp)) z hz

theorem exists_euclideanCover_of_finite_flat (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    (hflat : ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0)
    (p : Z) : ∃ f : E2 → Z, f 0 = p ∧ ContMDiff (𝓡 2) (𝓡 2) r f ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) r f ∧
      (∀ x v w, k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
        (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w) ∧
      IsCoveringMap f ∧ Surjective f := by
  obtain ⟨f, hf0, hfc, hfl, hfi⟩ := exists_flatFermiMap k hr hnorm hflat p
  have hD : ∀ (x : E2) (v : TangentSpace (𝓡 2) x),
      ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ = ‖(v : E2)‖ₑ := by
    intro x v
    calc ‖mfderiv (𝓡 2) (𝓡 2) f x v‖ₑ =
        ENNReal.ofReal (Real.sqrt (k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
          (mfderiv (𝓡 2) (𝓡 2) f x v))) := hnorm _ _
      _ = ENNReal.ofReal (Real.sqrt (inner ℝ v v)) :=
        congrArg (fun a => ENNReal.ofReal (Real.sqrt a)) (hfi x v v)
      _ = ‖(v : E2)‖ₑ := by rw [← norm_eq_sqrt_real_inner, ofReal_norm]
  have hf1 : IsLocalDiffeomorph (𝓡 2) (𝓡 2) 1 f := by
    intro x
    obtain ⟨d, hx, hd⟩ := hfl x
    exact ⟨PartialDiffeomorph.ofLE d (by exact_mod_cast (le_trans (by norm_num) hr : 1 ≤ r)),
      hx, hd⟩
  obtain ⟨hcover, hsurj⟩ := isCoveringMap_finite_localIsometry k hnorm hf1 hD
  exact ⟨f, hf0, hfc, hfl, hfi, hcover, hsurj⟩

end Plane

end DifferentialGeometry.Geometry.FiniteFlatSurface
