import DifferentialGeometry.Geometry.Connection.ParallelTransport.VectorBundle
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantSet
import DifferentialGeometry.Geometry.Metric.BundleSetDistance
import DifferentialGeometry.Analysis.Convex.NormalCone
import DifferentialGeometry.Geometry.Connection.AlongCurveRegularity
import DifferentialGeometry.Analysis.Calculus.LocalExtrema

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

open DifferentialGeometry.Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V] [ContMDiffVectorBundle ∞ F V I]

theorem IsParallelSet.exists_parallel_support_on_Icc
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    {γ : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (p ν : V (γ t₀))
    (hν : ν ∈ normalCone {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1) :
    ∃ P N : ∀ t : ℝ, V (γ t),
      P t₀ = p ∧ N t₀ = ν ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) ∞
        (fun t => (⟨γ t, P t⟩ : TotalSpace F V)) (Icc a b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) ∞
        (fun t => (⟨γ t, N t⟩ : TotalSpace F V)) (Icc a b) ∧
      (∀ t ∈ Icc a b, cov.derivAlongWithin γ P (Icc a b) t = 0) ∧
      (∀ t ∈ Icc a b, cov.derivAlongWithin γ N (Icc a b) t = 0) ∧
      (∀ t ∈ Icc a b,
        N t ∈ normalCone {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} (P t)) ∧
      (∀ t ∈ Icc a b, ‖N t‖ = ‖ν‖) ∧
      ∀ t ∈ Icc a b, ∀ w : V (γ t),
        inner ℝ (N t) (w - P t) ≤ fiberInfDist K (⟨γ t, w⟩ : TotalSpace F V) := by
  have hγparam : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : ℝ × ℝ => γ q.1) (Icc a b ×ˢ univ) :=
    hγ.comp contMDiffOn_fst (fun _ hq => hq.1)
  obtain ⟨T, hT₀, hTf, _, hTp, hTm⟩ :=
    hmetric.exists_parallel_transport_on_Icc (IP := 𝓘(ℝ, ℝ))
      (γ := fun t (_ : ℝ) => γ t) hcov ht₀ hγparam
  have hsmooth (v : V (γ t₀)) :
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) ∞
        (fun t => (⟨γ t, T t 0 v⟩ : TotalSpace F V)) (Icc a b) := by
    let e := trivializationAt F V (γ t₀)
    have he : γ t₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t₀)
    have harg : ContMDiff 𝓘(ℝ, ℝ)
        ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => ((t, (0 : ℝ)), e.continuousLinearMapAt ℝ (γ t₀) v)) :=
      (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
    have h := (hTf e).comp harg.contMDiffOn (fun _ ht => ⟨ht, he⟩)
    simpa only [Function.comp_def, e.symmL_continuousLinearMapAt he] using h
  have hnormal (t : ℝ) (ht : t ∈ Icc a b) :
      T t 0 ν ∈ normalCone {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} (T t 0 p) := by
    have hmap := hK.image_eq_of_parallel ht₀ hγ (fun s => T s 0) (hT₀ 0)
      (fun v => (hsmooth v).mdifferentiableOn (by simp)) (hTp 0) ht
    refine ⟨?_, ?_⟩
    · rw [← hmap]
      exact ⟨p, hν.1, rfl⟩
    · intro w hw
      rw [← hmap] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rw [← map_sub, hTm t ht]
      exact hν.2 v hv
  have hnorm (t : ℝ) (ht : t ∈ Icc a b) : ‖T t 0 ν‖ = ‖ν‖ :=
    ((T t 0).toLinearEquiv.isometryOfInner (hTm t ht 0)).norm_map ν
  exact ⟨(fun t => T t 0 p), (fun t => T t 0 ν), hT₀ 0 p, hT₀ 0 ν,
    hsmooth p, hsmooth ν, hTp 0 p, hTp 0 ν, hnormal, hnorm,
    fun t ht w => inner_sub_le_infDist_of_mem_normalCone (hnormal t ht)
      ((hnorm t ht).le.trans hνnorm) w⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [ContMDiffVectorBundle ∞ F V I] in
private theorem derivWithin_inner_sub_inner_of_parallel
    [ContMDiffVectorBundle 1 F V I]
    {cov : CovariantDerivative I F V} (hmetric : cov.IsMetricCompatible)
    {γ : ℝ → M} {P N Z : ∀ t : ℝ, V (γ t)} {s : Set ℝ} {t : ℝ}
    (hP : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, P t⟩ : TotalSpace F V)) s t)
    (hN : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, N t⟩ : TotalSpace F V)) s t)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) s t)
    (hPpar : cov.derivAlongWithin γ P s t = 0)
    (hNpar : cov.derivAlongWithin γ N s t = 0) :
    derivWithin (fun t => inner ℝ (N t) (Z t) - inner ℝ (N t) (P t)) s t =
      inner ℝ (N t) (cov.derivAlongWithin γ Z s t) := by
  have hNZ : DifferentiableWithinAt ℝ (fun t => inner ℝ (N t) (Z t)) s t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp (hN.inner_bundle hZ)
  have hNP : DifferentiableWithinAt ℝ (fun t => inner ℝ (N t) (P t)) s t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp (hN.inner_bundle hP)
  rw [derivWithin_fun_sub hNZ hNP, hmetric.derivAlongWithin_inner hN hZ,
    hmetric.derivAlongWithin_inner hN hP, hNpar, hPpar]
  simp only [inner_zero_left, inner_zero_right, zero_add, add_zero, sub_zero]

theorem IsParallelSet.inner_derivAlongWithin_eq_zero_of_fiberInfDist_max
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b) t₀)
    (p ν : V (γ t₀))
    (hν : ν ∈ normalCone {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (Z t₀ - p) = fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V))
    (hmax : ∀ t ∈ Icc a b, fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) ≤
      fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V)) :
    inner ℝ ν (cov.derivAlongWithin γ Z (Icc a b) t₀) = 0 := by
  have ht₀' : t₀ ∈ Icc a b := ⟨ht₀.1.le, ht₀.2.le⟩
  have hnhds : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  obtain ⟨P, N, hP₀, hN₀, hP, hN, hPpar, hNpar, _, _, hsupport⟩ :=
    hK.exists_parallel_support_on_Icc hcov hmetric ht₀' hγ p ν hν hνnorm
  let ψ : ℝ → ℝ := fun t => inner ℝ (N t) (Z t) - inner ℝ (N t) (P t)
  have hψ₀ : ψ t₀ = fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V) := by
    dsimp only [ψ]
    rw [hN₀, hP₀, ← inner_sub_right, hcontact]
  have hψmax : IsLocalMax ψ t₀ := by
    filter_upwards [hnhds] with t ht
    calc
      ψ t ≤ fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) := by
        simpa only [ψ, inner_sub_right] using hsupport t ht (Z t)
      _ ≤ ψ t₀ := by rw [hψ₀]; exact hmax t ht
  have hPd := (hP.mdifferentiableOn (by simp)) t₀ ht₀'
  have hNd := (hN.mdifferentiableOn (by simp)) t₀ ht₀'
  have hd : derivWithin ψ (Icc a b) t₀ =
      inner ℝ ν (cov.derivAlongWithin γ Z (Icc a b) t₀) := by
    have h := derivWithin_inner_sub_inner_of_parallel hmetric hPd hNd hZ
      (hPpar t₀ ht₀') (hNpar t₀ ht₀')
    simpa only [hN₀] using h
  rw [← hd, derivWithin_of_mem_nhds hnhds]
  exact hψmax.deriv_eq_zero

theorem IsParallelSet.inner_second_derivAlongWithin_nonpos_of_fiberInfDist_max
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hZ : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 2
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (p ν : V (γ t₀))
    (hν : ν ∈ normalCone {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (Z t₀ - p) = fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V))
    (hmax : ∀ t ∈ Icc a b, fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) ≤
      fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V)) :
    inner ℝ ν (cov.derivAlongWithin γ
      (fun t => cov.derivAlongWithin γ Z (Icc a b) t) (Icc a b) t₀) ≤ 0 := by
  have ht₀' : t₀ ∈ Icc a b := ⟨ht₀.1.le, ht₀.2.le⟩
  have hnhds : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  obtain ⟨P, N, hP₀, hN₀, hP, hN, hPpar, hNpar, _, _, hsupport⟩ :=
    hK.exists_parallel_support_on_Icc hcov hmetric ht₀' hγ p ν hν hνnorm
  let ψ : ℝ → ℝ := fun t => inner ℝ (N t) (Z t) - inner ℝ (N t) (P t)
  have hψ₀ : ψ t₀ = fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V) := by
    dsimp only [ψ]
    rw [hN₀, hP₀, ← inner_sub_right, hcontact]
  have hψmax : IsLocalMax ψ t₀ := by
    filter_upwards [hnhds] with t ht
    calc
      ψ t ≤ fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) := by
        simpa only [ψ, inner_sub_right] using hsupport t ht (Z t)
      _ ≤ ψ t₀ := by rw [hψ₀]; exact hmax t ht
  have hPd := hP.mdifferentiableOn (by simp)
  have hNd := hN.mdifferentiableOn (by simp)
  have hZd := hZ.mdifferentiableOn (by simp)
  have hψcont : ContinuousAt ψ t₀ :=
    (((hNd t₀ ht₀').inner_bundle (hZd t₀ ht₀')).sub
      ((hNd t₀ ht₀').inner_bundle (hPd t₀ ht₀'))).continuousWithinAt.continuousAt hnhds
  have hDZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, cov.derivAlongWithin γ Z (Icc a b) t⟩ : TotalSpace F V))
      (Icc a b) t₀ :=
    (cov.contMDiffAt_derivAlongWithin hcov (m := 1) hnhds
      (hZ.contMDiffAt hnhds) (by norm_num)).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
  have hderiv : deriv ψ =ᶠ[𝓝 t₀]
      (fun t => inner ℝ (N t) (cov.derivAlongWithin γ Z (Icc a b) t)) := by
    filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact derivWithin_inner_sub_inner_of_parallel hmetric (hPd t ht') (hNd t ht')
      (hZd t ht') (hPpar t ht') (hNpar t ht')
  have hsecond : deriv (deriv ψ) t₀ =
      inner ℝ ν (cov.derivAlongWithin γ
        (fun t => cov.derivAlongWithin γ Z (Icc a b) t) (Icc a b) t₀) := by
    rw [hderiv.deriv_eq, ← derivWithin_of_mem_nhds hnhds,
      hmetric.derivAlongWithin_inner (hNd t₀ ht₀') hDZ, hNpar t₀ ht₀']
    simp only [inner_zero_left, zero_add, hN₀]
  rw [← hsecond]
  exact hψmax.deriv_deriv_nonpos hψcont

theorem IsParallelSet.exists_projection_support_test_on_Icc
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b t₀ r : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hZ : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 2
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hne : {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K}.Nonempty)
    (hclosed : IsClosed {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K})
    (hconvex : Convex ℝ {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K})
    (hr : 0 < r)
    (hcontact : fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V) = r)
    (hmax : ∀ t ∈ Icc a b, fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) ≤ r) :
    ∃ p : V (γ t₀), (⟨γ t₀, p⟩ : TotalSpace F V) ∈ K ∧ ‖Z t₀ - p‖ = r ∧
      inner ℝ (r⁻¹ • (Z t₀ - p)) (cov.derivAlongWithin γ Z (Icc a b) t₀) = 0 ∧
      inner ℝ (r⁻¹ • (Z t₀ - p)) (cov.derivAlongWithin γ
        (fun t => cov.derivAlongWithin γ Z (Icc a b) t) (Icc a b) t₀) ≤ 0 := by
  let L := VectorBundle.continuousLinearEquivAt ℝ F V (γ t₀)
  have : FiniteDimensional ℝ (V (γ t₀)) :=
    FiniteDimensional.of_injective L.toLinearMap L.injective
  have : CompleteSpace (V (γ t₀)) := FiniteDimensional.complete ℝ (V (γ t₀))
  obtain ⟨p, ⟨hp, hmin⟩, _⟩ :=
    existsUnique_norm_sub_eq_infDist hne hclosed.isComplete hconvex (Z t₀)
  have hnorm : ‖Z t₀ - p‖ = r := hmin.trans hcontact
  have hnormal : r⁻¹ • (Z t₀ - p) ∈
      normalCone {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} p :=
    smul_mem_normalCone (inv_nonneg.mpr hr.le) ((sub_mem_normalCone_iff hconvex hp).mpr hmin)
  have hunit : ‖r⁻¹ • (Z t₀ - p)‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), hnorm, inv_mul_cancel₀ hr.ne']
  have htouch : inner ℝ (r⁻¹ • (Z t₀ - p)) (Z t₀ - p) =
      fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V) := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm, hcontact, pow_two,
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hmaximum : ∀ t ∈ Icc a b, fiberInfDist K (⟨γ t, Z t⟩ : TotalSpace F V) ≤
      fiberInfDist K (⟨γ t₀, Z t₀⟩ : TotalSpace F V) := by
    intro t ht
    rw [hcontact]
    exact hmax t ht
  exact ⟨p, hp, hnorm,
    hK.inner_derivAlongWithin_eq_zero_of_fiberInfDist_max hcov hmetric ht₀ hγ
      ((hZ.mdifferentiableOn (by simp)) t₀ ⟨ht₀.1.le, ht₀.2.le⟩)
      p _ hnormal hunit.le htouch hmaximum,
    hK.inner_second_derivAlongWithin_nonpos_of_fiberInfDist_max hcov hmetric ht₀ hγ hZ
      p _ hnormal hunit.le htouch hmaximum⟩

end CovariantDerivative
