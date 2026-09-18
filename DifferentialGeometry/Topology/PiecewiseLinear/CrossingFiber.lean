import DifferentialGeometry.Topology.PiecewiseLinear.HeightLevelLink
import DifferentialGeometry.Topology.PiecewiseLinear.RadialEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.exists_continuousOn_injOn_real_inter
    {A B : Set E} {p : E} (hcross : HasPLCrossingAt A B p) :
    ∃ (U : Set E) (f : E → ℝ), IsOpen U ∧ p ∈ U ∧
      ContinuousOn f (U ∩ (A ∩ B)) ∧ InjOn f (U ∩ (A ∩ B)) := by
  obtain ⟨U₀, V, h, P, Q, α, β, hU₀, -, hpU₀, hh, -, -, -, hI, -, -, -, -, hlocal⟩ :=
    hcross
  let R : Submodule ℝ E := P ⊓ Q
  obtain ⟨T, hRT⟩ := Submodule.exists_isCompl R
  let π : E →L[ℝ] R := (R.projectionOnto T hRT).toContinuousLinearMap
  let e : R ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa only [Module.finrank_self] using hI)
  have hinj : ∀ {x y : E}, x ∈ R → y ∈ R → e (π x) = e (π y) → x = y := by
    intro x y hx hy hxy
    have heq := e.injective hxy
    change R.projectionOnto T hRT x = R.projectionOnto T hRT y at heq
    rw [R.projectionOnto_apply_of_mem_left hRT hx,
      R.projectionOnto_apply_of_mem_left hRT hy] at heq
    exact congrArg Subtype.val heq
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U₀ ∩ N, fun x => e (π (h x)), hU₀.inter hN, ⟨hpU₀, hpN⟩, ?_, ?_⟩
  · exact (e.continuous.comp π.continuous).comp_continuousOn
      (hh.isPiecewiseAffineOn.continuousOn.mono (fun _ hx => hx.1.1))
  · intro x hx y hy hxy
    apply hh.bijOn.injOn hx.1.1 hy.1.1
    apply hinj _ _ hxy
    · exact ⟨((hNsub hx.1.2).1.mp hx.2.1).1, ((hNsub hx.1.2).2.mp hx.2.2).1⟩
    · exact ⟨((hNsub hy.1.2).1.mp hy.2.1).1, ((hNsub hy.1.2).2.mp hy.2.2).1⟩

theorem HasPLCrossingAt.encard_geometricLink_le_two
    [DecidableEq E] {A B : Set E} {p : E} (hcross : HasPLCrossingAt A B p)
    (K : Geometry.SimplicialComplex ℝ E)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ K.space → x ∈ A ∩ B) :
    (SimplicialComplex.geometricLink K {p}).space.encard ≤ 2 := by
  obtain ⟨U, f, hU, hpU, hf, hinj⟩ := hcross.exists_continuousOn_injOn_real_inter
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hlocal
  apply (isRadiallyInjective_geometricLink K).encard_le_two_of_real_embedding
    (notMem_geometricLink_space K) hf hinj
  intro q hq
  have hcont : Continuous (fun t : ℝ => p + t • (q - p)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun t : ℝ => p + t • (q - p)) (𝓝 0) (𝓝 p) := by
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  have hnear := htend.eventually_mem ((hU.inter hV).mem_nhds ⟨hpU, hpV⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min (δ / 2) 1, lt_min (by positivity) zero_lt_one, fun t ht => ?_⟩
  have htδ : t < δ := lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (by linarith)
  have ht1 : t ≤ 1 := ht.2.trans (min_le_right _ _)
  have hpoint : p + t • (q - p) ∈ U ∩ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact htδ)
  refine ⟨hpoint.1, hVsub hpoint.2 ?_⟩
  exact mem_convexHull_insert_of_mem_geometricLink_space K hq ht.1 ht1

theorem HasPLCrossingAt.encard_geometricLink_fiber_le_two
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hcross : HasPLCrossingAt K.space {x | ℓ x = ℓ p} p) :
    ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤ 2 := by
  obtain ⟨F, f, -, hFspace, -, hf⟩ := exists_isPLHomeomorphOn_geometricLink_fiber K hp ℓ
  have hbound := hcross.encard_geometricLink_le_two F
    (Filter.Eventually.of_forall fun _ hx => hFspace.subset hx)
  rw [← hf.image_eq, hf.bijOn.injOn.encard_image]
  exact hbound

omit [FiniteDimensional ℝ E] in
theorem geometricLink_fiber_eq_empty_of_isolated
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {p : E} (ℓ : E →ₗ[ℝ] ℝ)
    (hisolated : {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p) :
    (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro q ⟨hq, hqlevel⟩
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hisolated
  have hcont : Continuous (fun r : ℝ => p + r • (q - p)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun r : ℝ => p + r • (q - p)) (𝓝[>] 0) (𝓝 p) := by
    simpa only [zero_smul, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨r, hrU, hr, hr1⟩ :=
    ((htend.eventually_mem hU).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have hpoint : p + r • (q - p) = p := hsub ⟨hrU,
    mem_convexHull_insert_of_mem_geometricLink_space K hq hr.le hr1.le, by
      change ℓ (p + r • (q - p)) = ℓ p
      have hqeq : ℓ q = ℓ p := hqlevel
      rw [map_add, map_smul, smul_eq_mul, map_sub, hqeq, sub_self, mul_zero, add_zero]⟩
  have hsmul : r • (q - p) = 0 := by simpa only [add_eq_left] using hpoint
  have hqp : q = p := sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left hr.ne')
  exact notMem_geometricLink_space K (hqp ▸ hq)

theorem encard_geometricLink_fiber_le_two_of_notMem_heightSingularPoints
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hregular : p ∉ heightSingularPoints K.space ℓ) :
    ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤ 2 := by
  by_cases hcross : HasPLCrossingAt K.space {x | ℓ x = ℓ p} p
  · exact hcross.encard_geometricLink_fiber_le_two K hp ℓ
  · have hisolated : {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p := by
      by_contra hnot
      exact hregular ⟨K.vertices_subset_space hp, hcross, hnot⟩
    rw [geometricLink_fiber_eq_empty_of_isolated K ℓ hisolated, encard_empty]
    exact zero_le

end DifferentialGeometry.Topology.PiecewiseLinear
