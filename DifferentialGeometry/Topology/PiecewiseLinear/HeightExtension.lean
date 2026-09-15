import DifferentialGeometry.Topology.PiecewiseLinear.ConeAmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.ConeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.HeightChange

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_extension_coneComplex_union_preserving_height
    {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) {p q : E} (hp : IsConeBase p L) (hq : IsConeBase q L)
    (hinter : (coneComplex hp).space ∩ (coneComplex hq).space = L.space)
    (hfrontier : frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
      (coneComplex (hp.of_faces_subset hB)).space ∪ (coneComplex (hq.of_faces_subset hB)).space)
    {f : E → E} (hf : IsPLHomeomorphOn f L.space L.space) (hfix : EqOn f id B.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ∀ z ∈ L.space, ℓ (f z) = ℓ z) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h f L.space ∧
      h '' (coneComplex hp).space = (coneComplex hp).space ∧
      h '' (coneComplex hq).space = (coneComplex hq).space ∧
      EqOn h id ((coneComplex hp).space ∪ (coneComplex hq).space)ᶜ ∧
      (∀ x, ℓ (h x) = ℓ x) := by
  obtain ⟨h, hh, hhf, hhP, hhQ, hhfix, hhp, hhq, hPrad, hQrad⟩ :=
    exists_isPLHomeomorphOn_extension_coneComplex_union_radial hB hp hq hinter hfrontier hf hfix
  have hcone {r : E} (hr : IsConeBase r L) (hrfix : h r = r)
      (hrad : ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        h (r + s • (z - r)) = r + s • (f z - r)) :
      ∀ x ∈ (coneComplex hr).space, ℓ (h x) = ℓ x := by
    intro x hx
    rcases (mem_coneComplex_space_iff hr).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · rw [hrfix]
    · rw [hrad z hz s hs.le hs']
      simp only [map_add, map_smul, map_sub, hℓ z hz]
  refine ⟨h, hh, hhf, hhP, hhQ, hhfix, fun x => ?_⟩
  by_cases hx : x ∈ (coneComplex hp).space ∪ (coneComplex hq).space
  · exact hx.elim (hcone hp hhp hPrad x) (hcone hq hhq hQrad x)
  · rw [hhfix hx, id_eq]

open Classical in
theorem exists_isPLHomeomorphOn_extension_coneComplex_union_of_subset_fiber
    {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) {p q : E} (hp : IsConeBase p L) (hq : IsConeBase q L)
    (hinter : (coneComplex hp).space ∩ (coneComplex hq).space = L.space)
    (hfrontier : frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
      (coneComplex (hp.of_faces_subset hB)).space ∪ (coneComplex (hq.of_faces_subset hB)).space)
    {f : E → E} (hf : IsPLHomeomorphOn f L.space L.space) (hfix : EqOn f id B.space)
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} (hL : L.space ⊆ {x | ℓ x = r}) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h f L.space ∧
      EqOn h id ((coneComplex hp).space ∪ (coneComplex hq).space)ᶜ ∧
      (∀ x, ℓ (h x) = ℓ x) ∧ (∀ S : Set E, heightIndex (h '' S) ℓ = heightIndex S ℓ) := by
  obtain ⟨h, hh, hhf, -, -, hhfix, hhℓ⟩ :=
    exists_isPLHomeomorphOn_extension_coneComplex_union_preserving_height hB hp hq hinter
      hfrontier hf hfix ℓ (fun z hz => (hL (hf.bijOn.mapsTo hz)).trans (hL hz).symm)
  exact ⟨h, hh, hhf, hhfix, hhℓ, fun _ => heightIndex_image h hh hhℓ⟩

omit [FiniteDimensional ℝ E] in
theorem exists_lt_gt_linearMap_of_isOpen (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {W : Set E} (hW : IsOpen W) {x : E} (hx : x ∈ W) :
    ∃ p ∈ W, ∃ q ∈ W, ℓ p < ℓ x ∧ ℓ x < ℓ q := by
  obtain ⟨u, hu⟩ : ∃ u : E, ℓ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  let v := (ℓ u)⁻¹ • u
  have hv : ℓ v = 1 := by simp only [v, map_smul, smul_eq_mul, inv_mul_cancel₀ hu]
  have hminus : Continuous (fun t : ℝ => x - t • v) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hplus : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : {t : ℝ | x - t • v ∈ W ∧ x + t • v ∈ W} ∈ 𝓝 0 := by
    have hm := hminus.continuousAt.preimage_mem_nhds
      (show W ∈ 𝓝 (x - (0 : ℝ) • v) by simpa only [zero_smul, sub_zero] using hW.mem_nhds hx)
    have hp := hplus.continuousAt.preimage_mem_nhds
      (show W ∈ 𝓝 (x + (0 : ℝ) • v) by simpa only [zero_smul, add_zero] using hW.mem_nhds hx)
    exact Filter.inter_mem hm hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hhalf : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hpW, hqW⟩ := hball hhalf
  refine ⟨x - (ε / 2) • v, hpW, x + (ε / 2) • v, hqW, ?_, ?_⟩
  · simp only [map_sub, map_smul, smul_eq_mul, hv, mul_one]
    linarith
  · simp only [map_add, map_smul, smul_eq_mul, hv, mul_one]
    linarith

open Classical in
theorem exists_isPLHomeomorphOn_extension_preserving_height
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) (hL : L.space ⊆ {x | ℓ x = r})
    (hbase : ∀ z ∈ L.space, z ∉ B.space → L.space ∈ 𝓝[{x | ℓ x = r}] z)
    {f : E → E} (hf : IsPLHomeomorphOn f L.space L.space) (hfix : EqOn f id B.space)
    {W : Set E} (hW : Convex ℝ W) (hWopen : IsOpen W) (hLW : L.space ⊆ W) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h f L.space ∧ EqOn h id Wᶜ ∧
      (∀ x, ℓ (h x) = ℓ x) ∧ (∀ S : Set E, heightIndex (h '' S) ℓ = heightIndex S ℓ) := by
  rcases L.space.eq_empty_or_nonempty with hempty | ⟨z, hz⟩
  · have hid : IsPLHomeomorphOn (Homeomorph.refl E) univ univ := by
      refine ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ, ?_⟩
      exact (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx =>
        (bijOn_id univ).invOn_invFunOn.1 hx
    exact ⟨Homeomorph.refl E, hid, fun x hx => (hempty ▸ hx).elim,
      fun _ _ => rfl, fun _ => rfl, fun _ => heightIndex_image _ hid (fun _ => rfl)⟩
  · obtain ⟨p, hpW, q, hqW, hp, hq⟩ := exists_lt_gt_linearMap_of_isOpen ℓ hℓ hWopen (hLW hz)
    have hzheight : ℓ z = r := hL hz
    rw [hzheight] at hp hq
    let hpL := isConeBase_of_subset_fiber ℓ L hL hp.ne
    let hqL := isConeBase_of_subset_fiber ℓ L hL hq.ne'
    obtain ⟨h, hh, hhf, hhfix, hhℓ, hhInd⟩ :=
      exists_isPLHomeomorphOn_extension_coneComplex_union_of_subset_fiber hB hpL hqL
        (coneComplex_space_inter_of_subset_fiber ℓ hL hpL hqL hp hq)
        (frontier_coneComplex_union_subset_of_mem_nhdsWithin ℓ hB hL hpL hqL hp hq hbase)
        hf hfix ℓ hL
    have hcone {a : E} (haL : IsConeBase a L) (haW : a ∈ W) : (coneComplex haL).space ⊆ W := by
      intro x hx
      rcases (mem_coneComplex_space_iff haL).mp hx with rfl | ⟨y, hy, s, hs, hs', rfl⟩
      · exact haW
      · simpa only [AffineMap.lineMap_apply_module', add_comm] using
          hW.lineMap_mem haW (hLW hy) ⟨hs.le, hs'⟩
    refine ⟨h, hh, hhf, ?_, hhℓ, hhInd⟩
    intro x hx
    exact hhfix (fun hxCone => hx (hxCone.elim (fun hy => hcone hpL hpW hy) (fun hy => hcone hqL hqW hy)))
end DifferentialGeometry.Topology.PiecewiseLinear
