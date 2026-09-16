import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def centralProjection (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ) (p x : E) : E :=
  p + ((r - ℓ p) / (ℓ x - ℓ p)) • (x - p)

theorem centralProjection_of_mem_fiber (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {p x : E}
    (hp : ℓ p ≠ r) (hx : ℓ x = r) : centralProjection ℓ r p x = x := by
  simp only [centralProjection, hx, div_self (sub_ne_zero.mpr hp.symm), one_smul, add_sub_cancel]

theorem apply_centralProjection (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ) {p x : E}
    (hx : ℓ x ≠ ℓ p) : ℓ (centralProjection ℓ r p x) = r := by
  simp only [centralProjection, map_add, map_smul, map_sub, smul_eq_mul]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
  ring

theorem centralProjection_add_smul_sub (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {p z : E}
    (hp : ℓ p ≠ r) (hz : ℓ z = r) {s : ℝ} (hs : s ≠ 0) :
    centralProjection ℓ r p (p + s • (z - p)) = z := by
  simp only [centralProjection, map_add, map_smul, map_sub, smul_eq_mul, hz,
    add_sub_cancel_left]
  rw [smul_smul]
  have h : (r - ℓ p) / (s * (r - ℓ p)) * s = 1 := by
    field_simp
  rw [h, one_smul, add_sub_cancel]

theorem add_smul_centralProjection_sub (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {p x : E}
    (hp : ℓ p ≠ r) (hx : ℓ x ≠ ℓ p) :
    p + ((ℓ x - ℓ p) / (r - ℓ p)) • (centralProjection ℓ r p x - p) = x := by
  simp only [centralProjection, add_sub_cancel_left, smul_smul]
  rw [div_mul_div_cancel₀ (sub_ne_zero.mpr hp.symm),
    div_self (sub_ne_zero.mpr hx), one_smul, add_sub_cancel]

theorem continuousAt_centralProjection [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ) {p x : E} (hx : ℓ x ≠ ℓ p) :
    ContinuousAt (centralProjection ℓ r p) x := by
  exact continuousAt_const.add ((continuousAt_const.div
    (ℓ.continuous_of_finiteDimensional.continuousAt.sub continuousAt_const) (sub_ne_zero.mpr hx)).smul
      (continuousAt_id.sub continuousAt_const))

open Classical in
theorem eventually_mem_coneComplex_of_mem_nhdsWithin [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {L : Geometry.SimplicialComplex ℝ E}
    {p x : E} (hpL : IsConeBase p L) (hp : ℓ p ≠ r) (hx : ℓ x ≠ ℓ p)
    (hpos : 0 < (ℓ x - ℓ p) / (r - ℓ p))
    (hbase : L.space ∈ 𝓝[{z | ℓ z = r}] (centralProjection ℓ r p x)) :
    ∀ᶠ y in 𝓝 x, (ℓ y - ℓ p) / (r - ℓ p) ≤ 1 → y ∈ (coneComplex hpL).space := by
  have hne : ∀ᶠ y in 𝓝 x, ℓ y ≠ ℓ p :=
    ℓ.continuous_of_finiteDimensional.continuousAt.eventually_ne hx
  have hmap : Filter.Tendsto (centralProjection ℓ r p) (𝓝 x)
      (𝓝[{z | ℓ z = r}] (centralProjection ℓ r p x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuousAt_centralProjection ℓ r hx).tendsto,
      hne.mono (fun y hy => apply_centralProjection ℓ r hy)⟩
  have hpositive : ∀ᶠ y in 𝓝 x, 0 < (ℓ y - ℓ p) / (r - ℓ p) :=
    ((ℓ.continuous_of_finiteDimensional.sub continuous_const).div_const (r - ℓ p)).continuousAt.eventually
      (Ioi_mem_nhds hpos)
  filter_upwards [hmap.eventually hbase, hne, hpositive] with y hy hyne hypos hybound
  exact (mem_coneComplex_space_iff hpL).mpr (Or.inr
    ⟨centralProjection ℓ r p y, hy, (ℓ y - ℓ p) / (r - ℓ p), hypos, hybound,
      (add_smul_centralProjection_sub ℓ hp hyne).symm⟩)

open Classical in
theorem mem_interior_coneComplex_of_mem_nhdsWithin [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {L : Geometry.SimplicialComplex ℝ E}
    {p x : E} (hpL : IsConeBase p L) (hp : ℓ p ≠ r) (hx : ℓ x ≠ ℓ p)
    (hpos : 0 < (ℓ x - ℓ p) / (r - ℓ p)) (hlt : (ℓ x - ℓ p) / (r - ℓ p) < 1)
    (hbase : L.space ∈ 𝓝[{z | ℓ z = r}] (centralProjection ℓ r p x)) :
    x ∈ interior (coneComplex hpL).space := by
  apply mem_interior_iff_mem_nhds.mpr
  have hbound : ∀ᶠ y in 𝓝 x, (ℓ y - ℓ p) / (r - ℓ p) < 1 :=
    ((ℓ.continuous_of_finiteDimensional.sub continuous_const).div_const (r - ℓ p)).continuousAt.eventually
      (Iio_mem_nhds hlt)
  filter_upwards [eventually_mem_coneComplex_of_mem_nhdsWithin ℓ hpL hp hx hpos hbase,
    hbound] with y hy hybound
  exact hy hybound.le

open Classical in
theorem mem_interior_coneComplex_union_of_mem_nhdsWithin [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {L : Geometry.SimplicialComplex ℝ E}
    {p q x : E} (hpL : IsConeBase p L) (hqL : IsConeBase q L)
    (hp : ℓ p < r) (hq : r < ℓ q) (hx : ℓ x = r)
    (hbase : L.space ∈ 𝓝[{z | ℓ z = r}] x) :
    x ∈ interior ((coneComplex hpL).space ∪ (coneComplex hqL).space) := by
  have hratio {a : E} (ha : ℓ a ≠ r) : (ℓ x - ℓ a) / (r - ℓ a) = 1 := by
    rw [hx, div_self (sub_ne_zero.mpr ha.symm)]
  have hlocal {a : E} (haL : IsConeBase a L) (ha : ℓ a ≠ r) :
      ∀ᶠ y in 𝓝 x, (ℓ y - ℓ a) / (r - ℓ a) ≤ 1 → y ∈ (coneComplex haL).space :=
    eventually_mem_coneComplex_of_mem_nhdsWithin ℓ haL ha (hx ▸ ha.symm)
      (by rw [hratio ha]; exact zero_lt_one)
      (by rwa [centralProjection_of_mem_fiber ℓ ha hx])
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hlocal hpL hp.ne, hlocal hqL hq.ne'] with y hyP hyQ
  by_cases hy : ℓ y ≤ r
  · exact Or.inl (hyP ((div_le_one (sub_pos.mpr hp)).mpr (sub_le_sub_right hy _)))
  · exact Or.inr (hyQ ((div_le_one_of_neg (sub_neg.mpr hq)).mpr
      (sub_le_sub_right (le_of_not_ge hy) _)))

open Classical in
theorem frontier_coneComplex_union_subset_of_mem_nhdsWithin [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) (hL : L.space ⊆ {x | ℓ x = r})
    {p q : E} (hpL : IsConeBase p L) (hqL : IsConeBase q L) (hp : ℓ p < r) (hq : r < ℓ q)
    (hbase : ∀ z ∈ L.space, z ∉ B.space → L.space ∈ 𝓝[{x | ℓ x = r}] z) :
    frontier ((coneComplex hpL).space ∪ (coneComplex hqL).space) ⊆
      (coneComplex (hpL.of_faces_subset hB)).space ∪
        (coneComplex (hqL.of_faces_subset hB)).space := by
  have hcone {a : E} (haL : IsConeBase a L) (ha : ℓ a ≠ r)
      (hasub : (coneComplex haL).space ⊆ (coneComplex hpL).space ∪ (coneComplex hqL).space)
      {x : E} (hx : x ∈ (coneComplex haL).space) :
      x ∈ (coneComplex (haL.of_faces_subset hB)).space ∨
        x ∈ interior ((coneComplex hpL).space ∪ (coneComplex hqL).space) := by
    rcases (mem_coneComplex_space_iff haL).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact Or.inl (apex_mem_coneComplex_space (haL.of_faces_subset hB))
    · by_cases hzB : z ∈ B.space
      · exact Or.inl ((mem_coneComplex_space_iff (haL.of_faces_subset hB)).mpr
          (Or.inr ⟨z, hzB, s, hs, hs', rfl⟩))
      · right
        by_cases hs1 : s = 1
        · simpa only [hs1, one_smul, add_sub_cancel] using
            mem_interior_coneComplex_union_of_mem_nhdsWithin ℓ hpL hqL hp hq (hL hz)
              (hbase z hz hzB)
        · have hzheight : ℓ z = r := hL hz
          have hheight : ℓ (a + s • (z - a)) - ℓ a = s * (r - ℓ a) := by
            simp only [map_add, map_smul, map_sub, smul_eq_mul, hzheight, add_sub_cancel_left]
          have hratio : (ℓ (a + s • (z - a)) - ℓ a) / (r - ℓ a) = s := by
            rw [hheight, mul_div_cancel_right₀ _ (sub_ne_zero.mpr ha.symm)]
          have hne : ℓ (a + s • (z - a)) ≠ ℓ a := by
            apply sub_ne_zero.mp
            rw [hheight]
            exact mul_ne_zero hs.ne' (sub_ne_zero.mpr ha.symm)
          apply interior_mono hasub
          apply mem_interior_coneComplex_of_mem_nhdsWithin ℓ haL ha hne
            (hratio.symm ▸ hs) (hratio.symm ▸ lt_of_le_of_ne hs' hs1)
          rw [centralProjection_add_smul_sub ℓ ha hzheight hs.ne']
          exact hbase z hz hzB
  let _ : Finite (coneComplex hpL).faces :=
    (coneComplex_faces_finite hpL (Set.toFinite L.faces)).to_subtype
  let _ : Finite (coneComplex hqL).faces :=
    (coneComplex_faces_finite hqL (Set.toFinite L.faces)).to_subtype
  have hclosed := (isPolyhedron_space (coneComplex hpL)).isClosed.union
    (isPolyhedron_space (coneComplex hqL)).isClosed
  intro x hx
  have hxU : x ∈ (coneComplex hpL).space ∪ (coneComplex hqL).space := by
    simpa only [hclosed.closure_eq] using hx.1
  rcases hxU with hxP | hxQ
  · exact (hcone hpL hp.ne subset_union_left hxP).elim Or.inl (fun h => (hx.2 h).elim)
  · exact (hcone hqL hq.ne' subset_union_right hxQ).elim Or.inr (fun h => (hx.2 h).elim)
theorem isConeBase_of_subset_fiber (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.space ⊆ {x | ℓ x = r})
    {p : E} (hp : ℓ p ≠ r) : IsConeBase p L := by
  let A : Unit → E →ᵃ[ℝ] ℝ := fun _ => ℓ.toAffineMap - AffineMap.const ℝ E r
  have hzero : ∀ x ∈ L.space, ∀ i, A i x = 0 := fun x hx _ => sub_eq_zero.mpr (hL hx)
  apply isConeBase_of_affine_halfSpaces A L
    (fun x hx i => (hzero x hx i).ge)
    (fun s hs => ⟨(), fun v hv => hzero v (L.subset_space hs hv) ()⟩)
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · exact Or.inr (fun _ => sub_neg.mpr hlt)
  · exact Or.inl (fun _ => sub_pos.mpr hgt)

open Classical in
theorem coneComplex_space_inter_of_subset_fiber (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    {L : Geometry.SimplicialComplex ℝ E} (hL : L.space ⊆ {x | ℓ x = r})
    {p q : E} (hpL : IsConeBase p L) (hqL : IsConeBase q L) (hp : ℓ p < r) (hq : r < ℓ q) :
    (coneComplex hpL).space ∩ (coneComplex hqL).space = L.space := by
  let A : Unit → E →ᵃ[ℝ] ℝ := fun _ => AffineMap.const ℝ E r - ℓ.toAffineMap
  have hzero : ∀ x ∈ L.space, ∀ i, A i x = 0 := fun x hx _ => sub_eq_zero.mpr (hL hx).symm
  exact coneComplex_space_inter_of_affine_halfSpaces A
    (fun x hx i => (hzero x hx i).ge) (fun x hx => ⟨(), hzero x hx ()⟩)
    hpL hqL (fun _ => sub_nonneg.mpr hp.le) (fun _ => sub_neg.mpr hq)
end DifferentialGeometry.Topology.PiecewiseLinear
