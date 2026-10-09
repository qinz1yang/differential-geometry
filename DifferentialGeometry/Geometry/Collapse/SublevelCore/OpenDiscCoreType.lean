import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallCoreType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# LC61, bundle side: the interior of a disc core is diffeomorphic to the whole bundle

Master207A, A:23460 (LC61): the open ball is identified with the interior of the model core,
which is a disc core `{x | ‖(e.symm x).2‖ ≤ T}` of a diffeomorphism `e : E ≃ N` from the total
space of a smooth Riemannian vector bundle (LC55, `point_distance_core_normalFlow_discCore`);
its interior is the image of the open disc bundle `{‖z.2‖ < T}`, which is diffeomorphic to the
whole total space by the fibrewise map of `exists_openDisk_partialDiffeomorph` (for the quadratic
`Q = T⁻² ‖·‖²`).

* `interior_closedDisc_eq_openDisc`: `int {‖z.2‖ ≤ T} = {‖z.2‖ < T}` for `T > 0`.
* `exists_partialDiffeomorph_discCore_interior`: `int {x | ‖(e.symm x).2‖ ≤ T} ≃ E` as an open
  partial diffeomorphism with target everything.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB ∞ F V]

variable (IB) in
include IB in
/-- The fibre norm is continuous on the total space of a smooth Riemannian bundle. -/
theorem continuous_fiberNorm : Continuous (fun z : TotalSpace F V => ‖z.2‖) := by
  have h := (contMDiff_fiberRadiusSquared (IB := IB) (F := F) (V := V)).continuous.sqrt
  simpa only [fiberRadiusSquared, ← norm_eq_sqrt_real_inner] using h

variable (IB) in
include IB in
/-- The interior of the closed radius-`T` disc bundle is the open radius-`T` disc bundle. -/
theorem interior_closedDisc_eq_openDisc {T : ℝ} (hT : 0 < T) :
    interior {z : TotalSpace F V | ‖z.2‖ ≤ T} = {z | ‖z.2‖ < T} := by
  have hc := continuous_fiberNorm IB (F := F) (V := V)
  apply Subset.antisymm
  · intro z hz
    have hzT' : z ∈ {z : TotalSpace F V | ‖z.2‖ ≤ T} := interior_subset hz
    have hzT : ‖z.2‖ ≤ T := hzT'
    rcases hzT.lt_or_eq with h | h
    · exact h
    exfalso
    let γ : ℝ → TotalSpace F V := fun s => ⟨z.proj, (1 + s) • z.2⟩
    have hγ : Continuous γ :=
      ((contMDiff_totalSpace_smul (IB := IB) (F := F) (V := V)).comp
        ((contMDiff_const.add contMDiff_id).prodMk (contMDiff_const (c := z)))).continuous
    have hγ0 : γ 0 = z := by
      change (⟨z.proj, (1 + 0 : ℝ) • z.2⟩ : TotalSpace F V) = z
      rw [add_zero, one_smul]
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ interior {z : TotalSpace F V | ‖z.2‖ ≤ T} :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact isOpen_interior.mem_nhds hz)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hs : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith
    have hmem' : γ (δ / 2) ∈ {z : TotalSpace F V | ‖z.2‖ ≤ T} := interior_subset (hball hs)
    have hmem : ‖(1 + δ / 2) • z.2‖ ≤ T := hmem'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), h] at hmem
    nlinarith
  · exact interior_maximal (fun z (hz : ‖z.2‖ < T) => show ‖z.2‖ ≤ T from le_of_lt hz)
      (isOpen_lt hc continuous_const)

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **The interior of a disc core is the whole bundle.** For a diffeomorphism `e` from the total
space of a smooth Riemannian bundle and `T > 0`, there is an open partial diffeomorphism with
source `int {x | ‖(e.symm x).2‖ ≤ T}` and target the whole total space. -/
theorem exists_partialDiffeomorph_discCore_interior
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) {T : ℝ} (hT : 0 < T) :
    ∃ Ψ : PartialDiffeomorph IN (IB.prod 𝓘(ℝ, F)) N (TotalSpace F V) ∞,
      Ψ.source = interior {x : N | ‖(e.symm x).2‖ ≤ T} ∧ Ψ.target = univ := by
  -- the open disc bundle of radius `T` is the whole bundle
  let Q : TotalSpace F V → ℝ := fun z => (T⁻¹) ^ 2 * fiberRadiusSquared z
  have hQ : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ Q :=
    contMDiff_const.mul (contMDiff_fiberRadiusSquared (IB := IB) (F := F) (V := V))
  have hQ0 : ∀ z, 0 ≤ Q z := fun z =>
    mul_nonneg (sq_nonneg _) (real_inner_self_nonneg (x := z.2))
  have hQsmul : ∀ (c : ℝ) (z : TotalSpace F V), Q ⟨z.proj, c • z.snd⟩ = c ^ 2 * Q z := by
    intro c z
    change (T⁻¹) ^ 2 * inner ℝ (c • z.2) (c • z.2) = c ^ 2 * ((T⁻¹) ^ 2 * inner ℝ z.2 z.2)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  obtain ⟨Ψ₀, hΨ₀s, hΨ₀t, -, -⟩ := exists_openDisk_partialDiffeomorph Q hQ hQ0 hQsmul
  have hQdisc : {z : TotalSpace F V | Q z < 1} = {z | ‖z.2‖ < T} := by
    ext z
    change (T⁻¹) ^ 2 * inner ℝ z.2 z.2 < 1 ↔ ‖z.2‖ < T
    rw [real_inner_self_eq_norm_sq, ← mul_pow, inv_mul_eq_div]
    constructor
    · intro h
      have h1 : ‖z.2‖ / T < 1 := by
        by_contra hge
        push Not at hge
        nlinarith
      rwa [div_lt_one hT] at h1
    · intro h
      have h1 : ‖z.2‖ / T < 1 := (div_lt_one hT).mpr h
      have h0 : 0 ≤ ‖z.2‖ / T := div_nonneg (norm_nonneg _) hT.le
      nlinarith
  -- the interior of the disc core is carried by `e⁻¹` onto the open disc bundle
  set O : Set N := interior {x : N | ‖(e.symm x).2‖ ≤ T} with hOdef
  have hOimg : e.symm '' O = {z : TotalSpace F V | ‖z.2‖ < T} := by
    have hpre : {x : N | ‖(e.symm x).2‖ ≤ T} = e.symm ⁻¹' {z : TotalSpace F V | ‖z.2‖ ≤ T} :=
      rfl
    have hint : interior (e.symm ⁻¹' {z : TotalSpace F V | ‖z.2‖ ≤ T}) =
        e.symm ⁻¹' interior {z : TotalSpace F V | ‖z.2‖ ≤ T} :=
      (e.symm.toHomeomorph.preimage_interior _).symm
    rw [hOdef, hpre, hint, interior_closedDisc_eq_openDisc IB hT]
    exact image_preimage_eq _ e.symm.surjective
  obtain ⟨Φ₀, hΦ₀s, hΦ₀t, hΦ₀⟩ := exists_partialDiffeomorph_restrict
    e.symm.toPartialDiffeomorph isOpen_interior (subset_univ O)
  refine ⟨Φ₀.trans Ψ₀, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΦ₀s, hΨ₀s, hQdisc]
    refine inter_eq_left.mpr fun x hx => ?_
    change Φ₀ x ∈ {z : TotalSpace F V | ‖z.2‖ < T}
    rw [hΦ₀, ← hOimg]
    exact ⟨x, hx, rfl⟩
  · apply eq_univ_of_forall
    intro w
    have hw : w ∈ Ψ₀.target := by rw [hΨ₀t]; exact mem_univ w
    refine ⟨hw, ?_⟩
    change Ψ₀.symm w ∈ Φ₀.target
    have h1 : Ψ₀.symm w ∈ Ψ₀.source := Ψ₀.toPartialEquiv.map_target hw
    have hOimg' : e.symm.toPartialDiffeomorph '' O = {z : TotalSpace F V | ‖z.2‖ < T} := hOimg
    rw [hΦ₀t, hOimg', ← hQdisc, ← hΨ₀s]
    exact h1

end DifferentialGeometry.Geometry.Collapse
