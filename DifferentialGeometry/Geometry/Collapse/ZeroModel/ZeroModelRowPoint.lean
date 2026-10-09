import DifferentialGeometry.Topology.VectorBundle.FrameTrivializationApplications
import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Descend
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# The point-soul zero model: `D_T(V) ≅ D³ = ClosedCell 3` (LFR51 point row, LFR54 → `ZeroModel.ball`)

Lane LFR54-ROW, group G2. Frozen blueprint master207A, LFR51 (A:29309, table (LFR51.1), first row
`{*} | ℝ³ | D³`) and LFR54 (A:29526, type `D³` "on the ACTUAL sublevels … including their
boundary"). For a smooth Riemannian vector bundle `V` over a one-point base (`[Subsingleton B]
[Nonempty B]`, `finrank EB = 0`, rank `m + 1`):

* `exists_euclidean_diffeomorph_totalSpace_of_subsingleton`: the total space is `ℝ^(m+1)`, through
  a smooth diffeomorphism carrying the fibre norm to the Euclidean norm (51-P + dropping the point);
* `exists_closedCell_diffeomorph_normClosedDisc_of_norm_eq` (kernel): a norm-preserving smooth
  diffeomorphism of the total space onto `ℝ^(m+1)` identifies every closed `T`-disc bundle (native
  boundary charts) with the closed cell `ClosedCell (m + 1)` (`𝓡∂ (m + 1)`), radius divided by `T`;
* `exists_closedCell_diffeomorph_normClosedDisc_of_subsingleton`: the point row on `D_T(V)`;
* `exists_closedCell_diffeomorph_discCore_of_subsingleton`: the point row on every actual disc core
  `D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N` of a carrier `e` (X84 `discCoreChartedSpace`), for every `T > 0`.

In each form the SAME diffeomorphism `Ψ` satisfies `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`, hence carries the
boundary `{‖(e⁻¹ x).2‖ = T}` exactly onto the boundary sphere `‖·‖ = 1` of the cell (stated as the
second clause).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle

/-- The boundary charts of the closed cell `ClosedCell (m + 1)` (`𝓡∂ (m + 1)`). -/
local instance cellCharts_LFR54ROW (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc m

/-- The closed cell is a smooth manifold with boundary. -/
local instance cellSmooth_LFR54ROW (m : ℕ) : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold m

section Trivial

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fibre coordinate of the trivial bundle is smooth. -/
theorem contMDiff_trivial_fiberCoord :
    ContMDiff (IB.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun z : TotalSpace E (Trivial B E) => z.2) := by
  intro z
  let trivAtlas_LFR54ROW : MemTrivializationAtlas (Trivial.trivialization B E) :=
    ⟨Set.mem_singleton _⟩
  have h := (Trivial.trivialization B E).contMDiffOn (IB := IB) (n := ∞)
  have hz : ContMDiffAt (IB.prod 𝓘(ℝ, E)) (IB.prod 𝓘(ℝ, E)) ∞
      (fun z : TotalSpace E (Trivial B E) => (z.proj, z.2)) z :=
    h.contMDiffAt (by simpa only [Trivial.trivialization_source] using Filter.univ_mem)
  exact contMDiffAt_snd.comp z hz

/-- A point of the base with a smooth fibre coordinate is a smooth map into the trivial bundle. -/
theorem contMDiff_trivial_mk_const (b₀ : B) :
    ContMDiff 𝓘(ℝ, E) (IB.prod 𝓘(ℝ, E)) ∞ (fun x : E => (⟨b₀, x⟩ : TotalSpace E (Trivial B E))) := by
  intro x
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
  exact contMDiffAt_id

/-- Over a one-point base the total space of the trivial bundle is the fibre. -/
def trivialPointDiffeomorph [Subsingleton B] (b₀ : B) :
    Diffeomorph (IB.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (TotalSpace E (Trivial B E)) E ∞ where
  toFun z := z.2
  invFun x := ⟨b₀, x⟩
  left_inv z := by
    obtain ⟨b, v⟩ := z
    rcases Subsingleton.elim b b₀
    rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_trivial_fiberCoord
  contMDiff_invFun := contMDiff_trivial_mk_const b₀

end Trivial

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] in
/-- **LFR51 point row, total space.** Over a one-point base a smooth Riemannian vector bundle of
rank `k` is `ℝᵏ`, through a smooth diffeomorphism carrying the fibre norm to the Euclidean norm. -/
theorem exists_euclidean_diffeomorph_totalSpace_of_subsingleton [Subsingleton B] [Nonempty B]
    {k : ℕ} (hk : finrank ℝ F = k) :
    ∃ Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (TotalSpace F V)
        (EuclideanSpace ℝ (Fin k)) ∞,
      ∀ z, ‖Φ z‖ = ‖z.2‖ := by
  obtain ⟨Φ₀, -, hn⟩ := exists_normPreserving_trivialization_of_subsingleton (IB := IB) (V := V) hk
  obtain ⟨b₀⟩ := (inferInstance : Nonempty B)
  refine ⟨Φ₀.symm.trans (trivialPointDiffeomorph b₀), fun z => ?_⟩
  have h := hn (Φ₀.symm z)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

omit [FiniteDimensional ℝ F] in
/-- **Kernel: closed disc bundles of a bundle isometric to `ℝ^(m+1)`.** A smooth diffeomorphism of
the total space onto `ℝ^(m+1)` carrying the fibre norm to the Euclidean norm identifies each closed
`T`-disc bundle (native boundary charts) with `ClosedCell (m + 1)`, radius divided by `T`; the
boundary `‖z‖ = T` goes exactly onto the boundary sphere. -/
theorem exists_closedCell_diffeomorph_normClosedDisc_of_norm_eq [FiniteDimensional ℝ F] {m : ℕ}
    (hd : finrank ℝ (EB × F) = m + 1)
    (Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (TotalSpace F V)
      (EuclideanSpace ℝ (Fin (m + 1))) ∞)
    (hΦ : ∀ z, ‖Φ z‖ = ‖z.2‖) (T : ℝ) (hT : 0 < T) :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
        {z : TotalSpace F V // ‖z.2‖ ≤ T} (ClosedCell (m + 1)) ∞,
      (∀ z, T * ‖(Ψ z).val‖ = ‖z.val.2‖) ∧ ∀ z, ‖z.val.2‖ = T ↔ ‖(Ψ z).val‖ = 1 := by
  let csDisc_LFR54ROW := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  have hΦs : ∀ y, ‖(Φ.symm y).2‖ = ‖y‖ := fun y => by
    rw [← hΦ (Φ.symm y), Diffeomorph.apply_symm_apply]
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  let fwd : {z : TotalSpace F V // ‖z.2‖ ≤ T} → ClosedCell (m + 1) := fun z =>
    ⟨T⁻¹ • Φ z.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hTinv, hΦ]
      calc T⁻¹ * ‖z.val.2‖ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_left z.property hTinv.le
        _ = 1 := inv_mul_cancel₀ hT.ne'⟩
  let bwd : ClosedCell (m + 1) → {z : TotalSpace F V // ‖z.2‖ ≤ T} := fun x =>
    ⟨Φ.symm (T • x.val), by
      rw [hΦs, norm_smul, Real.norm_eq_abs, abs_of_pos hT]
      have hx : ‖x.val‖ ≤ 1 := x.property
      nlinarith⟩
  have hemb := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion m
  have hval : ContMDiff (morseModelWithCornersHalfSpace m) (IB.prod 𝓘(ℝ, F)) ∞
      (Subtype.val : {z : TotalSpace F V // ‖z.2‖ ≤ T} → TotalSpace F V) :=
    RankOneQuotient.contMDiff_normClosedDisc_val hd T hT
  have hfwdv : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡 (m + 1)) ∞
      (Subtype.val ∘ fwd) :=
    (contDiff_const_smul T⁻¹).contMDiff.comp (Φ.contMDiff.comp hval)
  have hfwd : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1)) ∞ fwd :=
    (ContMDiff.iff_comp_isImmersion hemb.isImmersion).mpr
      ⟨continuous_induced_rng.2 hfwdv.continuous, hfwdv⟩
  have hbwd : ContMDiff (𝓡∂ (m + 1)) (morseModelWithCornersHalfSpace m) ∞ bwd := by
    apply (RankOneQuotient.contMDiff_normClosedDisc_iff hd hT).mpr
    exact Φ.symm.contMDiff.comp ((contDiff_const_smul T).contMDiff.comp hemb.contMDiff)
  have hlr : ∀ z, bwd (fwd z) = z := fun z => by
    apply Subtype.ext
    change Φ.symm (T • T⁻¹ • Φ z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul, Diffeomorph.symm_apply_apply]
  have hrl : ∀ x, fwd (bwd x) = x := fun x => by
    apply Subtype.ext
    change T⁻¹ • Φ (Φ.symm (T • x.val)) = x.val
    rw [Diffeomorph.apply_symm_apply, smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  let Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
      {z : TotalSpace F V // ‖z.2‖ ≤ T} (ClosedCell (m + 1)) ∞ :=
    { toFun := fwd, invFun := bwd, left_inv := hlr, right_inv := hrl,
      contMDiff_toFun := hfwd, contMDiff_invFun := hbwd }
  have hnorm : ∀ z, T * ‖(Ψ z).val‖ = ‖z.val.2‖ := fun z => by
    change T * ‖T⁻¹ • Φ z.val‖ = ‖z.val.2‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hTinv, hΦ, ← mul_assoc,
      mul_inv_cancel₀ hT.ne', one_mul]
  refine ⟨Ψ, hnorm, fun z => ?_⟩
  rw [← hnorm z]
  constructor
  · intro h
    exact mul_left_cancel₀ hT.ne' (h.trans (mul_one T).symm)
  · intro h
    rw [h, mul_one]

/-- **LFR51 point row, disc bundle (`D³`).** Over a one-point base (`finrank EB = 0`) every closed
`T`-disc bundle of a smooth Riemannian bundle of rank `m + 1`, with its native boundary charts, is
diffeomorphic to `ClosedCell (m + 1)`, radius divided by `T`, boundary onto the boundary sphere. -/
theorem exists_closedCell_diffeomorph_normClosedDisc_of_subsingleton [Subsingleton B] [Nonempty B]
    {m : ℕ} (hd : finrank ℝ (EB × F) = m + 1) (h0 : finrank ℝ EB = 0) (T : ℝ) (hT : 0 < T) :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
        {z : TotalSpace F V // ‖z.2‖ ≤ T} (ClosedCell (m + 1)) ∞,
      (∀ z, T * ‖(Ψ z).val‖ = ‖z.val.2‖) ∧ ∀ z, ‖z.val.2‖ = T ↔ ‖(Ψ z).val‖ = 1 := by
  have hk : finrank ℝ F = m + 1 := by
    rw [finrank_prod, h0, zero_add] at hd
    exact hd
  obtain ⟨Φ, hΦ⟩ := exists_euclidean_diffeomorph_totalSpace_of_subsingleton (IB := IB) (V := V) hk
  exact exists_closedCell_diffeomorph_normClosedDisc_of_norm_eq hd Φ hΦ T hT

/-- **LFR54 point soul, on the actual disc core.** If `e` identifies `N` with a smooth Riemannian
bundle of rank `m + 1` over a one-point base, EVERY disc core `D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N`,
`T > 0`, with its transported boundary charts (X84 `discCoreChartedSpace`), is diffeomorphic to
`ClosedCell (m + 1)` by a `Ψ` with `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`; in particular `Ψ` carries the
boundary `{‖(e⁻¹ x).2‖ = T}` exactly onto the boundary sphere. -/
theorem exists_closedCell_diffeomorph_discCore_of_subsingleton [Subsingleton B] [Nonempty B]
    {m : ℕ} (hd : finrank ℝ (EB × F) = m + 1) (h0 : finrank ℝ EB = 0)
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e hd T hT
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
        {x : N // ‖(e.symm x).2‖ ≤ T} (ClosedCell (m + 1)) ∞,
      (∀ x, T * ‖(Ψ x).val‖ = ‖(e.symm x.val).2‖) ∧
      ∀ x, ‖(e.symm x.val).2‖ = T ↔ ‖(Ψ x).val‖ = 1 := by
  let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
  obtain ⟨Ψ₀, hΨ₀, hbd₀⟩ :=
    exists_closedCell_diffeomorph_normClosedDisc_of_subsingleton (IB := IB) (V := V) hd h0 T hT
  let D := discCoreDiffeomorph e hd T hT
  have hD : ∀ x, ‖(e.symm x.val).2‖ = ‖(D.symm x).val.2‖ := fun x => by
    have h : (D (D.symm x)).val = e (D.symm x).val := rfl
    rw [Diffeomorph.apply_symm_apply] at h
    rw [h, Diffeomorph.symm_apply_apply]
  refine ⟨D.symm.trans Ψ₀, fun x => ?_, fun x => ?_⟩
  · rw [hD x]
    exact hΨ₀ (D.symm x)
  · rw [hD x]
    exact hbd₀ (D.symm x)

end DifferentialGeometry.Geometry.Collapse.ZeroModel
