import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiscCoreType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallDiffeomorph
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCoreApplications
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCoreBinding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# LC61 at a fixed normalized scale: every open ball is the whole normal bundle

Master207A, A:23460 (LC61), noncompact branch, at the normalized scale of LC57. The data are those
of the LC57 noncompact branch at that scale: LC50's actual maps `j i : U → M i` with the `C¹`
pullback convergence on the buffered open set `U ⊇ closedBall(n, 10)`; the model radial function
`ζ` with LC55's errors; a field `V` with LC55's collar bounds; the fibre radius
`u = c ‖(e.symm ·).2‖` of a diffeomorphism `e : E ≃ N` from a smooth Riemannian vector bundle over a
compact base with `du(V) > 0` beyond `T₀` (LC54's normal flow: `point_outward_normalFlow_kernel_u_inputs`);
and selected source radial functions `η i` with LC30's clauses. Then one tail has, for every
`ρ ∈ [1/5, 2]`, a diffeomorphism of the OPEN distance ball `B(p_i, ρ)` onto the whole total space
`E` (for the soul's normal bundle: `B(p_i, ρ) ≅ νS ≅ N`).

The proof composes, with ONE model core `D = {ζ ≤ 1}`:
* LC51/LC48 (`eventually_core_isotopies_of_point_distance_core`): an ambient isotopy of `M i`
  carries `j i (D)` onto `{η i ≤ ρ}`;
* LC60 (`exists_open_distance_ball_diffeomorph`): `int {η i ≤ ρ} ≅ B(p_i, ρ)`;
* the LC61 kernel (`exists_partialDiffeomorph_interior_of_core_isotopies`): `int D ≅ B(p_i, ρ)`;
* LC55 (`point_distance_core_isotopy_discCore`): `D` is a disc core of `e' = e ∘ H₁⁻¹`;
* `exists_partialDiffeomorph_discCore_interior`: `int D ≅ E`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]
  {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
  {Vb : B → Type*} [TopologicalSpace (TotalSpace F Vb)]
  [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
  [FiberBundle F Vb] [VectorBundle ℝ F Vb] [IsContMDiffRiemannianBundle IB ∞ F Vb]

/-- **LC61 at a fixed normalized scale** (master207A, A:23460, noncompact branch). With the LC57
noncompact data at the normalized scale (LC50 maps, the model radial function `ζ`, the collar field
`V`, the fibre radius `u = c ‖(e.symm ·).2‖` of a bundle diffeomorphism `e : E ≃ N`, and selected
source radial functions `η i`), one tail has, for every `ρ ∈ [1/5, 2]`, a diffeomorphism of the
open ball `B(p_i, ρ)`, `p_i = j i n`, onto the whole total space `E`. -/
theorem eventually_open_ball_bundle_type {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens N) (n : U)
    (hbuffer : Metric.closedBall (n : N) 10 ⊆ U)
    (hSeq : ℕ → SmoothRiemannianMetric I U)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i))
    (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I U (M i) ∞)
    (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : U, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : U → M i) x v) (mfderiv I I (j i : U → M i) x w))
    (hconv : ∀ C : Set U, IsCompact C →
      MetricCPConvergenceOn C 1 hSeq (g.restrictOpen U) (g.restrictOpen U))
    {ζ : N → ℝ} {εN : ℝ≥0} (hεN : (εN : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist (n : N) x| < 1 / 80)
    (hlip : LipschitzWith εN (fun x => ζ x - dist (n : N) x))
    {Wζ : Set N} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ)
    (V : (x : N) → TangentSpace I x)
    (hVB : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hNorm (n : N) x, g.inner x (V x) w ≤ -(1 / 4))
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) N ∞) {c : ℝ} (hc : 0 < c)
    {u : N → ℝ} (hue : ∀ x, u x = c * ‖(e.symm x).2‖)
    {T₀ : ℝ} (hT₀pos : 0 < T₀) (hT₀ : {x | u x ≤ T₀} ⊆ Metric.ball (n : N) (1 / 2))
    {Wu : Set N} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x))
    {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 32)
    (η : ∀ i, M i → ℝ) (eη : ℕ → ℝ)
    (hη : ∀ᶠ i in atTop, eη i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < eη i) ∧
      LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
      ∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
            (gradientFun (I := I) (gSeq i) (η i) x)) :
    ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I (IB.prod 𝓘(ℝ, F)) (M i) (TotalSpace F Vb) ∞,
        Ψ.source = Metric.ball (j i n) ρ ∧ Ψ.target = univ := by
  -- the fibre radius as an LC55 coordinate
  have hrad := continuous_discCoreRadius_of_isContMDiffRiemannianBundle e
  have hu : Continuous u := (continuous_const.mul hrad).congr fun x => (hue x).symm
  have hucpt : ∀ T, IsCompact {x | u x ≤ T} := by
    intro T
    have hset : {x | u x ≤ T} = {x | ‖(e.symm x).2‖ ≤ T / c} := by
      ext x
      change u x ≤ T ↔ ‖(e.symm x).2‖ ≤ T / c
      rw [hue, le_div_iff₀ hc, mul_comm]
    rw [hset]
    exact isCompact_discCore e (T / c)
  have hsub : {x : N | 0 < u x} ⊆ {x : N | (e.symm x).2 ≠ 0} := by
    intro x hx
    have hx' : 0 < c * ‖(e.symm x).2‖ := by rw [← hue]; exact hx
    exact norm_pos_iff.mp (pos_of_mul_pos_right hx' hc.le)
  have hupos : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u {x | 0 < u x} := by
    have h := ((contDiff_const (c := c)).mul contDiff_id).contMDiff.comp_contMDiffOn
      ((contMDiffOn_discCoreRadius_off_zero e).mono hsub)
    exact h.congr fun x _ => (hue x).trans (by rfl)
  have hWu' : IsOpen (Wu ∩ {x | 0 < u x}) := hWu.inter (isOpen_lt continuous_const hu)
  have hWuT' : {x | T₀ ≤ u x} ⊆ Wu ∩ {x | 0 < u x} := fun x hx =>
    ⟨hWuT hx, lt_of_lt_of_le hT₀pos hx⟩
  -- LC51 on the source side
  obtain ⟨_, -, -, hM⟩ := eventually_core_isotopies_of_point_distance_core g hNorm U n hbuffer hSeq
    gSeq hSeqNorm j hj hmetric hconv hεN hclose hlip hWζ hcollarW hζW V hVB hVdir hu hucpt hT₀ hWu'
    hWuT' (hupos.mono inter_subset_right) (hVW.mono inter_subset_left) huV hε η eη hη
  -- LC55 on the model side: `D` is a disc core, whose interior is the whole bundle
  obtain ⟨-, -, hD2, -, -, T₁, hT₁, hiso⟩ := point_distance_core_isotopy_discCore g hNorm (n : N)
    hεN hclose hlip hWζ hcollarW hζW V hVB hVdir e hc hue hT₀pos hT₀ hWu hWuT hVW huV
  obtain ⟨-, -, -, -, -, -, ed, -, hDdisc⟩ :=
    hiso ((T₀ + T₁) / 2) ⟨by linarith, by linarith⟩
  obtain ⟨Ψb, hΨbs, hΨbt⟩ :=
    exists_partialDiffeomorph_discCore_interior ed (T := (T₀ + T₁) / 2 / c)
      (div_pos (by linarith) hc)
  rw [← hDdisc] at hΨbs
  have hDU : {x | ζ x ≤ 1} ⊆ U := fun x hx =>
    hbuffer (Metric.closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 10)
      (Metric.ball_subset_closedBall (hD2 hx)))
  filter_upwards [hM, hη] with i hi hηi ρ hρ
  obtain ⟨heη, hclη, hlipη, Wi, hWi, hCWi, hηWi, hgradη⟩ := hηi
  obtain ⟨Hs, -, hHs⟩ := hi ρ hρ
  obtain ⟨J, hJs, hJt, -⟩ := exists_open_distance_ball_diffeomorph hdim (gSeq i) (hSeqNorm i)
    (by linarith : (ε : ℝ) < 1 / 4) heη hclη hlipη hWi hCWi hηWi hgradη hρ
  -- the model embedding `N ⊇ U → M i`
  let ι := openSubtypePartialDiffeomorph I U ⟨n⟩
  let Φ := ι.symm.trans (j i)
  have hDΦ : {x | ζ x ≤ 1} ⊆ Φ.source := by
    intro x hx
    rw [PartialDiffeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [PartialDiffeomorph.symm_source, openSubtypePartialDiffeomorph_target]
      exact hDU hx
    · rw [mem_preimage, hj i]
      exact mem_univ _
  have hΦD : Φ '' {x | ζ x ≤ 1} = (j i : U → M i) '' (Subtype.val ⁻¹' {x | ζ x ≤ 1}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hDU hx⟩, hx, ?_⟩
      change j i ⟨x, hDU hx⟩ = j i (ι.symm x)
      rw [openSubtypePartialDiffeomorph_symm_apply I U ⟨n⟩ (hDU hx)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.1, hx, ?_⟩
      change j i (ι.symm x.1) = j i x
      rw [openSubtypePartialDiffeomorph_symm_apply I U ⟨n⟩ x.2]
  obtain ⟨Ψa, hΨas, hΨat, -⟩ := exists_partialDiffeomorph_interior_of_core_isotopies Φ hDΦ
    (Hs 1) (by rw [hΦD]; exact hHs) J hJs hJt (Diffeomorph.refl I N ∞)
    (by rw [Diffeomorph.coe_refl, image_id])
  refine ⟨Ψa.symm.trans Ψb, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_source, hΨat]
    refine inter_eq_left.mpr fun y hy => ?_
    have hy' : y ∈ Ψa.target := by rw [hΨat]; exact hy
    change Ψa.symm y ∈ Ψb.source
    rw [hΨbs, ← hΨas]
    exact Ψa.toPartialEquiv.map_target hy'
  · apply eq_univ_of_forall
    intro w
    have hw : w ∈ Ψb.target := by rw [hΨbt]; exact mem_univ w
    refine ⟨hw, ?_⟩
    change Ψb.symm w ∈ Ψa.symm.target
    rw [PartialDiffeomorph.symm_target, hΨas, ← hΨbs]
    exact Ψb.toPartialEquiv.map_target hw

end DifferentialGeometry.Geometry.Collapse
