import DifferentialGeometry.Geometry.Collapse.SublevelCore.TransverseCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Globalization
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport
import DifferentialGeometry.Topology.Manifold.RegularLevel.SublevelTransfer
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# LC38, noncompact alternative: every radial sublevel is a closed normal disc bundle

Master207A, A:21622 (LC38) with the noncompact LC37 packet (A:21601). The packet's specified
diffeomorphism `D_N ≃ D(νS)` is encoded as a smooth partial diffeomorphism
`eN : TotalSpace F V ⇀ N` from (an open neighbourhood of) the closed unit disc bundle of a smooth
Riemannian vector bundle over a compact base, with `D_N = eN '' D₁`. The bundle is arbitrary, so
the soul's normal bundle (NB-INST) is an instance; LC55's disc-core output is the case of a global
diffeomorphism. The packet's enclosure and outward transversality of `D = j(D_N)` are exactly the
hypotheses of LC36 (`radial_core_isotopy_of_transverse`).

* `exists_closedDisc_diffeomorph_sublevel` (generic): a smooth partial diffeomorphism `Ψ` from the
  total space with `D₁ ⊆ Ψ.source` and `Ψ '' D₁ = {f ≤ a}` for a smooth `f` regular at `a` gives a
  diffeomorphism of manifolds with boundary from X84's closed unit disc bundle onto the regular
  sublevel `{f ≤ a}` (via `exists_sublevel_diffeomorph_of_contMDiffOn`).
* `lc38_noncompact_sublevel_disc_embedding`: the LC36 isotopy `H` and `Ψ = H₁ ∘ j ∘ eN`, a smooth
  embedding of a neighbourhood of `D₁` carrying `D₁` onto `A_ρ`, for every `ρ ∈ [1/5, 2]`.
* `lc38_noncompact_sublevel_diffeomorph`: `A_ρ` with the regular-sublevel structure of a globally
  smooth `f` that equals `η` near the band `η⁻¹[1/8, 3]` (so `{f ≤ ρ} = A_ρ`) is diffeomorphic, as
  a manifold with boundary, to the closed unit disc bundle; the diffeomorphism is `H₁ ∘ j ∘ eN`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Topology.VectorBundle

section Disc

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **A partial diffeomorphism carrying the closed unit disc bundle onto a regular sublevel
restricts to a diffeomorphism of manifolds with boundary.** The disc carries X84's structure
`normClosedDiscBundleChartedSpace`, the sublevel `{f ≤ a}` the regular-sublevel structure for the
model `I` transported to `MorseModel (m + 1)`. -/
theorem exists_closedDisc_diffeomorph_sublevel {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (eM : E ≃L[ℝ] MorseModel (m + 1))
    (Ψ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ Ψ.source)
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff (I.transContinuousLinearEquiv eM) 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv (I.transContinuousLinearEquiv eM) 𝓘(ℝ, ℝ) f x ≠ 0)
    (himg : (Ψ : TotalSpace F V → M) '' {z | ‖z.2‖ ≤ 1} = {x | f x ≤ a}) :
    let _ := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
    let _ := sublevelChartedSpace (I.transContinuousLinearEquiv eM) hf hr
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} {x : M // f x ≤ a} ∞, ∀ z, (Φ z : M) = Ψ z := by
  let J := bundleRadiusBoundaryModel (IB := IB) hd
  let I' := I.transContinuousLinearEquiv eM
  have hf₁ : ContMDiff J 𝓘(ℝ, ℝ) ∞ (fiberRadiusSquared (F := F) (V := V)) :=
    (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      contMDiff_fiberRadiusSquared
  have hr₁ : ∀ z : TotalSpace F V, fiberRadiusSquared z = 1 ^ 2 →
      mfderiv J 𝓘(ℝ, ℝ) (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
    intro z hz hzero
    apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) one_pos z hz
    exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
      (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero
  have hrad : ∀ z : TotalSpace F V, fiberRadiusSquared z ≤ 1 ^ 2 ↔ ‖z.2‖ ≤ 1 := by
    intro z
    rw [fiberRadiusSquared, real_inner_self_eq_norm_sq]
    exact sq_le_sq₀ (norm_nonneg _) zero_le_one
  have hS₂ : {y | f y ≤ a} ⊆ Ψ.target := by
    rw [← himg]
    rintro y ⟨z, hz, rfl⟩
    exact Ψ.map_source (hdisc hz)
  have hψ : ContMDiffOn J I' ∞ Ψ Ψ.source :=
    (bundleRadiusBoundaryEquiv hd).contMDiffOn_transContinuousLinearEquiv_left.mpr
      (eM.contMDiffOn_transContinuousLinearEquiv_right.mpr Ψ.contMDiffOn)
  have hφ : ContMDiffOn I' J ∞ Ψ.symm Ψ.target :=
    eM.contMDiffOn_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd).contMDiffOn_transContinuousLinearEquiv_right.mpr
        Ψ.symm.contMDiffOn)
  have hψS : ∀ z : TotalSpace F V, fiberRadiusSquared z ≤ 1 ^ 2 → f (Ψ z) ≤ a := by
    intro z hz
    have h : Ψ z ∈ (Ψ : TotalSpace F V → M) '' {z | ‖z.2‖ ≤ 1} := ⟨z, (hrad z).1 hz, rfl⟩
    rw [himg] at h
    exact h
  have hφS : ∀ y, f y ≤ a → fiberRadiusSquared (Ψ.symm y) ≤ 1 ^ 2 := by
    intro y hy
    have h : y ∈ (Ψ : TotalSpace F V → M) '' {z | ‖z.2‖ ≤ 1} := by rw [himg]; exact hy
    obtain ⟨z, hz, rfl⟩ := h
    rw [Ψ.symm_apply_apply (hdisc hz)]
    exact (hrad z).2 hz
  obtain ⟨Φ₀, hΦ₀⟩ := exists_sublevel_diffeomorph_of_contMDiffOn J I' hf₁ hr₁ hf hr
    Ψ.open_source Ψ.open_target (fun z hz => hdisc ((hrad z).1 hz)) hS₂ hψ hφ hψS hφS
    (fun z hz => Ψ.symm_apply_apply (hdisc ((hrad z).1 hz)))
    (fun y hy => Ψ.apply_symm_apply (hS₂ hy))
  let _ := closedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
  have := closedDiscBundle_isManifold (IB := IB) (V := V) hd 1 one_pos
  let _ := sublevelChartedSpace I' hf hr
  let h := normClosedDiscSublevelHomeomorph (F := F) (V := V) 1 one_pos
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) h
  let D := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) h
  refine ⟨D.trans Φ₀, fun z => ?_⟩
  change (Φ₀ (h z) : M) = Ψ z
  exact hΦ₀ (h z)

end Disc

section Soul

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [CompactSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The image of the closed unit disc bundle under a partial homeomorphism-type map that is
continuous on a neighbourhood of it, followed by a second such map, is closed. -/
theorem isClosed_image_closedUnitDisc {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (j : PartialDiffeomorph I I N M ∞)
    (eN : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ eN.source)
    (hDN : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆ j.source) :
    IsClosed ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})) := by
  obtain ⟨gB, hgB, heq⟩ := (inferInstance : IsContMDiffRiemannianBundle IB ∞ F V).exists_contMDiff
  have : IsContinuousRiemannianBundle F V := ⟨gB, hgB.continuous, heq⟩
  have hc : IsCompact {z : TotalSpace F V | ‖z.2‖ ≤ 1} := isCompact_closedDiscBundle 1
  have hc' := hc.image_of_continuousOn (eN.contMDiffOn.continuousOn.mono hdisc)
  exact (hc'.image_of_continuousOn (j.contMDiffOn.continuousOn.mono hDN)).isClosed

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] in
/-- **LC38, noncompact alternative, embedding form** (master207A, A:21622). For the LC30 radial
function `η` and an LC37 packet — a model embedding `j`, the soul disc identification `eN` of
the closed unit disc bundle onto `D_N`, and the enclosure and outward transversality of
`D = j(D_N)` (the hypotheses of LC36) — and every `ρ ∈ [1/5, 2]`: a compactly supported smooth
ambient isotopy `H` with `H₁(D) = A_ρ`, and the smooth partial diffeomorphism `Ψ = H₁ ∘ j ∘ eN`,
defined near the closed unit disc bundle, carries that disc bundle onto `A_ρ = {η ≤ ρ}`. -/
theorem lc38_noncompact_sublevel_disc_embedding (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (j : PartialDiffeomorph I I N M ∞)
    (eN : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ eN.source)
    (hDN : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆ j.source)
    (hAD : {x | η x ≤ 1 / 8} ⊆
      interior ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})))
    (hDb : (j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}) ⊆ {x | η x < 3})
    (hdef : ∀ q ∈ frontier ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})),
      ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧
        ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})) ∩ U =
          {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q
          ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
            gradientFun (I := I) g η q))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      ∃ Ψ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞,
        {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ Ψ.source ∧
        (∀ z, Ψ z = Hs 1 (j (eN z))) ∧
        (Ψ : TotalSpace F V → M) '' {z | ‖z.2‖ ≤ 1} = {x | η x ≤ ρ} := by
  obtain ⟨Hs, h0, hs1, hs2, hsupp, himg⟩ := radial_core_isotopy_of_transverse g hEnorm hε1 he
    hclose hlip hW hCW hηW hgrad (isClosed_image_closedUnitDisc j eN hdisc hDN) hAD hDb hdef hρ
  refine ⟨Hs, h0, hs1, hs2, hsupp, eN.trans (j.trans (Hs 1).toPartialDiffeomorph), ?_,
    fun z => rfl, ?_⟩
  · intro z hz
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.trans_source]
    refine ⟨hdisc hz, hDN ⟨z, hz, rfl⟩, ?_⟩
    change j (eN z) ∈ (univ : Set M)
    exact mem_univ _
  · change ((Hs 1) ∘ (j : N → M) ∘ (eN : TotalSpace F V → N)) '' {z | ‖z.2‖ ≤ 1} = _
    rw [image_comp, image_comp]
    exact himg

/-- **LC38, noncompact alternative, as manifolds with boundary** (master207A, A:21622). Under the
hypotheses of `lc38_noncompact_sublevel_disc_embedding` and the dimension count
`dim (EB × F) = dim E = m + 1`: there is a globally smooth `f` equal to `η` near the band
`η⁻¹[1/8, 3]`, regular at `ρ`, with `{f ≤ ρ} = A_ρ`; with the regular-sublevel structure on
`{f ≤ ρ}` and X84's structure on the closed unit disc bundle, the map `H₁ ∘ j ∘ eN` (`H` the LC36
isotopy) is a diffeomorphism of manifolds with boundary from the disc bundle onto `A_ρ`. -/
theorem lc38_noncompact_sublevel_diffeomorph (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (j : PartialDiffeomorph I I N M ∞)
    (eN : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ eN.source)
    (hDN : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆ j.source)
    (hAD : {x | η x ≤ 1 / 8} ⊆
      interior ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})))
    (hDb : (j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}) ⊆ {x | η x < 3})
    (hdef : ∀ q ∈ frontier ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})),
      ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧
        ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})) ∩ U =
          {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q
          ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
            gradientFun (I := I) g η q))
    {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) (hE : Module.finrank ℝ E = m + 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    let I' := I.transContinuousLinearEquiv
      (ContinuousLinearEquiv.ofFinrankEq (hE.trans (Module.finrank_fin_fun ℝ).symm) :
        E ≃L[ℝ] MorseModel (m + 1))
    ∃ f : M → ℝ, ∃ hf : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f,
      ∃ hr : ∀ x, f x = ρ → mfderiv I' 𝓘(ℝ, ℝ) f x ≠ 0,
      (∀ x, f x ≤ ρ ↔ η x ≤ ρ) ∧ (∀ x, f x = ρ ↔ η x = ρ) ∧
      (∃ O : Set M, IsOpen O ∧ η ⁻¹' Icc (1 / 8) 3 ⊆ O ∧ EqOn f η O) ∧
      ∃ Hs : ℝ → Diffeomorph I I M M ∞,
        Hs 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
        (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo (1 / 8) 3 ∧
          ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
        let _ := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
        let _ := sublevelChartedSpace I' hf hr
        ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} {x : M // f x ≤ ρ} ∞,
          ∀ z, (Φ z : M) = Hs 1 (j (eN z)) := by
  intro I'
  let eM : E ≃L[ℝ] MorseModel (m + 1) :=
    ContinuousLinearEquiv.ofFinrankEq (hE.trans (Module.finrank_fin_fun ℝ).symm)
  obtain ⟨Hs, h0, hs1, hs2, hsupp, Ψ, hΨs, hΨ, hΨimg⟩ :=
    lc38_noncompact_sublevel_disc_embedding g hEnorm hε1 he hclose hlip hW hCW hηW hgrad j eN
      hdisc hDN hAD hDb hdef hρ
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hann := radialBand_subset_annulus hclose he
  have hKW : η ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ W := fun x hx =>
    hCW x (hann hx).1.le (hann hx).2.le
  obtain ⟨f, hfI, ⟨O, hO, hKO, hOW, hEq⟩, hlo, hhi⟩ :=
    exists_contMDiff_eqOn_band hη hW hηW (by norm_num : (1 / 8 : ℝ) < 3) hK hKW
  have hρb : ρ ∈ Icc (1 / 8 : ℝ) 3 := ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  have hle : ∀ x, f x ≤ ρ ↔ η x ≤ ρ := fun x => band_le_iff hEq hKO hlo hhi hρb
  have hf : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f := eM.contMDiff_transContinuousLinearEquiv_left.mpr hfI
  have hr : ∀ x, f x = ρ → mfderiv I' 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro x hx hzero
    have hηx : η x = ρ := (band_eq_iff hEq hKO hlo hhi hρb).1 hx
    have hxK : x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3 := by
      change η x ∈ Icc (1 / 8 : ℝ) 3
      rw [hηx]
      exact hρb
    have hzI : mfderiv I 𝓘(ℝ, ℝ) f x = 0 :=
      (isCriticalPointAt_transContinuousLinearEquiv_iff I eM f x).mp hzero
    have hfη : f =ᶠ[𝓝 x] η := Filter.eventuallyEq_of_mem (hO.mem_nhds (hKO hxK)) hEq
    have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ) η x :=
      (hηW.contMDiffAt (hW.mem_nhds (hKW hxK))).mdifferentiableAt (by simp)
    have hfd : HasMFDerivAt I 𝓘(ℝ, ℝ) f x (mfderiv I 𝓘(ℝ, ℝ) η x) :=
      hηd.hasMFDerivAt.congr_of_eventuallyEq hfη
    have hzη : mfderiv I 𝓘(ℝ, ℝ) η x = 0 := by
      rw [← hfd.mfderiv]
      exact hzI
    have hd0 : mvfderiv (I := I) η x = 0 := by
      unfold mvfderiv
      rw [hzη]
      rfl
    have hpos : 0 < g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := by
      have hm : 0 < 1 - (ε : ℝ) := by linarith
      exact lt_of_lt_of_le (by positivity) (hgrad x (hann hxK).1.le (hann hxK).2.le)
    rw [inner_gradientFun, hd0] at hpos
    exact lt_irrefl _ hpos
  have himg : (Ψ : TotalSpace F V → M) '' {z | ‖z.2‖ ≤ 1} = {x | f x ≤ ρ} := by
    rw [hΨimg]
    ext x
    exact (hle x).symm
  refine ⟨f, hf, hr, hle, fun x => band_eq_iff hEq hKO hlo hhi hρb, ⟨O, hO, hKO, hEq⟩, Hs, h0,
    hs1, hs2, hsupp, ?_⟩
  obtain ⟨Φ, hΦ⟩ := exists_closedDisc_diffeomorph_sublevel hd eM Ψ hΨs hf hr himg
  exact ⟨Φ, fun z => (hΦ z).trans (hΨ z)⟩

end Soul

end DifferentialGeometry.Geometry.Collapse
