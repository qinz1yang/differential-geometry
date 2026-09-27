import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Fiberwise
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Diffeomorph.CompactLocalIsotopy
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Tensor.LinearAlgebra.HyperplaneInterpolation
import DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import Mathlib.Analysis.Calculus.FDeriv.Mul

open Set Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_apply_tangent_of_eqOn_zeroSection
    {F : E × ℝ → E × ℝ} {U : Set E} {x : E}
    (hU : UniqueDiffWithinAt ℝ U x)
    (hfixed : ∀ y ∈ U, F (y, 0) = (y, 0)) (hx : x ∈ U)
    (hF : DifferentiableAt ℝ F (x, 0)) (v : E) :
    fderiv ℝ F (x, 0) (v, 0) = (v, 0) := by
  have hd := hF.hasFDerivAt.comp (f := fun y : E => (y, (0 : ℝ))) x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x))
  have hid := ((hasFDerivAt_id x).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)).hasFDerivWithinAt.congr hfixed (hfixed x hx)
  exact congrArg (fun L : E →L[ℝ] E × ℝ => L v)
    (hU.eq hd.hasFDerivWithinAt hid)

private theorem injective_fderiv_collar_interpolation
    {F : E × ℝ → E × ℝ} {U : Set E} {x : E}
    (hU : UniqueDiffWithinAt ℝ U x)
    (hfixed : ∀ y ∈ U, F (y, 0) = (y, 0)) (hx : x ∈ U)
    (hF : DifferentiableAt ℝ F (x, 0))
    (hpos : 0 < (fderiv ℝ F (x, 0) (0, 1)).2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective (fderiv ℝ (fun p => (1 - t) • p + t • F p) (x, 0)) := by
  let B := fderiv ℝ F (x, 0)
  have htangent (v : E) : B (v, 0) = (v, 0) :=
    fderiv_apply_tangent_of_eqOn_zeroSection hU hfixed hx hF v
  have hnormal (v : E × ℝ) : (B v).2 = (B (0, 1)).2 * v.2 := by
    rw [show v = (v.1, 0) + v.2 • (0, (1 : ℝ)) from by ext <;> simp,
      map_add, map_smul, htangent]
    simp [mul_comm]
  have hd : HasFDerivAt (fun p => (1 - t) • p + t • F p)
      ((1 - t) • ContinuousLinearMap.id ℝ (E × ℝ) + t • B) (x, 0) :=
    ((hasFDerivAt_id (x, (0 : ℝ))).const_smul (1 - t)).add
      (hF.hasFDerivAt.const_smul t)
  rw [hd.fderiv]
  exact (ContinuousLinearMap.id ℝ (E × ℝ)).toLinearMap.injective_convex_combination_of_eqOn_ker
    B.toLinearMap (ContinuousLinearMap.snd ℝ E ℝ).toLinearMap
    (ContinuousLinearMap.snd ℝ E ℝ).toLinearMap Function.injective_id
    (fun v hv => by
      change v = B v
      change v.2 = 0 at hv
      rw [show v = (v.1, 0) from Prod.ext rfl hv]
      exact (htangent v.1).symm)
    zero_lt_one hpos (by apply LinearMap.ext; intro v; exact (one_mul v.2).symm)
    (by apply LinearMap.ext; intro v; exact hnormal v) ht


theorem exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination_preserving_linear_map
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (L : E →L[ℝ] A) (hL : ∀ x ∈ W, L (F x) = L x)
    {S : Set E} (hfixed : EqOn F id (S ∩ W))
    {K : Set E} (hK : IsCompact K) (hKSW : K ⊆ S ∩ W)
    (hinj : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x))
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
        (∀ t x, L (Φ t x) = L x) ∧
        ∃ C : Set E, IsCompact C ∧ C ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ := by
  classical
  by_cases hne : K.Nonempty
  · let H : ℝ × E → E := fun z => (1 - z.1) • z.2 + z.1 • F z.2
    let G : ℝ × E → ℝ × E := fun z => (z.1, H z)
    let C : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ K
    have hC : IsCompact C := isCompact_Icc.prod hK
    have hCne : C.Nonempty := nonempty_Icc.mpr zero_le_one |>.prod hne
    have hGfixed (z : ℝ × E) (hz : z.2 ∈ S ∩ W) : G z = z := by
      simp only [G, H, hfixed hz, id_eq, ← add_smul, sub_add_cancel, one_smul]
    have hGcore (z : ℝ × E) (hz : z ∈ C) : G z = z := hGfixed z (hKSW hz.2)
    have hH : ContDiffOn ℝ ∞ H (univ ×ˢ W) :=
      ((contDiff_const.sub contDiff_fst).contDiffOn.smul contDiff_snd.contDiffOn).add
        (contDiff_fst.contDiffOn.smul (hF.comp contDiff_snd.contDiffOn (fun _ hz => hz.2)))
    have hGloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞ G C := by
      intro z
      apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_prod_of_injective_fderiv
        (isOpen_univ.prod hW) hH
      · exact ⟨mem_univ _, (hKSW z.property.2).2⟩
      · have hd : HasFDerivAt (fun p => (1 - z.val.1) • p + z.val.1 • F p)
            ((1 - z.val.1) • ContinuousLinearMap.id ℝ E + z.val.1 • fderiv ℝ F z.val.2)
            z.val.2 := ((hasFDerivAt_id z.val.2).const_smul (1 - z.val.1)).add
          (((hF.contDiffAt (hW.mem_nhds (hKSW z.property.2).2)).differentiableAt
            (by simp)).hasFDerivAt.const_smul z.val.1)
        change Function.Injective (fderiv ℝ (fun p => (1 - z.val.1) • p + z.val.1 • F p) z.val.2)
        rw [hd.fderiv]
        exact hinj _ z.property.2 _ z.property.1
    obtain ⟨φ, hCφ, hφ⟩ :=
      DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
        hGloc hC hCne (by intro z hz w hw h; rwa [hGcore z hz, hGcore w hw] at h)
    let A := φ.source ∩ (univ ×ˢ W)
    have hA : IsOpen A := φ.open_source.inter (isOpen_univ.prod hW)
    let T := A ∩ φ ⁻¹' A
    have hT : IsOpen T := (φ.contMDiffOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      hA hA
    have hCT : C ⊆ T := by
      intro z hz
      have hzA : z ∈ A := ⟨hCφ hz, mem_univ _, (hKSW hz.2).2⟩
      refine ⟨hzA, ?_⟩
      change φ z ∈ A
      rw [show φ z = z from by rw [hφ]; exact hGcore z hz]
      exact hzA
    obtain ⟨ψ, hψs, _, hψ⟩ :=
      DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
        (show IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞ φ T from
          fun z => φ.isLocalDiffeomorphAt _ _ _ z.property.1.1)
        hT (hCne.mono hCT) (φ.toPartialEquiv.injOn.mono (fun _ hz => hz.1.1))
    have hψG : ψ.toFun = G := hψ.trans hφ
    have hzero (z : ℝ × E) (hz : z ∈ A) (hzS : z.2 ∈ S) : φ z = z := by
      rw [hφ]
      exact hGfixed z ⟨hzS, hz.2.2⟩
    have hfix : ∀ z ∈ ψ.source, z.2 ∈ S → (ψ z).2 = z.2 := by
      intro z hz hzS
      rw [hψs] at hz
      rw [hψ, hzero z hz.1 hzS]
    have hreflect : ∀ z ∈ ψ.source, (ψ z).2 ∈ S → z.2 ∈ S := by
      intro z hz hzS
      rw [hψs] at hz
      rw [hψ] at hzS
      have heq : z = φ z := φ.toPartialEquiv.injOn hz.1.1 hz.2.1
        (hzero (φ z) hz.2 hzS).symm
      rw [heq]
      exact hzS
    obtain ⟨V, hV, hKV, _, Φ, hΦ, hΦi, hΦ0, htrack, hΦS, hΦL, hsupport⟩ :=
      ψ.exists_contDiff_compact_isotopy_eqOn_fibers_preserving_linear_map
        (fun z _ => by rw [hψG]) L (fun z hz => by
          rw [hψs] at hz
          rw [hψG]
          change L ((1 - z.1) • z.2 + z.1 • F z.2) = L z.2
          rw [map_add, map_smul, map_smul, hL z.2 hz.1.2.2, ← add_smul, sub_add_cancel, one_smul])
        hfix hreflect hK
        (by rw [hψs]; exact hCT) hO (by
          rintro _ ⟨z, hz, rfl⟩
          rw [hψG, hGcore z hz]
          exact ⟨mem_univ _, hKO hz.2⟩)
    refine ⟨V ∩ W, hV.inter hW, fun p hp => ⟨hKV hp, (hKSW hp).2⟩, inter_subset_right,
      Φ, hΦ, hΦi, hΦ0, ?_, hΦS, hΦL, hsupport⟩
    intro t ht p hp
    have h := htrack t ht p hp.1
    simpa only [hψG, G, H, sub_zero, one_smul, zero_smul, add_zero] using h
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, isOpen_empty, by simp [hKempty], empty_subset _, fun _ => Diffeomorph.refl _ _ ∞,
      contDiff_snd, contDiff_snd, rfl, ?_, ?_, (fun _ _ => rfl), ∅, isCompact_empty, empty_subset _, ?_⟩
    · intro _ _ _ h
      exact h.elim
    · intro _
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · intro _
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {S : Set E} (hfixed : EqOn F id (S ∩ W))
    {K : Set E} (hK : IsCompact K) (hKSW : K ⊆ S ∩ W)
    (hinj : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x))
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hKV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfixed, _, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination_preserving_linear_map
      hW hF (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) hfixed hK hKSW hinj hO hKO
  exact ⟨V, hV, hKV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfixed, hsupport⟩

theorem exists_contDiff_compact_isotopy_eqOn_fst_preserving_germ
    {F : ℝ × ℝ → ℝ × ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) {p : ℝ × ℝ} (hp : p ∈ W)
    (hfixed : F p = p) (hfirst : ∀ z ∈ W, (F z).1 = z.1)
    (hpos : 0 < (fderiv ℝ F p).det)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ Φ : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (Φ 1 : (ℝ × ℝ) → ℝ × ℝ) =ᶠ[𝓝 p] F ∧
      (∀ t z, (Φ t z).1 = z.1) ∧
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ O ∧ ∀ t,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  let B := fderiv ℝ F p
  have hd : HasFDerivAt F B p :=
    ((hF.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hBfst (v : ℝ × ℝ) : (B v).1 = v.1 := by
    have heq : (fun z => (F z).1) =ᶠ[𝓝 p] Prod.fst :=
      Filter.Eventually.mono (hW.mem_nhds hp) (fun z hz => hfirst z hz)
    have hder := hd.fst.congr_of_eventuallyEq heq.symm
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v)
      (hder.unique hasFDerivAt_fst)
  let b := (B (0, 1)).2
  have hBhor (v : ℝ) : B (0, v) = (0, b * v) := by
    rw [show ((0 : ℝ), v) = v • (0, (1 : ℝ)) by ext <;> simp, map_smul]
    apply Prod.ext
    · change v * (B (0, 1)).1 = 0
      rw [hBfst, mul_zero]
    · change v * b = b * v
      ring
  have hdet : B.det = b := by
    have h := DifferentialGeometry.Analysis.det_eq_normal_mul_of_horizontal
      B.toLinearMap (LinearMap.mulLeft ℝ b) hBhor
    change B.det = (B (1, 0)).1 * (LinearMap.mulLeft ℝ b).det at h
    rw [hBfst, LinearMap.det_mulLeft, one_mul] at h
    exact h
  have hb : 0 < b := hdet ▸ hpos
  have hinj (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • B) := by
    let T := (1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • B
    have hcoeff : 0 < 1 - t + t * b := by
      by_cases ht0 : t = 0
      · simp [ht0]
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2)
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hb)
    have hTf (z : ℝ × ℝ) : (T z).1 = z.1 := by
      change (1 - t) * z.1 + t * (B z).1 = z.1
      rw [hBfst]
      ring
    have hkernel (z : ℝ × ℝ) (hz : T z = 0) : z = 0 := by
      have hz1 : z.1 = 0 := by simpa only [hTf, Prod.fst_zero] using congrArg Prod.fst hz
      have hz' : z = (0, z.2) := Prod.ext hz1 rfl
      have hsecond := congrArg Prod.snd hz
      rw [hz'] at hsecond
      change (1 - t) * z.2 + t * (B (0, z.2)).2 = 0 at hsecond
      rw [hBhor] at hsecond
      have hz2 : z.2 = 0 := by nlinarith
      exact Prod.ext hz1 hz2
    intro x y hxy
    have hz : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hkernel _ hz)
  obtain ⟨V, hV, hpV, _, Φ, hΦ, hΦi, hΦ0, htrack, _, hΦfst, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination_preserving_linear_map
      hW hF (ContinuousLinearMap.fst ℝ ℝ ℝ) hfirst
      (S := {p}) (K := {p})
      (by rintro z ⟨rfl, _⟩; exact hfixed) isCompact_singleton
      (by intro z hz; exact ⟨hz, (mem_singleton_iff.mp hz) ▸ hp⟩)
      (by intro z hz t ht; rw [mem_singleton_iff.mp hz]; exact hinj t ht)
      hO (singleton_subset_iff.mpr hpO)
  refine ⟨Φ, hΦ, hΦi, hΦ0, ?_, hΦfst, hsupport⟩
  filter_upwards [hV.mem_nhds (hpV (mem_singleton p))] with z hz
  simpa only [sub_self, zero_smul, one_smul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ z hz

theorem exists_contDiff_compact_isotopy_eqOn_zeroSection
    [FiniteDimensional ℝ E] {F : E × ℝ → E × ℝ}
    {W : Set (E × ℝ)} (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {S : Set E} (hfixed : ∀ x ∈ S, (x, 0) ∈ W → F (x, 0) = (x, 0))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    (hKW : K ×ˢ ({0} : Set ℝ) ⊆ W)
    (hdiff : ∀ x ∈ K, UniqueDiffWithinAt ℝ S x)
    (hpos : ∀ x ∈ K, 0 < (fderiv ℝ F (x, 0) (0, 1)).2)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hKO : K ×ˢ ({0} : Set ℝ) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id (S ×ˢ ({0} : Set ℝ)) ∧
          EqOn (Φ t).symm id (S ×ˢ ({0} : Set ℝ))) ∧
        ∃ L : Set (E × ℝ), IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  apply exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination hW hF
    (S := S ×ˢ ({0} : Set ℝ))
  · rintro ⟨x, y⟩ ⟨hx, hxW⟩
    have hy : y = 0 := hx.2
    subst y
    exact hfixed x hx.1 hxW
  · exact hK.prod isCompact_singleton
  · intro p hp
    exact ⟨⟨hKS hp.1, hp.2⟩, hKW hp⟩
  · rintro ⟨x, y⟩ hx t ht
    have hy : y = 0 := hx.2
    subst y
    have hd := (hF.contDiffAt (hW.mem_nhds (hKW hx))).differentiableAt (by simp)
    have hder := ((hasFDerivAt_id (x, (0 : ℝ))).const_smul (1 - t)).add
      (hd.hasFDerivAt.const_smul t)
    rw [← hder.fderiv]
    let U := S ∩ (fun z : E => (z, (0 : ℝ))) ⁻¹' W
    have hU : UniqueDiffWithinAt ℝ U x :=
      (hdiff x hx.1).inter
        ((hW.preimage (continuous_id.prodMk continuous_const)).mem_nhds (hKW hx))
    exact injective_fderiv_collar_interpolation hU
      (fun z hz => hfixed z hz.1 hz.2) ⟨hKS hx.1, hKW hx⟩ hd (hpos x hx.1) ht
  · exact hO
  · exact hKO

theorem exists_contDiff_compact_isotopy_eqOn_collar
    [FiniteDimensional ℝ E] {F : E × ℝ → E × ℝ}
    {W : Set (E × ℝ)} (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {U : Set E} (hU : IsOpen U) (hUW : U ×ˢ ({0} : Set ℝ) ⊆ W)
    (hfixed : ∀ x ∈ U, F (x, 0) = (x, 0))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < (fderiv ℝ F (x, 0) (0, 1)).2)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hKO : K ×ˢ ({0} : Set ℝ) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id (univ ×ˢ ({0} : Set ℝ)) ∧
          EqOn (Φ t).symm id (univ ×ˢ ({0} : Set ℝ))) ∧
        ∃ S : Set (E × ℝ), IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let W' := W ∩ (U ×ˢ (univ : Set ℝ))
  obtain ⟨V, hV, hKV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_zeroSection
      (show IsOpen W' from hW.inter (hU.prod isOpen_univ))
      (hF.mono inter_subset_left) (S := univ)
      (fun x _ hx => hfixed x hx.2.1) hK (subset_univ _)
      (fun p hp => ⟨hUW ⟨hKU hp.1, hp.2⟩, hKU hp.1, mem_univ _⟩)
      (fun _ _ => uniqueDiffWithinAt_univ) hpos hO hKO
  exact ⟨V, hV, hKV, hVW.trans inter_subset_left, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hsupport⟩

private theorem normal_coefficient_eq_det_of_fixed_zeroSection
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (B : (E × ℝ) →ₗ[ℝ] (E × ℝ)) (hfixed : ∀ z, B (z, 0) = (z, 0)) :
    (B (0, 1)).2 = B.det := by
  let e := LinearEquiv.prodComm ℝ E ℝ
  let L := e.toLinearMap.comp (B.comp e.symm.toLinearMap)
  have htangent (z : E) : L (0, z) = (0, z) := by
    change (B (z, 0)).swap = (0, z)
    rw [hfixed]
    rfl
  have h := DifferentialGeometry.Analysis.det_eq_normal_mul_of_horizontal
    L LinearMap.id htangent
  have hdet : L.det = B.det := LinearMap.det_conj B e
  rw [hdet, LinearMap.det_id, mul_one] at h
  exact h.symm

theorem exists_diffeomorph_eqOn_neighborhood_of_fixed_zeroSection
    [FiniteDimensional ℝ E]
    (F : (E × ℝ) ≃ₘ[ℝ] (E × ℝ))
    {C : Set (E × ℝ)} (hC : IsCompact C) (hFc : EqOn F id Cᶜ)
    {S : Set E} (hfixed : EqOn F id (S ×ˢ ({0} : Set ℝ)))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    (hdiff : ∀ x ∈ K, UniqueDiffWithinAt ℝ S x)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hKO : K ×ˢ ({0} : Set ℝ) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∃ G : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), EqOn G F V ∧
        EqOn G id (S ×ˢ ({0} : Set ℝ)) ∧
        EqOn G.symm id (S ×ˢ ({0} : Set ℝ)) ∧
        ∃ L : Set (E × ℝ), IsCompact L ∧ L ⊆ O ∧
          EqOn G id Lᶜ ∧ EqOn G.symm id Lᶜ := by
  have hpos (x : E) (hx : x ∈ K) : 0 < (fderiv ℝ F (x, 0) (0, 1)).2 := by
    change 0 < ((fderiv ℝ F (x, 0)).toLinearMap (0, 1)).2
    rw [normal_coefficient_eq_det_of_fixed_zeroSection (fderiv ℝ F (x, 0)).toLinearMap
      (fun v => fderiv_apply_tangent_of_eqOn_zeroSection (hdiff x hx)
        (fun y hy => hfixed ⟨hy, rfl⟩) (hKS hx)
        (F.contDiff.differentiable (by simp) (x, 0)) v)]
    exact F.det_fderiv_pos_of_eqOn_compl_isCompact hC hFc (x, 0)
  obtain ⟨V, hV, hKV, _, Φ, _, _, _, htrack, hfix, L, hL, hLO, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_zeroSection isOpen_univ F.contDiff.contDiffOn
      (fun x hx _ => hfixed ⟨hx, rfl⟩) hK hKS (subset_univ _) hdiff hpos hO hKO
  refine ⟨V, hV, hKV, Φ 1, ?_, (hfix 1).1, (hfix 1).2,
    L, hL, hLO, (hsupport 1).1, (hsupport 1).2⟩
  intro z hz
  simpa only [sub_self, zero_smul, one_smul, zero_add] using htrack 1 (by simp) z hz

end Diffeomorph

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z H M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ Z H}

theorem exists_contMDiff_compact_isotopy_eqOn_collar_in_chart
    (e : OpenPartialHomeomorph M (E × ℝ))
    (he : ContMDiffOn I 𝓘(ℝ, E × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ e.symm e.target)
    {F : E × ℝ → E × ℝ} {W : Set (E × ℝ)} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) {U : Set E} (hU : IsOpen U)
    (hUW : U ×ˢ ({0} : Set ℝ) ⊆ W) (hfixed : ∀ x ∈ U, F (x, 0) = (x, 0))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < (fderiv ℝ F (x, 0) (0, 1)).2)
    (hKt : K ×ˢ ({0} : Set ℝ) ⊆ e.target)
    {S : Set M} (hS : ∀ x ∈ S ∩ e.source, (e x).2 = 0)
    {O : Set M} (hO : IsOpen O) (hKO : e.symm '' (K ×ˢ ({0} : Set ℝ)) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧ V ⊆ W ∩ e.target ∧
      ∃ Φ : ℝ → Diffeomorph I I M M ∞,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V,
          Φ t (e.symm p) = e.symm ((1 - t) • p + t • F p)) ∧
        (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
        ∃ C : Set M, IsCompact C ∧ C ⊆ O ∩ e.source ∧ ∀ t : ℝ,
          EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ := by
  let Q := e.target ∩ e.symm ⁻¹' O
  have hQ : IsOpen Q := hei.continuousOn.isOpen_inter_preimage e.open_target hO
  have hKQ : K ×ˢ ({0} : Set ℝ) ⊆ Q := fun p hp => ⟨hKt hp, hKO ⟨p, hp, rfl⟩⟩
  obtain ⟨V, hV, hKV, hVW, D, hD, hDi, hD0, htrack, hDzero, L, hL, hLQ, hfix⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_collar
      hW hF hU hUW hfixed hK hKU hpos hQ hKQ
  obtain ⟨J, hJ, hJi, hJe, hJL, hJLs, hJfix⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family e he hei D hD hDi hL
      (fun p hp => (hLQ hp).1) (fun t p hp => ⟨(hfix t).1 hp, (hfix t).2 hp⟩)
  refine ⟨V ∩ e.target, hV.inter e.open_target,
    fun p hp => ⟨hKV hp, hKt hp⟩, fun p hp => ⟨hVW hp.1, hp.2⟩,
    J, hJ, hJi, ?_, ?_, ?_, e.symm '' L, hJL, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hD0]
    by_cases hx : x ∈ e.source
    · exact (show extendChartById e (Diffeomorph.refl _ _ ∞) x = e.symm (e x) from
        if_pos hx).trans (e.left_inv hx)
    · exact if_neg hx
  · intro t ht p hp
    rw [(hJe t (e.symm p)).1]
    rw [show extendChartById e (D t) (e.symm p) = e.symm (D t (e (e.symm p))) from
      if_pos (e.map_target hp.2), e.right_inv hp.2, htrack t ht p hp.1]
  · intro t
    constructor
    · intro x hx
      rw [(hJe t x).1]
      by_cases hxs : x ∈ e.source
      · rw [show extendChartById e (D t) x = e.symm (D t (e x)) from if_pos hxs,
          (hDzero t).1 ⟨mem_univ _, hS x ⟨hx, hxs⟩⟩]
        exact e.left_inv hxs
      · exact if_neg hxs
    · intro x hx
      rw [(hJe t x).2]
      by_cases hxs : x ∈ e.source
      · rw [show extendChartById e (D t).symm x = e.symm ((D t).symm (e x)) from if_pos hxs,
          (hDzero t).2 ⟨mem_univ _, hS x ⟨hx, hxs⟩⟩]
        exact e.left_inv hxs
      · exact if_neg hxs
  · rintro x ⟨p, hp, rfl⟩
    exact ⟨(hLQ hp).2, hJLs ⟨p, hp, rfl⟩⟩
  · intro t
    exact ⟨fun x hx => (hJfix t x hx).1, fun x hx => (hJfix t x hx).2⟩

end DifferentialGeometry.Topology.Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z H M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ Z H}

theorem exists_contMDiff_compact_isotopy_eqOn_collar
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) I (E × ℝ) M ∞)
    {U : Set E} (hU : IsOpen U)
    (h₀ : U ×ˢ ({0} : Set ℝ) ⊆ φ₀.source)
    (h₁ : U ×ˢ ({0} : Set ℝ) ⊆ φ₁.source)
    (heq : ∀ x ∈ U, φ₀ (x, 0) = φ₁ (x, 0))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < (fderiv ℝ (φ₁.trans φ₀.symm) (x, 0) (0, 1)).2)
    {S : Set M} (hS : ∀ x ∈ S ∩ φ₀.target, (φ₀.symm x).2 = 0)
    {O : Set M} (hO : IsOpen O) (hKO : φ₀ '' (K ×ˢ ({0} : Set ℝ)) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧
      V ⊆ φ₀.source ∩ φ₁.source ∧
      ∃ Φ : ℝ → Diffeomorph I I M M ∞,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ p ∈ V, Φ 1 (φ₀ p) = φ₁ p) ∧
        (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
        ∃ C : Set M, IsCompact C ∧ C ⊆ O ∩ φ₀.target ∧ ∀ t : ℝ,
          EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ := by
  let F := φ₁.trans φ₀.symm
  have hUF : U ×ˢ ({0} : Set ℝ) ⊆ F.source := by
    intro p hp
    refine ⟨h₁ hp, ?_⟩
    have hp0 : p = (p.1, 0) := Prod.ext rfl hp.2
    change φ₁ p ∈ φ₀.target
    rw [hp0, ← heq p.1 hp.1]
    exact φ₀.map_source (h₀ ⟨hp.1, rfl⟩)
  have hFzero (x : E) (hx : x ∈ U) : F (x, 0) = (x, 0) := by
    change φ₀.symm (φ₁ (x, 0)) = (x, 0)
    rw [← heq x hx]
    exact φ₀.left_inv (h₀ ⟨hx, rfl⟩)
  obtain ⟨V, hV, hKV, hVsub, J, hJ, hJi, hJ0, htrack, hfix, C, hC, hCO, hsupport⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiff_compact_isotopy_eqOn_collar_in_chart
      φ₀.symm.toOpenPartialHomeomorph φ₀.symm.contMDiffOn φ₀.contMDiffOn
      F.open_source F.contMDiffOn.contDiffOn hU hUF hFzero hK hKU hpos
      (fun p hp => h₀ ⟨hKU hp.1, hp.2⟩) hS hO hKO
  refine ⟨V, hV, hKV, fun p hp => ⟨(hVsub hp).2, (hVsub hp).1.1⟩,
    J, hJ, hJi, hJ0, ?_, hfix, C, hC, hCO, hsupport⟩
  intro p hp
  have ht := htrack 1 (by simp) p hp
  have himg : φ₁ p ∈ φ₀.target := (hVsub hp).1.2
  change J 1 (φ₀ p) = φ₀ ((1 - (1 : ℝ)) • p + 1 • (φ₀.symm (φ₁ p))) at ht
  simp only [sub_self, zero_smul, one_smul, zero_add] at ht
  exact ht.trans (φ₀.right_inv himg)

end PartialDiffeomorph
