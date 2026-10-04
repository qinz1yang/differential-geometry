import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.TwoArcSlab
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Setup
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.LevelMatch

/-!
# From a matching of the lower levels to a diffeomorphism of slabs

Lane RG03c (MD2b). `exists_slabDiffeo_of_matching` is the gluing half of
`oneSaddleSlabUniqueness`, stated for arbitrary maps `h`, `h'` between the lower levels with the
properties produced by `exists_levelMatching` or `exists_levelMatching_connected`: two strips of
the same model radius on the slabs, a level matching `ψ` (`exists_levelMatch`) and the glued maps
`glue D D' ψ h`, `glue D' D ψ⁻¹ h'` give a level-preserving diffeomorphism of the slab manifolds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse

universe uN uN'

namespace GC.Seifert.SaddleSlabProof

theorem exists_slabDiffeo_of_matching {E H : Type} {N : Type uN} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ N] {E' H' : Type} {N' : Type uN'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] [TopologicalSpace N'] [ChartedSpace H' N']
    [T2Space N'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [IsManifold I' ∞ N']
    (hdim : Module.finrank ℝ E = 2) (hdim' : Module.finrank ℝ E' = 2) {f : N → ℝ}
    {f' : N' → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f')
    {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0) {p : N} {p' : N'}
    (D : GradientLikeStrip (modelJ I hdim) f a b {p})
    (D' : GradientLikeStrip (modelJ I' hdim') f' a' b' {p'}) (hk : (ch D).k = 1)
    (hk' : (ch D').k = 1) (hr₀ : (ch D').r₀ = (ch D).r₀) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    (hrm' : 8 * (ch D').r₀ ≤ rmD D') (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b)
    (ha' : a' < f' p' - 2 * eps D) (hb' : f' p' + 2 * eps D < b') {h : N → N'} {h' : N' → N}
    (hL : ∀ z, f z = a → f' (h z) = a') (hL' : ∀ z, f' z = a' → f (h' z) = a)
    (hh : ∀ z, f z = a → h' (h z) = z) (hh' : ∀ z, f' z = a' → h (h' z) = z)
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t)
    (hH' : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h' (arc D' σ t) = arc D σ t)
    (hsm : ∀ x ∈ lowDomain D, f x ∈ Icc a b →
      ContMDiffWithinAt (modelJ I hdim) (modelJ I' hdim') ∞ (fun y => h (D.π a y))
        (f ⁻¹' Icc a b) x)
    (hsm' : ∀ x ∈ lowDomain D', f' x ∈ Icc a' b' →
      ContMDiffWithinAt (modelJ I' hdim') (modelJ I hdim) ∞ (fun y => h' (D'.π a' y))
        (f' ⁻¹' Icc a' b') x) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas hdim' hf' hab' hreg').toChartedSpace
    ∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f' a' b',
      ∀ x : slabSet f a b, (f x = a ↔ f' (e x) = a') ∧ (f x = b ↔ f' (e x) = b') := by
  have hfJ : ContMDiff (modelJ I hdim) 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf
  have hfJ' : ContMDiff (modelJ I' hdim') 𝓘(ℝ, ℝ) ∞ f' :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf'
  have hε' : eps D' = eps D := eps_eq D D' hr₀
  have hε := eps_pos D
  obtain ⟨ψ, hψm, hψa, hψb, hψ⟩ := exists_levelMatch (c := f p) (c' := f' p')
    (δ := 2 * eps D) (by linarith) ha hb ha' hb'
  have hψ'ψ : ∀ t, ψ.symm (ψ t) = t := fun t => ψ.symm_apply_apply t
  have hψψ' : ∀ t, ψ (ψ.symm t) = t := fun t => ψ.apply_symm_apply t
  have hψ' : ∀ t ∈ Icc (f' p' - 2 * eps D) (f' p' + 2 * eps D), ψ.symm t = t - f' p' + f p := by
    intro t ht
    have h1 := hψ (t - f' p' + f p) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [show t - f' p' + f p - f p + f' p' = t by ring] at h1
    calc ψ.symm t = ψ.symm (ψ (t - f' p' + f p)) := by rw [h1]
      _ = t - f' p' + f p := hψ'ψ _
  have hψ'm : StrictMono ψ.symm := fun s t hst => by
    by_contra hcon
    push Not at hcon
    have := hψm.monotone hcon
    rw [hψψ', hψψ'] at this
    linarith
  have hψ'a : ψ.symm a' = a := by rw [← hψa, hψ'ψ]
  have hψ'b : ψ.symm b' = b := by rw [← hψb, hψ'ψ]
  have hψs : ContDiff ℝ ∞ ψ := contMDiff_iff_contDiff.mp ψ.contMDiff
  have hψ's : ContDiff ℝ ∞ ψ.symm := contMDiff_iff_contDiff.mp ψ.symm.contMDiff
  have hr₀' : (ch D).r₀ = (ch D').r₀ := hr₀.symm
  have haD' : a' < f' p' - 2 * eps D' := by rw [hε']; exact ha'
  have hbD' : f' p' + 2 * eps D' < b' := by rw [hε']; exact hb'
  have hψD' : ∀ t ∈ Icc (f' p' - 2 * eps D') (f' p' + 2 * eps D'),
      ψ.symm t = t - f' p' + f p := by rw [hε']; exact hψ'
  have hHD' : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D' → h' (arc D' σ t) = arc D σ t := by
    rw [hε']; exact hH'
  have hψD : ∀ t ∈ Icc (f p - 2 * eps D') (f p + 2 * eps D'), ψ t = t - f p + f' p' := by
    rw [hε']; exact hψ
  have hHD : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D' → h (arc D σ t) = arc D' σ t := by
    rw [hε']; exact hH
  have haD : a < f p - 2 * eps D' := by rw [hε']; exact ha
  have hbD : f p + 2 * eps D' < b := by rw [hε']; exact hb
  set F := glue D D' ψ h with hF
  set G := glue D' D ψ.symm h' with hG
  have hspec : ∀ x, f x ∈ Icc a b → f' (F x) = ψ (f x) ∧ G (F x) = x := fun x hx =>
    glue_spec D D' hfJ hfJ' hk hk' hr₀ hrm hrm' ha hb ha' hb' hψm hψa hψb hψ hψ'ψ hψ' hL hh hH hH'
      hx
  have hspec' : ∀ y, f' y ∈ Icc a' b' → f (G y) = ψ.symm (f' y) ∧ F (G y) = y := fun y hy =>
    glue_spec D' D hfJ' hfJ hk' hk hr₀' hrm' hrm haD' hbD' haD hbD hψ'm hψ'a hψ'b hψD' hψψ'
      hψD hL' hh' hHD' hHD hy
  have hψI : ∀ t ∈ Icc a b, ψ t ∈ Icc a' b' := fun t ht =>
    ⟨hψa ▸ hψm.monotone ht.1, hψb ▸ hψm.monotone ht.2⟩
  have hψ'I : ∀ t ∈ Icc a' b', ψ.symm t ∈ Icc a b := fun t ht =>
    ⟨hψ'a ▸ hψ'm.monotone ht.1, hψ'b ▸ hψ'm.monotone ht.2⟩
  have hsmF : ∀ x, f x ∈ Icc a b → ContMDiffWithinAt I I' ∞ F (f ⁻¹' Icc a b) x := by
    intro x hx
    have h1 := contMDiffWithinAt_glue D D' hfJ hk hk' hr₀ hrm hrm' ha hb hψs hψ hH hsm hx
    exact (ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_right _).mp
      ((ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_left _).mp h1)
  have hsmG : ∀ y, f' y ∈ Icc a' b' → ContMDiffWithinAt I' I ∞ G (f' ⁻¹' Icc a' b') y := by
    intro y hy
    have h1 := contMDiffWithinAt_glue D' D hfJ' hk' hk hr₀' hrm' hrm haD' hbD' hψ's hψD' hHD'
      hsm' hy
    exact (ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_right _).mp
      ((ContinuousLinearEquiv.contMDiffWithinAt_transContinuousLinearEquiv_left _).mp h1)
  let C := slabAtlas hdim hf hab hreg
  let C' := slabAtlas hdim' hf' hab' hreg'
  let := C.toChartedSpace
  let := C'.toChartedSpace
  have hmem : ∀ x : slabSet f a b, f x.val ∈ Icc a b := fun x =>
    (mem_slabSet_iff hab.le x.val).mp x.2
  have hmem' : ∀ y : slabSet f' a' b', f' y.val ∈ Icc a' b' := fun y =>
    (mem_slabSet_iff hab'.le y.val).mp y.2
  have hFmem : ∀ x : slabSet f a b, F x.val ∈ slabSet f' a' b' := fun x =>
    (mem_slabSet_iff hab'.le _).mpr ((hspec x.val (hmem x)).1 ▸ hψI _ (hmem x))
  have hGmem : ∀ y : slabSet f' a' b', G y.val ∈ slabSet f a b := fun y =>
    (mem_slabSet_iff hab.le _).mpr ((hspec' y.val (hmem' y)).1 ▸ hψ'I _ (hmem' y))
  refine ⟨{ toFun := fun x => ⟨F x.val, hFmem x⟩
            invFun := fun y => ⟨G y.val, hGmem y⟩
            left_inv := fun x => Subtype.ext (hspec x.val (hmem x)).2
            right_inv := fun y => Subtype.ext (hspec' y.val (hmem' y)).2
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }, fun x => ?_⟩
  · refine (C'.contMDiff_iff_subtype_val _).mpr fun x => ?_
    have h1 := (hsmF x.val (hmem x)).comp x (C.contMDiff_subtype_val.contMDiffAt.contMDiffWithinAt
      (s := univ)) (fun z _ => hmem z)
    exact h1.contMDiffAt univ_mem
  · refine (C.contMDiff_iff_subtype_val _).mpr fun y => ?_
    have h1 := (hsmG y.val (hmem' y)).comp y
      (C'.contMDiff_subtype_val.contMDiffAt.contMDiffWithinAt (s := univ)) (fun z _ => hmem' z)
    exact h1.contMDiffAt univ_mem
  · change (f x.val = a ↔ f' (F x.val) = a') ∧ (f x.val = b ↔ f' (F x.val) = b')
    rw [(hspec x.val (hmem x)).1, ← hψa, ← hψb]
    exact ⟨hψm.injective.eq_iff.symm, hψm.injective.eq_iff.symm⟩

end GC.Seifert.SaddleSlabProof
