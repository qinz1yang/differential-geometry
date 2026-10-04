import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Setup
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Matching
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.LevelMatch

/-!
# Uniqueness of the one-saddle slab

Lane RG03c (MD2). `oneSaddleSlabUniqueness` proves the named Prop `OneSaddleSlabUniqueness` of
`SaddleSlabUniqueness.lean`. Both surfaces are read in the model `MorseModel 2`; at the two
saddles we take index-one Morse normal charts of one common small radius `r` and build
gradient-like strips `D`, `D'` (`exists_strip_of_radius`), so that both flows are the same model
flow `θ (y₀, -y₁)` near the saddles. With a level matching `ψ` that is a translation near the
critical values (`exists_levelMatch`) and maps `h`, `h'` between the lower levels that match the
attaching arcs (`exists_levelMatching`, built from circle parametrisations of the two lower
circles and `exists_addCircle_diffeo_arc`), the glued maps `glue D D' ψ h` and `glue D' D ψ⁻¹ h'`
are smooth on the slabs (`contMDiffWithinAt_glue`), inverse to each other and carry `f` to
`ψ ∘ f` (`glue_spec`). `exists_planarBase_of_saddleSlab'` and
`exists_planarBase_of_saddleSlab_upper'` are the two corollaries of `SaddleSlabUniqueness.lean`
without the hypothesis `hU`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Seifert.SaddleSlabProof GC.Endpoint GC.GraphManifold

universe w uN uN'

namespace GC.Seifert

private theorem exists_radius {R R' δ : ℝ} (hR : 0 < R) (hR' : 0 < R') (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ 16 * r < R ∧ 16 * r < R' ∧ 2 * r ^ 2 < δ := by
  refine ⟨min (min (R / 32) (R' / 32)) (min 1 (δ / 4)), ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by linarith) (by linarith)) (lt_min one_pos (by linarith))
  · have := (min_le_left (min (R / 32) (R' / 32)) (min 1 (δ / 4))).trans (min_le_left _ _)
    linarith
  · have := (min_le_left (min (R / 32) (R' / 32)) (min 1 (δ / 4))).trans (min_le_right _ _)
    linarith
  · set r := min (min (R / 32) (R' / 32)) (min 1 (δ / 4))
    have hr0 : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (lt_min one_pos (by linarith))
    have h1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith

theorem oneSaddleSlabUniqueness : OneSaddleSlabUniqueness.{uN, uN'} := by
  intro E H N E' H' N' _ _ _ _ _ _ _ _ _ _ _ _ _ _ I _ _ I' _ _ hdim hdim' f f' hf hf' a b a' b'
    hab hab' hreg hreg' p p' hp hp' hnd hnd' hidx hidx' huniq huniq' hcpt hcpt' hconn hconn'
    hlow hlow'
  set J := modelJ I hdim with hJ
  set J' := modelJ I' hdim' with hJ'
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf
  have hfJ' : ContMDiff J' 𝓘(ℝ, ℝ) ∞ f' :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf'
  have hregJ : ∀ x, f x = a ∨ f x = b → mfderiv J 𝓘(ℝ, ℝ) f x ≠ 0 := fun x hx hc =>
    hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
  have hregJ' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv J' 𝓘(ℝ, ℝ) f' x ≠ 0 := fun x hx hc =>
    hreg' x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I' (modelL hdim') f' x).mp hc)
  obtain ⟨c, hck, hcO⟩ := exists_saddleChart hdim hf hab hreg hp hnd hidx huniq hcpt
  obtain ⟨c', hck', hcO'⟩ := exists_saddleChart hdim' hf' hab' hreg' hp' hnd' hidx' huniq' hcpt'
  obtain ⟨r, hr, hrc, hrc', hrδ⟩ := exists_radius c.R_pos c'.R_pos
    (show 0 < min (min (f p - a) (b - f p)) (min (f' p' - a') (b' - f' p')) from
      lt_min (lt_min (by linarith [hp.1]) (by linarith [hp.2]))
        (lt_min (by linarith [hp'.1]) (by linarith [hp'.2])))
  have hδ1 := (min_le_left (min (f p - a) (b - f p)) (min (f' p' - a') (b' - f' p')))
  have hδ2 := (min_le_right (min (f p - a) (b - f p)) (min (f' p' - a') (b' - f' p')))
  have hδa := min_le_left (f p - a) (b - f p)
  have hδb := min_le_right (f p - a) (b - f p)
  have hδa' := min_le_left (f' p' - a') (b' - f' p')
  have hδb' := min_le_right (f' p' - a') (b' - f' p')
  obtain ⟨D, hk, hrD, hrm, ha, hb⟩ := exists_strip_of_radius hdim hf hab hreg hp hnd huniq hcpt
    c hck hcO hr (by linarith) (by linarith) (by linarith)
  obtain ⟨D', hk', hrD', hrm', ha', hb'⟩ := exists_strip_of_radius hdim' hf' hab' hreg' hp'
    hnd' huniq' hcpt' c' hck' hcO' hr (by linarith) (by linarith) (by linarith)
  have hr₀ : (ch D').r₀ = (ch D).r₀ := hrD'.trans hrD.symm
  have hε' : eps D' = eps D := eps_eq D D' hr₀
  rw [hε'] at ha' hb'
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
  obtain ⟨h, h', hL, hL', hh, hh', hH, hH', hsm, hsm'⟩ := exists_levelMatching D D' hfJ hfJ' hk
    hk' hr₀ hrm hrm' ha hb ha' hb' hregJ hregJ' hcpt hcpt' hconn.isPreconnected
    hconn'.isPreconnected hlow hlow'
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

theorem exists_planarBase_of_saddleSlab'
    {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (hlow : ¬ IsPreconnected (f ⁻¹' {a})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    ∃ e : planarSet.{w} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b,
      ∀ j t, f (e (pantsPlanarBase.{w}.collar j (t, halfZero))) = if j.val = 0 then b else a :=
  exists_planarBase_of_saddleSlab.{w} oneSaddleSlabUniqueness.{uN, 0} I hdim hf hab hreg hp hnd
    hidx huniq hcpt hconn hlow

theorem exists_planarBase_of_saddleSlab_upper'
    {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (hup : ¬ IsPreconnected (f ⁻¹' {b})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    ∃ e : planarSet.{w} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b,
      ∀ j t, f (e (pantsPlanarBase.{w}.collar j (t, halfZero))) = if j.val = 0 then a else b :=
  exists_planarBase_of_saddleSlab_upper.{w} oneSaddleSlabUniqueness.{uN, 0} I hdim hf hab hreg hp
    hnd hidx huniq hcpt hconn hup

end GC.Seifert
