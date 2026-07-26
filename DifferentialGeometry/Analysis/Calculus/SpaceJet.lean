import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import DifferentialGeometry.Analysis.Calculus.TimeJetEvolution

/-!
# Spatial jets of parameterized functions

This file contains the basic open-domain bridge from joint smoothness of a
function on `ℝ × E` to joint continuity of every spatial iterated Fréchet
derivative of its time slices.
-/

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `SpaceJetDiff q G J V` means that every spatial iterated Fréchet
derivative of the time-dependent family `G` is jointly `C^q` on `J × V`.
This is the anisotropic finite-order invariant used by the time-space
regularity bootstrap. -/
def SpaceJetDiff (q : ℕ) (G : ℝ → E → F) (J : Set ℝ) (V : Set E) : Prop :=
  ∀ r : ℕ,
    ContDiffOn ℝ q
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2)
      (J ×ˢ V)

/-- Every spatial iterated Fréchet derivative allowed by the joint regularity
of a parameterized family is jointly continuous on the same open domain. -/
theorem spaceJet_contOn
    {f : ℝ × E → F} {U : Set (ℝ × E)} {n : WithTop ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (k : ℕ) (hk : (k : WithTop ℕ∞) ≤ n) :
    ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ k (fun z : E => f (q.1, z)) q.2) U := by
  classical
  have hUniq : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hfull : ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k f q) U := by
    refine (hf.continuousOn_iteratedFDerivWithin (m := k) hk hUniq).congr ?_
    intro q hq
    exact (iteratedFDerivWithin_of_isOpen k hU hq).symm
  have hslice : ∀ q ∈ U,
      iteratedFDeriv ℝ k (fun z : E => f (q.1, z)) q.2 =
        (iteratedFDeriv ℝ k f q).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E) := by
    intro q hq
    obtain ⟨t, y⟩ := q
    set inrE : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hinrE
    set s' : Set (ℝ × E) := (fun p : ℝ × E => p + ((t, 0) : ℝ × E)) ⁻¹' U with hs'def
    have hs'_open : IsOpen s' := hU.preimage (by fun_prop)
    have hsl_open : IsOpen ((fun z : E => ((t, z) : ℝ × E)) ⁻¹' U) :=
      hU.preimage (by fun_prop)
    have hy_sl : y ∈ (fun z : E => ((t, z) : ℝ × E)) ⁻¹' U := hq
    have hpre : inrE ⁻¹' s' = (fun z : E => ((t, z) : ℝ × E)) ⁻¹' U := by
      ext z
      simp only [hs'def, hinrE, Set.mem_preimage, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    have hfun : (fun z : E => f (t, z)) =
        (fun p : ℝ × E => f (p + (t, 0))) ∘ inrE := by
      ext z
      simp only [hinrE, Function.comp_apply, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    have hfshift : ContDiffOn ℝ n (fun p : ℝ × E => f (p + (t, 0))) s' :=
      hf.comp (by fun_prop) (fun p hp => hp)
    have hinr_y : inrE y ∈ s' := by
      simp only [hs'def, hinrE, Set.mem_preimage, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
      exact hq
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right inrE hfshift
      hs'_open.uniqueDiffOn (by rw [hpre]; exact hsl_open.uniqueDiffOn) hinr_y
      (i := k) hk
    rw [hpre] at hcomp
    have htrans :
        iteratedFDerivWithin ℝ k (fun p : ℝ × E => f (p + (t, 0))) s' (inrE y) =
          iteratedFDerivWithin ℝ k f U (t, y) := by
      have hpoint : inrE y = ((0, y) : ℝ × E) := by
        simp only [hinrE, ContinuousLinearMap.inr_apply]
      rw [hpoint,
        iteratedFDerivWithin_comp_add_right k ((t, 0) : ℝ × E) ((0, y) : ℝ × E)]
      congr 1
      · ext p
        simp only [hs'def, Set.mem_vadd_set, Set.mem_preimage]
        constructor
        · rintro ⟨r, hr, rfl⟩
          rw [vadd_eq_add, add_comm (t, 0) r]
          exact hr
        · intro hp
          refine ⟨p - (t, 0), ?_, ?_⟩
          · simpa using hp
          · rw [vadd_eq_add]
            abel
      · simp
    rw [hfun, ← iteratedFDerivWithin_of_isOpen k hsl_open hy_sl, hcomp, htrans,
      iteratedFDerivWithin_of_isOpen k hU hq]
  have hrestricted : ContinuousOn
      (fun q : ℝ × E => (iteratedFDeriv ℝ k f q).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) U := by
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp_continuousOn
      hfull).congr ?_
    intro q _
    simp only [Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  exact hrestricted.congr (fun q hq => hslice q hq)

/-- At a point with enough joint differentiability, the corresponding spatial
jet of the time slices is jointly continuous at that point. -/
theorem spaceJet_contAt
    {f : ℝ × E → F} {q : ℝ × E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f q) (k : ℕ) (hk : (k : WithTop ℕ∞) ≤ n) :
    ContinuousAt
      (fun p : ℝ × E => iteratedFDeriv ℝ k (fun z : E => f (p.1, z)) p.2) q := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn hk (by simp)
  obtain ⟨v, hvu, hv, hqv⟩ := mem_nhds_iff.mp hu
  have hlocal := spaceJet_contOn hv (hfu.mono hvu) k le_rfl
  exact hlocal.continuousAt (hv.mem_nhds hqv)

/-- Smooth postcomposition preserves joint finite-order regularity of every
spatial jet.  The outer map is only required to be smooth on an open set
containing the image of the parameterized family. -/
theorem spaceJet_comp
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Φ : A → B} {u : ℝ → E → A}
    {J : Set ℝ} {V : Set E} {Ω : Set A} {q : ℕ}
    (hJ : IsOpen J) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (huΩ : Set.MapsTo (Function.uncurry u) (J ×ˢ V) Ω)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hus : ∀ t ∈ J, ContDiffOn ℝ ∞ (u t) V)
    (hu : SpaceJetDiff q u J V) :
    SpaceJetDiff q (fun t x => Φ (u t x)) J V := by
  classical
  let S : Set (ℝ × E) := J ×ˢ V
  have hS : IsOpen S := hJ.prod hV
  have huJointRaw :=
    (continuousMultilinearCurryFin0 ℝ E A).contDiff.comp_contDiffOn (hu 0)
  have huJoint : ContDiffOn ℝ q (Function.uncurry u) S :=
    huJointRaw.congr fun p _ => by
      rcases p with ⟨t, y⟩
      rfl
  have hΦjet : ∀ m : ℕ,
      ContDiffOn ℝ q (fun a => iteratedFDeriv ℝ m Φ a) Ω := by
    intro m a ha
    have hΦa : ContDiffAt ℝ ∞ Φ a :=
      (hΦ a ha).contDiffAt (hΩ.mem_nhds ha)
    exact (hΦa.iteratedFDeriv_right (m := q) (i := m)
      (by exact_mod_cast le_top)).contDiffWithinAt
  intro r
  have hterm : ∀ c : OrderedFinpartition r,
      ContDiffOn ℝ q
        (fun p : ℝ × E =>
          c.compAlongOrderedFinpartition
            (iteratedFDeriv ℝ c.length Φ (u p.1 p.2))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (u p.1) p.2)) S := by
    intro c
    have houter : ContDiffOn ℝ q
        (fun p : ℝ × E => iteratedFDeriv ℝ c.length Φ (u p.1 p.2)) S :=
      (hΦjet c.length).comp huJoint huΩ
    have hinner : ContDiffOn ℝ q
        (fun p : ℝ × E =>
          fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i) (u p.1) p.2) S :=
      contDiffOn_pi' fun i => hu (c.partSize i)
    let Lflip : ContinuousMultilinearMap ℝ
        (fun i : Fin c.length => E [×c.partSize i]→L[ℝ] A)
        ((A [×c.length]→L[ℝ] B) →L[ℝ] E [×r]→L[ℝ] B) :=
      (c.compAlongOrderedFinpartitionL ℝ E A B).flipMultilinear
    have hflip : ContDiffOn ℝ q
        (fun p : ℝ × E =>
          Lflip
            (fun i : Fin c.length =>
              iteratedFDeriv ℝ (c.partSize i) (u p.1) p.2)) S :=
      have hL : ContDiff ℝ q Lflip :=
        ContinuousMultilinearMap.contDiff
          (𝕜 := ℝ)
          (F := (A [×c.length]→L[ℝ] B) →L[ℝ] E [×r]→L[ℝ] B)
          (E := fun i : Fin c.length => E [×c.partSize i]→L[ℝ] A)
          (n := q) Lflip
      hL.comp_contDiffOn hinner
    simpa only [Lflip, ContinuousLinearMap.flipMultilinear_apply_apply,
      OrderedFinpartition.compAlongOrderedFinpartitionL_apply] using
      hflip.clm_apply houter
  have hsum : ContDiffOn ℝ q
      (fun p : ℝ × E =>
        ∑ c : OrderedFinpartition r,
          c.compAlongOrderedFinpartition
            (iteratedFDeriv ℝ c.length Φ (u p.1 p.2))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (u p.1) p.2)) S := by
    simpa using
      (ContDiffOn.sum (s := Finset.univ) fun c _ => hterm c)
  refine hsum.congr fun p hp => ?_
  have hΦp : ContDiffAt ℝ r Φ (u p.1 p.2) :=
    ((hΦ _ (huΩ hp)).contDiffAt (hΩ.mem_nhds (huΩ hp))).of_le
      (by exact_mod_cast le_top)
  have hup : ContDiffAt ℝ r (u p.1) p.2 :=
    ((hus p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2)).of_le
      (by exact_mod_cast le_top)
  simpa only [FormalMultilinearSeries.taylorComp, Function.comp_def] using
    iteratedFDeriv_comp hΦp hup le_rfl

/-- Taking one spatial Fréchet derivative preserves the anisotropic
`SpaceJetDiff` invariant. -/
theorem SpaceJetDiff.fderiv
    {G : ℝ → E → F} {J : Set ℝ} {V : Set E} {q : ℕ}
    (hG : SpaceJetDiff q G J V) :
    SpaceJetDiff q (fun t x => fderiv ℝ (G t) x) J V := by
  intro r
  let curryFun : (E [×(r + 1)]→L[ℝ] F) → E [×r]→L[ℝ] (E →L[ℝ] F) :=
    fun A => (continuousMultilinearCurryRightEquiv' ℝ r E F) A
  have hcurry : @IsBoundedLinearMap ℝ
      (E [×(r + 1)]→L[ℝ] F) (E [×r]→L[ℝ] (E →L[ℝ] F)) _
      (inferInstance : NormedAddCommGroup (E [×(r + 1)]→L[ℝ] F)).toSeminormedAddCommGroup
      (inferInstance : NormedSpace ℝ (E [×(r + 1)]→L[ℝ] F)).toModule
      (inferInstance : NormedAddCommGroup (E [×r]→L[ℝ] (E →L[ℝ] F))).toSeminormedAddCommGroup
      (inferInstance : NormedSpace ℝ (E [×r]→L[ℝ] (E →L[ℝ] F))).toModule
      curryFun :=
    IsLinearMap.with_bound
      { map_add := fun A B => by simp only [curryFun, map_add]
        map_smul := fun c A => by simp only [curryFun, map_smul] }
      1 fun A => by
        rw [one_mul]
        exact (continuousMultilinearCurryRightEquiv' ℝ r E F).norm_map A |>.le
  have hraw := hcurry.contDiff.comp_contDiffOn (hG (r + 1))
  refine hraw.congr fun p _ => ?_
  rcases p with ⟨t, x⟩
  simp only [curryFun, Function.comp_apply, iteratedFDeriv_succ_eq_comp_right,
    LinearIsometryEquiv.apply_symm_apply]

/-- The spatial derivative of an order-`r` spatial jet is jointly `C^q`
whenever the full spatial jet tower is jointly `C^q`. -/
theorem SpaceJetDiff.jet_fderiv
    {G : ℝ → E → F} {J : Set ℝ} {V : Set E} {q : ℕ}
    (hG : SpaceJetDiff q G J V) (r : ℕ) :
    ContDiffOn ℝ q
      (fun p : ℝ × E => _root_.fderiv ℝ (iteratedFDeriv ℝ r (G p.1)) p.2)
      (J ×ˢ V) := by
  let curryFun : (E [×(r + 1)]→L[ℝ] F) → E →L[ℝ] (E [×r]→L[ℝ] F) :=
    fun A =>
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) F A
  have hcurry : @IsBoundedLinearMap ℝ
      (E [×(r + 1)]→L[ℝ] F) (E →L[ℝ] (E [×r]→L[ℝ] F)) _
      (inferInstance : NormedAddCommGroup (E [×(r + 1)]→L[ℝ] F)).toSeminormedAddCommGroup
      (inferInstance : NormedSpace ℝ (E [×(r + 1)]→L[ℝ] F)).toModule
      (inferInstance : NormedAddCommGroup (E →L[ℝ] (E [×r]→L[ℝ] F))).toSeminormedAddCommGroup
      (inferInstance : NormedSpace ℝ (E →L[ℝ] (E [×r]→L[ℝ] F))).toModule
      curryFun :=
    IsLinearMap.with_bound
      { map_add := fun A B => by simp only [curryFun, map_add]
        map_smul := fun c A => by simp only [curryFun, map_smul] }
      1 fun A => by
        rw [one_mul]
        exact (continuousMultilinearCurryLeftEquiv
          ℝ (fun _ : Fin (r + 1) => E) F).norm_map A |>.le
  have hraw := hcurry.contDiff.comp_contDiffOn (hG (r + 1))
  refine hraw.congr fun p _ => ?_
  rcases p with ⟨t, x⟩
  rfl

/-- Pairing two slice-wise smooth families preserves their common
`SpaceJetDiff` order. -/
theorem SpaceJetDiff.prodMk
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → E → F} {g : ℝ → E → G}
    {J : Set ℝ} {V : Set E} {q : ℕ}
    (hV : IsOpen V)
    (hfs : ∀ t ∈ J, ContDiffOn ℝ ∞ (f t) V)
    (hgs : ∀ t ∈ J, ContDiffOn ℝ ∞ (g t) V)
    (hf : SpaceJetDiff q f J V) (hg : SpaceJetDiff q g J V) :
    SpaceJetDiff q (fun t x => (f t x, g t x)) J V := by
  intro r
  have hpair := (hf r).prodMk (hg r)
  have hraw :=
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin r => E) F G).contDiff.comp_contDiffOn
      hpair
  refine hraw.congr fun p hp => ?_
  have hfp : ContDiffAt ℝ r (f p.1) p.2 :=
    ((hfs p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2)).of_le
      (by exact_mod_cast le_top)
  have hgp : ContDiffAt ℝ r (g p.1) p.2 :=
    ((hgs p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2)).of_le
      (by exact_mod_cast le_top)
  exact iteratedFDeriv_prodMk hfp hgp le_rfl

/-- The value, first derivative, and second derivative packaged by `jet2`
inherit the same joint finite-order anisotropic regularity. -/
theorem SpaceJetDiff.jet2
    {G : ℝ → E → F} {J : Set ℝ} {V : Set E} {q : ℕ}
    (hV : IsOpen V) (hGs : ∀ t ∈ J, ContDiffOn ℝ ∞ (G t) V)
    (hG : SpaceJetDiff q G J V) :
    SpaceJetDiff q (fun t x => jet2 (G t) x) J V := by
  have hG₁s : ∀ t ∈ J,
      ContDiffOn ℝ ∞ (fun x => _root_.fderiv ℝ (G t) x) V := by
    intro t ht x hx
    have hAt : ContDiffAt ℝ ∞ (G t) x :=
      (hGs t ht x hx).contDiffAt (hV.mem_nhds hx)
    exact (hAt.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).contDiffWithinAt
  have hG₂s : ∀ t ∈ J,
      ContDiffOn ℝ ∞
        (fun x => _root_.fderiv ℝ (fun y => _root_.fderiv ℝ (G t) y) x) V := by
    intro t ht x hx
    have hAt : ContDiffAt ℝ ∞ (fun y => _root_.fderiv ℝ (G t) y) x :=
      (hG₁s t ht x hx).contDiffAt (hV.mem_nhds hx)
    exact (hAt.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).contDiffWithinAt
  have hG₁ := hG.fderiv
  have hG₂ := hG₁.fderiv
  have hderiv := hG₁.prodMk hV hG₁s hG₂s hG₂
  have hderivS : ∀ t ∈ J, ContDiffOn ℝ ∞
      (fun x =>
        (_root_.fderiv ℝ (G t) x,
          _root_.fderiv ℝ (fun y => _root_.fderiv ℝ (G t) y) x)) V := by
    intro t ht
    exact (hG₁s t ht).prodMk (hG₂s t ht)
  simpa only [jet2] using hG.prodMk hV hGs hderivS hderiv

/-- A spatial two-jet difference is bounded by a common bound for the
corresponding iterated Fréchet derivatives of orders zero, one, and two. -/
theorem jet2_sub_le
    {f g : E → F} {x : E} {B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (h₀ : ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ ≤ B)
    (h₁ : ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ ≤ B)
    (h₂ : ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 g x‖ ≤ B) :
    ‖jet2 f x - jet2 g x‖ ≤ B := by
  have h₂ne : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h₁ne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h₂top : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have hf₀ := hf.of_le (by norm_num : (0 : WithTop ℕ∞) ≤ 2)
  have hg₀ := hg.of_le (by norm_num : (0 : WithTop ℕ∞) ≤ 2)
  have hf₁ := hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hg₁ := hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hfd := hf.differentiableAt h₂ne
  have hgd := hg.differentiableAt h₂ne
  have hffdC : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
    simpa using hf.fderiv_right (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hgfdC : ContDiffAt ℝ 1 (fderiv ℝ g) x := by
    simpa using hg.fderiv_right (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hffd := hffdC.differentiableAt h₁ne
  have hgfd := hgfdC.differentiableAt h₁ne
  have hfEv : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually h₂top] with y hy
    exact hy.differentiableAt h₂ne
  have hgEv : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually h₂top] with y hy
    exact hy.differentiableAt h₂ne
  have hsubEv : (fun y => fderiv ℝ (f - g) y) =ᶠ[nhds x]
      (fun y => fderiv ℝ f y - fderiv ℝ g y) := by
    filter_upwards [hfEv, hgEv] with y hyf hyg
    exact fderiv_sub hyf hyg
  have hv : ‖f x - g x‖ ≤ B := by
    calc
      _ = ‖iteratedFDeriv ℝ 0 (f - g) x‖ :=
        (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f - g)).symm
      _ = ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ :=
        congrArg norm (iteratedFDeriv_sub_apply hf₀ hg₀)
      _ ≤ B := h₀
  have hd₁ : ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ B := by
    calc
      _ = ‖fderiv ℝ (f - g) x‖ := congrArg norm (fderiv_sub hfd hgd).symm
      _ = ‖iteratedFDeriv ℝ 1 (f - g) x‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := f - g)).symm
      _ = ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ :=
        congrArg norm (iteratedFDeriv_sub_apply hf₁ hg₁)
      _ ≤ B := h₁
  have hd₂eq : fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x =
      fderiv ℝ (fderiv ℝ (f - g)) x :=
    (fderiv_sub hffd hgfd).symm.trans hsubEv.fderiv_eq.symm
  have hd₂ : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x‖ ≤ B := by
    calc
      _ = ‖fderiv ℝ (fderiv ℝ (f - g)) x‖ := congrArg norm hd₂eq
      _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (f - g)) x‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ (f - g))).symm
      _ = ‖iteratedFDeriv ℝ 2 (f - g) x‖ := by
        simpa only [one_add_one_eq_two] using
          (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f - g) (x := x) (n := 1))
      _ = ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 g x‖ :=
        congrArg norm (iteratedFDeriv_sub_apply hf hg)
      _ ≤ B := h₂
  simp only [jet2, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_le_iff]
  exact ⟨hv, hd₁, hd₂⟩

/-- Continuity of the first three spatial iterated derivatives of a parameterized
family implies continuity of its spatial two-jet at the fixed spatial point. -/
theorem jet2_contOn
    {g : ℝ → E → F} {s : Set ℝ} {x : E}
    (h₀ : ContinuousOn (fun t => iteratedFDeriv ℝ 0 (g t) x) s)
    (h₁ : ContinuousOn (fun t => iteratedFDeriv ℝ 1 (g t) x) s)
    (h₂ : ContinuousOn (fun t => iteratedFDeriv ℝ 2 (g t) x) s) :
    ContinuousOn (fun t => jet2 (g t) x) s := by
  have hvRaw := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn h₀
  have hv : ContinuousOn (fun t => g t x) s := hvRaw.congr fun t _ => by
    simp only [Function.comp_apply, continuousMultilinearCurryFin0_apply,
      iteratedFDeriv_zero_apply]
  have hd₁Raw := (continuousMultilinearCurryFin1 ℝ E F).continuous.comp_continuousOn h₁
  have hd₁ : ContinuousOn (fun t => fderiv ℝ (g t) x) s := hd₁Raw.congr fun t _ => by
    ext v
    simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply,
      iteratedFDeriv_one_apply]
    rfl
  have hd₂Raw := (continuousMultilinearCurryRightEquiv' ℝ 1 E F).continuous.comp_continuousOn h₂
  have hd₂Raw' :=
    (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).continuous.comp_continuousOn hd₂Raw
  have hd₂ : ContinuousOn (fun t => fderiv ℝ (fun y => fderiv ℝ (g t) y) x) s :=
    hd₂Raw'.congr fun t _ => by
      ext v w
      simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply,
        continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_two_apply]
      rfl
  simpa only [jet2] using hv.prodMk (hd₁.prodMk hd₂)

end Analysis
end DifferentialGeometry
