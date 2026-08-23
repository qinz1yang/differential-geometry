import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Pointwise

namespace DifferentialGeometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Analysis

theorem fderivWithin_iteratedFDerivWithin_apply_eq {G W : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set G} (hs : UniqueDiffOn ℝ s) (hs' : s ⊆ closure (interior s))
    (n : ℕ) {f : G → W}
    (hf : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) f s) (u : G) :
    ∀ x ∈ s,
      fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x u =
        iteratedFDerivWithin ℝ n
          (fun y => fderivWithin ℝ f s y u) s x := by
  induction n generalizing f with
  | zero =>
      intro x hx
      rw [iteratedFDerivWithin_zero_eq_comp,
        LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
      ext m
      rw [ContinuousLinearMap.comp_apply, iteratedFDerivWithin_zero_apply]
      rfl
  | succ n ih =>
      intro x hx
      set H := iteratedFDerivWithin ℝ n f s with hH_def
      set e :=
        (continuousMultilinearCurryLeftEquiv
          ℝ (fun _ : Fin (n + 1) => G) W).symm with he_def
      have hLHS :
          fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x u =
            e (fderivWithin ℝ (fderivWithin ℝ H s) s x u) := by
        rw [iteratedFDerivWithin_succ_eq_comp_left]
        rw [e.comp_fderivWithin (f := fderivWithin ℝ H s) (hs x hx)]
        rfl
      have hIHeq :
          Set.EqOn
            (iteratedFDerivWithin ℝ n
              (fun y => fderivWithin ℝ f s y u) s)
            (fun y => fderivWithin ℝ H s y u) s :=
        fun y hy => (ih (hf.of_le (by norm_cast; omega)) y hy).symm
      have hRHS :
          iteratedFDerivWithin ℝ (n + 1)
              (fun y => fderivWithin ℝ f s y u) s x =
            e (fderivWithin ℝ
              (fun y => fderivWithin ℝ H s y u) s x) := by
        rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
          fderivWithin_congr hIHeq (hIHeq hx)]
      rw [hLHS, hRHS]
      congr 1
      have hHC2 : ContDiffWithinAt ℝ 2 H s x := by
        refine (hf x hx).iteratedFDerivWithin_right hs ?_ hx
        norm_cast
        omega
      have hn2 : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) :=
        le_of_eq minSmoothness_of_isRCLikeNormedField
      have hsymH : IsSymmSndFDerivWithinAt ℝ H s x :=
        hHC2.isSymmSndFDerivWithinAt hn2 hs (hs' hx) hx
      have hHdiff :
          DifferentiableWithinAt ℝ (fderivWithin ℝ H s) s x :=
        (hHC2.fderivWithin_right hs (m := 1) le_rfl hx).differentiableWithinAt
          (by simp)
      have hflip :
          fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x =
            (fderivWithin ℝ (fderivWithin ℝ H s) s x).flip u := by
        rw [fderivWithin_clm_apply (hs x hx) hHdiff
            (differentiableWithinAt_const u),
          fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add]
      refine ContinuousLinearMap.ext (fun v => ?_)
      rw [hflip, ContinuousLinearMap.flip_apply]
      exact hsymH.eq u v

end Analysis

theorem fderiv_iter_apply
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (n : ℕ) (u : E) :
    fderiv ℝ (iteratedFDeriv ℝ n f) x u =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ f y u) x := by
  have hle :
      (((n + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hfn : ContDiffAt ℝ ((n : WithTop ℕ∞) + 2) f x :=
    hf.of_le (by simpa using hle)
  have hne : ((n : WithTop ℕ∞) + 2) ≠ ∞ :=
    Ne.symm (ne_of_beq_false rfl)
  obtain ⟨t, ht, hft⟩ :=
    hfn.contDiffOn le_rfl (fun h => (hne h).elim)
  let U : Set E := interior t
  have hU : IsOpen U := isOpen_interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr ht
  have hfU : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) f U :=
    hft.mono interior_subset
  have hUclosure : U ⊆ closure (interior U) := by
    rw [hU.interior_eq]
    exact subset_closure
  have hcomm :=
    Analysis.fderivWithin_iteratedFDerivWithin_apply_eq
      hU.uniqueDiffOn hUclosure n hfU u x hxU
  have hiter :
      Set.EqOn (iteratedFDerivWithin ℝ n f U)
        (iteratedFDeriv ℝ n f) U :=
    iteratedFDerivWithin_of_isOpen n hU
  rw [fderivWithin_congr hiter (hiter hxU),
    fderivWithin_of_isOpen hU hxU] at hcomm
  rw [iteratedFDerivWithin_of_isOpen n hU hxU] at hcomm
  have hfirst :
      (fun y => fderivWithin ℝ f U y u) =ᶠ[𝓝 x]
        fun y => fderiv ℝ f y u := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [fderivWithin_of_isOpen hU hy]
  have hright :
      iteratedFDeriv ℝ n (fun y => fderivWithin ℝ f U y u) x =
        iteratedFDeriv ℝ n (fun y => fderiv ℝ f y u) x :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hfirst n).eq_of_nhds
  exact hcomm.trans hright

theorem iterFDeriv_clm_apply
    {c : E → F →L[ℝ] G} {x : E} (hc : ContDiffAt ℝ ∞ c x)
    (n : ℕ) (u : F) (m : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => c y u) x m =
      iteratedFDeriv ℝ n c x m u := by
  have hcn : ContDiffAt ℝ n c x :=
    hc.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)
  obtain ⟨t, ht, hct⟩ := hcn.contDiffOn le_rfl (by simp)
  let U : Set E := interior t
  have hU : IsOpen U := isOpen_interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr ht
  have hcU : ContDiffOn ℝ n c U := hct.mono interior_subset
  have hwithin :=
    iteratedFDerivWithin_clm_apply_const_apply
      hU.uniqueDiffOn hcU le_rfl hxU (u := u) (m := m)
  rw [iteratedFDerivWithin_of_isOpen n hU hxU,
    iteratedFDerivWithin_of_isOpen n hU hxU] at hwithin
  exact hwithin

theorem iterFDeriv_apply₂
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {c : E → F →L[ℝ] G →L[ℝ] W} {x : E}
    (hc : ContDiffAt ℝ ∞ c x) (n : ℕ) (u : F) (v : G)
    (m : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => c y u v) x m =
      iteratedFDeriv ℝ n c x m u v := by
  calc
    iteratedFDeriv ℝ n (fun y => c y u v) x m =
        iteratedFDeriv ℝ n (fun y => c y u) x m v :=
      iterFDeriv_clm_apply
        (hc.clm_apply contDiffAt_const) n v m
    _ = iteratedFDeriv ℝ n c x m u v := by
      rw [iterFDeriv_clm_apply hc n u m]

theorem iterFDeriv_rotate
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    (iteratedFDeriv ℝ n f x).domDomCongr (finRotate n) =
      iteratedFDeriv ℝ n f x := by
  cases n with
  | zero =>
      ext v
      rfl
  | succ n =>
      ext v
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      let w : Fin (n + 1) → E := fun i => v (finRotate (n + 1) i)
      change iteratedFDeriv ℝ (n + 1) f x w =
        iteratedFDeriv ℝ (n + 1) f x v
      have hinit : Fin.init w = Fin.tail v := by
        ext i
        change v (finRotate (n + 1) i.castSucc) = v i.succ
        congr 1
        apply Fin.ext
        rw [coe_finRotate_of_ne_last i.castSucc_ne_last]
        rfl
      have hlast : w (Fin.last n) = v 0 := by
        change v (finRotate (n + 1) (Fin.last n)) = v 0
        rw [finRotate_last]
      have hDf : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x :=
        hf.fderiv_right (m := ∞) le_rfl
      calc
        iteratedFDeriv ℝ (n + 1) f x w =
            iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
              (Fin.init w) (w (Fin.last n)) :=
          iteratedFDeriv_succ_apply_right w
        _ = iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
              (Fin.tail v) (v 0) := by rw [hinit, hlast]
        _ = iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (v 0)) x
              (Fin.tail v) :=
          (iterFDeriv_clm_apply hDf n (v 0) (Fin.tail v)).symm
        _ = fderiv ℝ (iteratedFDeriv ℝ n f) x (v 0) (Fin.tail v) := by
          rw [← fderiv_iter_apply hf n (v 0)]
        _ = iteratedFDeriv ℝ (n + 1) f x v :=
          (iteratedFDeriv_succ_apply_left v).symm

private def iterFDerivStab {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ v, A (fun i => v (σ i)) = A v}
  one_mem' := by
    intro v
    rfl
  mul_mem' := by
    intro σ τ hσ hτ v
    simpa only [Equiv.Perm.mul_apply] using
      (hτ (fun i => v (σ i))).trans (hσ v)
  inv_mem' := by
    intro σ hσ v
    have h := hσ (fun i => v (σ⁻¹ i))
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using h.symm

theorem iterFDeriv_perm
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (iteratedFDeriv ℝ n f x).domDomCongr σ =
      iteratedFDeriv ℝ n f x := by
  induction n generalizing f with
  | zero =>
      have hσ : σ = 1 := Subsingleton.elim _ _
      subst σ
      ext v
      rfl
  | succ n ih =>
      cases n with
      | zero =>
          have hσ : σ = 1 := by
            apply Equiv.ext
            intro i
            exact (Fin.eq_zero (σ i)).trans
              (Fin.eq_zero ((1 : Equiv.Perm (Fin 1)) i)).symm
          subst σ
          ext v
          rfl
      | succ k =>
          let A := iteratedFDeriv ℝ (k + 2) f x
          let c : Equiv.Perm (Fin (k + 2)) := finRotate (k + 2)
          let H : Subgroup (Equiv.Perm (Fin (k + 2))) :=
            iterFDerivStab A
          have hc : c ∈ H := by
            change ∀ v, A (fun i => v (c i)) = A v
            intro v
            have hrot := iterFDeriv_rotate hf (k + 2)
            have happ := congrArg
              (fun B : ContinuousMultilinearMap ℝ
                (fun _ : Fin (k + 2) => E) F => B v) hrot
            simpa only [A, c,
              ContinuousMultilinearMap.domDomCongr_apply] using happ
          have hs : Equiv.swap (0 : Fin (k + 2)) (c 0) ∈ H := by
            cases k with
            | zero =>
                have hsc :
                    Equiv.swap (0 : Fin 2) (c 0) = c := by
                  ext i
                  fin_cases i <;> decide
                rw [hsc]
                exact hc
            | succ k =>
                change ∀ v, A
                  (fun i => v (Equiv.swap (0 : Fin (k + 3)) (c 0) i)) =
                    A v
                intro v
                let s : Equiv.Perm (Fin (k + 3)) :=
                  Equiv.swap 0 1
                let st : Equiv.Perm (Fin (k + 2)) :=
                  Equiv.swap 0 1
                have hc0 : c 0 = (1 : Fin (k + 3)) := by
                  simp only [c, finRotate_apply_zero]
                let w : Fin (k + 3) → E := fun i => v (s i)
                have hlast :
                    w (Fin.last (k + 2)) = v (Fin.last (k + 2)) := by
                  change v (Equiv.swap 0 1 (Fin.last (k + 2))) =
                    v (Fin.last (k + 2))
                  rw [Equiv.swap_apply_of_ne_of_ne] <;>
                    apply Fin.ne_of_val_ne <;> simp
                have hinit :
                    Fin.init w =
                      fun i => Fin.init v (st i) := by
                  ext i
                  change v (Equiv.swap 0 1 i.castSucc) =
                    v (Equiv.swap 0 1 i).castSucc
                  congr 1
                  apply Fin.ext
                  have hcast0 :
                      i.castSucc = (0 : Fin (k + 3)) ↔
                        i = (0 : Fin (k + 2)) := by
                    change i.castSucc = (0 : Fin (k + 2)).castSucc ↔ i = 0
                    exact Fin.castSucc_inj
                  have hcast1 :
                      i.castSucc = (1 : Fin (k + 3)) ↔
                        i = (1 : Fin (k + 2)) := by
                    change i.castSucc = (1 : Fin (k + 2)).castSucc ↔ i = 1
                    exact Fin.castSucc_inj
                  simp only [Equiv.swap_apply_def, hcast0, hcast1,
                    Fin.val_castSucc]
                  split_ifs <;> rfl
                have hDf :
                    ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x :=
                  hf.fderiv_right (m := ∞) le_rfl
                have hg :
                    ContDiffAt ℝ ∞
                      (fun y => fderiv ℝ f y (v (Fin.last (k + 2)))) x :=
                  hDf.clm_apply contDiffAt_const
                have htail := ih hg st
                have htailv := congrArg
                  (fun B : ContinuousMultilinearMap ℝ
                    (fun _ : Fin (k + 2) => E) F =>
                      B (Fin.init v)) htail
                have htailEval :
                    iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y (v (Fin.last (k + 2)))) x
                        (fun i => Fin.init v (st i)) =
                      iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y (v (Fin.last (k + 2)))) x
                        (Fin.init v) := by
                  simpa only [
                    ContinuousMultilinearMap.domDomCongr_apply] using htailv
                rw [hc0]
                change A w = A v
                calc
                  A w =
                      iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y) x
                        (Fin.init w) (w (Fin.last (k + 2))) :=
                    iteratedFDeriv_succ_apply_right w
                  _ = iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y
                          (v (Fin.last (k + 2)))) x
                        (Fin.init w) := by
                    rw [hlast]
                    exact (iterFDeriv_clm_apply hDf (k + 2)
                      (v (Fin.last (k + 2))) (Fin.init w)).symm
                  _ = iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y
                          (v (Fin.last (k + 2)))) x
                        (Fin.init v) := by
                    rw [hinit]
                    exact htailEval
                  _ = iteratedFDeriv ℝ (k + 2)
                        (fun y => fderiv ℝ f y) x
                        (Fin.init v) (v (Fin.last (k + 2))) :=
                    iterFDeriv_clm_apply hDf (k + 2)
                      (v (Fin.last (k + 2))) (Fin.init v)
                  _ = A v :=
                    (iteratedFDeriv_succ_apply_right v).symm
          have hgen :
              Subgroup.closure
                  ({c, Equiv.swap (0 : Fin (k + 2)) (c 0)} :
                    Set (Equiv.Perm (Fin (k + 2)))) =
                ⊤ := by
            exact Equiv.Perm.closure_cycle_adjacent_swap
              isCycle_finRotate support_finRotate 0
          have hclosure :
              Subgroup.closure
                  ({c, Equiv.swap (0 : Fin (k + 2)) (c 0)} :
                    Set (Equiv.Perm (Fin (k + 2)))) ≤ H := by
            rw [Subgroup.closure_le]
            intro τ hτ
            rcases hτ with hτ | hτ
            · simpa only [Set.mem_singleton_iff] using hτ ▸ hc
            · simpa only [Set.mem_singleton_iff] using hτ ▸ hs
          have hσH : σ ∈ H := by
            apply hclosure
            rw [hgen]
            trivial
          ext v
          rw [ContinuousMultilinearMap.domDomCongr_apply]
          exact hσH v

theorem iteratedDeriv_line
    {f : E → F} {x v : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 =
      iteratedFDeriv ℝ n f x (fun _ => v) := by
  have hfn : ContDiffAt ℝ n f x :=
    hf.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)
  obtain ⟨u, hu, hfu⟩ := hfn.contDiffOn le_rfl (by simp)
  let U : Set E := interior u
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hu
  have hfU : ContDiffOn ℝ n f U := hfu.mono interior_subset
  let S : Set E := (fun y : E => x + y) ⁻¹' U
  have hS_open : IsOpen S :=
    hU_open.preimage (continuous_const.add continuous_id)
  have hzeroS : (0 : E) ∈ S := by
    simpa only [S, Set.mem_preimage, add_zero] using hxU
  have hxS : x +ᵥ S = U := by
    ext y
    simp only [Set.mem_vadd_set]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [S, Set.mem_preimage, vadd_eq_add] using hz
    · intro hy
      refine ⟨y - x, ?_, ?_⟩
      · have hxy : x + (y - x) = y := by abel
        simpa only [S, Set.mem_preimage, hxy] using hy
      · rw [vadd_eq_add]
        abel
  let q : E → F := fun y => f (x + y)
  have hq : ContDiffOn ℝ n q S :=
    hfU.comp (contDiff_const.add contDiff_id).contDiffOn
      (fun y hy => hy)
  let L : ℝ →L[ℝ] E :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let T : Set ℝ := L ⁻¹' S
  have hT_open : IsOpen T := hS_open.preimage L.continuous
  have hzeroT : (0 : ℝ) ∈ T := by
    simpa only [T, Set.mem_preimage, L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, zero_smul] using hzeroS
  have hLzero : L (0 : ℝ) ∈ S := by
    exact hzeroT
  have hLzero_eq : L (0 : ℝ) = 0 := by
    simp only [L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, zero_smul]
  have hcomp :=
    L.iteratedFDerivWithin_comp_right hq hS_open.uniqueDiffOn
      hT_open.uniqueDiffOn hLzero (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hT_open hzeroT] at hcomp
  have hshift :=
    iteratedFDerivWithin_comp_add_left
      (𝕜 := ℝ) (f := f) (s := S) n x (0 : E)
  rw [add_zero, hxS,
    iteratedFDerivWithin_of_isOpen n hU_open hxU] at hshift
  change iteratedFDerivWithin ℝ n q S 0 =
    iteratedFDeriv ℝ n f x at hshift
  rw [hLzero_eq, hshift] at hcomp
  have hline : q ∘ L = fun t : ℝ => f (x + t • v) := by
    funext t
    simp only [q, Function.comp_apply, L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply]
  rw [hline] at hcomp
  have happ := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) F =>
      A (fun _ => (1 : ℝ))) hcomp
  simpa only [iteratedDeriv_eq_iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Function.comp_apply, L, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul] using happ

theorem iteratedDeriv_clm
    {f : ℝ → F} {x : ℝ} (L : F →L[ℝ] G)
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    iteratedDeriv n (fun t => L (f t)) x =
      L (iteratedDeriv n f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv,
    show (fun t => L (f t)) = L ∘ f from rfl,
    L.iteratedFDeriv_comp_left hf (by exact_mod_cast le_top)]
  rfl

theorem iteratedDeriv_apply₂
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {c : ℝ → F →L[ℝ] G →L[ℝ] W} {x : ℝ}
    (hc : ContDiffAt ℝ ∞ c x) (n : ℕ) (u : F) (v : G) :
    iteratedDeriv n (fun t => c t u v) x =
      iteratedDeriv n c x u v := by
  simpa only [iteratedDeriv_eq_iteratedFDeriv] using
    iterFDeriv_apply₂ hc n u v (fun _ => (1 : ℝ))

end DifferentialGeometry

end
